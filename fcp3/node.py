#!/usr/bin/env python
# encoding: utf-8

"""
An implementation of a freenet client library for
FCP v2, offering considerable flexibility.

Clients should instantiate FCPNode, then execute
its methods to perform tasks with FCP.

This module was written by aum, May 2006, released under the GNU Lesser General
Public License.

No warranty, yada yada

For FCP documentation, see http://wiki.freenetproject.org/FCPv2

"""

import queue
import base64
import mimetypes
import os
import pprint
import select
import hashlib
import socket
import stat
import sys
import tempfile # for doctests
import _thread
import threading
import traceback
import re
import unicodedata
import uuid
import time
from pathlib import Path, PurePosixPath, PosixPath
import _io

try:
    import magic
except ModuleNotFoundError:
    raise ModuleNotFoundError('magic module is required')

from . import pseudopythonparser

_pollInterval = 0.03


class ConnectionRefused(Exception):
    """
    cannot connect to given host/port
    """

    
class PrivacyRisk(Exception):
    """
    The following code would pose a privacy risk
    """

    
class FCPException(Exception):
    
    def __init__(self, info=None, **kw):
        #print "Creating fcp exception"
        if not info:
            info = kw
        self.info = info
        #print "fcp exception created"
        Exception.__init__(self, str(info))
    
    def __str__(self):
        
        parts = []
        for k in ['header', 'ShortCodeDescription', 'CodeDescription']:
            if k in self.info:
                parts.append(str(self.info[k]))
        return ";".join(parts) or "??"

    
class FCPGetFailed(FCPException):
    pass


class FCPPutFailed(FCPException):
    pass


class FCPProtocolError(FCPException):
    pass


class FCPNodeFailure(Exception):
    """
    node seems to have died
    """

    
class FCPSendTimeout(FCPException):
    """
    timed out waiting for command to be sent to node
    """
    pass


class FCPNodeTimeout(FCPException):
    """
    timed out waiting for node to respond
    """

    
class FCPNameLookupFailure(Exception):
    """
    name services name lookup failed
    """

    
# where we can find the freenet node FCP port
FCP_HOST = 'localhost'

FCP_PORT = 9481

FPROXY_HOST = 'localhost'

FPROXY_PORT = 8888

# may set environment vars for FCP host/port
if "FCP_HOST" in os.environ:
    FCP_HOST = os.environ["FCP_HOST"].strip()

if "FCP_PORT" in os.environ:
    FCP_PORT = int(os.environ["FCP_PORT"].strip())

# ditto for fproxy host/port
if "FPROXY_HOST" in os.environ:
    FPROXY_HOST = os.environ["FPROXY_HOST"].strip()

if "FPROXY_PORT" in os.environ:
    FPROXY_PORT = int(os.environ["FPROXY_PORT"].strip())

# poll timeout period for manager thread
POLL_TIMEOUT = 0.1
#POLL_TIMEOUT = 3

# list of keywords sent from node to client, which have
# int values
intKeys = [
    'DataLength', 'Code',
    ]

# for the FCP 'ClientHello' handshake
expectedVersion="2.0"

# logger verbosity levels
SILENT = 0
FATAL = 1
CRITICAL = 2
ERROR = 3
INFO = 4
DETAIL = 5
DEBUG = 6
NOISY = 7

# peer note types
PEER_NOTE_PRIVATE_DARKNET_COMMENT = 1

DEFAULT_VERBOSITY = CRITICAL

ONE_YEAR = 86400 * 365

COMPRESSION_CODECS = [('GZIP', 0), ('BZIP2', 1), ('LZMA', 2)] # safe defaults

fcpVersion = '0.3.4'

class FCPNode(object):
    """
    Represents an interface to a freenet node via its FCP port,
    and exposes primitives for the basic genkey, get, put and putdir
    operations as well as peer management primitives.
    
    Only one instance of FCPNode is needed across an entire
    running client application, because its methods are quite thread-safe.
    Creating 2 or more instances is a waste of resources.
    
    Clients, when invoking methods, have several options regarding flow
    control and event notification:
    
        - synchronous call (the default). Here, no pending status messages
          will ever be seen, and the call will only control when it has
          completed (successfully, or otherwise)
          
        - asynchronous call - this is invoked by passing the keyword argument
          'async=True' to any of the main primitives. When a primitive is invoked
          asynchronously, it will return a 'job ticket object' immediately. This
          job ticket has methods for polling for job completion, or blocking
          awaiting completion
          
        - setting a callback. You can pass to any of the primitives a
          'callback=somefunc' keyword arg, where 'somefunc' is a callable object
          conforming to 'def somefunc(status, value)'
          
          The callback function will be invoked when a primitive succeeds or fails,
          as well as when a pending message is received from the node.
          
          The 'status' argument passed will be one of:
              - 'successful' - the primitive succeeded, and 'value' will contain
                the result of the primitive
              - 'pending' - the primitive is still executing, and 'value' will
                contain the raw pending message sent back from the node, as a
                dict
              - 'failed' - the primitive failed, and as with 'pending', the
                argument 'value' contains a dict containing the message fields
                sent back from the node
                
          Note that callbacks can be set in both synchronous and asynchronous
          calling modes.
          
    """
    
    def __init__(self, **kw):
        """
        Create a connection object
        
        Keyword Arguments:
            - name - name of client to use with reqs, defaults to random. This
              is crucial if you plan on making persistent requests
            - host - hostname, defaults to environment variable FCP_HOST, and
              if this doesn't exist, then FCP_HOST
            - port - port number, defaults to environment variable FCP_PORT, and
              if this doesn't exist, then FCP_PORT
            - logfile - a pathname or writable file object, to which log messages
              should be written, defaults to stdout unless logfunc is specified
            - logfunc - a function to which log messages should be written or None
              for no such function should be used, defaults to None
            - verbosity - how detailed the log messages should be, defaults to 0
              (silence)
            - socket_timeout - value to pass to socket object's settimeout() if
              available and the value is not None, defaults to None
    
        Attributes of interest:
            - jobs - a dict of currently running jobs (persistent and nonpersistent).
              keys are job ids and values are JobTicket objects
    
        Notes:
            - when the connection is created, a 'hello' handshake takes place.
              After that handshake, the node sends back a list of outstanding persistent
              requests left over from the last connection (based on the value of
              the 'name' keyword passed into this constructor).
              
              This object then wraps all this info into JobTicket instances and stores
              them in the self.persistentJobs dict
                                                           
        """
        # Be sure that we have all of our attributes during __init__
        self.running = False
        self.node_is_alive = False
        self.no_close_socket = True
        self.tested_DDA = {}

        # grab and save parms
        env = os.environ
        self.name = kw.get('name', self.__get_unique_id())
        self.host = kw.get('host', env.get("FCP_HOST", FCP_HOST))
        self.port = kw.get('port', env.get("FCP_PORT", FCP_PORT))
        self.port = int(self.port)
        self.socket_timeout = kw.get('socket_timeout', None)

        #: The id for the connection
        self.connectionidentifier = None

        # set up the logger
        logfile = kw.get('logfile', None)
        logfunc = kw.get('logfunc', None)

        if logfile == None and logfunc == None:
            self.logfile = sys.stdout
        else:
            try:
                assert type(logfile) is str or type(logfile) is _io.TextIOWrapper
                self.logfile = open(logfile, 'a') if type(logfile) is str else logfile

            except AssertionError:
                raise Exception('Bad logfile "{0}", must be pathname or file object'.format(logfile))

        self.logfunc = logfunc
        self.verbosity = kw.get('verbosity', DEFAULT_VERBOSITY)
    
        # try to connect to node
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

        if self.socket_timeout != None:
            try:
                assert type(self.socket_timeout) is int
            except AssertionError:
                raise AssertionError('socket timout must be integer')

            self.socket.settimeout(self.socket_timeout)

        try:
            self.socket.connect((self.host, self.port))
        except Exception as e:
            raise type(e)(
                'Failed to connect to {0}:{1} - {2}'.format(
                    self.host, self.port, e)).with_traceback(
                        sys.exc_info()[2])
            
        # now do the hello
        self.__hello()
        self.node_is_alive = True
    
        # the pending job tickets
        self.jobs = {} # keyed by request ID
        self.keep_jobs = [] # job ids that should never be removed from self.jobs
    
        # queue for incoming client requests
        self.client_req_queue = queue.Queue()
    
        # launch receiver thread
        self.running = True
        self.shutdown_lock = threading.Lock()
        _thread.start_new_thread(self.__mgr_thread, ())
    
        # and set up the name service
        namesitefile = kw.get('namesitefile', None)
        self.namesiteInit(namesitefile)

    def __del__(self):
        """
        object is getting cleaned up, so disconnect
        """
        # terminate the node
        try:
            self.shutdown()
        except:
            traceback.print_exc()
            pass

    def __enter__(self):
        """Set up a node for use in a with-block."""
        return self

    def __exit__(self, type, value, traceback):
        """Finalize a node at the end of a with-block."""
        self.shutdown()
    

    # basic FCP primitives
    
    def gen_key(self, **kw):
        """
        Generates and returns an SSK keypair
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - usk - default False - if True, returns USK uris
            - ksk - default False - if True, returns KSK uris
            - name - the path to put at end, optional
        """

        async = kw.get('async', False)
        try:
            assert type(async) is bool
        except AssertionError:
            raise AssertionError('sync must be bool')

        callback = kw.get('callback', None)
        try:
            assert callback == None or callable(kw.get('callback', None)) == True
        except AssertionError:
            raise AssertionError('callback must be callable')


        _id = kw.get('_id', None)
        try:
            assert _id == None or type(_id) is str
        except AssertionError:
            raise AssertionError('_id must be str')

        ksk = kw.get('ksk', False)
        try:
            assert type(ksk) is bool
        except AssertionError:
            raise AssertionError('ksk must be bool')

        
        usk = kw.get('usk', False)
        try:
            assert type(usk) is bool
        except AssertionError:
            raise AssertionError('usk must be bool')

        name = kw.get('name', None)
        try:
            assert name == None or type(name) is str
        except AssertionError:
            raise AssertionError('name must be str')

        if ksk and usk:
            raise Exception('you must set one of them')

        if ksk:
            return 'KSK@{0}'.format(str(uuid.uuid4()))

        _id = _id if _id else self.__get_unique_id()

        pub, priv = self.submit_cmd(_id, 'GenerateSSK', Identifier=_id, **kw)

        if name:
            pub += name
            priv += name
    
            if usk:
                pub = '{0}{1}'.format(pub.replace('SSK@', 'USK@'), '/0')
                priv = '{0}{1}'.format(priv.replace('SSK@', 'USK@'), '/0')

        return pub, priv

    def fcp_plugin_message(self, **kw):
        """
        Sends an FCPPluginMessage and returns FCPPluginReply message contents
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - plugin_name - A name to identify the plugin. The same as class name
              shown on plugins page.
            - plugin_params - a dict() containing the key-value pairs to be sent
              to the plugin as parameters
        """

        async = kw.get('async', False)
        try:
            assert type(async) is bool
        except AssertionError:
            raise AssertionError('async must be bool')

        callback = kw.get('callback', None)
        try:
            assert callback == None or callable(callback) == True
        except AssertionError:
            raise AssertionError('callback must be callable')

        _id = kw.get('_id', None)
        try:
            assert _id== None or type(_id) is str
        except AssertionError:
            raise AssertionError('_id must be string')

        plugin_name = kw.get('plugin_name', None)
        try:
            assert type(plugin_name) is str
        except AssertionError:
            raise AssertionError('plugin_name must be string')

        _id = _id if _id else self.__get_unique_id()

        params = dict(PluginName = plugin_name,
                      Identifier = id,
                      async      = async,
                      callback   = callback)

        for key, val in kw.get('plugin_params',{}).items():
            params.update({'Param.%s' % str(key) : val})

        return self.submit_cmd(_id, 'FCPPluginMessage', **params)

    def get(self, uri, **kw):
        """
        Does a direct get of a key
    
        :param uri: the string of the uri.
    
        Keywords:
            - async - whether to return immediately with a job ticket object, default
              False (wait for completion)

            - persistence - default 'connection' - the kind of persistence for
              this request. If 'reboot' or 'forever', this job will be able to
              be recalled in subsequent FCP sessions. Other valid values are
              'reboot' and 'forever', as per FCP spec
            
            - global_queue - default false - if evaluates to true, puts this request
              on the global queue. If you set this, persistence must be 'reboot' or 'forever'
            
            - Verbosity - default 0 - sets the Verbosity mask passed in the
              FCP message - case-sensitive
            
            - priority - the PriorityClass for retrieval, default 2, may be between
              0 (highest) to 6 (lowest)
    
            - dsonly - whether to only check local datastore
            
            - ignoreds - don't check local datastore
    
            - file - if given, this is a pathname to which to store the retrieved key
            
            - follow_redirect - follow a redirect if true, otherwise fail the get
            
            - nodata - if true, no data will be returned. This can be a useful
              test of whether a key is retrievable, without having to consume
              resources by retrieving it
            
            - stream - if given, this is a writeable file object, to which the
              received data should be written a chunk at a time
            
            - timeout - timeout for completion, in seconds, default one year
    
        Returns a 3-tuple, depending on keyword args:
            - if 'file' is given, returns (mimetype, pathname) if key is returned
            - if 'file' is not given, returns (mimetype, data, msg) if key is returned
            - if 'nodata' is true, returns (mimetype, 1) if key is returned
            - if 'stream' is given, returns (mimetype, None) if key is returned,
              because all the data will have been written to the stream
        If key is not found, raises an exception
        """
        
        try:
            assert uri.startswith('SSK@') or uri.startswith('USK@') or uri.startswith('KSK@')
        except AssertionError:
            raise AssertionError('key must be started with SSK@, USK@ or KSK@')

        try:
            assert len(uri.split('@')) == 2
        except AssertionError:
             raise AssertionError('key must be good formed')

        async = kw.get('async', False)
        try:
            assert type(async) is bool
        except AssertionError:
            raise AssertionError('async must be False or True')

        persistence = kw.get('persistence', 'connection')
        try:
            assert persistence in ['connection', 'reboot', 'forever'] 
        except AssertionError:
            raise AssertionError('persistence must be connection, reboot or forever')

        global_queue = kw.get('global_queue', False)
        try:
            assert type(global_queue) is bool
        except AssertionError:
            raise AssertionError('global_queue must be bool')

        callback = kw.get('callback', None)
        try:
            assert callback == None or callable(callback) == True
        except AssertionError:
            raise AssertionError('callback must be callable')

        _id = kw.get('_id', None)
        try:
            assert _id == None or type(_id) is str
        except AssertionError:
            raise AssertionError('id must be string')

        verbosity = kw.get('verbosity', 0)
        try:
            assert type(verbosity) is int
        except AssertionError:
            raise AssertionError('verbosity must be 0 or 1')

        priority = kw.get('priority', 2)
        try:
            assert priority in range(0, 7)
        except AssertionError:
            raise AssertionError('priority must be between 0 and 6')

        dsonly = kw.get('dsonly', False)
        try:
            assert type(dsonly) is bool
        except AssertionError:
            raise AssertionError('dsonly must be bool')

        ignoreds = kw.get('ignoreds', False)
        try:
            assert type(ignoreds) is bool
        except AssertionError:
            raise AssertionError('ignoreds must be bool')

        file = kw.get('file', None)
        
        try:
            assert file == None or type(file) is str
        except AssertionError:
            raise AssertionError('file must be string path')
        
        if file:
            if not PosixPath(file).exists():
                raise FileNotFoundError('file not found {0}'.format(file))

        follow_redirect = kw.get('follow_redirect', False)
        try:
            assert type(follow_redirect) is bool
        except AssertionError:
            raise AssertionError('follow_redirect must be bool')

        nodata = kw.get('nodata', False)
        try:
            assert type(nodata) is bool
        except AssertionError:
            raise AssertionError('nodata must be bool')

        stream = kw.get('stream', None)
        try:
            assert type(stream) is _io.TextIOWrapper or stream == None
        except AssertionError:
            raise AssertionError('stream must be bool')

        wait_until_sent = kw.get('wait_until_sent', False)
        try:
            assert type(wait_until_sent) is bool
        except AssertionError:
            raise AssertionError('wait_until_sent must be bool')

        realtime = kw.get('realtime', False)
        try:
            assert type(realtime) is bool
        except AssertionError:
            raise AssertionError('realtime must be bool')

        maxretries = kw.get("maxretries", -1)
        try:
            assert type(maxretries) is int
        except AssertionError:
            raise AssertionError('maxretries must be int')

        maxsize = kw.get("maxsize", 1000000000000)
        try:
            assert maxsize > 0
        except AssertionError:
            raise AssertionError('maxsize must be integer and > than zero')

        timeout = kw.get('timeout', ONE_YEAR)
        try:
            assert timeout > 0
        except AssertionError:
            raise AssertionError('timeout must be integer and > than zero')

        self._log(INFO, 'get: uri={0}'.format(uri))

        self._log(DETAIL, 'get: kw={0}'.format(kw))

        # ---------------------------------
        # format the request
        opts = {}

        _id = kw.get('id', None) if kw.pop('id',None) else self.__get_unique_id()

        opts['async'] = async
        opts['follow_redirect'] = follow_redirect
        opts['wait_until_sent'] = wait_until_sent

        if 'callback' in kw:
            opts['callback'] = callback

        opts['Persistence'] = persistence

        opts['Global'] = global_queue

        opts['Verbosity'] = verbosity

        if global_queue and persistence == 'connection':
            raise Exception("Global requests must be persistent")

        if file:
            opts['ReturnType'] = "disk"
            opts['Filename'] = file
            # need to do a TestDDARequest to have a chance of a
            # successful get to file.
            self.testDDA(Directory=str(PurePosixPath(file).parent),
                         WantWriteDirectory=True)

        elif nodata:
            opts['ReturnType'] = "none"
        elif stream:
            opts['ReturnType'] = "direct"
            opts['stream'] = stream
        else:
            opts['ReturnType'] = "direct"

        opts['Identifier'] = _id

        opts["IgnoreDS"] = ignoreds

        opts["DSOnly"] = dsonly

        opts['realtime'] = realtime

        opts['MaxRetries'] = maxretries

        opts['MaxSize'] = maxsize

        opts['PriorityClass'] = priority

        opts['timeout'] = timeout

        opts['URI'] = uri

        # ---------------------------------
        # now enqueue the request
        return self.submit_cmd(_id, "ClientGet", **opts)

    def put(self, uri="CHK@", **kw):
        """
        Inserts a key
        
        Arguments:
            - uri - uri under which to insert the key
        
        Keywords - you must specify one of the following to choose an insert mode:
            - file - path of file from which to read the key data

            - data - the raw data of the key as string

            - redirect - the target URI to redirect to

        Keywords for 'file' mode:
            - target_file_name - human-readable target filename - default is taken from URI 
    
        Keywords for 'file' and 'data' modes:
            - chk_only - only generate CHK, don't insert - default false

            - dont_compress - do not compress on insert - default false
    
        Keywords for 'file', 'data' and 'redirect' modes:
            - mimetype - the mime type, default application/octet-stream
    
        Keywords valid for all modes:
            - async - whether to do the job asynchronously, returning a job ticket
              object (default False)

            - wait_until_sent - default False, if True, and if async=True, waits
              until the command has been sent to the node before returning a 
              job object

            - persistence - default 'connection' - the kind of persistence for
              this request. If 'reboot' or 'forever', this job will be able to
              be recalled in subsequent FCP sessions. Other valid values are
              'reboot' and 'forever', as per FCP spec

            - global_queue - default false - if evaluates to true, puts this request
              on the global queue. Note the capital G in Global. If you set this,
              persistence must be 'reboot' or 'forever'

            - Verbosity - default 0 - sets the Verbosity mask passed in the
              FCP message - case-sensitive

            - local_request_only - default False - whether to insert the data
              into only the local datastore, instead of sending it into the
              network. This does not allow others to fetch the data and is
              only useful for testing purposes.

            - maxretries - maximum number of retries, default 3

            - priority - the PriorityClass for retrieval, default 3, may be between
              0 (highest) to 6 (lowest)

            - realtime true/false - sets the RealTimeRequest flag.
    
            - timeout - timeout for completion, in seconds, default one year

            - ignore_usk_date_hints 
    
        Notes:
            - exactly one of 'file', 'data' keyword arguments must be present
        """

        try:
            assert uri.startswith('SSK@') or uri.startswith('USK@') or uri.startswith('KSK@') or uri.startswith('CHK@')
        except AssertionError:
            raise AssertionError('key must be started with SSK@, USK@, CHK@ or KSK@')

        try:
            assert len(uri.split('@')) == 2
        except AssertionError:
             raise AssertionError('key must be good formed')

        async =  kw.get('async', False)
        try:
            assert async in [False, True]
        except AssertionError:
            raise AssertionError('async must be False or True')
 
        keep  = kw.get('keep', False)
        try:
            assert keep in [False, True]
        except AssertionError:
            raise AssertionError('keep must be False or True')

        wait_until_sent =  kw.get('wait_until_sent', False)
        try:
            assert wait_until_sent in [False, True]
        except AssertionError:
            raise AssertionError('wait_until_sent must be False or True')
     
        persistence = kw.get('persistence', 'connection')
        try:
            assert persistence in ['connection', 'reboot', 'forever'] 
        except AssertionError:
            raise AssertionError('persistence must be connection, reboot or forever')

        global_queue = kw.get('global_queue', False)
        try:
            assert global_queue in [False, True] 
        except AssertionError:
            raise AssertionError('global_queue must be False or True')

        callback = kw.get('callback', None)
        try:
            assert callback == None or callable(kw.get('callback', None))
        except AssertionError:
            raise AssertionError('callback must be callable')

        _id = kw.get('_id', None)
        try:
            assert _id == None or type(_id) is str
        except AssertionError:
            raise AssertionError('id must be string')

        verbosity = kw.get('verbosity', 0)
        try:
            assert verbosity in [0, 1]
        except AssertionError:
            raise AssertionError('verbosity must be 0 or 1')

        maxretries = kw.get('maxretries', -1)
        try:
            assert maxretries in range(-1, 1000000)
        except AssertionError:
            raise AssertionError('maxretries must be integer between -1 and 999999')

        priority = kw.get('priority', 2)
        try:
            assert priority in range(0, 7)
        except AssertionError:
            raise AssertionError('priority must be between 0 and 6')

        file = kw.get('file', None)
        try:
            assert file == None or type(file) is str
        except AssertionError:
            raise AssertionError('file must be None or string path')

        data = kw.get('data', None)
        try:
            assert data == None or type(data) is str or type(data) is bytes
        except AssertionError:
            raise AssertionError('data must be None or string')

        redirect = kw.get('redirect', False)
        try:
            assert type(redirect) is bool
        except AssertionError:
            raise AssertionError('redirect must be bool')

        mime_type = kw.get('mime_type', None)
        try:
            assert mime_type == None or type(mime_type) is str
        except AssertionError:
            raise AssertionError('mime_type must be None or string')

        target_file_name = kw.get('target_file_name', None)
        try:
            assert target_file_name == None or type(target_file_name) is str
        except AssertionError:
            raise AssertionError('target_file_name must be None or string')

        target_uri = kw.get('target_uri', None)
        try:
            assert target_uri == None or type(target_uri) is str
        except AssertionError:
            raise AssertionError('target_uri must be None or string')

        local_request_only = kw.get('local_request_only', False)
        try:
            assert local_request_only in [False, True]
        except AssertionError:
            raise AssertionError('local_request_only must be False or True')

        realtime = kw.get('realtime', False)
        try:
            assert realtime in [False, True]
        except AssertionError:
            raise AssertionError('realtime must be False or True')
  
        extra_inserts_single_block = kw.get('extra_inserts_single_block', 0)
        try:
            assert extra_inserts_single_block in range(0, 3)
        except AssertionError:
            raise AssertionError('extra_inserts_single_block must be >= 0')

        dont_compress = kw.get('dont_compress', False)
        try:
            assert dont_compress in [False, True]
        except AssertionError:
            raise AssertionError('dont_compress must be False or True')

        chk_only = kw.get('chk_only', False)
        try:
            assert chk_only in [False, True]
        except AssertionError:
            raise AssertionError('chk_only must be False or True')

        timeout = kw.get('timeout', ONE_YEAR)
        try:
            assert timeout > 0
        except AssertionError:
            raise AssertionError('timeout must be integer and > than zero')

        local_Request_only = kw.get('local_Request_only', False)
        try:
            assert local_Request_only in [False, True]
        except AssertionError:
            raise AssertionError('local_Request_only must be False or True')

        ignore_usk_date_hints = kw.get('ignore_usk_date_hints', False)
        try:
            assert ignore_usk_date_hints in [False, True]
        except AssertionError:
            raise AssertionError('ignore_usk_date_hints must be False or True')


        # ---------------------------------
        # format the request
        opts = {}
    
        opts['async'] = async
        opts['wait_until_sent'] = wait_until_sent
        opts['keep'] = keep

        if callback: opts['callback'] = callback
    
        self._log(DETAIL, 'put: uri={0} async={1} wait_until_sent={2}'.format(
                            uri, opts['async'], opts['wait_until_sent']))

        opts['Persistence'] = persistence
        
        opts['Global'] = global_queue

        if global_queue and persistence == 'connection':
            raise Exception("Global requests must be persistent")
    
        if global_queue:
            # listen to the global queue
            self.listen_global()
    
        opts['URI'] = uri

        _id = _id if _id else self.__get_unique_id()
        opts['Identifier'] = _id

        if (data and file and redirect) \
            or (data and file) \
            or (data and redirect) \
            or (file and redirect):
            raise Exception('you must specify one of them: file, data or redirect')

        if data:
            if mime_type:
                opts['Metadata.ContentType'] = mime_type
            else:
                opts['Metadata.ContentType'] = 'application/octet-stream'

            opts['UploadFrom'] = 'direct'
            opts['Data'] = data
            if target_file_name:
                opts['TargetFilename'] = target_file_name

        elif file:
            opts['Metadata.ContentType'] = magic.from_file(file, mime=True).decode()
            opts['UploadFrom'] = 'disk'
            opts['Filename'] = file
            opts['FileHash'] = base64.b64encode(
            sha256dda(self.connectionidentifier, _id, 
                      path=file)).decode('utf-8')

            self.testDDA(Directory=str(PurePosixPath(file).parent),
                         WantReadDirectory=True)

        elif redirect:
            opts['UploadFrom'] = 'redirect'
            # We should check target_uri
            opts['TargetURI'] = target_uri

        elif not chk_only:
            raise Exception('Must specify file, data or redirect keywords')

        opts['Verbosity'] = verbosity
        opts['MaxRetries'] = maxretries
        opts['PriorityClass'] = priority
        opts['RealTimeFlag'] = realtime
        opts['GetCHKOnly'] = chk_only
        opts['DontCompress'] = dont_compress
        opts['ExtraInsertsSingleBlock'] = extra_inserts_single_block

        if not dont_compress:
            opts['Codecs'] = kw.get('codecs', 
                                self.default_compression_codecs_string())

        opts['LocalRequestOnly'] = local_Request_only

        if target_file_name: # for CHKs
            opts['TargetFilename'] = target_file_name

        opts['timeout'] = timeout

        opts["IgnoreUSKDatehints"] = ignore_usk_date_hints

        return self.submit_cmd(_id, 'ClientPut', **opts)

    def put_directory(self, uri, **kw):

        '''
        uri - private key
        
        directory - directory to upload without subdir
        
        site_name = 
        
        usk =
        
        version =
        
        maxretries =
        
        _id =
        
        async =
        
        persistence
        
        global_queue
        
        verbosity
        
        timeout

        priority
        
        chk_only 
        
        dont_compress 
        
        codecs

        target_filename

        default_index

        realtime
        '''

        log = self._log
        try:
            assert uri.startswith('SSK@') or uri.startswith('USK@') or uri.startswith('KSK@') or uri.startswith('CHK@')
        except AssertionError:
            raise AssertionError('key must be started with SSK@, USK@ or KSK@')

        directory = kw.get('directory', None)

        try:
            assert type(directory) is str
        except AssertionError:
            raise AssertionError('directory must be str')

        site_name = kw.get('site_name', None)
        try:
            assert type(site_name) is str
        except AssertionError:
            raise AssertionError('site_name must be str')

        usk = kw.get('usk', False)
        try:
            assert type(usk) is bool
        except AssertionError:
            raise AssertionError('usk must be bool')

        version = kw.get('version', 0)
        try:
            assert type(version) is int
        except AssertionError:
            raise AssertionError('version must be int')

        _id =  kw.get('_id', None)
        assert type(_id) is str or _id == None

        async = kw.get('async', False)
        assert type(async) is bool
        
        wait_until_sent = kw.get('wait_until_sent', False)
        assert type(wait_until_sent) is bool

        persistence = kw.get('persistence', 'connection')
        assert persistence in ['connection', 'reboot', 'forever']

        global_queue = kw.get('global_queue', False)
        assert type(global_queue) is bool

        verbosity = kw.get('verbosity', 0)
        assert verbosity == 0 or verbosity == 1

        timeout = kw.get('timeout', ONE_YEAR)
        assert timeout > 0

        priority = kw.get('priority', 2)
        assert priority in range(0,7)

        chk_only = kw.get('chk_only', False)
        assert type(chk_only) is bool

        dont_compress = kw.get('dont_compress', True)
        assert type(dont_compress) is bool

        target_filename = kw.get('target_filename', False)
        assert type(target_filename) is bool
        
        realtime = kw.get('realtime', False)
        assert type(realtime) is bool
        
        maxretries = kw.get('maxretries', -1)
        assert type(maxretries) is int
        
        default_index = kw.get('default_index', 'index.html')
        assert type(default_index) is str
        
        callback = kw.get('callback', False)
        assert type(callback) is bool or callable(callback)

        full_uri = '{0}{1}/'.format(uri, site_name)

        upload_from = kw.get('upload_from', 'disk')
        assert type(upload_from) is str and upload_from in ['direct', 'disk', 'redirect']

        if usk:
            full_uri = uri.replace('SSK@', 'USK@')
            full_uri = full_uri.split('/')[0]
            full_uri = '{0}/{1}/{2}'.format(full_uri, site_name, version)

        if not _id:
            _id = self.__get_unique_id()

        if global_queue:
            persistence = 'forever'
            self.listen_global()
        else:
            persistence = 'connection'

        codecs = kw.get('codecs', 
                self.default_compression_codecs_string())

        files = list(Path(directory).glob('*'))
        jobs = []

        if upload_from == 'redirect' :
            log(INFO, 'put_directoru: starting inserts')
            for index, file in enumerate(files):
                raw = Path(file)
                job = self.put("CHK@",
                                data = raw.read_bytes(),
                                mime_type = magic.from_file(str(file), mime=True).decode(),
                                async = True,
                                wait_until_sent = True,
                                verbosity = verbosity,
                                chk_only = False,
                                priority = priority,
                                global_queue = global_queue,
                                persistence = persistence,
                                maxretries=maxretries,
                                target_file_name = file.name)

                total = len(files)
                reset = total - index
                complete = total - reset

                log(INFO, 'put_directory: waiting inserts total={0} complete{1} reset={2}'.format(total,reset,complete))
                job.wait()
                jobs.append({'target_uri' : job.result, 'file_full_path' : str(file), 'file_relative_path' : str(file.name),
                             'mime_type' : magic.from_file(str(file), mime=True).decode()})

        data_to_append = []
        msg_lines = ['ClientPutComplexDir',
                    'Identifier={0}'.format(_id),
                    'Verbosity={0}'.format(verbosity),
                    'MaxRetries={0}'.format(maxretries),
                    'PriorityClass={0}'.format(priority), 
                    'URI={0}'.format(full_uri),
                    'Persistence={0}'.format(persistence),
                    'Global={0}'.format(global_queue),
                    'DefaultName={0}'.format(default_index),
                    ]

        if upload_from == 'redirect' :
            for index, job in enumerate(jobs):
            
                if isinstance(job['target_uri'], Exception):
                    log(ERROR, 'File {0} failed to insert'.format(job['file_relative_path']))
                    continue

                log(DETAIL, 'n={0} relpath={1}'.format(repr(index), repr(job['file_relative_path'])))

                msg_lines.extend(['Files.{0}.Name={1}'.format(index, job['file_relative_path'])])

                if not job['target_uri']:
                    raise Exception('Can\'t find a URI for file {0}'.format(job['file_relative_path']))

                msg_lines.extend(['Files.{0}.UploadFrom=redirect'.format(index),
                                  'Files.{0}.TargetURI={1}'.format(index, job['target_uri'])])

        elif upload_from == 'disk':
            self.testDDA(Directory = directory,
                         WantReadDirectory = True)
            for index, file in enumerate(files):

                msg_lines.extend(["Files.%d.UploadFrom=disk" % index,
                                  'Files.%d.Name=%s' %(index, str(file.name)),
                                  "Files.%d.Filename=%s" % (index, str(file)),
                                  "Files.%d.Metadata.ContentType=%s" % (index, magic.from_file(str(file), mime=True).decode()),
                                  ])
        else:
            for index, file in enumerate(files):

                data = open(str(file), 'rb').read()
                data_to_append.append(data)

                msg_lines.extend(["Files.%d.UploadFrom=direct" % index,
                                  'Files.%d.Name=%s' %(index, str(file.name)),
                                  "Files.%d.DataLength=%s" % (index, str(file.stat().st_size)),
                                  "Files.%d.Metadata.ContentType=%s" % (index, magic.from_file(str(file), mime=True).decode()),
                                  ])
        
        # finish the command buffer
        if data_to_append:
            msg_lines.append("Data")
        else:
            msg_lines.append("EndMessage")

        manifest_insert_cmd_buf = b"\n".join(i.encode("utf-8") for i in msg_lines) + b"\n"
        manifest_insert_cmd_buf += b"".join(data_to_append)

        # gotta log the command buffer here, since it's not sent via .put()
        for line in msg_lines:
            log(DETAIL, line)
        
        # now dispatch the manifest insertion job
        if chk_only:
            return "no_uri"
        else:
            if dont_compress:
                return self.submit_cmd(
                                _id, 'ClientPutComplexDir',
                                rawcmd = manifest_insert_cmd_buf,
                                async = async,
                                Global = global_queue,
                                persistence = persistence,
                                wait_until_sent = wait_until_sent,
                                DontCompress = dont_compress,
                                callback = callback)
            else:
                return self.submit_cmd(
                                _id, 'ClientPutComplexDir',
                                rawcmd = manifest_insert_cmd_buf,
                                async = async,
                                Global = global_queue,
                                persistence = persistence,
                                wait_until_sent = wait_until_sent,
                                DontCompress = dont_compress,
                                Codecs = codecs,
                                callback = callback)
 
    def modify_config(self, **kw):
        """
        Modifies node configuration
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - keywords, which are the same as for the FCP message and documented in the wiki: http://wiki.freenetproject.org/FCP2p0ModifyConfig
        """
        return self.submit_cmd("__global", "ModifyConfig", **kw)
    

    def get_config(self, **kw):
        """
        Gets node configuration
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - WithCurrent - default False - if True, the current configuration settings will be returned in the "current" tree of the ConfigData message fieldset
            - WithShortDescription - default False - if True, the configuration setting short descriptions will be returned in the "shortDescription" tree of the ConfigData message fieldset
            - other keywords, which are the same as for the FCP message and documented in the wiki: http://wiki.freenetproject.org/FCP2p0GetConfig
        """
        
        return self.submit_cmd("__global", "GetConfig", **kw)
    

    def invert_private(self, private_key):
        """
        Converts an SSK or USK private key to a public equivalent
        """
        is_str = type(private_key) is str

        if is_str:
            private_key = private_key.encode('utf-8')
                
        is_usk = private_key.startswith(b'USK@')
        
        if is_usk:
            private_key = private_key.replace(b'USK@', b'SSK@')
    
        bits = private_key.split(b'/', 1)
        mainUri = bits[0].decode('utf-8')
    
        uri = self.put(mainUri+'/foo', data=b'bar', chk_only = True)
    
        uri = uri.split('/')[0].encode('utf-8')
        uri = b'/'.join([uri] + bits[1:])
    
        if is_usk:
            uri = uri.replace(b'SSK@', b'USK@')

        if is_str:
            return uri.decode('utf-8')
        return uri

    def redirect(self, src_key, des_key, **kw):
        """
        Inserts key srcKey, as a redirect to destKey.
        srcKey must be a KSK, or a path-less SSK or USK (and not a CHK)
        """
        uri = self.put(src_key, redirect=des_key, **kw)
    
        return uri
    

    def gen_chk(self, **kw):
        """
        Returns the CHK URI under which a data item would be
        inserted.
        
        Keywords - you must specify one of the following:
            - file - path of file from which to read the key data
            - data - the raw data of the key as string
    
        Keywords - optional:
            - mimetype - defaults to text/plain - THIS AFFECTS THE CHK!!
        """
        return self.put(chk_only=True, **kw)
    

    def list_peers(self, **kw):
        """
        Gets the list of peers from the node
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - WithMetadata - default False - if True, returns a peer's metadata
            - WithVolatile - default False - if True, returns a peer's volatile info
        """
        
        return self.submit_cmd("__global", "ListPeers", **kw)
    

    def list_peer_notes(self, **kw):
        """
        Gets the list of peer notes for a given peer from the node
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - NodeIdentifier - one of name, identity or IP:port for the desired peer
        """
        
        return self.submit_cmd("__global", "ListPeerNotes", **kw)
    

    def ref_stats(self, **kw):
        """
        Gets node reference and possibly node statistics.
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - GiveOpennetRef - default False - if True, return the node's Opennet reference rather than the node's Darknet reference
            - WithPrivate - default False - if True, includes the node's private node reference fields
            - WithVolatile - default False - if True, returns a node's volatile info
        """
        # The GetNode answer has no id, so we have to use __global.
        return self.submit_cmd("__global", "GetNode", **kw)
    

    def testDDA(self, **kw):
        """
        Test for Direct Disk Access capability on a directory (can the node and the FCP client both access the same directory?)
        
        Keywords:
            - callback - if given, this should be a callable which accepts 2
                arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - Directory - directory to test
            - WantReadDirectory - default False - if True, want node to read from directory for a put operation
            - WantReadDirectory - default False - if True, want node to write to directory for a get operation
        """
        # cache the testDDA:
        
        directory = kw.get('Directory', None)

        try:
            assert type(directory) is str
        except AssertionError:
            raise AssertionError('directory must be path str')

        if not Path(directory).exists():
            raise FileNotFoundError('directory not found')

        want_read_directory = kw.get('WantReadDirectory', False)
        try:
            assert type(want_read_directory) is bool
        except AssertionError:
            raise AssertionError('want_read_directory must be bool')

        want_write_directory = kw.get('WantWriteDirectory', False)
        try:
            assert type(want_write_directory) is bool
        except AssertionError:
            raise AssertionError('want_write_directory must be bool')

        DDAkey = (directory, want_read_directory, want_write_directory)

        try:
            return self.tested_DDA[DDAkey]
        except KeyError:
            pass # we actually have to test this dir.

        try:
            opts = {'Directory' : directory, 
                    'WantReadDirectory' : want_read_directory, 
                    'WantWriteDirectory' : want_write_directory}

            request_result = self.submit_cmd('__global', 'TestDDARequest', **opts)
        except FCPProtocolError as e:
            self._log(DETAIL, str(e))
            return False

        write_filename = None
        opts = {}
        opts['Directory'] = request_result['Directory']
        if 'ReadFilename' in request_result:
            read_filename = request_result['ReadFilename']
            read_file = Path(read_filename)

            if read_file.exists():
                read_file_contents = read_file.read_text('utf-8')
            else:
                read_file_contents = ''

            opts['ReadFilename'] = read_filename
            opts['ReadContent'] = read_file_contents
            
        if 'WriteFilename' in request_result and 'ContentToWrite' in request_result:
            write_filename = request_result['WriteFilename']
            content_to_write = request_result['ContentToWrite'].encode('utf-8')
            write_file = pathlib.Path(write_filename)

            if write_file.exists():
                write_file.write_bytes(content_to_write.encode('utf-8'))
                write_file_stat_object = os.stat(write_filename)
                write_file_mode = write_file_stat_object.st_mode
                os.chmod(write_filename, write_file_mode | stat.S_IREAD | stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
                
        response_result = self.submit_cmd("__global", "TestDDAResponse", **opts)

        if write_filename is not None:
            file_to_delete = pathlib.Path(write_filename)
            file_to_delete.unlink()

        # cache this result, so we do not calculate it twice.
        self.tested_DDA[DDAkey] = response_result
        return response_result

    def add_peer(self, **kw):
        """
        Add a peer to the node
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - File - filepath of a file containing a noderef in the node's directory
            - URL - URL of a copy of a peer's noderef to add
            - kwdict - If neither File nor URL are provided, the fields of a noderef can be passed in the form of a Python dictionary using the kwdict keyword
        """
        
        return self.submit_cmd("__global", "AddPeer", **kw)
    

    def list_peer(self, **kw):
        """
        Modify settings on one of the node's peers
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - NodeIdentifier - one of name (except for opennet peers), identity or IP:port for the desired peer
        """
        
        return self.submit_cmd("__global", "ListPeer", **kw)
    

    def modify_peer(self, **kw):
        """
        Modify settings on one of the node's peers
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - IsDisabled - default False - enables or disabled the peer accordingly
            - IsListenOnly - default False - sets ListenOnly on the peer
            - NodeIdentifier - one of name, identity or IP:port for the desired peer
        """
        
        return self.submit_cmd("__global", "ModifyPeer", **kw)
    

    def modify_peer_note(self, **kw):
        """
        Modify settings on one of the node's peers
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - NodeIdentifier - one of name, identity or IP:port for the desired peer
            - NoteText - base64 encoded string of the desired peer note text
            - PeerNoteType - code number of peer note type: currently only private peer note is supported by the node with code number 1 
        """
        
        return self.submit_cmd("__global", "ModifyPeerNote", **kw)
    

    def remove_peer(self, **kw):
        """
        Removes a peer from the node
        
        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object
            - callback - if given, this should be a callable which accepts 2
              arguments:
                  - status - will be one of 'successful', 'failed' or 'pending'
                  - value - depends on status:
                      - if status is 'successful', this will contain the value
                        returned from the command
                      - if status is 'failed' or 'pending', this will contain
                        a dict containing the response from node
            - NodeIdentifier - one of name, identity or IP:port for the desired peer
        """
        
        return self.submit_cmd("__global", "RemovePeer", **kw)
    

    # methods for namesites
    def namesiteInit(self, path):
        """
        Initialise the namesites layer and load our namesites list
        """
        if path:
            self.namesiteFile = path
        else:
            self.namesiteFile = os.path.join(os.path.expanduser("~"), ".freenames")
    
        self.namesiteLocals = []
        self.namesitePeers = []
    
        # create empty file 
        if os.path.isfile(self.namesiteFile):
            self.namesiteLoad()
        else:
            self.namesiteSave()
    

    def namesiteLoad(self):
        """
        """
        try:
            parser = pseudopythonparser.Parser()
            env = parser.parse(open(self.namesiteFile).read())
            self.namesiteLocals = env['locals']
            self.namesitePeers = env['peers']
        except:
            traceback.print_exc()
            env = {}
    

    def namesiteSave(self):
        """
        Save the namesites list
        """
        f = open(self.namesiteFile, "w")
    
        f.write("# pyFreenet namesites registration file\n\n")
    
        pp = pprint.PrettyPrinter(width=72, indent=2, stream=f)
    
        f.write("locals = ")
        pp.pprint(self.namesiteLocals)
        f.write("\n")
    
        f.write("peers = ")
        pp.pprint(self.namesitePeers)
        f.write("\n")
    
        f.close()
    

    def namesiteAddLocal(self, name, privuri=None):
        """
        Create a new nameservice that we own
        """
        if not privuri:
            privuri = self.genkey()[1]
        puburi = self.invert_private(privuri)
        
        privuri = self.namesiteProcessUri(privuri)
        puburi = self.namesiteProcessUri(puburi)
    
        for rec in self.namesiteLocals:
            if rec['name'] == name:
                raise Exception("Already got a local service called '%s'" % name)
        
        self.namesiteLocals.append(
            {'name':name,
             'privuri':privuri,
             'puburi': puburi,
             'cache': {},
            })
    
        self.namesiteSave()
    

    def namesiteDelLocal(self, name):
        """
        Delete a local nameservice
        """
        rec = None
        for r in self.namesiteLocals:
            if r['name'] == name:
                self.namesiteLocals.remove(r)
    
        self.namesiteSave()
    

    def namesiteAddRecord(self, localname, domain, uri):
        """
        Adds a (domainname -> uri) record to one of our local
        services
        """
        rec = None
        for r in self.namesiteLocals:
            if r['name'] == localname:
                rec = r
        if not rec:
            raise Exception("No local service '%s'" % localname)
    
        cache = rec['cache']
    
        # bail if domain is known and is pointing to same uri
        if cache.get(domain, None) == uri:
            return
    
        # domain is new, or uri has changed
        cache[domain] = uri
    
        # save local records
        self.namesiteSave()
    
        # determine the insert uri
        localPrivUri = rec['privuri'] + "/" + domain + "/0"
    
        # and stick it in, via global queue
        id = "namesite|%s|%s|%s" % (localname, domain, int(time.time()))
        self.put(
            localPrivUri,
            id=id,
            data=uri,
            persistence="forever",
            Global=True,
            priority=0,
            async=True,
            )
    
        self.refresh_persistent_requests()
    

    def namesiteDelRecord(self, localname, domain):
        """
        Removes a domainname record from one of our local
        services
        """
        rec = None
        for r in self.namesiteLocals:
            if r['name'] == localname:
                if domain in r['cache']:
                    del r['cache'][domain]
    
        self.namesiteSave()
    

    def namesiteAddPeer(self, name, uri):
        """
        Adds a namesite to our list
        """
        # process URI
        uri = uri.split("freenet:")[-1]
    
        # validate uri TODO reject private uris
        if not uri.startswith("USK"):
            raise Exception("Invalid URI %s, should be a public USK" % uri)
    
        # just uplift the public key part, remove path
        uri = uri.split("freenet:")[-1]
        uri = uri.split("/")[0]
    
        if self.namesiteHasPeer(name):
            raise Exception("Peer nameservice '%s' already exists" % name)
    
        self.namesitePeers.append({'name':name, 'puburi':uri})
    
        self.namesiteSave()
    

    def namesiteHasPeer(self, name):
        """
        returns True if we have a peer namesite of given name
        """    
        return self.namesiteGetPeer(name) is not None
    

    def namesiteGetPeer(self, name):
        """
        returns record for given peer
        """
        for rec in self.namesitePeers:
            if rec['name'] == name:
                return rec
        return None
    

    def namesiteRemovePeer(self, name):
        """
        Removes a namesite from our list
        """
        for rec in self.namesitePeers:
            if rec['name'] == name:
                self.namesitePeers.remove(rec)
        
        self.namesiteSave()
    

    def namesiteLookup(self, domain, **kw):
        """
        Attempts a lookup of a given 'domain name' on our designated
        namesites
        
        Arguments:
            - domain - the domain to look up
        
        Keywords:
            - localonly - whether to only search local cache
            - peer - if given, search only that peer's namesite (not locals)
        """
        self.namesiteLoad()
    
        localonly = kw.get('localonly', False)
        peer = kw.get('peer', None)
        
        if not peer:
            # try local cache first
            for rec in self.namesiteLocals:
                if domain in rec['cache']:
                    return rec['cache'][domain]
    
        if localonly:
            return None
    
        # the long step
        for rec in self.namesitePeers:
    
            if peer and (peer != rec['name']):
                continue
    
            uri = rec['puburi'] + "/" + domain + "/0"
    
            try:
                mimetype, tgtUri = self.get(uri)
                return tgtUri
            except:
                pass
    
        return None
    

    def namesiteProcessUri(self, uri):
        """
        Reduces a URI
        """
        # strip 'freenet:'
        uri1 = uri.split("freenet:")[-1]
        
        # change SSK to USK, and split path
        uri1 = uri1.replace("SSK@", "USK@").split("/")[0]
        
        # barf if bad uri
        if not uri1.startswith("USK@"):
            usage("Bad uri %s" % uri)
        
        return uri1
    

    # high level client methods
    def listen_global(self, **kw):
        """
        Enable listening on global queue
        """
        self.submit_cmd(None, "WatchGlobal", Enabled="true", **kw)
    

    def ignore_global(self, **kw):
        """
        Stop listening on global queue
        """
        self.submit_cmd(None, "WatchGlobal", Enabled="false", **kw)
    

    def purge_persistent_jobs(self):
        """
        Cancels all persistent jobs in one go
        """
        for job in self.get_persistent_jobs():
            job.cancel()
    

    def get_all_jobs(self):
        """
        Returns a list of persistent jobs, excluding global jobs
        """
        return list(self.jobs.values())
    

    def get_persistent_jobs(self):
        """
        Returns a list of persistent jobs, excluding global jobs
        """
        return [j for j in list(self.jobs.values()) if j.is_persistent and not j.is_global]
    

    def get_global_jobs(self):
        """
        Returns a list of global jobs
        """
        return [j for j in list(self.jobs.values()) if j.is_global]
    

    def get_transient_jobs(self):
        """
        Returns a list of non-persistent, non-global jobs
        """
        return [j for j in list(self.jobs.values()) if not j.is_persistent]
    

    def refresh_persistent_requests(self, **kw):
        """
        Sends a ListPersistentRequests to node, to ensure that
        our records of persistent requests are up to date.
        
        Since, upon connection, the node sends us a list of all
        outstanding persistent requests anyway, I can't really
        see much use for this method. I've only added the method
        for FCP spec compliance
        """
        self._log(DETAIL, "listPersistentRequests")
    
        if '__global' in self.jobs:
            raise Exception("An existing non-identifier job is currently pending")
    
        # ---------------------------------
        # format the request
        opts = {}
    
        _id = '__global'
        opts['Identifier'] = _id
    
        opts['async'] = kw.pop('async', False)
        if 'callback' in kw:
            opts['callback'] = kw['callback']
    
        # ---------------------------------
        # now enqueue the request
        return self.submit_cmd(_id, "ListPersistentRequests", **opts)
    

    def clear_global_job(self, _id):
        """
        Removes a job from the jobs queue
        """
        self.submit_cmd(_id, "RemovePersistentRequest",
                        Identifier=_id, Global=True, async=True, wait_until_sent=True)
    

    def get_socket_timeout(self):
        """
        Gets the socket_timeout for future socket calls;
        returns None if not supported by Python version
        """

        return self.socket.gettimeout()

    

    def set_socket_timeout(self, socket_timeout):
        """
        Sets the socket_timeout for future socket calls
        
        >>> node = FCPNode()
        >>> timeout = node.getsocket_timeout()
        >>> newtimeout = 1800
        >>> node.setsocket_timeout(newtimeout)
        >>> node.getsocket_timeout()
        1800.0
        """

        self.socket_timeout = socket_timeout
        self.socket.settimeout(self.socket_timeout)

    

    def get_verbosity(self):
        """
        Gets the verbosity for future logging calls

        >>> node = FCPNode()
        >>> node.getVerbosity() # default
        3
        >>> node.setVerbosity(INFO)
        >>> node.getVerbosity()
        4
        """
        return self.verbosity
    

    def set_verbosity(self, verbosity):
        """
        Sets the verbosity for future logging calls
        """
        self.verbosity = verbosity
    

    def shutdown(self):
        """
        Terminates the manager thread
        
        You should explicitly shutdown any existing nodes
        before exiting your client application
        """
        log = self._log
    
        log(DETAIL, "shutdown: entered")
        if not self.running:
            log(DETAIL, "shutdown: already shut down")
            return
    
        self.running = False
    
        # give the manager thread a chance to bail out
        time.sleep(POLL_TIMEOUT * 3)
    
        # wait for mgr thread to quit
        log(DETAIL, "shutdown: waiting for manager thread to terminate")
        self.shutdown_lock.acquire()
        log(DETAIL, "shutdown: manager thread terminated")
    
        # shut down FCP connection
        if hasattr(self, 'socket'):
            if not self.no_close_socket:
                self.socket.close()
                del self.socket
    
        # and close the logfile
        if None != self.logfile and self.logfile not in [sys.stdout, sys.stderr]:
            self.logfile.close()
    
        log(DETAIL, "shutdown: done?")
    

    def kill(self, **kw):
        """
        Shutdown the node, not the manager thread.

        Keywords:
            - async - whether to do this call asynchronously, and
              return a JobTicket object, default False
            - wait_until_sent - whether to block until this command has been sent
              to the node, default False
        """
        return self.submit_cmd("__global", "Shutdown", **kw)

        
    # methods for manager thread
    def __mgr_thread(self):
        """
        This thread is the nucleus of pyFreenet, and coordinates incoming
        client commands and incoming node responses
        """
        log = self._log
    
        self.shutdown_lock.acquire()
    
        log(DETAIL, "FCPNode: manager thread starting")
        try:
            while self.running:
    
                log(NOISY, "__mgr_thread: Top of manager thread")
    
                # try for incoming messages from node
                log(NOISY, "__mgr_thread: Testing for incoming message")
                if self.__msg_incoming():
                    log(DEBUG, "__mgr_thread: Retrieving incoming message")
                    msg = self.__rx_msg()
                    log(DEBUG, "__mgr_thread: Got incoming message, dispatching")
                    self.__on_rx_msg(msg)
                    log(DEBUG, "__mgr_thread: back from on_rx_msg")
                else:
                    log(NOISY, "__mgr_thread: No incoming message from node")
        
                # try for incoming requests from clients
                log(NOISY, "__mgr_thread: Testing for client req")
                try:
                    req = self.client_req_queue.get(True, POLL_TIMEOUT)
                    log(DEBUG, "__mgr_thread: Got client req, dispatching")
                    self.__on_client_req(req)
                    log(DEBUG, "__mgr_thread: Back from on_clientReq")
                except queue.Empty:
                    log(NOISY, "__mgr_thread: No incoming client req")
                    pass
    
            self._log(DETAIL, "__mgr_thread: Manager thread terminated normally")
    
        except Exception as e:
            traceback.print_exc()
            self._log(CRITICAL, "__mgr_thread: manager thread crashed")
    
            # send the exception to all waiting jobs
            for id, job in list(self.jobs.items()):
                job._put_result(e)
            
            # send the exception to all queued jobs
            while True:
                try:
                    job = self.client_req_queue.get(True, POLL_TIMEOUT)
                    job._put_result(e)
                except queue.Empty:
                    log(NOISY, "__mgr_thread: No incoming client req")
                    break
    
        self.shutdown_lock.release()
    

    def __msg_incoming(self):
        """
        Returns True if a message is coming in from the node
        """
        return len(select.select([self.socket], [], [], POLL_TIMEOUT)[0]) > 0
    

    def submit_cmd(self, _id, cmd, **kw):
        """
        Submits a command for execution
        
        Arguments:
            - _id - the command identifier
            - cmd - the command name, such as 'ClientPut'
        
        Keywords:
            - async - whether to return a JobTicket object, rather than
              the command result
            - callback - a function taking 2 args 'status' and 'value'.
              Status is one of 'successful', 'pending' or 'failed'.
              value is the primitive return value if successful, or the raw
              node message if pending or failed
            - follow_redirect - follow a redirect if true, otherwise fail the get
            - rawcmd - a raw command buffer to send directly
            - options specific to command such as 'URI'
            - timeout - timeout in seconds for job completion, default 1 year
            - wait_until_sent - whether to block until this command has been sent
              to the node, default False
            - keep - whether to keep the job on our jobs list after it completes,
              default False
        
        Returns:
            - if command is sent in sync mode, returns the result
            - if command is sent in async mode, returns a JobTicket
              object which the client can poll or block on later

        >>> import fcp
        >>> n = fcp.node.FCPNode()
        >>> cmd = "ClientPut"
        >>> jobid = "id2291160822224650"
        >>> opts = {'Metadata.ContentType': 'text/html', 'async': False, 'UploadFrom': 'direct', 'Verbosity': 0, 'Global': 'false', 'URI': 'CHK@', 'keep': False, 'DontCompress': 'false', 'MaxRetries': -1, 'timeout': 31536000, 'Codecs': 'GZIP, BZIP2, LZMA, LZMA_NEW', 'GetCHKOnly': 'true', 'RealTimeFlag': 'false', 'wait_until_sent': False, 'Identifier': jobid, 'Data': '<!DOCTYPE html>\\n<html>\\n<head>\\n<title>Sitemap for freenet-plugin-bare</title>\\n</head>\\n<body>\\n<h1>Sitemap for freenet-plugin-bare</h1>\\nThis listing was automatically generated and inserted by freesitemgr\\n<br><br>\\n<table cellspacing=0 cellpadding=2 border=0>\\n<tr>\\n<td><b>Size</b></td>\\n<td><b>Mimetype</b></td>\\n<td><b>Name</b></td>\\n</tr>\\n<tr>\\n<td>19211</td>\\n<td>text/html</td>\\n<td><a href="index.html">index.html</a></td>\\n</tr>\\n</table>\\n<h2>Keys of large, separately inserted files</h2>\\n<pre>\\n</pre></body></html>\\n', 'PriorityClass': 3, 'Persistence': 'connection', 'TargetFilename': 'sitemap.html'}
        >>> n.submit_cmd(jobid, cmd, **opts)
        'CHK@FR~anQPhpw7lZjxl96o1b875tem~5xExPTiSa6K3Wus,yuGOWhpqFY5N9i~N4BjM0Oh6Bk~Kkb7sE4l8GAsdBEs,AAMC--8/sitemap.html'
        >>> # n.submit_cmd(id=None, cmd='WatchGlobal', **{'Enabled': 'true'})
        
        """
        if not self.node_is_alive:
            raise FCPNodeFailure('{0}:{1}: node closed connection'.format(cmd, _id))

        # if identifier is not given explicitly in the options, we
        # need to add it to ensure that the replies find matching
        # jobs.
        if not "Identifier":
            kw["Identifier"] = _id

        log = self._log

        if self.verbosity >= DEBUG:
            log(DEBUG, "submit_cmd: _id=" + repr(_id) + ", cmd=" + repr(cmd) + ", **" + repr(kw))
    
        async = kw.pop('async', False)
        follow_redirect = kw.pop('follow_redirect', True)
        stream = kw.pop('stream', None)
        wait_until_sent = kw.pop('wait_until_sent', False)
        keep_job = kw.pop('keep', False)
        timeout = kw.pop('timeout', ONE_YEAR)
        
        if( "kwdict" in kw):
            kwdict = kw[ "kwdict" ]
            del kw[ "kwdict" ]
            for key in list(kwdict.keys()):
                kw[ key ] = kwdict[ key ]
        
        job = JobTicket(
            self, _id, cmd, kw,
            verbosity=self.verbosity, logger=self._log, keep=keep_job,
            stream=stream)
    
        log(DEBUG, "submit_cmd: timeout=%s" % timeout)
        
        job.follow_redirect = follow_redirect
    
        if cmd == 'ClientGet' and 'URI' in kw:
            job.uri = kw['URI']
    
        if cmd == 'ClientPut' and 'Metadata.ContentType' in kw:
            job.mimetype = kw['Metadata.ContentType']
    
        self.client_req_queue.put(job)
    
        # log(DEBUG, "submit_cmd: _id='%s' cmd='%s' kw=%s" % (id, cmd, # truncate long commands
        #                                                    str([(k,str(kw.get(k, ""))[:128])
        #                                                         for k 
        #                                                         in kw])))

        if async:
            if wait_until_sent:
                job.wait_till_req_sent()
            return job
        elif cmd in ['WatchGlobal', 'RemovePersistentRequest']:
            return

        log(DETAIL, "Waiting on job")
        return job.wait(timeout)

    def __on_client_req(self, job):
        """
        takes an incoming request job from client and transmits it to
        the fcp port, and also registers it so the manager thread
        can action responses from the fcp port.
        """
        id = job.id
        cmd = job.cmd
        kw = job.kw
    
        # register the req
        if cmd != 'WatchGlobal':
            self.jobs[id] = job
            self._log(DEBUG, "__on_client_req: cmd=%s id=%s lock=%s" % (
                cmd, repr(id), job.lock))
        
        # now can send, since we're the only one who will
        self._tx_msg(cmd, **kw)
    
        job.time_queued = int(time.time())
    
        job.req_sent_lock.release()
    

    def __on_rx_msg(self, msg):
        """
        Handles incoming messages from node
        
        If an incoming message represents the termination of a command,
        the job ticket object will be notified accordingly
        """
        log = self._log
    
        # ArneBab => http://freenet.mantishub.io/view.php?id=6890

        # find the job this relates to
        _id = msg.get('Identifier', '__global')
    
        hdr = msg['header']
    
        job = self.jobs.get(_id, None)
        if not job:
            # we have a global job and/or persistent job from last connection
            log(DETAIL, "***** Got %s from unknown job _id %s" % (hdr, repr(_id)))
            job = JobTicket(self, _id, hdr, msg)
            self.jobs[_id] = job
    
        # action from here depends on what kind of message we got
    
        # -----------------------------
        # handle GenerateSSK responses
    
        if hdr == 'SSKKeypair':
            # got requested keys back
            keys = (msg['RequestURI'], msg['InsertURI'])
            job.callback('successful', keys)
            job._put_result(keys)
    
            # and remove job from queue
            self.jobs.pop(_id, None)
            return
    
        # -----------------------------
        # handle ClientGet responses
    
        if hdr == 'DataFound':
            if( 'URI' in job.kw):
                log(INFO, "Got DataFound for URI=%s" % job.kw['URI'])
            else:
                log(ERROR, "Got DataFound without URI")
            mimetype = msg['Metadata.ContentType']
            if 'Filename' in job.kw:
                # already stored to disk, done
                #resp['file'] = file
                result = (mimetype, job.kw['Filename'], msg)
                job.callback('successful', result)
                job._put_result(result)
                return
    
            elif job.kw['ReturnType'] == 'none':
                result = (mimetype, 1, msg)
                job.callback('successful', result)
                job._put_result(result)
                return
    
            # otherwise, we're expecting an AllData and will react to it then
            else:
                # is this a persistent get?
                if job.kw['ReturnType'] == 'direct' \
                and job.kw.get('Persistence', None) != 'connection':
                    # gotta poll for request status so we can get our data
                    # FIXME: this is a hack, clean it up
                    log(INFO, "Request was persistent")
                    if not hasattr(job, "gotPersistentDataFound"):
                        if job.is_global:
                            is_global = "true"
                        else:
                            is_global = "false"
                        job.gotPersistentDataFound = True
                        log(INFO, "  --> sending GetRequestStatus")
                        self._tx_msg("GetRequestStatus",
                                    Identifier=job.kw['Identifier'],
                                    Persistence=msg.get("Persistence", "connection"),
                                    Global=is_global,
                                    )
    
                job.callback('pending', msg)
                job.mimetype = mimetype
                return
    
        if hdr == 'CompatibilityMode':
            # information, how to insert the file to make it an exact match.
            # TODO: Use the information.
            job.callback('pending', msg)
            return
    
        if hdr == 'ExpectedMIME':
            # information, how to insert the file to make it an exact match.
            # TODO: Use the information.
            mimetype = msg['Metadata.ContentType']
            job.mimetype = mimetype
            job.callback('pending', msg)
            return

        if hdr == 'ExpectedDataLength':
            # The expected filesize.
            # TODO: Use the information.
            size = msg['DataLength']
            job.callback('pending', msg)
            return

        if hdr == 'AllData':
            result = (job.mimetype, msg['Data'], msg)
            job.callback('successful', result)
            job._put_result(result)
            return

        if hdr == 'GetFailed':
            # see if it's just a redirect problem
            if job.follow_redirect and (msg.get('ShortCodeDescription', None) == "New URI" or msg.get('Code', None) == 27):
                uri = msg['RedirectURI']
                job.kw['URI'] = uri
                job.kw['id'] = self.__get_unique_id();
                self._tx_msg(job.cmd, **job.kw)
                log(DETAIL, "Redirect to %s" % uri)
                return
            # see if it's just a TOO_MANY_PATH_COMPONENTS redirect
            if job.follow_redirect and (msg.get('ShortCodeDescription', None) == "Too many path components" or msg.get('Code', None) == 11):
                uri = msg['RedirectURI']
                job.kw['URI'] = uri
                job.kw['id'] = self.__get_unique_id();
                self._tx_msg(job.cmd, **job.kw)
                log(DETAIL, "Redirect to %s" % uri)
                return
    
            # return an exception
            job.callback("failed", msg)
            job._put_result(FCPGetFailed(msg))
            return
    
        # -----------------------------
        # handle ClientPut responses
    
        if hdr == 'URIGenerated':
            if 'URI' not in msg:
                log(ERROR, "message {} without 'URI'. This is very likely a bug in Freenet. Check whether you have files in uploads or downloads without URI (clickable link).".format(hdr))
            else:
                job.uri = msg['URI']
                newUri = msg['URI']
            job.callback('pending', msg)
    
            return
    
            # bail here if no data coming back
            if job.kw.get('GetCHKOnly', False) == 'true':
                # done - only wanted a CHK
                job._put_result(newUri)
                return
    
        if hdr == 'PutSuccessful':
            if 'URI' not in msg:
                log(ERROR, "message {} without 'URI'. This is very likely a bug in Freenet. Check whether you have files in uploads or downloads without URI (clickable link).".format(hdr))
            else:
                result = msg['URI']
                job._put_result(result)
                job.callback('successful', result)
            # print "*** PUTSUCCESSFUL"
            return
    
        if hdr == 'PutFailed':
            job.callback('failed', msg)
            job._put_result(FCPPutFailed(msg))
            return
        
        if hdr == 'PutFetchable':
            if 'URI' not in msg:
                log(ERROR, "message {} without 'URI'. This is very likely a bug in Freenet. Check whether you have files in uploads or downloads without URI (clickable link).".format(hdr))
            else:
                uri = msg['URI']
                job.kw['URI'] = uri
            job.callback('pending', msg)
            return
    
        # -----------------------------
        # handle ConfigData
        if hdr == 'ConfigData':
            # return all the data recieved
            job.callback('successful', msg)
            job._put_result(msg)
    
            # remove job from queue
            self.jobs.pop(_id, None)
            return
    
        # -----------------------------
        # handle progress messages
    
        if hdr == 'StartedCompression':
            job.callback('started_compress', msg)
            return
    
        if hdr == 'FinishedCompression':
            job.callback('finished_compress', msg)
            return
    
        if hdr == 'SimpleProgress':
            job.callback('progress', msg)
            return
    
        if hdr == 'SendingToNetwork':
            job.callback('pending', msg)
            return
    
        if hdr == 'EnterFiniteCooldown':
            job.callback('pending', msg)
            return

        if hdr == 'ExpectedHashes':
            # The hashes the file must have.
            # TODO: Use the information.
            sha256 = msg['Hashes.SHA256']
            job.callback('pending', msg)
            return
    

        # -----------------------------
        # handle LoadPlugin replies
        
        if hdr == 'PluginInfo':
            job._append_msg(msg)
            job.callback('successful', job.msgs)
            job._put_result(job.msgs)
            return
        
        # -----------------------------
        # handle FCPPluginMessage replies
        
        if hdr == 'FCPPluginReply':
            job._append_msg(msg)
            job.callback('successful', job.msgs)
            job._put_result(job.msgs)
            return   
        
        # -----------------------------
        # handle peer management messages
        
        if hdr == 'EndListPeers':
            job._append_msg(msg)
            job.callback('successful', job.msgs)
            job._put_result(job.msgs)
            return   
        
        if hdr == 'Peer':
            if(job.cmd == "ListPeers"):
                job.callback('pending', msg)
                job._append_msg(msg)
            else:
                job.callback('successful', msg)
                job._put_result(msg)
            return
        
        if hdr == 'PeerRemoved':
            job._append_msg(msg)
            job.callback('successful', job.msgs)
            job._put_result(job.msgs)
            return   
        
        if hdr == 'UnknownNodeIdentifier':
            job._append_msg(msg)
            job.callback('failed', job.msgs)
            job._put_result(job.msgs)
            return   
    
        # -----------------------------
        # handle peer note management messages
        
        if hdr == 'EndListPeerNotes':
            job._append_msg(msg)
            job.callback('successful', job.msgs)
            job._put_result(job.msgs)


            return   
        
        if hdr == 'PeerNote':
            if(job.cmd == "ListPeerNotes"):
                job.callback('pending', msg)
                job._append_msg(msg)
            else:
                job.callback('successful', msg)
                job._put_result(msg)
            return
        
        if hdr == 'UnknownPeerNoteType':
            job._append_msg(msg)
            job.callback('failed', job.msgs)
            job._put_result(job.msgs)
            return   
    
        # -----------------------------
        # handle persistent job messages
    
        if hdr == 'PersistentGet':
            job.callback('pending', msg)
            job._append_msg(msg)
            return
    
        if hdr == 'PersistentPut':
            job.callback('pending', msg)
            job._append_msg(msg)
            return
    
        if hdr == 'PersistentPutDir':
            job.callback('pending', msg)
            job._append_msg(msg)
            return
    
        if hdr == 'EndListPersistentRequests':
            job._append_msg(msg)
            job.callback('successful', job.msgs)
            job._put_result(job.msgs)
            return
        
        if hdr == 'PersistentRequestRemoved':
            if _id in self.jobs:
                del self.jobs[_id]
            return
        
        # ----------------------------- 
        # handle USK Subscription , thanks to Enzo Matrix

        # Note from Enzo Matrix: I just needed the messages to get
        # passed through to the job, and have its callback function
        # called so I can do something when a USK gets updated. I
        # handle the checking whether the message was a
        # SubscribedUSKUpdate in the callback, which is defined in the
        # spider.
        if hdr == 'SubscribedUSK': 
            job.callback('successful', msg) 
            return 

        if hdr == 'SubscribedUSKUpdate': 
            job.callback('successful', msg) 
            return 

        if hdr == 'SubscribedUSKRoundFinished': 
            job.callback('successful', msg) 
            return

        if hdr == 'SubscribedUSKSendingToNetwork': 
            job.callback('successful', msg) 
            return

        # -----------------------------
        # handle testDDA messages
        
        if hdr == 'TestDDAReply':
            # return all the data recieved
            job.callback('successful', msg)
            job._put_result(msg)
    
            # remove job from queue
            self.jobs.pop(_id, None)
            return
        
        if hdr == 'TestDDAComplete':
            # return all the data recieved
            job.callback('successful', msg)
            job._put_result(msg)
    
            # remove job from queue
            self.jobs.pop(_id, None)
            return
    
        # -----------------------------
        # handle NodeData
        if hdr == 'NodeData':
            # return all the data recieved
            job.callback('successful', msg)
            job._put_result(msg)
    
            # remove job from queue
            self.jobs.pop(_id, None)
            return
    
        # -----------------------------
        # handle various errors
    
        if hdr == 'ProtocolError':
            job.callback('failed', msg)
            job._put_result(FCPProtocolError(msg))
            return
    
        if hdr == 'IdentifierCollision':
            log(ERROR, "IdentifierCollision on _id %s ???" % _id)
            job.callback('failed', msg)
            job._put_result(Exception("Duplicate job identifier %s" % _id))
            return

        # Ignore informational headers (since 1254)
        if hdr == 'ExpectedHashes' or hdr == 'CompatibilityMode':
            return

        # -----------------------------
        # wtf is happening here?!?
    
        log(ERROR, "Unknown message type from node: %s" % hdr)
        job.callback('failed', msg)
        job._put_result(FCPException(msg))
        return

    

    # low level noce comms methods
    

    def __hello(self):
        """
        perform the initial FCP protocol handshake
        """
        self._tx_msg("ClientHello", 
                         Name=self.name,
                         ExpectedVersion=expectedVersion)

        resp = self.__rx_msg()

        self.node_version = resp['Version'] if 'Version' in resp else None

        self.node_fcp_version = resp['FCPVersion'] if 'FCPVersion' in resp else None

        self.node_build = resp['Build'] if 'Build' in resp else None

        self.node_revision = resp['Revision'] if 'Revision' in resp else None
            
        self.node_ext_build = resp['ExtBuild'] if('ExtBuild' in resp) else None

        self.node_ext_revision = resp['ExtRevision'] if 'Revision' in resp else None
            
        self.node_is_tfestnet = True if 'Testnet' in resp else False
        
        self.connectionidentifier = resp['ConnectionIdentifier'] if 'ConnectionIdentifier' in resp else None

        
        self.compression_codecs = self.__parse_compression_codecs(
            resp ['CompressionCodecs']) if 'CompressionCodecs' in resp else COMPRESSION_CODECS

        return resp

    def __parse_compression_codecs(self, compression_codecs_string):
        """
        Turn the CompressionCodecsString returned by the node into a list
        of name and number of the codec.

        @param CompressionCodecsString: "3 - GZIP(0), BZIP2(1), LZMA(2)"
        @return: [(name, number), ...]

        """
        return [(name, int(number[:-1])) 
                for name, number 
                in [i.split("(") 
                    for i in compression_codecs_string.split(
                            " - ")[1].split(", ")]]

    def default_compression_codecs_string(self):
        """
        Turn the CompressionCodecs into a string accepted by the node.

        @param CompressionCodecs: [(name, number), ...]
        @return: "GZIP, BZIP2, LZMA" (example)

        """
        return ", ".join([name for name, num in self.compression_codecs])

    def __get_unique_id(self):
        """
        Allocate a unique ID for a request
        """
        return 'id_{0}'.format(str( uuid.uuid4()))
    

    def _tx_msg(self, msgType, **kw):
        """
        low level message send
        
        Arguments:
            - msgType - one of the FCP message headers, such as 'ClientHello'
            - args - zero or more (keyword, value) tuples
        Keywords:
            - rawcmd - if given, this is the raw buffer to send
            - other keywords depend on the value of msgType
        """
        log = self._log
    
        # just send the raw command, if given    
        rawcmd = kw.get('rawcmd', None)
        if rawcmd:
            self.socket.sendall(rawcmd)
            log(DETAIL, "CLIENT: %s" % rawcmd)
            return
    
        if "Data" in kw:
            data = kw.pop("Data")
            sendEndMessage = False
        else:
            data = None
            sendEndMessage = True
    
        items = [msgType.encode('utf-8') + b"\n"]
        log(DETAIL, "CLIENT: %s" % msgType)
    
        #print "CLIENT: %s" % msgType
        for k, v in list(kw.items()):
            #print "CLIENT: %s=%s" % (k,v)
            line = k.encode('utf-8') + b"=" + str(v).encode('utf-8')
            items.append(line + b"\n")
            log(DETAIL, "CLIENT: %s" % line)
    
        if data != None:
            items.append(("DataLength=%d\n" % len(data)).encode('utf-8'))
            log(DETAIL, "CLIENT: DataLength=%d" % len(data))
            items.append(b"Data\n")
            log(DETAIL, "CLIENT: ...data...")
            items.append(data)
    
        #print "sendEndMessage=%s" % sendEndMessage
    
        if sendEndMessage:
            items.append(b"EndMessage\n")
            log(DETAIL, "CLIENT: %s" % b"EndMessage")
        
        # ensure that every item is a byte
        items = [(i if not isinstance(i, str) else i.encode("utf-8"))
                 for i in items]
        
        try:
            raw = b"".join(items)
        except TypeError as e:
            # at least one item is no bytearray
            log(ERROR, str(e))
            for item in items:
                try:
                    print(item) # can print strings
                    log(ERROR, item)
                except TypeError:
                    print(item.decode("utf-8")) # to still show those which should have worked
                    log(ERROR, item.decode("utf-8"))
            raise
    
        self.socket.sendall(raw)
    

    def __rx_msg(self):
        """
        Receives and returns a message as a dict
        
        The header keyword is included as key 'header'
        """
        log = self._log
    
        log(DETAIL, "NODE: ----------------------------")
    
        # shorthand, for reading n bytes
        def read(n):
            if n > 1:
                log(DEBUG, "read: want %d bytes" % n)
            chunks = bytearray()
            remaining = n
            while remaining > 0:
                chunk = self.socket.recv(remaining)
                chunklen = len(chunk)
                if chunk:
                    chunks += chunk
                else:
                    self.node_is_alive = False
                    raise FCPNodeFailure("FCP socket closed by node")
                remaining -= chunklen
                if remaining > 0:
                    if n > 1:
                        log(DEBUG,
                            "wanted %s, got %s still need %s bytes" % (n, chunklen, remaining)
                            )
                    pass
            return chunks
    
        # read a line
        def readln():
            buf = bytearray()
            while True:
                c = read(1)
                buf += c
                if c == b'\n':
                    break
            log(DETAIL, "NODE: " + buf[:-1].decode('utf-8'))
            return buf
    
        items = {}
    
        # read the header line
        # It is not binary; decode.
        while True:
            line = readln().decode('utf-8').strip()
            if line:
                items['header'] = line
                break
    
        # read the body
        while True:
            line = readln().strip()
            if line in [b'End', b'EndMessage']:
                break
    
            if line == b'Data':
                # read the following data
                
                # try to locate job
                id = items['Identifier']
                job = self.jobs[id]
                if job.stream:
                    # loop to transfer from socket to stream
                    remaining = items['DataLength']
                    stream = job.stream
                    while remaining > 0:
                        buf = self.socket.recv(remaining)
                        stream.write(buf)
                        stream.flush()
                        remaining -= len(buf)
                    items['Data'] = None
                else:
                    buf = read(items['DataLength'])
                    items['Data'] = buf
                log(DETAIL, "NODE: ...<%d bytes of data>" % len(buf))
                break
            else:
                # it's a normal 'key=val' pair
                # Pairs are not binary; decode as UTF-8.
                try:
                    line = line.decode('utf-8')
                    k, v = line.split("=", 1)
                except:
                    log(ERROR, "__rx_msg: barfed splitting '%s'" % repr(line))
                    raise
    
                # attempt int conversion
                try:
                    v = int(v)
                except:
                    pass
    
                items[k] = v
    
        # all done
        return items
    

    def _log(self, level, msg):
        """
        Logs a message. If level > verbosity, don't output it
        """
        if level > self.verbosity:
            return
        
        if(None != self.logfile):
            if not msg.endswith("\n"):
                msg += "\n"
            self.logfile.write(msg)
            self.logfile.flush()
        if(None != self.logfunc):
            while( msg.endswith("\n") ):
                msg = msg[ : -1 ]
            msglines = msg.split("\n")
            for msgline in msglines:
                self.logfunc(msgline)

class JobTicket(object):
    """
    A JobTicket is an object returned to clients making
    asynchronous requests. It puts them in control of how
    they manage n concurrent requests.
    
    When you as a client receive a JobTicket, you can choose to:
        - block, awaiting completion of the job
        - poll the job for completion status
        - receive a callback upon completion
        
    Attributes of interest:
        - is_persistent - True if job is persistent
        - is_global - True if job is global
        - follow_redirect - follow a redirect if true, otherwise fail the get
        - value - value returned upon completion, or None if not complete
        - node - the node this job belongs to
        - _id - the job Identifier
        - cmd - the FCP message header word
        - kw - the keywords in the FCP header
        - msgs - any messages received from node in connection
          to this job
    """

    def __init__(self, node, _id, cmd, kw, **opts):
        """
        You should never instantiate a JobTicket object yourself
        """
        self.node = node
        self.id = _id
        self.cmd = cmd

        self.verbosity = opts.get('Verbosity', ERROR)
        self._log = opts.get('logger', self.default_logger)
        self.keep = opts.get('keep', False)
        self.stream = opts.get('stream', None)
        self.follow_redirect = opts.get('follow_redirect', True)

        print(node, " ", kw.get("Persistence", "connection"))
        # find out if persistent
        if kw.get("Persistence", "connection") != "connection":
            self.is_persistent = True

        else:
            self.is_persistent = False

        if kw.get('Global', False) == True:
            self.is_global = True
        else:
            self.is_global = False

        self.kw = kw

        self.msgs = []
    
        callback = kw.pop('callback', None)
        if callback:
            self.callback = callback
    
        self.timeout = int(kw.pop('timeout', 86400*365))
        self.time_queued = int(time.time())
        self.timeSent = None
    
        self.lock = threading.Lock()
    
        self.lock.acquire()
        self.result = None
    
        self.req_sent_lock = threading.Lock()
        self.req_sent_lock.acquire()
    

    def is_complete(self):
        """
        Returns True if the job has been completed
        """
        return self.result != None
    

    def wait(self, timeout=None):
        """
        Waits forever (or for a given timeout) for a job to complete
        """
        log = self._log
    
        log(DEBUG, "wait:%s:%s: timeout=%ss" % (self.cmd, self.id, timeout))
    
        # wait forever for job to complete, if no timeout given
        if timeout is None:
            log(DEBUG, "wait:%s:%s: no timeout" % (self.cmd, self.id))
            while not self.lock.acquire(False):
                time.sleep(_pollInterval)
            self.lock.release()
            return self.get_result()
    
        # wait for timeout
        then = int(time.time())
    
        # ensure command has been sent, wait if not
        while not self.req_sent_lock.acquire(False):
    
            # how long have we waited?
            elapsed = int(time.time()) - then
    
            # got any time left?
            if elapsed < timeout:
                # yep, patience remains
                time.sleep(_pollInterval)
                log(DEBUG, "wait:%s:%s: job not dispatched, timeout in %ss" % \
                     (self.cmd, self.id, timeout-elapsed))
                continue
    
            # no - timed out waiting for job to be sent to node
            log(DEBUG, "wait:%s:%s: timeout on send command" % (self.cmd, self.id))
            raise FCPSendTimeout(
                    header="Command '%s' took too long to be sent to node" % self.cmd
                    )
    
        log(DEBUG, "wait:%s:%s: job now dispatched" % (self.cmd, self.id))
    
        # wait now for node response
        while not self.lock.acquire(False):
            # how long have we waited?
            elapsed = int(time.time()) - then
    
            # got any time left?
            if elapsed < timeout:
                # yep, patience remains
                time.sleep(_pollInterval)
    
                #print "** lock=%s" % self.lock
    
                if timeout < ONE_YEAR:
                    log(DEBUG, "wait:%s:%s: awaiting node response, timeout in %ss" % \
                         (self.cmd, self.id, timeout-elapsed))
                continue
    
            # no - timed out waiting for node to respond
            log(DEBUG, "wait:%s:%s: timeout on node response" % (self.cmd, self.id))
            raise FCPNodeTimeout(
                    header="Command '%s' took too long for node response" % self.cmd
                    )
    
        log(DEBUG, "wait:%s:%s: job complete" % (self.cmd, self.id))
    
        # if we get here, we got the lock, command completed
        self.lock.release()
    
        # and we have a result
        return self.get_result()
    

    def wait_till_req_sent(self):
        """
        Waits till the request has been sent to node
        """
        self.req_sent_lock.acquire()
    

    def get_result(self):
        """
        Returns result of job, or None if job still not complete
    
        If result is an exception object, then raises it
        """
        if isinstance(self.result, Exception):
            raise self.result

        return self.result
    

    def callback(self, status, value):
        """
        This will be replaced in job ticket instances wherever
        user provides callback arguments
        """
        # no action needed
    

    def cancel(self):
        """
        Cancels the job, if it is persistent
        
        Does nothing if the job was not persistent
        """
        if not self.is_persistent:
            return
    
        # remove from node's jobs lists
        try:
            del self.node.jobs[self.id]
        except:
            pass
        
        # send the cancel
        if self.is_global:
            is_global = True
        else:
            is_global = False
    
        self.node._tx_msg("RemovePersistentRequest",
                         Global=is_global,
                         Identifier=self.id)

    def _append_msg(self, msg):
        self.msgs.append(msg)
    

    def _put_result(self, result):
        """
        Called by manager thread to indicate job is complete,
        and submit a result to be picked up by client
        """
        self.result = result
    
        if not (self.keep or self.is_persistent or self.is_global):
            try:
                del self.node.jobs[self.id]
            except:
                pass
    
        #print "** job: lock=%s" % self.lock
    
        try:
            self.lock.release()
        except:
            pass
    
        #print "** job: lock released"
    

    def __repr__(self):
        if "URI" in self.kw:
            uri = " URI=%s" % self.kw['URI']
        else:
            uri = ""
        return "<FCP job %s:%s%s" % (self.id, self.cmd, uri)
    

    def default_logger(self, level, msg):
        
        if level > self.verbosity:
            return
    
        if not msg.endswith("\n"): msg += "\n"
    
        sys.stdout.write(msg)
        sys.stdout.flush()
    



def toBool(arg):
    try:
        arg = int(arg)
        if arg:
            return "true"
    except:
        pass
    
    if isinstance(arg, str):
        if arg.strip().lower()[0] == 't':
            return "true"
        else:
            return "false"
    
    if arg:
        return True
    else:
        return False

def readdir(dirpath, prefix='', gethashes=False):
    """
    Reads a directory, returning a sequence of file dicts.

    TODO: Currently this uses sha1 as hash. Freenet uses 256. But the
          hashes are not used.
    
    Arguments:
      - dirpath - relative or absolute pathname of directory to scan
      - gethashes - also include a 'hash' key in each file dict, being
        the SHA1 hash of the file's name and contents
      
    Each returned dict in the sequence has the keys:
      - fullpath - usable for opening/reading file
      - relpath - relative path of file (the part after 'dirpath'),
        for the 'SSK@blahblah//relpath' URI
      - mimetype - guestimated mimetype for file

    >>> tempdir = tempfile.mkdtemp()
    >>> filename = "test.txt"
    >>> testfile = os.path.join(tempdir, filename)
    >>> with open(testfile, "w") as f:
    ...     f.write("test")
    >>> correct = [{'mimetype': 'text/plain', 'fullpath': testfile, 'relpath': filename}]
    >>> correct == readdir(tempdir)
    True
    >>> tempdir = tempfile.mkdtemp()
    >>> filename = "test"
    >>> testfile = os.path.join(tempdir, filename)
    >>> with open(testfile, "w") as f:
    ...     f.write("test")
    >>> correct = [{'mimetype': 'application/octet-stream', 'fullpath': testfile, 'relpath': filename}]
    >>> correct == readdir(tempdir)
    True
    >>> res = readdir(tempdir, gethashes=True)
    >>> res[0]["hash"] == hash_file(testfile)
    True
    """
    
    #set_trace()
    #print "dirpath=%s, prefix='%s'" % (dirpath, prefix)
    entries = []
    for f in os.listdir(dirpath):
        relpath = prefix + f
        fullpath = os.path.join(dirpath, f)
        # FIXME: horrible hack to avoid putting unencodable values into a list
        if f == '.freesiterc' or f == b".freesiterc" or (f[1:] and (f[-1] == "~" or f[-1] == b"~")):
            continue
        if os.path.isdir(fullpath) \
        or os.path.islink(fullpath) and os.path.isdir(os.path.realpath(fullpath)):
            entries.extend(
                readdir(
                    os.path.join(dirpath, f),
                    relpath + os.path.sep.encode("utf-8"),
                    gethashes
                    )
                )
        else:
            #entries[relpath] = {'mimetype':'blah/shit', 'fullpath':dirpath+"/"+relpath}
            fullpath = os.path.join(dirpath, f)
            entry = {'relpath' :relpath,
                     'fullpath':fullpath,
                     'mimetype':guessMimetype(f)
                     }
            if gethashes:
                entry['hash'] = hash_file(fullpath)
            entries.append(entry)
    entries.sort(key=lambda k: k['relpath'])
    
    return entries

def hash_file(path):
    """
    returns an SHA(1) hash of a file's contents

    >>> oslevelid, filepath = tempfile.mkstemp(text=True)
    >>> with open(filepath, "w") as f:
    ...     f.write("test")
    >>> hash_file(filepath) == hashlib.sha1("test").hexdigest()
    True
    """
    raw = open(path, "rb").read()
    return hashlib.sha1(raw).hexdigest()

def sha256dda(nodehelloid, identifier, path=None):
    """
    returns a sha256 hash of a file's contents for bypassing TestDDA

    >>> oslevelid, filepath = tempfile.mkstemp(text=True)
    >>> with open(filepath, "wb") as f:
    ...     f.write("test")
    >>> print sha256dda("1","2",filepath) == hashlib.sha256("1-2-" + "test").digest()
    True
    """
    tohash = b"-".join([nodehelloid.encode('utf-8'), identifier.encode('utf-8'), open(path, "rb").read()])
    return hashlib.sha256(tohash).digest()

def guessMimetype(filename):
    """
    Returns a guess of a mimetype based on a filename's extension
    """
    if isinstance(filename, bytes):
        if filename.endswith(b".tar.bz2"):
            return ('application/x-tar', 'bzip2')
    else:
        if filename.endswith(".tar.bz2"):
            return ('application/x-tar', 'bzip2')
    
    try:
        m = mimetypes.guess_type(filename, False)[0]
    except:
        m = None
    if m == "audio/mpegurl": # disallowed mime type by FF
        m = "audio/x-mpegurl"
    if m is None: # either an exception or a genuine None
        # FIXME: log(INFO, "Could not find mimetype for filename %s" % filename)
        m = "application/octet-stream"
    return m

_re_slugify = re.compile('[^\w\s\.-]', re.UNICODE)
_re_slugify_multidashes = re.compile('[-\s]+', re.UNICODE)
def to_url_safe(filename):
    """Make a filename url-safe, keeping only the basename and killing all
potentially unfitting characters.
    
    :returns: urlsafe basename of the file as string."""
    filename = os.path.basename(filename)
    filename = unicodedata.normalize('NFKD', filename).encode("ascii", "ignore")
    filename = _re_slugify.sub('', filename.decode('utf-8')).strip()
    filename = _re_slugify_multidashes.sub('-', filename)
    return str(filename)


def uri_is_private(uri):
    """
    analyses an SSK URI, and determines if it is an SSK or USK private key

    for details see https://wiki.freenetproject.org/Signed_Subspace_Key

    >>> uri_is_private("SSK@~Udj39wzRUN4J-Kqn1aWN8kJyHL6d44VSyWoqSjL60A,iAtIH8348UGKfs8lW3mw0lm0D9WLwtsIzZhvMWelpK0,AQACAAE/")
    False
    >>> uri_is_private("SSK@R-skbNbiXqWkqj8FPDTusWyk7u8HLvbdysyRY3eY9A0,iAtIH8348UGKfs8lW3mw0lm0D9WLwtsIzZhvMWelpK0,AQECAAE/")
    True
    >>> uri_is_private("USK@AIcCHvrGspY-7J73J3VR-Td3DuPvw3IqCyjjRK6EvJol,hEvqa41cm72Wc9O1AjZ0OoDU9JVGAvHDDswIE68pT7M,AQECAAE/test.R1/0")
    True
    >>> uri_is_private("KSK@AIcCHvrGspY-7J73J3VR-Td3DuPvw3IqCyjjRK6EvJol,hEvqa41cm72Wc9O1AjZ0OoDU9JVGAvHDDswIE68pT7M,AQECAAE/test.R1/0")
    False
    >>> uri_is_private("SSK@JhtPxdPLx30sRN0c5S2Hhcsif~Yqy1lsGiAx5Wkq7Lo,-e0kLAjmmclSR7uL0TN901tS3iSx2-21Id8tUp4tyzg,AQECAAE/")
    True
    """
    # strip leading stuff
    if uri.startswith("freenet:"):
        uri = uri[8:]
    if uri.startswith("//"):
        uri = uri[2:]
    # actual recognition: SSK or USK
    if not (uri.startswith("SSK@") or uri.startswith("USK@")):
        return False
    try:
        symmetric, publicprivate, extra = uri.split(",")[:3]
    except (IndexError, ValueError):
        return False
    if "/" in extra:
        extra = extra.split("/")[0]
    extra += "/"
    extrabytes = base64.decodestring(extra)

    is_private = ord(extrabytes[1])
    
    if is_private:
        return True

    return False

def parse_time(t):
    """
    Parses a time value, recognising suffices like 'm' for minutes,
    's' for seconds, 'h' for hours, 'd' for days, 'w' for weeks,
    'M' for months.
    
    >>> endings = {'s':1, 'm':60, 'h':60*60, 'd':60*60*24, 'w':60*60*24*7, 'M':60*60*24*30}
    >>> not False in [endings[i]*3 == parse_time("3"+i) for i in endings]
    True

    Returns time value in seconds
    """
    if not t:
        raise Exception("Invalid time '%s'" % t)
    
    if not isinstance(t, str):
        t = str(t)
    
    t = t.strip()
    if not t:
        raise Exception("Invalid time value '%s'"%  t)
    
    endings = {'s':1, 'm':60, 'h':3600, 'd':86400, 'w':86400*7, 'M':86400*30}
    
    lastchar = t[-1]
    
    if lastchar in list(endings.keys()):
        t = t[:-1]
        multiplier = endings[lastchar]
    else:
        multiplier = 1
    
    return int(t) * multiplier


# functions to encode/decode base64, freenet alphabet
def base64encode(raw):
    """
    Encodes a string to base64, using the Freenet alphabet
    """
    # encode using standard RFC1521 base64
    enc = base64.encodestring(raw)
    
    # convert the characters to freenet encoding scheme
    enc = enc.replace("+", "~")
    enc = enc.replace("/", "-")
    enc = enc.replace("=", "_")
    enc = enc.replace("\n", "")
    
    return enc

def base64decode(enc):
    """
    Decodes a freenet-encoded base64 string back to a binary string
    
    Arguments:
     - enc - base64 string to decode
    """
    # TODO: Are underscores actually used anywhere?
    enc = enc.replace("_", "=")

    # Add padding. Freenet may omit it.
    while (len(enc) % 4) != 0:
        enc += '='

    # Now ready to decode. ~ instead of +; - instead of /.
    raw = base64.b64decode(enc, '~-')
    
    return raw

def _base30hex(integer):
    """Turn an integer into a simple lowercase base30hex encoding."""
    base30 = "0123456789abcdefghijklmnopqrst"
    b30 = []
    while integer:
        b30.append(base30[integer%30])
        integer = int(integer / 30)
    return "".join(reversed(b30))
        

def _test():
    import doctest
    tests = doctest.testmod()
    if tests.failed:
        return "☹"*tests.failed

    return "^_^ (" + _base30hex(tests.attempted) + ")"
        

if __name__ == "__main__":
    print(_test())
