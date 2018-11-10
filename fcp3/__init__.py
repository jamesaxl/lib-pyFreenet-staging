import sys, os

from .node import FCPNode
from .node import JobTicket
from .node import ConnectionRefused
from .node import FCPException
from .node import FCPGetFailed
from .node import FCPPutFailed
from .node import FCPProtocolError
from .node import fcpVersion
from .node import SILENT
from .node import FATAL
from .node import CRITICAL
from .node import ERROR
from .node import INFO
from .node import DETAIL
from .node import DEBUG
from .node import NOISY

#from put import main as put
#from get import main as get
#from genkey import main as genkey
#from invertkey import main as invertkey
#from redirect import main as redirect
#from names import main as names

from . import upload 
from . import put 
from . import get 
from . import genkey # will be gen_key
from . import invertkey 
from . import redirect 
from . import names
from . import fproxyproxy
#import fproxyaddref
from . import pseudopythonparser

isDoze = sys.platform.lower().startswith("win")

if not isDoze:
    from . import freenetfs


__all__ = ['node', 'sitemgr', 'xmlrpc',
           'FCPNode', 'JobTicket',
           'ConnectionRefused', 'FCPException', 'FCPPutFailed',
           'FCPProtocolError',
           'get', 'put', 'genkey', 'invertkey', 'redirect', 'names',
           'fproxyproxy', "fproxyaddref",
           ]

if not isDoze:
    __all__.append('freenetfs')
