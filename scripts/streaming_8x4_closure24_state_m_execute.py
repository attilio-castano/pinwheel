"""Complete fresh M with state-aware observational process evidence only."""
import argparse
import signal
import sys
from pathlib import Path
import streaming_8x4_closure24_m_state_isolation as ISOLATION

_body=ISOLATION.load_controller(__name__,__file__)
globals().update({name:value for name,value in vars(_body).items()if not name.startswith('__')})

if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='rederive':
        parser=argparse.ArgumentParser();parser.add_argument('mode',choices=('rederive',))
        parser.add_argument('--prepared',required=True,type=Path);parser.add_argument('--output',required=True,type=Path)
        args=parser.parse_args();previous=signal.getsignal(signal.SIGTERM)
        def interrupted(signum,frame):raise KeyboardInterrupt('Root termination signal '+str(signum))
        signal.signal(signal.SIGTERM,interrupted)
        try:ISOLATION.rederive(args.prepared,args.output)
        finally:signal.signal(signal.SIGTERM,previous)
    else:main()
