"""New typed M generation controller; immutable original-N context repair only."""
from pathlib import Path
import streaming_8x4_closure24_m_context as CONTEXT

_body=CONTEXT.load_controller('generation',__name__,__file__)
globals().update({n:v for n,v in vars(_body).items() if not n.startswith('__')})

if __name__=='__main__':
    main()
