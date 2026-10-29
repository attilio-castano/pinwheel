"""New typed complete M executor; unchanged Native/private/runtime algorithms."""
import streaming_8x4_closure24_m_context as CONTEXT

_body=CONTEXT.load_controller('execution',__name__,__file__)
globals().update({n:v for n,v in vars(_body).items() if not n.startswith('__')})

if __name__=='__main__':
    main()
