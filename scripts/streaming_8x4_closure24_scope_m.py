"""Fresh typed M generation entry; isolate introduced source context scope."""
import streaming_8x4_closure24_m_scope as SCOPE

_body=SCOPE.load_controller('generation',__name__,__file__)
globals().update({n:v for n,v in vars(_body).items() if not n.startswith('__')})

if __name__=='__main__':
    main()
