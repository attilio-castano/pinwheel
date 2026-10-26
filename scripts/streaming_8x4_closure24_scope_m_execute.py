"""Fresh typed M executor; complete original Native/private gates unchanged."""
import streaming_8x4_closure24_m_scope as SCOPE

_body=SCOPE.load_controller('execution',__name__,__file__)
globals().update({n:v for n,v in vars(_body).items() if not n.startswith('__')})

if __name__=='__main__':
    main()
