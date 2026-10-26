"""New typed read-only PG observer with retained Tech ownership; Root GO only."""
import streaming_8x4_closure24_pg_lifetime_context as LIFETIME

_body = LIFETIME.load_controller(__name__, __file__)
globals().update({name: value for name, value in vars(_body).items() if not name.startswith('__')})

if __name__ == '__main__':
    main()
