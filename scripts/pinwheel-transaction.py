#!/usr/bin/env python3
"""Compile, inspect and run a request-bound Pinwheel transaction artifact."""
import argparse
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys

from pinwheel_transactions import Transaction, TransactionSpec, compile_transaction


ROOT = Path(__file__).resolve().parents[1]


def _integer(text, minimum, maximum=None):
    try:
        value = int(text, 0)
    except ValueError as error:
        raise argparse.ArgumentTypeError('Use an integer, optionally prefixed with 0x') from error
    if value < minimum or maximum is not None and value > maximum:
        bound = f'{minimum}..{maximum}' if maximum is not None else f'at least {minimum}'
        raise argparse.ArgumentTypeError('Value must be ' + bound)
    return value


def _tag(text):
    if not re.fullmatch(r'[A-Za-z0-9_-]+', text):
        raise argparse.ArgumentTypeError('Use letters, numbers, hyphens or underscores in tags')
    return text


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON field: ' + key)
        result[key] = value
    return result


def build_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_subparsers(dest='action', required=True)
    compile_action = actions.add_parser('compile', help='Compile a protocol request into a bound artifact')
    compile_action.add_argument('--request', type=Path, required=True)
    compile_action.add_argument('--output', type=Path, required=True)
    inspect = actions.add_parser('inspect', help='Revalidate the request/program binding and inspect resources')
    inspect.add_argument('--transaction', type=Path, required=True)
    run = actions.add_parser('run', help='Run a bound artifact on the existing local interpreted package')
    run.add_argument('--transaction', type=Path, required=True)
    run.add_argument('--tag', type=_tag, required=True)
    run.add_argument('--payload', type=lambda value: _integer(value, 0, 255), default=0)
    run.add_argument('--incoming', type=lambda value: _integer(value, 0, 3), default=3)
    run.add_argument('--timeout-cycles', type=lambda value: _integer(value, 0), default=100_000)
    demo = actions.add_parser('demo', help='Run the unified transaction demonstration gate')
    demo.add_argument('--tag', type=_tag, required=True)
    return parser


def main(argv=None):
    args = build_parser().parse_args(argv)
    try:
        if args.action == 'compile':
            request = json.loads(args.request.read_bytes(), object_pairs_hook=_object)
            transaction = compile_transaction(TransactionSpec.from_request(request))
            transaction.write(args.output)
            print(json.dumps(dict(artifact=str(args.output), request=transaction.spec.request,
                                  **transaction.inspect()), indent=2))
        elif args.action == 'inspect':
            transaction = Transaction.from_bytes(args.transaction.read_bytes())
            print(json.dumps(dict(request=transaction.spec.request, **transaction.inspect()), indent=2))
        elif args.action == 'run':
            transaction = Transaction.from_bytes(args.transaction.read_bytes())
            transaction.validate_payload(args.payload)
            from transaction_package import run_transaction
            run_transaction(args.tag, transaction, payload=args.payload,
                            incoming=args.incoming, timeout_cycles=args.timeout_cycles)
        else:
            runpy.run_path(str(ROOT / 'scripts/check-transaction-programs.py'))['run_gate'](args.tag)
        return 0
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        print('Transaction command failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
