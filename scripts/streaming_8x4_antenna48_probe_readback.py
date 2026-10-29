"""Pure HOST closed diagnostic reader; no Native or physical promotion."""
import argparse
import json
from streaming_8x4_antenna48_probe import reopen


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--report',required=True)
    args=parser.parse_args();row=reopen(args.report)
    print(json.dumps(dict(schema=row['schema'],mode=row['mode'],
        measurement_complete=row['measurement_complete'],observation=row['observation'],
        passed=False,physical_acceptance=False,eligible_final_target=False),sort_keys=True))


if __name__=='__main__':main()
