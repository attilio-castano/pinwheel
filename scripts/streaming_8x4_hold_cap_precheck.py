"""Run pinned Tiny Tapeout precheck on the exact hold/capacitance candidate."""

import argparse
from pathlib import Path
import time

from streaming_8x4_e982_native import official
from streaming_8x4_hold_cap_physical import setup


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    parser.add_argument("--deadline", type=int, default=int(time.time()) + 5400)
    args = parser.parse_args()
    official(setup(args.history.resolve()), args.deadline)


if __name__ == "__main__":
    main()
