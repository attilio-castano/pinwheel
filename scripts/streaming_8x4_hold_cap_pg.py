"""Run geometric power connectivity on the frozen hold/cap candidate."""

import argparse
from pathlib import Path
import time

from streaming_8x4_e982_native import pg
from streaming_8x4_hold_cap_physical import setup


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history", type=Path, required=True)
    args = parser.parse_args()
    pg(setup(args.history.resolve()), int(time.time()) + 600)


if __name__ == "__main__":
    main()
