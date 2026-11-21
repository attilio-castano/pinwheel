#!/usr/bin/env python3
"""Run the depth-two SPI configuration of the shared sampled-ready workflow."""

from typed_ready_workflow import main


if __name__ == "__main__":
    main(spi_only=True)
