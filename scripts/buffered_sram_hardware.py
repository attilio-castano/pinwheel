"""Versioned images for the opt-in latency-one shared-branch SRAM target.

Source admission and upload commands are the shared-branch contract. The target
stores instruction words in two broadcast-written 64x64 SRAM replicas and keeps
row metadata, dictionary, owner state and a START word in controller registers.
This host names that implementation explicitly; it does not select it silently.
"""
from dataclasses import dataclass
import hashlib
import json

from buffered_engine import BufferedProgram
from buffered_shared_branches import (BRANCH_CAPACITY, BRANCH_INDEX_WIDTH,
    INSTRUCTION_CAPACITY, INSTRUCTION_WIDTH, ROW_WIDTH,
    BufferedSharedBranchesHost, BufferedSharedBranchesImage, lower_shared_branches)


FORMAT = 'pinwheel-buffered-shared-branches32-sram64-v1'
SRAM_COPIES = 2
SRAM_ADDRESS_WIDTH = 6
SRAM_WORD_WIDTH = 64
SRAM_WORDS = 64
ALLOCATED_SRAM_BITS = SRAM_COPIES * SRAM_WORDS * SRAM_WORD_WIDTH
ROW_METADATA_WIDTH = ROW_WIDTH - INSTRUCTION_WIDTH
START_WORD_BITS = 64
DECLARED_CONTROLLER_STATE_BITS = (
    INSTRUCTION_CAPACITY * ROW_METADATA_WIDTH + BRANCH_CAPACITY * 56 +
    BRANCH_CAPACITY + 383 + START_WORD_BITS)


@dataclass(frozen=True)
class BufferedSramHardwareImage(BufferedSharedBranchesImage):
    image_format: str = FORMAT

    def __post_init__(self):
        if self.image_format != FORMAT:
            raise ValueError('Wrong shared branch SRAM hardware image version')
        # Re-run the complete source binding, integer/type checks and canonical
        # first-use dictionary reconstruction before making this target's key.
        shared = BufferedSharedBranchesImage(self.words, self.controls,
            self.branch_indices, self.branch_table, self.program_key, self.source)
        object.__setattr__(self, '_reactive', shared._reactive)
        object.__setattr__(self, '_key', hashlib.sha256(json.dumps(self._canonical(),
            sort_keys=True, separators=(',', ':')).encode()).hexdigest())

    def storage(self):
        return dict(super().storage(), image_format=FORMAT,
            declared_state_bits=DECLARED_CONTROLLER_STATE_BITS,
            declared_controller_state_bits=DECLARED_CONTROLLER_STATE_BITS,
            instruction_sram_copies=SRAM_COPIES,
            instruction_sram_words=SRAM_WORDS,
            instruction_sram_word_bits=SRAM_WORD_WIDTH,
            allocated_instruction_sram_bits=ALLOCATED_SRAM_BITS,
            allocated_row_metadata_register_bits=INSTRUCTION_CAPACITY * ROW_METADATA_WIDTH,
            start_instruction_register_bits=START_WORD_BITS)


def lower_sram(program):
    shared = lower_shared_branches(program)
    return BufferedSramHardwareImage(shared.words, shared.controls,
        shared.branch_indices, shared.branch_table, shared.program_key, program)


class BufferedSramHardwareHost(BufferedSharedBranchesHost):
    """Same owned commands with strict source and SRAM-target version binding."""
    def _prepare_image(self, source):
        image = lower_sram(source) if type(source) is BufferedProgram else source
        if type(image) is not BufferedSramHardwareImage:
            raise ValueError('Shared branch SRAM load requires its versioned image')
        return BufferedSramHardwareImage.from_bytes(image.to_bytes())
