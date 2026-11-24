"""Exact Ready circuit adapter over the shared raw graph/certificate machinery."""
import streaming_readback as base
import readback_descriptor
from streaming_readback import (FRONTEND_INPUTS, adapt, check_interface, hints_source,
    graphs_source, sources_source, helper_source, boolean_abstractions,
    links_source, model_source, endpoints_source, proof_source, prefix_imports, register_term,
    mutation_specs, mutation_sources)
shared, decomposition = base.shared, base.decomposition


def descriptor_name(kind, addr_bits, tx_layout='ring'):
    """The checked-in descriptor for a Ready module. The shift TX layout has no
    descriptor of its own: it starts from the Streaming core's, whose ports and
    registers it shares, and edits the register table."""
    if kind == 'frontend':
        return 'frontend'
    return ('streaming' if tx_layout == 'shift' else 'ready') + '-core-d' + str(2**addr_bits)


def backend(kind, addr_bits=1, *, tx_layout='ring', descriptor=None):
    """Configure the importer for one Ready module.

    The module, types, circuit and port tables come from a Lean read-back
    descriptor: `descriptor` (a path or a loaded descriptor) when given, else
    the checked-in copy named by `descriptor_name`. A descriptor for another
    module is rejected."""
    if tx_layout not in ('ring', 'shift') or (tx_layout == 'shift' and (kind != 'core' or addr_bits != 1)):
        raise ValueError('Unsupported Ready TX layout for this component or depth')
    expected = readback_descriptor.checked_in(descriptor_name(kind, addr_bits, tx_layout))
    if descriptor is None:
        descriptor = expected
    elif not isinstance(descriptor, dict):
        descriptor = readback_descriptor.load(descriptor)
    if descriptor['module'] != expected['module']:
        raise ValueError(f"Descriptor for {descriptor['module']}, expected {expected['module']}")
    rb = base.backend(kind, addr_bits)
    readback_descriptor.apply(rb, descriptor)
    shift_import = ''
    if kind == 'core':
        rb.NAMESPACE = 'Pinwheel.Artifact.StreamingReadyCoreD' + str(2**addr_bits)
        if tx_layout == 'shift':
            shift_import = 'import Pinwheel.Hardware.StreamingReady.TxShiftCore\n'
            shift = 'Pinwheel.Hardware.StreamingReady.TxShiftCore'
            rb.TOP = readback_descriptor.checked_in(descriptor_name(kind, addr_bits))['module']
            rb.CIRCUIT = shift + '.circuit'
            rb.REGISTER_TYPE = shift + '.Register'
            rb.NAMESPACE += 'Shift'
            rb.RETAINED_REGISTER = shift + '.retained'
            del rb.REGISTERS['r_tx_head'], rb.REGISTERS['r_tx_tail']
            rb.REGISTER_PATTERNS = {name: f'⟨{ctor}, _⟩' for name, (_, ctor) in rb.REGISTERS.items()}
            rb.REGISTERS = {name: (width, register_term(rb, ctor))
                            for name, (width, ctor) in rb.REGISTERS.items()}
    else:
        rb.NAMESPACE = 'Pinwheel.Artifact.StreamingReadyFrontend'
    rb.HEADER = (shift_import + 'import Pinwheel.Hardware.StreamingReady.CoreEmit\n'
        'import Pinwheel.Hardware.Streaming.FrontendEmit\n'
        'open Pinwheel.Hardware Pinwheel.Hardware.Streaming\nnamespace ' + rb.NAMESPACE + '\n'
        'set_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\n'
        'set_option linter.unusedVariables false\n')
    return rb


def helper_source(rb, pairs):
    text = base.helper_source(rb, pairs)
    text = 'import Pinwheel.Hardware.StreamingReady.Readback\n' + text
    return text.replace('  try simp only [Pinwheel.Hardware.Streaming.Readback.count_lt2,',
        '  try simp only [Pinwheel.Hardware.StreamingReady.Readback.phase_lt5, Pinwheel.Hardware.Streaming.Readback.count_lt2,')


def mutation_specs(kind):
    result = base.mutation_specs(kind)
    if kind == 'frontend':
        # Exporter term limits can name the retained mux before its register
        # driver. Mutate the same retained-state arc in either spelling. The
        # caller still requires one match and a changed imported next graph.
        result = [(name,
            r'(?m)^(\s*(?:r_export_bits\s*<=|wire\s+\[6:0\]\s+_GEN_[0-9]+\s*=)[^;]*:\s*)r_export_bits;'
            if name == 'retained-export' else pattern, replacement, operation)
            for name, pattern, replacement, operation in result]
    if kind == 'core':
        result = [(name,
            r'(?m)^(\s*(?:r_word0\s*<=|wire\s+\[63:0\]\s+_GEN_[0-9]+\s*=)[^;]*\?\s*)word(\s*:\s*r_word0;)'
            if name == 'program-bank' else pattern, replacement, operation)
            for name, pattern, replacement, operation in result]
        result += [
            ('sampler-stage', r'(?m)^(\s*(?:r_stage2\s*<=|wire\s+\[1:0\]\s+_GEN_[0-9]+\s*=)[^;]*:\s*)r_stage1(;)',
                r'\g<1>raw_inputs\g<2>', 'next'),
            ('guard-bypass', r'(?m)^(\s*(?:r_current_word\s*<=|wire\s+\[63:0\]\s+_GEN_[0-9]+\s*=)[^;]*\?\s*)(_GEN_[0-9]+)(\s*:\s*r_current_word;)',
                r"\g<1>(\g<2> & 64'hbfffffffffffffff)\g<3>", 'next'),
        ]
    return result
