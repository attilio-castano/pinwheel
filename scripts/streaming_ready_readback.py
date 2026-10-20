"""Exact Ready circuit adapter over the shared raw graph/certificate machinery."""
import streaming_readback as base
from streaming_readback import (CORE_INPUTS, CORE_OUTPUTS, CORE_REGISTERS,
    FRONTEND_INPUTS, FRONTEND_REGISTERS, adapt, check_interface, hints_source,
    graphs_source, sources_source, helper_source, boolean_abstractions,
    links_source, model_source, endpoints_source, proof_source, prefix_imports,
    mutation_specs, mutation_sources)
shared, decomposition = base.shared, base.decomposition


def backend(kind, addr_bits=1):
    rb = base.backend(kind, addr_bits)
    if kind == 'core':
        rb.TOP = 'pinwheel_streaming_ready_core_d' + str(2**addr_bits)
        rb.CIRCUIT = '(Pinwheel.Hardware.StreamingReady.Core.circuit ' + str(addr_bits) + ')'
        rb.NAMESPACE = 'Pinwheel.Artifact.StreamingReadyCoreD' + str(2**addr_bits)
    else:
        rb.NAMESPACE = 'Pinwheel.Artifact.StreamingReadyFrontend'
    rb.HEADER = ('import Pinwheel.Hardware.StreamingReady.CoreEmit\n'
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
