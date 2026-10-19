"""Bounded native aggregation of already checked component cell facts.

The imports retain every original gate fact. Only the Cover proof is partitioned;
no circuit endpoint or state equation is taken as a premise.
"""
from streaming_mapped_certificate import namespace_name
from streaming_mapped_liberty import require
from streaming_tt_graph import cover_term, header


def generate(rb, metadata, *, prefix, last_cell_module, chunk=512):
    """Preserve the component realization API with small explicit Covers."""
    namespace_name(prefix)
    namespace_name(last_cell_module)
    namespace = metadata['namespace']
    namespace_name(namespace)
    count = metadata['nodes']
    require(type(count) is int and count > 0, 'Missing complete component cell count')
    require(type(chunk) is int and 1 <= chunk <= 1024, 'Unsupported aggregation chunk')
    parameters = f'(i : Values {rb.INPUT_TYPE}) (s : Values {rb.REGISTER_TYPE})'
    modules, covers = {}, []
    for start in range(0, count, chunk):
        end = min(start + chunk, count)
        name = prefix + 'RealizesChunk' + str(start // chunk)
        fact = 'allCellsChunk' + str(start // chunk)
        lines = [header([last_cell_module], namespace), 'open Pinwheel.Hardware',
            f'theorem {fact} {parameters} : Cover (cellAt i s) {start} {end - start} :=\n  ' +
            cover_term([f'(Cover.single (cell{index} i s))' for index in range(start, end)]),
            'end ' + namespace, '']
        modules[name] = '\n\n'.join(lines)
        covers.append((name, fact))
    name = metadata['realizes_module']
    lines = [header([module for module, _ in covers], namespace), 'open Pinwheel.Hardware',
        f'theorem allCells {parameters} : Cover (cellAt i s) 0 {count} :=\n  ' +
        cover_term([f'({fact} i s)' for _, fact in covers]),
        f'theorem realizes {parameters} : network.Realizes (inputValues i s) (assignment i s) where',
        '  input := by intro wire bound; exact if_pos bound',
        '  node := fun index => (allCells i s).get index.val (Nat.zero_le _) index.isLt index.isLt',
        f'theorem computed {parameters} (wire : Nat) (bound : wire < network.inputs + network.nodes) :',
        '    network.value (inputValues i s) wire = assignment i s wire :=',
        '  (Network.Realizes.unique network _ _ (realizes i s) wire bound).symm',
        'end ' + namespace, '']
    modules[name] = '\n\n'.join(lines)
    return modules
