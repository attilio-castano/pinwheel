"""Untrusted reconstruction hints for compact-row selection distribution.

Every discovered mux tree, row correspondence and final equation is checked by
Lean; the Python shape recognizer cannot discharge any semantic equality.
"""
import re


def tree_leaves(graph, root, bits):
    result = {}
    def visit(name, depth, index):
        if depth == bits:
            result[index] = name
            return
        node = graph.nodes[name]
        if node.op != 'mux' or len(node.args) != 3:
            raise ValueError('Not a complete balanced selection tree: ' + name)
        visit(node.args[1], depth + 1, index | (1 << depth))
        visit(node.args[2], depth + 1, index)
    visit(root, 0, 0)
    return result


def selection_source(rb, source, target, source_root, target_root,
                     namespace='Pinwheel.Artifact.BufferedSram.ReferenceLink',
                     hints_module='ReferenceHints', graphs_module='ReferenceGraphs'):
    for name in (namespace, hints_module, graphs_module):
        if not re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*', name):
            raise ValueError('Invalid Lean module or namespace')
    def child(graph, name, operation, width=None):
        node = graph.nodes[name]
        if node.op != operation or width is not None and node.width != width:
            raise ValueError('Changed selection graph shape: ' + name)
        return node
    sw = tree_leaves(source, source_root, 6)
    sr = {}
    for k, name in sw.items():
        word = child(source, name, 'concat', 144)
        low = child(source, word.args[1], 'slice', 88)
        if low.value != 0:
            raise ValueError('Changed row low slice')
        sr[k] = low.args[0]
        child(source, sr[k], 'mux', 92)
    expanded = child(target, target_root, 'concat', 144)
    low = child(target, expanded.args[1], 'slice', 88)
    if low.value != 0:
        raise ValueError('Changed selected row low slice')
    target_compact = low.args[0]
    tr = tree_leaves(target, target_compact, 6)
    def address(graph, root):
        guard = graph.nodes[root].args[0]
        node = child(graph, guard, 'slice', 1)
        if node.value != 0:
            raise ValueError('Changed selection LSB guard')
        return node.args[0]
    source_address, target_address = address(source, source_root), address(target, target_compact)
    def instruction(graph, rows):
        found = set()
        for k, root in rows.items():
            row = child(graph, root, 'mux', 92)
            payload = child(graph, row.args[1], 'concat', 92)
            if payload.args[0] != 'r_metadata' + str(k):
                raise ValueError('Changed row metadata coordinate')
            found.add(payload.args[1])
        if len(found) != 1:
            raise ValueError('Rows no longer share one instruction value')
        return found.pop()
    source_instruction, target_instruction = instruction(source, sr), instruction(target, tr)
    lines=['import ' + hints_module,'import ' + graphs_module,'import Pinwheel.Hardware.Buffered.ArtifactSelection',
    'open Pinwheel.Hardware Pinwheel.Hardware.Buffered',
    'namespace ' + namespace,
    'set_option maxRecDepth 20000','set_option maxHeartbeats 2000000',
    'def dictionary (s : Values Sram.Register) (k : BitVec 4) : BitVec 56 := s (.branch k)']
    for name,ns,arr,w in [('sourceRows','Source',sr,92),('sourceWords','Source',sw,144),('targetRows','RTL',tr,92)]:
     vals=', '.join(f'({ns}.{arr[k]} i s)'for k in range(64))
     lines += [f'def {name} (i : Values Sram.Input) (s : Values Sram.Register) (k : BitVec 6) : BitVec {w} :=',f'  (#[{vals}])[k.toFin.val]\'(k.toFin.isLt)']
    lines += ['theorem source_tree (i : Values Sram.Input) (s : Values Sram.Register) :',
    '    Source.__SOURCE_ROOT i s = ArtifactSelection.select 6 (sourceWords i s) (Source.__SOURCE_ADDRESS i s) := by','  rfl']
    # Per row lookup reconnection is a small, literal 16-way tree identity.
    for k in range(64):
     lines += [f'theorem source_expand_{k} (i : Values Sram.Input) (s : Values Sram.Register) :',
     f'    Source.{sw[k]} i s = ArtifactSelection.expand (dictionary s) (Source.{sr[k]} i s) := by',
     f'  change _ ++ (Source.{sr[k]} i s).extractLsb\' 0 88 = _ ++ (Source.{sr[k]} i s).extractLsb\' 0 88',
     f'  apply congrArg (fun d : BitVec 56 => d ++ (Source.{sr[k]} i s).extractLsb\' 0 88)',
     f'  change _ = dictionary s ((Source.{sr[k]} i s).extractLsb\' 88 4)',
     f'  rw [← ArtifactSelection.select_correct 4 (dictionary s) ((Source.{sr[k]} i s).extractLsb\' 88 4)]',
     '  rfl']
    lines += ['theorem source_words_expand (i : Values Sram.Input) (s : Values Sram.Register) (k : BitVec 6) :',
    '    sourceWords i s k = ArtifactSelection.expand (dictionary s) (sourceRows i s k) := by']
    term='(fun j => Fin.elim0 j)'
    for k in reversed(range(64)):term=f'(Fin.cases (source_expand_{k} i s) {term})'
    lines += ['  have h : ∀ j : Fin 64, sourceWords i s (BitVec.ofFin j) =',
    '      ArtifactSelection.expand (dictionary s) (sourceRows i s (BitVec.ofFin j)) := '+term,'  exact h k.toFin']
    lines += ['theorem target_tree (i : Values Sram.Input) (s : Values Sram.Register) :',
    '    RTL.__TARGET_COMPACT i s = ArtifactSelection.select 6 (targetRows i s) (RTL.__TARGET_ADDRESS i s) := by','  rfl',
     'theorem target_expand (i : Values Sram.Input) (s : Values Sram.Register) :',
     '    RTL.__TARGET_ROOT i s = ArtifactSelection.expand (dictionary s) (RTL.__TARGET_COMPACT i s) := by',
     '  change _ ++ (RTL.__TARGET_COMPACT i s).extractLsb\' 0 88 = _ ++ (RTL.__TARGET_COMPACT i s).extractLsb\' 0 88',
     '  apply congrArg (fun d : BitVec 56 => d ++ (RTL.__TARGET_COMPACT i s).extractLsb\' 0 88)',
     '  change _ = dictionary s ((RTL.__TARGET_COMPACT i s).extractLsb\' 88 4)',
     '  rw [← ArtifactSelection.select_correct 4 (dictionary s) ((RTL.__TARGET_COMPACT i s).extractLsb\' 88 4)]','  rfl']
    for k in range(64):
     guard=f'BitVec.ofBool (decide (({k}#7).toNat < (s (.core .count)).toNat))'
     lines += [f'theorem rows_equal_{k} (i : Values Sram.Input) (s : Values Sram.Register)',
     '    (hinstruction : Source.__SOURCE_INSTRUCTION i s = RTL.__TARGET_INSTRUCTION i s) :',
     f'    Source.{sr[k]} i s = RTL.{tr[k]} i s := by',
     f'  change (if {guard} = 1 then s (.metadata {k}#6) ++ Source.__SOURCE_INSTRUCTION i s else 0#92) =',
     f'    (if {guard} = 1 then s (.metadata {k}#6) ++ RTL.__TARGET_INSTRUCTION i s else 0#92)',
     '  rw [hinstruction]']
    lines += ['theorem rows_equal (i : Values Sram.Input) (s : Values Sram.Register)',
     '    (hinstruction : Source.__SOURCE_INSTRUCTION i s = RTL.__TARGET_INSTRUCTION i s) :',
     '    sourceRows i s = targetRows i s := by','  funext k']
    term='(fun j => Fin.elim0 j)'
    for k in reversed(range(64)):term=f'(Fin.cases (rows_equal_{k} i s hinstruction) {term})'
    lines += ['  have h : ∀ j : Fin 64, sourceRows i s (BitVec.ofFin j) = targetRows i s (BitVec.ofFin j) := '+term,'  exact h k.toFin',
     'theorem selection_entry (i : Values Sram.Input) (s : Values Sram.Register)',
     '    (haddress : Source.__SOURCE_ADDRESS i s = RTL.__TARGET_ADDRESS i s)',
     '    (hinstruction : Source.__SOURCE_INSTRUCTION i s = RTL.__TARGET_INSTRUCTION i s) :',
     '    Source.__SOURCE_ROOT i s = RTL.__TARGET_ROOT i s := by',
     '  calc',
     '    Source.__SOURCE_ROOT i s = ArtifactSelection.select 6 (sourceWords i s) (Source.__SOURCE_ADDRESS i s) := source_tree i s',
     '    _ = ArtifactSelection.select 6 (fun k => ArtifactSelection.expand (dictionary s) (sourceRows i s k)) (Source.__SOURCE_ADDRESS i s) :=',
     '      congrArg (fun f : BitVec 6 → BitVec 144 => ArtifactSelection.select 6 f (Source.__SOURCE_ADDRESS i s))',
     '        (funext (source_words_expand i s))',
     '    _ = ArtifactSelection.expand (dictionary s) (ArtifactSelection.select 6 (sourceRows i s) (Source.__SOURCE_ADDRESS i s)) :=',
     '      ArtifactSelection.expand_select (dictionary s) 6 (sourceRows i s) (Source.__SOURCE_ADDRESS i s)',
     '    _ = ArtifactSelection.expand (dictionary s) (ArtifactSelection.select 6 (targetRows i s) (RTL.__TARGET_ADDRESS i s)) := by',
     '      rw [rows_equal i s hinstruction, haddress]',
     '    _ = ArtifactSelection.expand (dictionary s) (RTL.__TARGET_COMPACT i s) :=',
     '      congrArg (ArtifactSelection.expand (dictionary s)) (target_tree i s).symm',
     '    _ = RTL.__TARGET_ROOT i s := (target_expand i s).symm',
     'end ' + namespace]
    text = '\n'.join(lines) + '\n'
    # Marker names are internal template placeholders, replaced by discovered
    # graph coordinates before elaboration. No marker equality is assumed.
    substitutions = {
        'Source.__SOURCE_ROOT': 'Source.' + source_root,
        'Source.__SOURCE_ADDRESS': 'Source.' + source_address,
        'Source.__SOURCE_INSTRUCTION': 'Source.' + source_instruction,
        'RTL.__TARGET_ROOT': 'RTL.' + target_root,
        'RTL.__TARGET_COMPACT': 'RTL.' + target_compact,
        'RTL.__TARGET_ADDRESS': 'RTL.' + target_address,
        'RTL.__TARGET_INSTRUCTION': 'RTL.' + target_instruction,
    }
    text = re.sub(r'\b(?:Source|RTL)\.[A-Za-z_]\w*\b',
                  lambda match: substitutions.get(match[0], match[0]), text)
    return text, {
        'source': source_root, 'target': target_root,
        'source_address': source_address, 'target_address': target_address,
        'source_instruction': source_instruction, 'target_instruction': target_instruction,
    }
