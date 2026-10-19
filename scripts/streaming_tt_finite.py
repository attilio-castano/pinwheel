"""Bounded kernel proofs of complete finite-index propositions.

Each private lemma checks at most 128 concrete indices. The public theorem
retains the full index type and combines every chunk using arithmetic bounds.
"""
import re
from streaming_mapped_liberty import require


def finite_forall(name, count, proposition, *, chunk_width=128):
    require(type(name) is str and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', name),
            'Invalid finite theorem name')
    require(type(count) is int and count >= 0, 'Invalid finite domain size')
    require(type(chunk_width) is int and 1 <= chunk_width <= 256,
            'Finite kernel chunk must be bounded')
    require(callable(proposition), 'Missing finite proposition')
    public = proposition('index')
    require(type(public) is str and public.strip(), 'Empty finite proposition')
    if count == 0:
        return (f'theorem {name} : ∀ index : Fin 0, {public} := by\n'
                '  intro index\n  exact Fin.elim0 index')
    chunks = []
    starts = list(range(0, count, chunk_width))
    for number, start in enumerate(starts):
        width = min(chunk_width, count - start)
        index = f'(⟨{start} + offset.val, by have h := offset.isLt; omega⟩ : Fin {count})'
        chunks.append(f'private theorem {name}_bounded_chunk_{number} : '
                      f'∀ offset : Fin {width}, {proposition(index)} := by decide +kernel')
    body = [f'theorem {name} : ∀ index : Fin {count}, {public} := by',
            '  intro index', '  have index_bound := index.isLt']
    for number, start in enumerate(starts):
        width = min(chunk_width, count - start)
        last = number == len(starts) - 1
        if not last:
            body += [f'  by_cases range_{number} : index.val < {start + width}', '  ·']
        indent = '  ' if last else '    '
        body += [
            indent + f'have chunk_offset : index.val - {start} < {width} := by omega',
            indent + f'have witness := {name}_bounded_chunk_{number} ⟨index.val - {start}, chunk_offset⟩',
            indent + f'have same : (⟨{start} + (index.val - {start}), by omega⟩ : Fin {count}) = index := '
                     f'by apply Fin.ext; change {start} + (index.val - {start}) = index.val; omega',
            indent + 'simpa only [same] using witness',
        ]
    return '\n\n'.join(chunks) + '\n\n' + '\n'.join(body)
