"""Strict consumer for the pinned resize-only function-proof branch."""
def validate_pair_function(proof, expected_resizes, original_signal_cells):
    assert set(proof)=={'original_cells','added_instances','resized_cells','normalized_signal_identity','pinned_resize_functions_checked'},'Unexpected resize-only proof schema'
    assert proof['original_cells']==original_signal_cells,'Signal-module count mismatch'
    assert proof['added_instances']==[],'Unexpected added instances'
    assert proof['resized_cells']==expected_resizes,'Unexpected resized-cell cohort'
    assert proof['normalized_signal_identity'] is True,'Normalized signal identity failed'
    assert proof['pinned_resize_functions_checked'] is True,'All-corner resized pin functions not checked'
