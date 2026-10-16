"""Exact completed-checkpoint admission for one failed native candidate."""
import re

def validate_producer_record(record, manifest, state, log):
    assert record['status']=='failed' and record['exit_code']==2
    assert record['container_termination']['status']=='absent' and record['inputs_unchanged'] is True
    assert record['preparation_sha256']==manifest['preparation_sha256']
    assert record['stop_after']=='OpenROAD.STAMidPNR-2'
    for path,digest in manifest['producer_artifacts_sha256'].items():
        assert record['artifacts_sha256'][path]==digest,path
    counts=manifest['inherited_power_metrics']
    assert counts=={'design__power_grid_violation__count':30396,
                    'design__power_grid_violation__count__net:VGND':10392,
                    'design__power_grid_violation__count__net:VPWR':20004}
    for key,value in counts.items():assert state['metrics'][key]==value,key
    assert re.search(r'One or more deferred errors were\s+encountered:',log)
    assert re.search(r'30396\s+power\s+grid\s+violations',log)
    assert state['odb']=='/work/recovery/runs/tt-buffered-sram-access-02/22-openroad-resizertimingpostcts/tt_um_pinwheel_buffered.odb'
    return {'overall_native_flow_status':'failed','overall_native_flow_exit_code':2,
            'completed_checkpoint_diagnostic_allowed':True,'deferred_inherited_power_count':30396,
            'fresh_native_PSM_and_metadata_checks_waived':False}
