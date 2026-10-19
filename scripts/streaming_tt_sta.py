"""Fresh-corner STA worker inside the pinned physical image.

Input state metrics/SDF are discarded. Nominal probes estimate from the exact
ODB and explicit LEF wire RC. Extracted probes require the actual final exported
netlist and SPEF in addition to ODB. Host orchestration must bind those inputs
to the final route and separately qualify annotation and extraction models.
"""
import argparse
from decimal import Decimal
import hashlib
import json
import math
from pathlib import Path
import time

from physical_checkpoint_sta import analysis_tcl
from physical_timing_acceptance import assess_timing
from streaming_tt_rc import CORNERS, validate_nominal_rc


def require(value,message):
    if not value: raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest()


def fresh_views(request):
    require(request.get('schema')=='pinwheel.streaming-tt-fresh-sta-request.v1', 'Wrong fresh STA request schema')
    require(request.get('mode') in ('nominal','extracted'), 'Unsupported STA measurement mode')
    require(type(request.get('views')) is dict, 'Missing STA views')
    expected={'odb'} if request['mode']=='nominal' else {'odb','nl','spef'}
    require(set(request['views'])==expected, 'Fresh STA refuses inherited/missing views')
    views=request['views']
    require(all(type(views[key]) is str and views[key] for key in expected-{'spef'}), 'Invalid STA file view')
    if request['mode']=='extracted':
        require(type(views['spef']) is dict and set(views['spef'])=={'nom_*'} and
            type(views['spef']['nom_*']) is str and views['spef']['nom_*'],
            'Exactly the declared nominal extracted SPEF is required')
    return dict(views,metrics={})


def native(request_path):
    from librelane.flows.classic import Classic
    from librelane.state import State
    from librelane.steps.openroad import STAMidPNR, STAPostPNR
    request_path=Path(request_path)
    require(request_path.is_file() and not request_path.is_symlink(), 'Regular native STA request required')
    request=json.loads(request_path.read_bytes())
    views=fresh_views(request)
    out=Path(request['out'])
    require(not out.exists(), 'Preserve earlier fresh STA attempts')
    out.mkdir(parents=True)
    frozen={str(request_path.resolve()):sha(request_path)}
    def freeze(path):
        path=Path(path)
        require(path.is_file() and not path.is_symlink(), 'Regular STA input required: '+str(path))
        frozen[str(path.resolve())]=sha(path)
    freeze(request['config']);freeze(request['tech_lef']);freeze(request['sdc'])
    for key,value in request['views'].items():
        if key=='spef':
            for file in value.values():freeze(file)
        else:freeze(value)
    config=json.loads(Path(request['config']).read_bytes())
    require(sorted(config['STA_CORNERS'])==sorted(CORNERS), 'Wrong declared STA corner inventory')
    require(config['CLOCK_PERIOD']==20 and config['CLOCK_PORT'] in ('clk',['clk']), 'Changed 20 ns clock contract')
    explicit_rc=config.get('LAYERS_RC')
    if request['mode']=='nominal':
        from physical_route_intake import ihp_layer_rc
        if not explicit_rc:config['LAYERS_RC']=ihp_layer_rc(request['tech_lef'])
        rc=validate_nominal_rc(config,request['tech_lef'])
        extra=analysis_tcl(dict(verify_nominal_layer_rc=True))
    else:
        rc=dict(extracted=True,rc_corners=['nominal'],min_max_rc_qualified=False)
        extra='puts "PINWHEEL_EXTRACTED_PROPAGATED_CLOCK [get_property [get_clocks clk] is_propagated]"\n'
    report=dict(schema='pinwheel.streaming-tt-fresh-sta.v1',measurements_completed=False,
        qualified=False,physical_acceptance_claim=False,mode=request['mode'],input_sha256=frozen,
        inherited_state_metrics=False,inherited_sdf=False,wire_model=rc,
        nominal_rc_injected_for_probe=request['mode']=='nominal' and not explicit_rc,
        corners={},annotation_qualified=False,extraction_model_qualified=False)
    def save():
        (out/'report.json').write_text(json.dumps(report,indent=2,sort_keys=True,allow_nan=False)+'\n')
    started=time.monotonic();save()
    try:
        extra_path=out/'analysis.tcl';extra_path.write_text(extra)
        report['analysis_tcl_sha256']=sha(extra_path);save()
        all_metrics={}
        for corner in CORNERS:
            cfg=dict(config,DEFAULT_CORNER=corner,STA_CORNERS=[corner],STA_THREADS=1,
                OPENROAD_THREADS=1,PNR_SDC_FILE=request['sdc'],SIGNOFF_SDC_FILE=request['sdc'],
                STA_EXTRA_CORNER_TCL_FILE=str(extra_path))
            flow=Classic(cfg,pdk_root=request['pdk'],pdk='ihp-sg13cmos5l',design_dir=request['design'])
            step=STAMidPNR if request['mode']=='nominal' else STAPostPNR
            directory=out/corner
            after=step(config=flow.config,state_in=State.load(views)).start(step_dir=str(directory))
            metrics={key:float(value) if isinstance(value,Decimal) else value for key,value in after.metrics.items()}
            # Preserve unavailable native values explicitly; required nonfinite
            # timing/electrical fields are rejected by assess_timing below.
            metrics={key:dict(native_nonfinite=str(value)) if type(value) is float and not math.isfinite(value)
                else value for key,value in metrics.items()}
            require(not any('__corner:' in key and not key.endswith('__corner:'+corner) for key in metrics),
                'Inherited/wrong-corner metrics in fresh STA')
            require(all(key+'__corner:'+corner in metrics for key in ('timing__setup__ws','timing__hold__ws')),
                'Missing fresh setup/hold measurement')
            files={str(path.relative_to(directory)):sha(path) for path in sorted(directory.rglob('*')) if path.is_file()}
            logs='\n'.join(path.read_text(errors='replace') for path in directory.rglob('*.log'))
            marker='PINWHEEL_NOMINAL_LAYER_RC_VERIFIED' if request['mode']=='nominal' else 'PINWHEEL_EXTRACTED_PROPAGATED_CLOCK 1'
            require(marker in logs,'Native wire model/clock verification marker missing')
            report['corners'][corner]=dict(metrics=metrics,artifacts_sha256=files);all_metrics.update(metrics);save()
        report['assessment']=assess_timing(all_metrics,list(CORNERS))
        require(all(sha(path)==digest for path,digest in frozen.items()),'Fresh STA inputs changed')
        report.update(measurements_completed=True,inputs_unchanged=True)
    except BaseException as error:
        report.update(error=type(error).__name__+': '+str(error));raise
    finally:
        report['elapsed_seconds']=round(time.monotonic()-started,3);save()
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-request',required=True,type=Path)
    args=parser.parse_args()
    report=native(args.native_request)
    print(json.dumps(dict(measurements_completed=report['measurements_completed'],
        timing=report['assessment']['status'],qualified=False),sort_keys=True))


if __name__=='__main__':main()
