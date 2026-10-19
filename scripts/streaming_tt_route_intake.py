"""Bind source replay and a closed actual checkpoint to one routing attempt.

This authorizes local diagnostic computation. Every physical acceptance gate
remains independent, including actual final correspondence and extracted STA.
"""
import argparse
from pathlib import Path
import subprocess

import streaming_tt_physical as physical
from streaming_tt_final import admission
from streaming_tt_opt_intake import artifacts
from streaming_tt_signoff import read,regular,require,sha,unchanged,write
from validation_run import fresh_directory


def entry(path):
    path=regular(path);return dict(path=str(path),sha256=sha(path))


def issue(replay_intake,coarse_report,state,tag):
    replay_intake,coarse_report,state=map(regular,(replay_intake,coarse_report,state))
    sealed=read(replay_intake)
    require(sealed.get('schema')=='pinwheel.streaming-tt-replay-intake.v1' and
        sealed.get('passed') is True and sealed.get('qualified') is False,'Independent source replay is not sealed')
    coarse=physical.read(coarse_report);design=Path(coarse['design']).resolve()
    report=dict(schema='pinwheel.streaming-tt-detailed-route-admission.v1',passed=True,
        qualified=False,physical_acceptance_claim=False,status='validating',source_commit=sealed['source_commit'],
        producer_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=physical.ROOT,text=True).strip(),
        physical_producer_commit=coarse['source_commit'],checked=dict(sealed['checked']),
        replay_intake=entry(replay_intake),coarse_report=entry(coarse_report),state=entry(state),
        prepared_input=entry(design/'inputs.json'),
        purpose='one_bounded_detailed_route_and_signoff_attempt',
        final_functional_correspondence_proved=False,final_extracted_timing_qualified=False,
        boundary='Permission to compute with this exact committed-source/replay/physical checkpoint. '
            'Final ODB readback, source correspondence, public-wire diagnostics, extracted timing, '
            'electrical, geometric power, DRC/LVS/antenna and official TT precheck remain required. '
            'Native success or a skipped unsupported check is not physical acceptance.')
    for key in ('parent_intake','frozen_replay','private_axiom_control','candidate_json','candidate_sv'):
        report[key]=sealed[key]
    frozen={value['path']:value['sha256'] for value in report.values()
        if type(value) is dict and set(value)=={'path','sha256'}}
    out=fresh_directory(physical.ROOT/'build/streaming-tt-optimization','route-intake-'+tag).resolve()
    path=out/'report.json';write(path,report)
    try:
        # The same strict consumer runs again during native preparation/use.
        # Independently rehash all earlier closed coarse artifacts here too.
        require(artifacts(coarse_report.parent,exclude=(coarse_report,))==coarse['artifact_sha256'],
            'Closed coarse physical artifact membership/bytes changed')
        admission(path,sha(path));unchanged(frozen)
        report.update(status='admitted',inputs_unchanged=True,closed_coarse_artifacts_verified=True,
            source_replay_intake_sha256=sha(replay_intake))
    except BaseException as error:
        report.update(passed=False,status='rejected',error=type(error).__name__+': '+str(error));raise
    finally:write(path,report)
    print(path,flush=True);return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('replay-intake','coarse-report','state','tag'):parser.add_argument('--'+name,required=True)
    args=parser.parse_args()
    require(regular(__file__).read_bytes()==subprocess.check_output(['git','show','HEAD:scripts/streaming_tt_route_intake.py'],cwd=physical.ROOT),
        'Commit routing admission producer before use')
    issue(args.replay_intake,args.coarse_report,args.state,args.tag)


if __name__=='__main__':main()
