#!/usr/bin/env python3
"""Attempt exactly one offline, resource-bounded frozen buffered TT baseline.

Missing runtime or views produce an explicit blocked receipt. No downloads,
installs, resumption, design changes, or relaxed acceptance gates happen here.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time
import uuid

from buffered_tt_physical import ROOT, read, sha, validate_flow_config, verify_prepared, write


def inspect_runtime(lock):
    result = subprocess.run(['docker','image','inspect',lock['container_tag']],capture_output=True,text=True,timeout=30)
    if result.returncode:
        raise RuntimeError(result.stderr.strip())
    image = json.loads(result.stdout)[0]
    runtime = {key:value for key,value in image['Config'].items() if value is not None}
    digest = hashlib.sha256(json.dumps(runtime,sort_keys=True).encode()).hexdigest()
    if (image['Architecture'] != 'arm64' or image['Os'] != 'linux' or
            image['RootFS']['Layers'] != lock['container_rootfs_diff_ids'] or
            digest != lock['container_runtime_config_sha256']):
        raise ValueError('Local runtime differs from pinned ARM64 LibreLane image')
    return dict(image_id=image['Id'], architecture=image['Architecture'],
                runtime_config_sha256=digest, rootfs_diff_ids=image['RootFS']['Layers'])


def verify_pdk(pdk, lock):
    receipt = read(pdk/'installed.json')
    if receipt['tree_sha256'] != lock['pdk_tree_sha256'] or receipt['revision'] != lock['pdk_revision']:
        raise ValueError('Wrong installed PDK identity')
    for relative,digest in receipt['files_sha256'].items():
        if sha(pdk/relative) != digest:
            raise ValueError('Modified installed PDK file: '+relative)
    for relative,target in receipt['symlinks'].items():
        path = pdk/relative
        if not path.is_symlink() or os.readlink(path) != target:
            raise ValueError('Modified installed PDK symlink: '+relative)
    return dict(directory=str(pdk),receipt_sha256=sha(pdk/'installed.json'),
                revision=receipt['revision'],regular_files=len(receipt['files_sha256']),symlinks=len(receipt['symlinks']))


def cleanup_container(owner, log):
    """Stop only IDs carrying this attempt's unguessable ownership label."""
    query=['docker','container','ls','--all','--no-trunc','--filter',
           'label=org.pinwheel.baseline_owner='+owner,'--format','{{.ID}}']
    receipt={'status':'unconfirmed','ownership_label':owner}
    try:
        result=subprocess.run(query,capture_output=True,text=True,timeout=10)
        if result.returncode:
            receipt['query_error']=result.stderr
            return receipt
        ids=result.stdout.splitlines()
        if any(not re.fullmatch(r'[0-9a-f]{64}',identity) for identity in ids):
            raise ValueError('Malformed ownership-filtered container ID')
        receipt['owned_container_ids']=ids
        for identity in ids:
            subprocess.run(['docker','stop','--time','10',identity],stdout=log,stderr=subprocess.STDOUT,timeout=30)
        result=subprocess.run(query,capture_output=True,text=True,timeout=10)
        if result.returncode:
            receipt['final_query_error']=result.stderr
        elif not result.stdout.strip():
            receipt['status']='absent'
        else:
            receipt['remaining_ids']=result.stdout.splitlines()
    except (OSError,ValueError,subprocess.TimeoutExpired) as error:
        receipt['cleanup_error']=str(error)
    return receipt


def check_container_name(name):
    result=subprocess.run(['docker','container','ls','--all','--filter','name='+name,
                           '--format','{{.Names}}'],capture_output=True,text=True,timeout=10)
    if result.returncode:
        raise RuntimeError(result.stderr.strip())
    if name in result.stdout.splitlines():
        raise ValueError('A preexisting container already owns this name: '+name)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--design',required=True)
    p.add_argument('--tag',required=True)
    p.add_argument('--pdk-root',type=Path,default=ROOT/'build/physical/pdk')
    p.add_argument('--timeout-seconds',type=int,default=1800)
    args=p.parse_args()
    if not 1 <= args.timeout_seconds <= 1800:
        p.error('The single baseline wall-time bound is at most 1800 seconds')
    if any(not re.fullmatch(r'[A-Za-z0-9_-]+',name) for name in [args.design,args.tag]):
        p.error('Use letters, numbers, hyphens and underscores for design/tag')
    base=ROOT/'build/physical'
    design=(base/args.design).resolve()
    if not design.is_relative_to(base.resolve()):
        raise ValueError('Design must stay inside this worktree physical stages')
    receipt_path=base/(args.tag+'-invocation.json')
    log_path=base/(args.tag+'.log')
    run_dir=design/'runs'/args.tag
    if receipt_path.exists() or log_path.exists() or run_dir.exists():
        raise ValueError('Choose a fresh tag; prior baseline evidence is immutable')
    inputs=verify_prepared(design)
    lock=read(ROOT/'tools/physical-toolchain.json')
    receipt=dict(schema='pinwheel-buffered-tt-physical-invocation-v1',status='preflight',
        baseline_started=False,design=args.design,tag=args.tag,
        inputs_sha256=sha(design/'inputs.json'),runner_sha256=sha(Path(__file__)),
        timeout_seconds=args.timeout_seconds,cpus=4,memory='6g',network='none',
        input_status=inputs['status'],boundary=inputs['boundary'],
        disabled_checks=inputs['disabled_checks'],blockers=[])
    if inputs['missing_macro_views']:
        receipt['blockers'].append(dict(kind='macro_views',files=inputs['missing_macro_views']))
    try:
        receipt['runtime']=inspect_runtime(lock)
        check_container_name('pinwheel-'+args.tag)
    except (OSError,subprocess.TimeoutExpired,ValueError,RuntimeError) as error:
        receipt['blockers'].append(dict(kind='runtime',reason=str(error)))
    pdk=args.pdk_root.resolve()
    try:
        receipt['pdk']=verify_pdk(pdk,lock)
    except (OSError,ValueError,KeyError) as error:
        receipt['blockers'].append(dict(kind='pdk',reason=str(error)))
    if receipt['blockers']:
        receipt['status']='blocked'
        write(receipt_path,receipt)
        print(receipt_path)
        return 2
    config=read(design/'core.json')
    validate_flow_config(config)
    owner=str(uuid.uuid4())
    command=['docker','run','--rm','--pull','never','--name','pinwheel-'+args.tag,
        '--label','org.pinwheel.baseline_owner='+owner,
        '--network','none','--cpus','4','--memory','6g',
        '--env','PYTHONPATH=/work/core',
        '--mount',f'type=bind,source={design},target=/work/core',
        '--mount',f'type=bind,source={pdk},target=/work/pdk,readonly',
        '--workdir','/work/core',receipt['runtime']['image_id'],
        'python3','-m','librelane','--manual-pdk','--pdk-root','/work/pdk',
        '--pdk','ihp-sg13cmos5l','--jobs','4','--run-tag',args.tag,
        '--force-run-dir','/work/core/runs/'+args.tag,'/work/core/core.json']
    # LibreLane's --force-run-dir is an existing directory path, rather than
    # the destination-creation behaviour of its default run-tag handling.
    run_dir.mkdir(parents=True)
    receipt.update(command=command,status='running',baseline_started=True,ownership_label=owner)
    write(receipt_path,receipt)
    started=time.monotonic()
    previous_term=signal.getsignal(signal.SIGTERM)
    def interrupt(signum, frame):
        raise KeyboardInterrupt('signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupt)
    with log_path.open('w') as log:
        try:
            result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=args.timeout_seconds)
            receipt.update(exit_code=result.returncode,status='flow_completed' if result.returncode==0 else 'failed')
        except subprocess.TimeoutExpired:
            receipt.update(exit_code=124,status='timed_out',stop_reason='wall_time_limit',container_termination={'status':'unconfirmed'})
            write(receipt_path,receipt)
        except KeyboardInterrupt as error:
            receipt.update(exit_code=130,status='interrupted',stop_reason=str(error) or 'interrupt',container_termination={'status':'unconfirmed'})
            write(receipt_path,receipt)
        except OSError as error:
            receipt.update(exit_code=127,status='failed',launch_error=str(error))
        finally:
            # The same named run is cleaned up after timeout, interruption,
            # launch failure and normal completion; never stop another run.
            receipt.setdefault('container_termination',{'status':'unconfirmed'})
            write(receipt_path,receipt)
            try:
                receipt['container_termination']=cleanup_container(owner,log)
            finally:
                signal.signal(signal.SIGTERM,previous_term)
                write(receipt_path,receipt)
    receipt['elapsed_seconds']=round(time.monotonic()-started,3)
    receipt['artifacts_sha256']={str(log_path.relative_to(base)):sha(log_path)}
    if receipt['container_termination']['status'] != 'unconfirmed':
        for path in sorted(run_dir.rglob('*')):
            if path.is_file() and (path.name in ('metrics.json','metrics.csv','or_metrics_out.json','state_out.json') or 'final' in path.parts):
                receipt['artifacts_sha256'][str(path.relative_to(base))]=sha(path)
    else:
        receipt['status']='cleanup_unconfirmed'
    try:
        verify_prepared(design)
        receipt['inputs_unchanged_after_run']=True
    except (OSError,ValueError) as error:
        receipt['inputs_unchanged_after_run']=False
        receipt['input_change_reason']=str(error)
        receipt['status']='invalidated'
    write(receipt_path,receipt)
    print(receipt_path)
    return receipt['exit_code'] or (3 if receipt['status'] in ('invalidated','cleanup_unconfirmed') else 0)


if __name__=='__main__':
    raise SystemExit(main())
