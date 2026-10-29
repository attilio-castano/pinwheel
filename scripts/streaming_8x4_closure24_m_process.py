"""Observational per-process memory journal; canonical proof journals stay exact.

The aggregate outer guard remains the resource authority. Missing short-lived
process observations are explicit unknowns, never inferred zero RSS or births.
"""
import json
import os
from pathlib import Path
import shlex
import subprocess
import threading
import time

import streaming_8x4_final_runtime as R
import streaming_tt_fresh_foundation as F

_LOCK=threading.Lock()
INTERVAL=1.0


def executable_identity(command):
    token=shlex.split(command)[0];path=Path(token)
    F.require(path.is_absolute(),'Observed executable path is not absolute')
    actual=path.resolve(strict=True)
    return dict(path=token,resolved=str(actual),sha256=R.digest(actual))


def lifetime(row):
    return {key:value for key,value in row.items()if key!='rss_kib'}


def append(path,row):
    with _LOCK:
        with Path(path).open('a') as stream:
            stream.write(json.dumps(row,sort_keys=True)+'\n');stream.flush();os.fsync(stream.fileno())


def snapshot(pids):
    """Exact kernel observations, with full untruncated command and start time."""
    result=subprocess.run(['/bin/ps','-ww','-p',','.join(map(str,pids)),
        '-o','pid=,ppid=,pgid=,rss=,lstart=,command='],capture_output=True,text=True,timeout=5)
    F.require(result.returncode in (0,1) and not result.stderr.strip(),'Process memory observation failed')
    rows={}
    for line in result.stdout.splitlines():
        parts=line.strip().split(None,9)
        F.require(len(parts)==10,'Malformed process memory observation')
        pid,ppid,pgid,rss=map(int,parts[:4])
        F.require(pid in pids and pid not in rows and rss>=0,'Unexpected process memory identity')
        rows[pid]=dict(pid=pid,ppid=ppid,pgid=pgid,rss_kib=rss,birth=' '.join(parts[4:9]),command=parts[9],
            observed_executable=executable_identity(parts[9]))
    return rows


def argv_matches(command,argv):
    actual=shlex.split(command)
    # Darwin may show the Python.app framework executable rather than its bin
    # launcher. Preserve that exact first token independently; never assert the
    # two executables are identical merely because their argument tails match.
    return bool(actual) and actual[1:]==list(argv)[1:]


def validate_sample(row,parent,child,argv,births):
    F.require(parent in row and set(row)<=set((parent,child)),'Missing parent or foreign memory observation')
    for pid,value in row.items():
        F.require(value['pid']==pid and type(value['rss_kib']) is int and value['rss_kib']>=0 and
            value['birth'] and value['command'] and value['observed_executable']==executable_identity(value['command']),
            'Incomplete process memory/executable observation')
        identity=lifetime(value)
        F.require(pid not in births or births[pid]==identity,'Process lifetime changed during observation')
        births[pid]=identity
        if pid==child:
            F.require(value['ppid']==parent and value['pgid']==child and argv_matches(value['command'],argv),
                'Observed child parent/group/argument tail differs')
    return sum(value['rss_kib'] for value in row.values())


class Watch:
    def __init__(self,pid,argv,path,label):
        self.pid=pid;self.parent=os.getpid();self.argv=list(argv);self.path=Path(path);self.label=label
        self.stop=threading.Event();self.error=None;self.births={};self.samples=0;self.child_samples=0
        self.maximum=None;self.started=time.monotonic()
        append(path,dict(event='start',label=label,parent_pid=self.parent,child_pid=pid,argv=self.argv))
        self.thread=threading.Thread(target=self.observe,name='M-process-observer',daemon=True);self.thread.start()

    def observe(self):
        try:
            while True:
                rows=snapshot((self.parent,self.pid));total=validate_sample(rows,self.parent,self.pid,self.argv,self.births)
                self.samples+=1;self.child_samples+=int(self.pid in rows)
                if self.parent in rows and self.pid in rows:self.maximum=total if self.maximum is None else max(self.maximum,total)
                append(self.path,dict(event='sample',label=self.label,seconds=round(time.monotonic()-self.started,6),
                    processes={str(k):v for k,v in rows.items()},parent_and_child_rss_kib=total if len(rows)==2 else None,
                    missing_pids=[pid for pid in (self.parent,self.pid) if pid not in rows]))
                if self.stop.wait(INTERVAL):break
        except BaseException as error:self.error=type(error).__name__+': '+str(error)

    def finish(self):
        self.stop.set();self.thread.join(timeout=7)
        if self.thread.is_alive():self.error='Process observer did not close'
        row=dict(event='finish',label=self.label,samples=self.samples,child_samples=self.child_samples,
            child_birth_observed=self.pid in self.births,maximum_observed_parent_and_child_rss_kib=self.maximum,
            error=self.error)
        append(self.path,row);F.require(self.error is None and self.samples>0,'Memory observer failed: '+str(self.error))
        return row


def start(pid,argv,path,*,label):return Watch(pid,argv,path,label)
def finish(watch):
    if watch is not None:return watch.finish()


def verify(path,commands,*,require_child_observed=False):
    rows=[json.loads(line,object_pairs_hook=F.pairs) for line in R.regular(path).read_text().splitlines()]
    at=0;parent=None;parent_lifetime=None;summary=[]
    for label,argv in commands:
        F.require(at<len(rows),'Missing process memory phase');begin=rows[at];at+=1
        F.require(begin.get('event')=='start' and begin.get('label')==label and begin.get('argv')==list(argv) and
            type(begin.get('parent_pid')) is int and type(begin.get('child_pid')) is int and
            begin['parent_pid']!=begin['child_pid'],'Process memory start differs')
        if parent is None:parent=begin['parent_pid']
        F.require(begin['parent_pid']==parent,'Memory journal changed parent process')
        births={};samples=0;children=0;maximum=None;last=-1
        while at<len(rows) and rows[at].get('event')=='sample':
            value=rows[at];at+=1;F.require(value['label']==label and value['seconds']>=last,'Memory phase/order differs');last=value['seconds']
            observed={int(k):v for k,v in value['processes'].items()}
            total=validate_sample(observed,parent,begin['child_pid'],argv,births)
            current=lifetime(observed[parent])
            if parent_lifetime is None:parent_lifetime=current
            F.require(parent_lifetime==current,'Parent lifetime/executable changed between memory phases')
            F.require(value['missing_pids']==[pid for pid in (parent,begin['child_pid'])if pid not in observed] and
                value['parent_and_child_rss_kib']==(total if len(observed)==2 else None),'Memory missing/aggregate observation differs')
            samples+=1;children+=int(begin['child_pid'] in observed)
            if len(observed)==2:maximum=total if maximum is None else max(maximum,total)
        F.require(at<len(rows),'Missing memory phase closeout');end=rows[at];at+=1
        F.require(end==dict(event='finish',label=label,samples=samples,child_samples=children,
            child_birth_observed=begin['child_pid'] in births,maximum_observed_parent_and_child_rss_kib=maximum,error=None)
            and samples>0 and (children>0 or not require_child_observed),'Memory closeout/coverage differs')
        summary.append(dict(label=label,child_samples=children,child_lifetime=births.get(begin['child_pid']),
            maximum_observed_parent_and_child_rss_kib=maximum))
    F.require(at==len(rows),'Extra/missing process memory phases')
    return dict(phases=len(summary),parent_pid=parent,parent_lifetime=parent_lifetime,observations=summary,
        missing_short_lived_child_observations_are_unknown=True,aggregate_outer_guard_remains_authority=True)
