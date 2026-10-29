"""State-aware observational memory journal, with durable raw ps before parse.

Only explicit Z children have unknown executable/argument identity. Live child
and parent identities remain strict; a parent may never be Z or absent. Kernel
RSS reported for Z is retained as raw data, not used as active memory evidence.
"""
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import threading
import time

import streaming_8x4_final_runtime as R
import streaming_tt_fresh_foundation as F

_LOCK=threading.Lock()
INTERVAL=1.0
LIVE=frozenset('RSDITUW')


def append(path,row):
    with _LOCK:
        with Path(path).open('a')as stream:
            stream.write(json.dumps(row,sort_keys=True)+'\n');stream.flush();os.fsync(stream.fileno())


def executable_identity(command):
    actual=shlex.split(command);F.require(bool(actual),'Observed executable token missing')
    path=Path(actual[0]);F.require(path.is_absolute(),'Observed LIVE executable path is not absolute')
    resolved=path.resolve(strict=True)
    return dict(path=actual[0],resolved=str(resolved),sha256=R.digest(resolved))


def argv_matches(command,argv):
    actual=shlex.split(command)
    # A framework redirect is an independently recorded executable witness.
    # Matching argument tails never claims bin and Python.app binary equality.
    return bool(actual)and actual[1:]==list(argv)[1:]


def lifetime(row):
    return {key:row[key]for key in ('pid','ppid','pgid','birth')}


def active_identity(row):
    F.require(row['state'][0]in LIVE and row['argv_identity_known']is True,'Active process identity required')
    return dict(lifetime(row),command=row['command'],observed_executable=row['observed_executable'])


def ps_argv(pids):return ['/bin/ps','-ww','-p',','.join(map(str,pids)),'-o','pid=,ppid=,pgid=,rss=,lstart=,stat=,command=']


def capture(pids):
    argv=ps_argv(pids)
    try:
        result=subprocess.run(argv,capture_output=True,text=True,timeout=5)
        return dict(argv=argv,returncode=result.returncode,stdout=result.stdout,stderr=result.stderr,error=None)
    except BaseException as error:
        def observed(name):
            value=getattr(error,name,None);return value.decode('utf-8',errors='replace')if isinstance(value,bytes)else value
        return dict(argv=argv,returncode=None,stdout=observed('stdout'),stderr=observed('stderr'),error=type(error).__name__+': '+str(error))


def parse(raw,pids):
    F.require(raw['argv']==ps_argv(pids)and raw['error']is None and raw['returncode']in(0,1)and
        type(raw['stdout'])is str and type(raw['stderr'])is str and not raw['stderr'].strip(),'Process-state observation failed')
    rows={}
    for line in raw['stdout'].splitlines():
        parts=line.strip().split(None,10);F.require(len(parts)==11,'Malformed raw process-state row')
        pid,ppid,pgid,rss=map(int,parts[:4]);state=parts[9]
        F.require(pid in pids and pid not in rows and rss>=0 and re.fullmatch('[A-Za-z+<>=NLsEWwX-]+',state),
            'Unexpected PID/RSS/state observation')
        F.require(state[0]in LIVE|{'Z'},'Unsupported process state')
        zombie=state[0]=='Z'
        rows[pid]=dict(pid=pid,ppid=ppid,pgid=pgid,rss_kib=rss,birth=' '.join(parts[4:9]),state=state,
            command=parts[10],raw_ps_line=line,observed_executable=None if zombie else executable_identity(parts[10]),
            argv_identity_known=not zombie,active_rss_kib=None if zombie else rss)
    return rows


def snapshot(pids,*,raw_path=None,label='startup'):
    raw=capture(pids)
    # Startup callers supply a fresh raw file; Watch uses its phase journal.
    # The raw record is durable before any command/state parsing can fail.
    if raw_path is not None:append(raw_path,dict(event='ps-raw',label=label,**raw))
    return parse(raw,pids)


def validate_sample(rows,parent,child,argv,tracked):
    F.require(parent in rows and set(rows)<=set((parent,child)),'Missing live parent or foreign process observation')
    for pid,row in rows.items():
        F.require(row['pid']==pid and type(row['rss_kib'])is int and row['rss_kib']>=0 and row['birth'],
            'Incomplete process lifetime/RSS observation')
        core=lifetime(row);old=tracked.get(pid)
        F.require(old is None or old['lifetime']==core,'Process PID/parent/group/birth drift')
        if old is None:old=dict(lifetime=core,active_identity=None,zombie_seen=False);tracked[pid]=old
        zombie=row['state'][0]=='Z'
        if pid==parent:F.require(not zombie and row['state'][0]in LIVE,'Parent must remain live')
        if pid==child:F.require(row['ppid']==parent and row['pgid']==child,'Observed child parent/group differs')
        if zombie:
            F.require(pid==child and row['observed_executable']is None and row['argv_identity_known']is False and
                row['active_rss_kib']is None,'Z observation must retain unknown executable/arguments/active RSS')
            old['zombie_seen']=True
        else:
            F.require(row['state'][0]in LIVE and not old['zombie_seen'] and row['argv_identity_known']is True and
                row['active_rss_kib']==row['rss_kib'] and row['observed_executable']==executable_identity(row['command']),
                'LIVE process executable/state identity differs')
            identity=active_identity(row)
            F.require(old['active_identity']is None or old['active_identity']==identity,'LIVE command/executable identity drift')
            old['active_identity']=identity
            if pid==child:F.require(argv_matches(row['command'],argv),'LIVE child argument tail differs')
    return (sum(row['rss_kib']for row in rows.values())if child in rows and rows[child]['state'][0]in LIVE else None)


class Watch:
    def __init__(self,pid,argv,path,label):
        self.pid=pid;self.parent=os.getpid();self.argv=list(argv);self.path=Path(path);self.label=label
        self.stop=threading.Event();self.error=None;self.tracked={};self.samples=0;self.children=0;self.zombies=0
        self.maximum=None;self.started=time.monotonic()
        append(path,dict(event='start',label=label,parent_pid=self.parent,child_pid=pid,argv=self.argv))
        self.thread=threading.Thread(target=self.observe,name='M-state-process-observer',daemon=True);self.thread.start()

    def observe(self):
        try:
            while True:
                seconds=round(time.monotonic()-self.started,6);raw=capture((self.parent,self.pid))
                append(self.path,dict(event='ps-raw',label=self.label,seconds=seconds,**raw))
                rows=parse(raw,(self.parent,self.pid));total=validate_sample(rows,self.parent,self.pid,self.argv,self.tracked)
                self.samples+=1;self.children+=int(self.pid in rows and rows[self.pid]['state'][0]in LIVE)
                self.zombies+=int(self.pid in rows and rows[self.pid]['state'][0]=='Z')
                if total is not None:self.maximum=total if self.maximum is None else max(self.maximum,total)
                append(self.path,dict(event='sample',label=self.label,seconds=seconds,processes={str(k):v for k,v in rows.items()},
                    parent_and_child_rss_kib=total,missing_pids=[pid for pid in(self.parent,self.pid)if pid not in rows],
                    defunct_child_observed=self.pid in rows and rows[self.pid]['state'][0]=='Z'))
                if self.stop.wait(INTERVAL):break
        except BaseException as error:
            self.error=type(error).__name__+': '+str(error)
            append(self.path,dict(event='observer-error',label=self.label,error=self.error))

    def finish(self):
        self.stop.set();self.thread.join(timeout=7)
        if self.thread.is_alive():self.error='Process-state observer did not close'
        row=dict(event='finish',label=self.label,samples=self.samples,child_samples=self.children,zombie_child_samples=self.zombies,
            child_birth_observed=self.pid in self.tracked,maximum_observed_parent_and_child_rss_kib=self.maximum,error=self.error)
        append(self.path,row);F.require(self.error is None and self.samples>0,'State memory observer failed: '+str(self.error));return row


def start(pid,argv,path,*,label):return Watch(pid,argv,path,label)
def finish(watch):
    if watch is not None:return watch.finish()


def verify_startup(path,row,*,label):
    records=[json.loads(line,object_pairs_hook=F.pairs)for line in R.regular(path).read_text().splitlines()]
    F.require(len(records)==1 and records[0]['event']=='ps-raw'and records[0]['label']==label,'Startup raw observation membership differs')
    observed=parse(records[0],(row['pid'],));F.require(observed=={row['pid']:row}and row['state'][0]in LIVE,
        'Actual startup raw/state/identity differs')
    return True


def verify(path,commands,*,require_child_observed=False):
    records=[json.loads(line,object_pairs_hook=F.pairs)for line in R.regular(path).read_text().splitlines()]
    at=0;parent=None;parent_lifetime=None;parent_active=None;summary=[]
    for label,argv in commands:
        F.require(at<len(records),'Missing state memory phase');begin=records[at];at+=1
        F.require(begin.get('event')=='start'and begin.get('label')==label and begin.get('argv')==list(argv)and
            type(begin.get('parent_pid'))is int and type(begin.get('child_pid'))is int and begin['parent_pid']!=begin['child_pid'],
            'State memory start differs')
        if parent is None:parent=begin['parent_pid']
        F.require(parent==begin['parent_pid'],'Memory parent PID changed')
        tracked={};samples=0;children=0;zombies=0;maximum=None;last=-1
        while at<len(records)and records[at].get('event')=='ps-raw':
            raw=records[at];at+=1
            F.require(raw['label']==label and raw['seconds']>=last,'Raw state sample order differs');last=raw['seconds']
            observed=parse(raw,(parent,begin['child_pid']));total=validate_sample(observed,parent,begin['child_pid'],argv,tracked)
            current=lifetime(observed[parent]);active=active_identity(observed[parent])
            if parent_lifetime is None:parent_lifetime=current;parent_active=active
            F.require(current==parent_lifetime and active==parent_active,'Parent lifetime/LIVE command changed between phases')
            F.require(at<len(records),'Raw state sample lacks its parsed observation');value=records[at];at+=1
            dead=begin['child_pid']in observed and observed[begin['child_pid']]['state'][0]=='Z'
            F.require(value==dict(event='sample',label=label,seconds=raw['seconds'],processes={str(k):v for k,v in observed.items()},
                parent_and_child_rss_kib=total,missing_pids=[pid for pid in(parent,begin['child_pid'])if pid not in observed],
                defunct_child_observed=dead),'Parsed state sample differs from exact preceding raw ps')
            samples+=1;children+=int(begin['child_pid']in observed and not dead);zombies+=int(dead)
            if total is not None:maximum=total if maximum is None else max(maximum,total)
        F.require(at<len(records),'Missing state memory closeout');end=records[at];at+=1
        F.require(end==dict(event='finish',label=label,samples=samples,child_samples=children,zombie_child_samples=zombies,
            child_birth_observed=begin['child_pid']in tracked,maximum_observed_parent_and_child_rss_kib=maximum,error=None)and
            samples>0 and(children>0 or not require_child_observed),'State memory coverage/error differs')
        child=tracked.get(begin['child_pid'],{})
        summary.append(dict(label=label,child_samples=children,zombie_child_samples=zombies,
            child_lifetime=child.get('lifetime'),child_active_identity=child.get('active_identity'),
            maximum_observed_parent_and_child_rss_kib=maximum))
    F.require(at==len(records),'Extra/missing state memory phases')
    return dict(phases=len(summary),parent_pid=parent,parent_lifetime=parent_lifetime,parent_active_identity=parent_active,
        observations=summary,missing_or_Z_only_child_active_memory_is_unknown=True,aggregate_outer_guard_remains_authority=True)
