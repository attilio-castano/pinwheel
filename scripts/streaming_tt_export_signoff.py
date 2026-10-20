"""Export fresh NL/PNL/CDL/abstract LEF from one authoritative actual ODB.

Run inside the pinned physical image. There is no carried netlist input and
no optimization, placement, routing or database write in this hook.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time


def require(value,message):
    if not value:raise ValueError(message)


def regular(path):
    path=Path(path);require(path.is_file() and not path.is_symlink(),'Regular signoff-export input required: '+str(path))
    return path.resolve()


def sha(path):
    with regular(path).open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest()


def literal(path):
    value=str(path)
    require(not any(char in value for char in '{}\n\r'),'Unsupported native Tcl path')
    return '{'+value+'}'


def export(database,config_path,out,*,timeout=900):
    database,config_path=map(regular,(database,config_path));out=Path(out)
    require(not out.exists(),'Preserve earlier actual ODB signoff exports')
    config=json.loads(config_path.read_bytes());top=config['DESIGN_NAME']
    require(re.fullmatch(r'tt_um_pinwheel_streaming_ready_d[24]',top),'Unexpected standard-cell target')
    require(config['RT_MAX_LAYER']=='Metal4' and config['CLOCK_PERIOD']==20,'Changed physical export contract')
    aliases={}
    def pdk_file(path):
        declared=Path(path);resolved=regular(declared.resolve())
        require(declared.is_absolute() and declared.is_relative_to('/work/pdk') and
            resolved.is_relative_to('/work/pdk'),'Signoff export input escaped the pinned PDK mount')
        aliases[str(declared)]=str(resolved);return resolved
    masters=[pdk_file(path) for key in ('CELL_CDLS','EXTRA_CDLS','PAD_CDLS') for path in (config.get(key) or [])]
    require(masters and len(masters)==len(set(masters)),'Missing/duplicate actual CDL master inputs')
    # OpenROAD loads exact actual Liberty ports before attaching the database.
    libraries=config.get('CELL_LIBS')
    require(type(libraries) is dict and config['DEFAULT_CORNER'] in libraries,
        'Resolved default-corner Liberty inventory unavailable')
    libs=libraries[config['DEFAULT_CORNER']]
    require(type(libs) is list and libs,'Explicit native Liberty files required')
    libs=[pdk_file(path) for path in libs]
    executable=regular(Path(shutil.which('openroad')).resolve())
    out.mkdir(parents=True)
    lines=['read_liberty '+literal(path) for path in libs]
    lines+=['read_db '+literal(database),
        'if {[[ord::get_db_block] getName] ne '+literal(top)+'} {error "Actual ODB top differs"}',
        'write_verilog '+literal(out/'implemented.v'),
        'write_verilog -include_pwr_gnd '+literal(out/'implemented.power.v'),
        'write_cdl -include_fillers -masters [list '+' '.join(literal(path) for path in masters)+'] '+literal(out/'implemented.cdl'),
        'write_abstract_lef '+literal(out/'implemented.lef')]
    script=out/'export.tcl';script.write_text('\n'.join(lines)+'\n')
    frozen={str(path):sha(path) for path in (database,config_path,executable,script,regular(__file__),*masters,*libs)}
    command=[str(executable),'-exit','-no_init',str(script)]
    report=dict(schema='pinwheel.streaming-tt-signoff-export.v1',completed=False,qualified=False,
        physical_acceptance_claim=False,top=top,actual_database=str(database),actual_database_sha256=sha(database),
        inherited_netlist=False,input_sha256_before=frozen,pdk_alias_resolution=aliases,argv=command,status='intent',
        boundary='Actual ODB-derived signoff views only. Readback correspondence, timing and layout checks remain separate.')
    def save():(out/'report.json').write_text(json.dumps(report,indent=2,sort_keys=True,allow_nan=False)+'\n')
    start=time.monotonic();save()
    try:
        with (out/'native.log').open('w') as log:
            result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
        report.update(status='completed',exit_code=result.returncode);save()
        require(result.returncode==0,'Native authoritative ODB signoff export failed')
        outputs=('implemented.v','implemented.power.v','implemented.cdl','implemented.lef')
        require(all(regular(out/name).stat().st_size>0 for name in outputs),'Missing/empty native signoff view')
        require(all(sha(path)==value for path,value in frozen.items()),'Actual export input changed')
        require(all(str(Path(path).resolve())==resolved for path,resolved in aliases.items()),'PDK export alias changed')
        report.update(completed=True,inputs_unchanged=True,artifacts_sha256={name:sha(out/name) for name in outputs})
    except BaseException as error:
        report.update(error=type(error).__name__+': '+str(error));raise
    finally:
        report.update(elapsed_seconds=round(time.monotonic()-start,3),native_log_sha256=sha(out/'native.log'));save()
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('database','config','out'):parser.add_argument('--'+name,required=True,type=Path)
    args=parser.parse_args();export(args.database,args.config,args.out)


if __name__=='__main__':main()
