#!/usr/bin/env python3
"""Inspect pinned public SRAM views; this does not install a complete PDK or map a design."""
import hashlib
import json
import re
import urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'build/storage/macros'
REV='5e6d592e4002946a4616f798c357f0f3c06cf3b6'
PREFIX='ihp-sg13g2/libs.ref/sg13g2_sram'
BASE=f'https://raw.githubusercontent.com/IHP-GmbH/IHP-Open-PDK/{REV}/{PREFIX}'
NAMES=['RM_IHPSG13_1P_64x64_c2_bm_bist','RM_IHPSG13_1P_512x8_c3_bm_bist','RM_IHPSG13_1P_512x64_c2_bm_bist']

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    manifest=json.loads((ROOT/'tools/storage-macros.json').read_text())
    assert manifest['library_revision']==REV and manifest['source_prefix']==BASE
    files={}
    def read(path):
        target=OUT/Path(path).name
        if not target.exists():
            with urllib.request.urlopen(BASE+'/'+path,timeout=30) as response: target.write_bytes(response.read())
        files[path]=hashlib.sha256(target.read_bytes()).hexdigest()
        if files[path] != manifest['files_sha256'][path]:
            raise RuntimeError(f'Mismatched pinned SRAM view: {target}')
        return target.read_text()
    metrics={}
    for name in NAMES:
        lef=read('lef/'+name+'.lef')
        model=read('verilog/'+name+'.v')
        sizes=re.findall(r'\bSIZE\s+([\d.]+)\s+BY\s+([\d.]+)',lef)
        assert len(sizes)==1
        x,y=map(float,sizes[0])
        libraries={}
        for corner in ['typ_1p20V_25C','slow_1p08V_125C']:
            lib=read('lib/'+name+'_'+corner+'.lib')
            libraries[corner]=dict(area=float(re.search(r'\barea\s*:\s*([\d.]+)',lib)[1]),time_unit=re.search(r'time_unit\s*:\s*"([^"]+)"',lib)[1])
        metrics[name]=dict(width_um=x,height_um=y,footprint_um2=x*y,libraries=libraries)
    model=read('verilog/RM_IHPSG13_1P_core_behavioral_bm_bist.v')
    assert 'posedge' in model
    report=dict(pdk_link_revision='607e18d4bd9214a52575c194b4181ef449f9252f',library_revision=REV,source_prefix=BASE,files_sha256=files,macros=metrics,boundary='LEF dimensions and Liberty metadata, not mapped machine area. Positive-edge memory behavior requires a separate scheduler contract and physical integration validation.')
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    for name,m in metrics.items(): print(name,m['width_um'],m['height_um'],m['footprint_um2'])
if __name__=='__main__':main()
