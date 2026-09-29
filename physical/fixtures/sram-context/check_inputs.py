"""Input guards for these pinned fixtures; not a general GDS or SRAM validator."""
import hashlib
import json
from pathlib import Path
import re

DUMMY='RSC_IHPSG13_CDLYX1_DUMMY'
DRIVER='RM_IHPSG13_1P_WLDRV16X8'
DELAY='RM_IHPSG13_1P_DLY_2'
HERE=Path(__file__).resolve().parent
def require(ok,msg):
    if not ok:raise RuntimeError(msg)

def translate(text,geometry):
    """Only this pinned cell's one metal-1 marker supports this correspondence."""
    block=re.search(r'^\.SUBCKT '+DUMMY+r'\b.*?^\.ENDS[^\n]*',text,re.M|re.S)
    require(block is not None,'Missing delay dummy subcircuit')
    resistors=[l for l in block[0].splitlines() if l.lstrip().upper().startswith('R')]
    require(len(resistors)==1,'Expected one declared resistor')
    line=resistors[0];tokens=line.split()
    require(tokens[:4]==['R0','Z','A','lvsres'],'Unknown resistor identity, terminals or model')
    require(len(tokens)==6,'Missing or extra resistor dimensions')
    dims=dict(token.split('=') for token in tokens[4:])
    require(set(dims)=={'w','l'},'Missing or duplicate resistor dimensions')
    require(float(dims['w'])>0 and float(dims['l'])>0,'Nonpositive resistor dimension')
    require(abs(float(dims['w'])*1e6-geometry['width_um'])<1e-12 and
            abs(float(dims['l'])*1e6-geometry['length_um'])<1e-12,'Source dimensions disagree with marker geometry')
    replacement=line.replace(' lvsres ',' res_metal1 ')
    require(replacement.split()[:3]==tokens[:3] and replacement.split()[4:]==tokens[4:],
            'Translation changed connectivity or dimensions')
    start=block.start()+block[0].index(line)
    return text[:start]+replacement+text[start+len(line):]

def check_parent_ports(text,top):
    block=re.search(r'^\.SUBCKT '+re.escape(top)+r'\b.*?^\.ENDS[^\n]*',text,re.M|re.S)
    require(block is not None,'Missing parent subcircuit')
    lines=block[0].splitlines();ports=lines[0].split()[2:]
    require(len(ports)==len(set(ports)),'Duplicate declared port')
    refs={p:0 for p in ports}
    for line in lines[1:]:
        tokens=line.split()
        if tokens and tokens[0].upper().startswith('X'):
            require(tokens[-2]=='/','Unknown instance syntax')
            for node in tokens[1:-2]:
                if node in refs:refs[node]+=1
    require(all(refs.values()),'Disconnected declared ports: '+','.join(p for p,n in refs.items() if not n))
    return refs

def main():
    identities=json.loads((HERE/'inputs.json').read_text())
    for name,row in identities.items():
        require(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==row['sha256'],'Changed fixture: '+name)
    for name in [DRIVER,DELAY]:
        check_parent_ports((HERE/(name+'.cdl')).read_text(),name)
    geometry=dict(width_um=0.26,length_um=0.6)
    for name in [DUMMY,DELAY]:
        source=(HERE/(name+'.cdl')).read_text();adapted=(HERE/(name+'.metal1.cdl')).read_text()
        # Packaging added license/context comments; compare all subcircuit text exactly.
        body=source[source.index('.SUBCKT'):]
        expected=adapted[adapted.index('.SUBCKT'):]
        require(translate(body,geometry)==expected,'Adapted schematic changed more than the resistor model')
    driver=(HERE/(DRIVER+'.cdl')).read_text()
    dangling=driver.replace('XBUF<0> A<0> Z<0>','XBUF<0> A<0> fault_open')
    require(dangling!=driver,'Missing counterexample target')
    try:check_parent_ports(dangling,DRIVER)
    except RuntimeError:pass
    else:raise RuntimeError('Native false-positive counterexample escaped the port-use guard')
    print(f'{len(identities)} fixture identities, two connected parent interfaces, two exact model translations, and dangling-port refusal passed.')

if __name__=='__main__':main()
