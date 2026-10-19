"""Read actual native KLayout reports without equating process exit with pass.

These are component results. The caller must bind native invocation, source
deck, unchanged GDS/reference and runtime before layout acceptance.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET


def require(value,message):
    if not value:raise ValueError(message)


def geometry_result(path,top,*,expected_categories=None):
    root=ET.parse(path).getroot()
    require(root.tag=='report-database' and root.findtext('top-cell')==top,'Wrong geometry report/top')
    categories=root.find('categories');items=root.find('items');cells=root.find('cells')
    require(categories is not None and items is not None and cells is not None,'Incomplete geometry report')
    names=[]
    def visit(parent,prefix=()):
        for category in parent:
            require(category.tag=='category','Unexpected geometry category entry')
            name=category.findtext('name');require(type(name) is str and name,'Unnamed geometry category')
            full=(*prefix,name);names.append(full)
            nested=category.find('categories')
            if nested is not None:visit(nested,full)
    visit(categories)
    require(names and len(names)==len(set(names)),'Empty/duplicate geometry category inventory')
    if expected_categories is not None:
        require(set(names)==set(map(tuple,expected_categories)),'Incomplete/changed native geometry checks')
    known_cells=[cell.findtext('name') for cell in cells]
    require(known_cells and len(known_cells)==len(set(known_cells)) and top in known_cells,'Incomplete geometry cell inventory')
    counts=Counter();multiplicity=0
    for item in items:
        require(item.tag=='item','Unexpected geometry report entry')
        category=item.findtext('category') or ''
        # KLayout report category paths are single quoted segments.
        parts=tuple(re.findall(r"'([^']+)'",category))
        require(parts in set(names) and '.'.join("'"+part+"'" for part in parts)==category,
            'Unknown/malformed geometry violation category')
        require(item.findtext('cell') in known_cells,'Unresolved geometry violation cell')
        count=item.findtext('multiplicity') or ''
        require(re.fullmatch(r'[1-9][0-9]*',count) is not None,'Invalid geometry violation multiplicity')
        multiplicity+=int(count);counts[category]+=1
    return dict(passed=len(items)==0,top=top,categories=[list(name) for name in names],
        category_count=len(names),violation_items=len(items),violation_multiplicity=multiplicity,
        violations_by_category=dict(sorted(counts.items())),
        check_inventory_qualified=expected_categories is not None)


def lvs_result(path,top):
    import klayout.db as pya
    database=pya.LayoutVsSchematic();database.read(str(path))
    pairs=[]
    for pair in database.xref().each_circuit_pair():
        layout,schematic=pair.first(),pair.second()
        pairs.append(dict(layout=None if layout is None else layout.name,
            schematic=None if schematic is None else schematic.name,status=str(pair.status())))
    require(pairs,'Empty native LVS comparison')
    top_pairs=[pair for pair in pairs if pair['layout']==top]
    require(len(top_pairs)==1 and top_pairs[0]['schematic']==top.upper(),'Missing/misbound LVS top circuit')
    layout_devices=sum(1 for circuit in database.netlist().each_circuit() for _ in circuit.each_device())
    schematic_devices=sum(1 for circuit in database.reference.each_circuit() for _ in circuit.each_device())
    require(layout_devices>0 and schematic_devices>0,'Vacuous native LVS device inventory')
    return dict(passed=all(pair['status']=='Match' and pair['layout'] is not None and pair['schematic'] is not None
        for pair in pairs),top=top,circuits=pairs,layout_devices=layout_devices,schematic_devices=schematic_devices)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kind',choices=('geometry','lvs'),required=True)
    parser.add_argument('--report',required=True,type=Path)
    parser.add_argument('--top',required=True)
    parser.add_argument('--expected-categories',type=Path)
    parser.add_argument('--out',required=True,type=Path)
    args=parser.parse_args();require(args.report.is_file() and not args.report.is_symlink(),'Regular native report required')
    require(not args.out.exists(),'Preserve earlier native report interpretation')
    before=args.report.read_bytes()
    expected=None if args.expected_categories is None else json.loads(args.expected_categories.read_bytes())
    result=lvs_result(args.report,args.top) if args.kind=='lvs' else geometry_result(args.report,args.top,expected_categories=expected)
    require(before==args.report.read_bytes(),'Native report changed during interpretation')
    report=dict(schema='pinwheel.streaming-tt-layout-result.v1',kind=args.kind,qualified=False,
        physical_acceptance_claim=False,report=str(args.report),report_sha256=hashlib.sha256(before).hexdigest(),
        reader_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),result=result,
        boundary='Native report interpretation only; unchanged native inputs, deck/runtime and complete invocation require separate binding.')
    args.out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(kind=args.kind,passed=result['passed'],qualified=False),sort_keys=True))


if __name__=='__main__':main()
