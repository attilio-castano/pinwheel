"""Build a checker control from the actual pinned two-transistor inverter GDS.

The negative adds only a long Metal1 shape to the inverter's actual A pin.
This is a detector test, not a candidate design or a DRC-legal geometry.
Run with the pinned native KLayout Python bindings.
"""
import argparse
import hashlib
import json
from pathlib import Path


def require(value,message):
    if not value:raise ValueError(message)


def main():
    import klayout.db as pya
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--library-gds',required=True,type=Path)
    parser.add_argument('--out',required=True,type=Path)
    args=parser.parse_args();require(not args.out.exists(),'Preserve earlier antenna controls')
    before=args.library_gds.read_bytes();source=pya.Layout();source.read(str(args.library_gds))
    name='sg13cmos5l_inv_1';cell=source.cell(name);require(cell is not None,'Missing actual pinned inverter')
    labels=[shape.text for shape in cell.shapes(source.layer(8,25)).each() if shape.is_text() and shape.text.string=='A']
    require(len(labels)==1,'Ambiguous actual inverter A label')
    point=labels[0].trans.disp
    shapes=[shape for shape in cell.shapes(source.layer(8,0)).each() if shape.bbox().contains(point)]
    require(len(shapes)==1 and shapes[0].is_box(),'Actual inverter A must have one Metal1 pin box')
    pin=shapes[0].bbox();require(pin.height()>200 and pin.width()>200,'Unexpected actual A pin geometry')
    extension=pya.Box(point.x-2000000,point.y-100,point.x+10,point.y+100)
    args.out.mkdir(parents=True);files={}
    for case in ('positive','excess-metal1'):
        layout=pya.Layout();layout.dbu=source.dbu;top=layout.create_cell(name);top.copy_tree(cell)
        if case!='positive':top.shapes(layout.layer(8,0)).insert(extension)
        output=args.out/(case+'.gds');layout.write(str(output));files[output.name]=hashlib.sha256(output.read_bytes()).hexdigest()
    require(before==args.library_gds.read_bytes(),'Pinned source GDS changed')
    manifest=dict(schema='pinwheel.streaming-tt-antenna-control-input.v1',qualified=False,
        source_gds_sha256=hashlib.sha256(before).hexdigest(),source_gds=str(args.library_gds),top=name,
        generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),dbu_um=source.dbu,
        actual_pin='A',pin_layer=[8,0],label_layer=[8,25],pin_box_dbu=str(pin),
        added_metal1_box_dbu=str(extension),files_sha256=files,
        boundary='Actual native antenna detector controls only; no streaming candidate acceptance.')
    (args.out/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')


if __name__=='__main__':main()
