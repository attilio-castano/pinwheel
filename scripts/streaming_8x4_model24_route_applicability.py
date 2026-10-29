"""HOST-only coarse routed-material applicability, authenticated final views only.

This launches no CAD, solver, container or exporter, changes no historical
receipt, and never qualifies a physical model, envelope, corner or timing.
"""
import argparse
import fnmatch
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_route_def as D
import streaming_8x4_closure24_signoff_execute as V
from streaming_tt_intake import dependency_closure

ROOT=Path(__file__).resolve().parents[1]
TECH_REL='ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/sg13cmos5l_tech.lef'
TECH_SHA='3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5'
HISTORICAL_VIA_CONTROLS=('Via1_XX','Via1_DC1B','Via2_XX','Via3_XX','TopVia1EWNS')
ENTRIES=('scripts/streaming_8x4_model24_route_applicability.py','scripts/streaming_8x4_model24_route_def.py')


def bound(path):
    path=V.regular(path).resolve();return dict(path=str(path),sha256=V.sha(path))


def source_identity():
    closure=dependency_closure(ROOT,ENTRIES)
    return dict(closure=closure,sha256={n:V.sha(ROOT/n) for n in closure['files']})


def authority(views_path):
    views_path=V.regular(views_path).resolve();view,preparation=V.closed_views(views_path)
    base=V.P.verify(Path(preparation['prepared']));pdk=Path(preparation['pdk_root']).resolve()
    D.need(pdk==Path(base['pdk_root']).resolve() and view['target']==preparation['target'],'Same-target certified PDK/view authority differs')
    tech=V.regular(pdk/TECH_REL).resolve();D.need(tech.is_relative_to(pdk) and base['pdk_identity']['complete_files_sha256'].get(TECH_REL)==TECH_SHA==V.sha(tech),
        'Exact certified technology asset identity differs')
    output=views_path.parent;design=V.regular(output/'design.def');stream=V.P.read(output/'native-report.json')
    D.need(stream['source_odb_sha256']==preparation['target']['actual_odb']['sha256'] and stream['generated_files_sha256']['design.def']==V.sha(design),
        'DEF is not the authenticated fresh same-ODB streamout')
    config=V.regular(Path(preparation['source_flow'])/'resolved.json');settings=V.P.read(config)
    matches=[n for pattern,n in settings['TECH_LEFS'].items() if fnmatch.fnmatch(settings['DEFAULT_CORNER'],pattern)]
    native_path=str(Path(settings['PDK_ROOT'])/TECH_REL)
    D.need(matches==[native_path],'Default-corner configured technology selector differs from certified asset')
    paths=dict(views_report=views_path,view_preparation=output/'preparation.json',fresh_DEF=design,canonical_streamout=output/'native-report.json',
        native_geometry=output/'native-geometry.json',actual_cell_pin_inventory=output/'actual-signal/inventory.json',
        certified_preparation=Path(preparation['prepared'])/'preparation.json',resolved_configuration=config,
        selected_final_ODB=Path(preparation['target']['actual_odb']['path']),technology_LEF=tech,pdk_git_tree=Path(base['pdk_tree']['path']))
    bindings={n:bound(p) for n,p in paths.items()};D.need(bindings['selected_final_ODB']['sha256']==preparation['target']['actual_odb']['sha256'],'Selected actual final ODB changed')
    return view,preparation,base,paths,bindings,native_path


def obligations(census):
    named=sorted(n for n,r in census['via_usage'].items() if r['definition']['kind']=='technology_via')
    generated=sorted(n for n,r in census['via_usage'].items() if r['definition']['kind']!='technology_via')
    nondefault={};patches={}
    for name,r in census['layer_usage'].items():
        default=census['technology_layer_metadata'][name]['width_dbu']
        for scope,widths in r['widths_by_scope'].items():
            other={w:n for w,n in widths.items() if int(w)!=default}
            if other:nondefault.setdefault(name,{})[scope]=other
        if r['rect_patch_count']:patches[name]=r['rect_patch_count']
    layers=census['used_routing_layers_including_via_metals']
    return dict(actual_routed_material_layers=layers,actual_used_named_vias=named,actual_used_generated_or_block_vias=generated,
        used_named_vias_outside_historical_five_fixture_names=sorted(set(named)-set(HISTORICAL_VIA_CONTROLS)),
        historical_fixture_names_are_not_qualification=True,generated_via_corner_contact_spreading_coverage_required=bool(generated),
        nondefault_segment_widths_by_scope=nondefault,relative_or_absolute_patch_counts_by_layer=patches,
        patch_min_dimension_is_not_a_wire_linewidth=True,
        TopMetal1_in_routed_material_footprint='TopMetal1' in layers,
        TopVia1_in_routed_via_cuts='TopVia1' in census['cut_layer_occurrences'],
        absent_routed_footprint_does_not_prove_absence_from_ports_or_cell_internal_or_field_context=True,
        same_net_neighbor_spacing_overlap_shield_and_macro_context_not_qualified=True,
        all_eight_model_coverage_fields_remain_unqualified=True,
        complete_precalibration_model_envelope_not_established=True,model_qualified=False,qualified_timing=False)


def build(views_path):
    view,preparation,base,paths,bindings,native_path=authority(views_path);producer=source_identity()
    raw=paths['fresh_DEF'].read_text();top=D.design_name(raw)
    D.need(top==V.Q.TOP,'Fresh DEF top does not match canonical selected target')
    census=D.parse(raw,paths['technology_LEF'].read_text())
    # No successful parse is a geometry/connectivity validity assertion. Nets
    # with multiple endpoints but no routed material are explicitly fail-closed
    # for this actual-target material census; legal short/abutment exceptions
    # require a distinct declared witness, never an inferred successful subset.
    missing={s:r['multi_endpoint_nets_without_route_material'] for s,r in census['routing_sections'].items() if r['multi_endpoint_nets_without_route_material']}
    D.need(not missing,'Missing routed material for multi-endpoint actual DEF nets')
    after=authority(views_path);D.need(after[0]==view and after[1]==preparation and after[4]==bindings and source_identity()==producer,'Final route source/target/view/PDK changed during HOST census')
    return dict(schema='pinwheel.model24-final-route-applicability-census.v1',HOST_only=True,native_executed=False,
        physical_candidate=view['physical_candidate'],selected_final_ODB_sha256=bindings['selected_final_ODB']['sha256'],
        exact_same_target_fresh_view_authority_closed=True,configured_native_technology_path=native_path,
        technology_asset_relative_path=TECH_REL,input_bindings=bindings,producer=producer,inputs_unchanged_during_read=True,
        census=census,model_coverage_obligations=obligations(census),
        inventory_scope='all parsed DEF NETS/SPECIALNETS routed primitives plus resolved named/generated via cut counts, explicit/default/NDR widths and centerline lengths',
        full_layout_material_and_pin_context_complete=False,spacing_context_complete=False,physical_corner_applicability_complete=False,
        qualified_model_envelope=False,model_qualified=False,qualified_timing=False,tapeout_ready=False)


def verify(path):
    path=V.regular(path);row=V.P.read(path)
    D.need(row.get('schema')=='pinwheel.model24-final-route-applicability-census.v1','Wrong typed coarse final-route census')
    actual=build(Path(row['input_bindings']['views_report']['path']));D.need(actual==row,'Final-route applicability source/raw/census/scope changed');return row


def main():
    q=argparse.ArgumentParser(description=__doc__);sub=q.add_subparsers(dest='action',required=True)
    p=sub.add_parser('read');p.add_argument('--views-report',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('verify');p.add_argument('--report',type=Path,required=True);a=q.parse_args()
    if a.action=='verify':verify(a.report);print('verified');return 0
    D.need(not a.output.exists() and a.output.parent.is_dir(),'Preserve previous final-route applicability evidence')
    D.need(not a.output.resolve().is_relative_to(a.views_report.resolve().parent),'Keep new census outside the immutable closed-view artifact tree')
    row=build(a.views_report);a.output.write_bytes(D.canonical(row)+b'\n');print(json.dumps(dict(selected_final_ODB_sha256=row['selected_final_ODB_sha256'],model_qualified=False)))
    return 0
if __name__=='__main__':raise SystemExit(main())
