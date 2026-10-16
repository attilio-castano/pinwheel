"""Host admission of a successful, source-bound scratch two-buffer producer."""
from pathlib import Path
from common import ROOT, IMAGE, read, sha

SOURCE_ODB_SHA = '95f0fdb260de137d5b4f77669c9aaa5eb3bf56e7dc55f4c9b7d51b2b8a16556e'
BOOL_GATES = ('movement_gate_passed','masters_unchanged','net_connectivity_unchanged',
              'clock_tree_unchanged','rows_regions_groups_unchanged','pins_power_geometry_unchanged',
              'placement_statuses_restored','outside_allowlist_placement_unchanged',
              'NDR_rule_definitions_and_net_associations_unchanged','TechLEF_unchanged',
              'native_noncomponent_DEF_unchanged')

def movement_contract(movement,policy,database_digest,netlist_digest):
    assert movement['status']=='measured' and all(movement.get(k) is True for k in BOOL_GATES)
    assert movement['source_database_sha256']==SOURCE_ODB_SHA
    assert movement['output_database_sha256']==database_digest
    allowed=policy['allowed_movable_instances']
    assert sorted(allowed)==['fanout2803','fanout2903'] and len(allowed)==len(set(allowed))
    assert policy['mandatory_destination_neighbors']==[]
    assert sorted(movement['allowed_instance_names'])==sorted(allowed)
    moved=movement['moved_instance_names']
    assert len(moved)==len(set(moved)) and set(moved)==set(allowed)
    assert not set(allowed).intersection(policy['protected_clock_instances'])
    assert movement['before_netlist_sha256']==movement['after_netlist_sha256']==netlist_digest

def rooted(value, base=ROOT):
    raw=Path(value)
    assert '..' not in raw.parts
    p=(raw if raw.is_absolute() else base/raw).resolve()
    assert p.is_relative_to(ROOT.resolve()) and p.is_file(),p
    return p

def validate(manifest_path, selection_path):
    manifest_path,selection_path=rooted(manifest_path),rooted(selection_path)
    m=read(manifest_path)
    assert m['schema']=='pinwheel-buffered-tt-two-buffer-admission-v1'
    assert m['selection_sha256']==sha(selection_path)
    selection=read(selection_path)
    policy_path=rooted(selection['references']['policy']['path'])
    assert sha(policy_path)==selection['references']['policy']['sha256']==m['policy_sha256']
    policy=read(policy_path)
    files={}
    for name,digest in m['files_sha256'].items():
        p=rooted(name)
        assert sha(p)==digest,name
        files[str(p)]=digest
    design=(ROOT/m['design_path']).resolve()
    assert design.is_relative_to(ROOT/'build/physical') and design.is_dir()
    descriptor_path=rooted(m['descriptor_path'])
    producer_path=rooted(m['producer_path'])
    movement_path=rooted(m['movement_path'])
    assert all(p.is_relative_to(design) for p in (descriptor_path,producer_path,movement_path))
    assert all(str(p) in files for p in (descriptor_path,producer_path,movement_path))
    descriptor,producer,movement=map(read,(descriptor_path,producer_path,movement_path))
    assert descriptor['schema']=='pinwheel-buffered-tt-two-buffer-checkpoint-v1'
    assert 'metrics' not in descriptor,'Scratch descriptor must not carry inherited metrics'
    container_root=descriptor['container_design_root']
    assert container_root in ('/work/core','/work/recovery')
    def view(key):
        value=descriptor[key]
        assert isinstance(value,str) and value.startswith(container_root+'/')
        rel=Path(value[len(container_root)+1:])
        assert not rel.is_absolute() and '..' not in rel.parts
        p=rooted(rel,design)
        assert p.is_relative_to(design)
        assert str(p) in files
        return p
    database,netlist=view('odb'),view('nl')
    assert sha(database)==m['database_sha256']
    assert producer['schema']=='pinwheel-buffered-tt-two-buffer-producer-v1'
    assert producer['status']=='passed' and producer['exit_code']==0 and producer['inputs_unchanged']
    assert producer['image_id']==IMAGE
    assert producer['network']=='none'
    assert producer['overall_bound_seconds']<=120
    assert producer['all_in_elapsed_seconds']<=producer['overall_bound_seconds']
    assert producer['container_termination']['status']=='absent'
    assert producer['container_termination']['ownership_label']==producer['ownership_label']
    assert producer['container_termination'].get('owned_container_ids',[])==[]
    assert producer['source_database_sha256']==SOURCE_ODB_SHA==m['source_database_sha256']
    source=rooted(producer['source_database'])
    assert sha(source)==SOURCE_ODB_SHA
    assert producer['input_sha256'].get(str(source))==SOURCE_ODB_SHA
    assert producer['input_sha256'].get(str(policy_path))==sha(policy_path)
    for name,digest in producer['input_sha256'].items():
        p=rooted(name)
        assert sha(p)==digest
        files[str(p)]=digest
    for name,digest in producer['artifact_sha256'].items():
        p=rooted(name,design)
        assert p.is_relative_to(design) and sha(p)==digest
        files[str(p)]=digest
    for p in (database,netlist,descriptor_path,movement_path):
        rel=str(p.relative_to(design))
        assert producer['artifact_sha256'].get(rel)==sha(p),('Native producer artifact not bound',rel)
    assert rooted(producer['completed_descriptor'])==descriptor_path
    assert producer['completed_descriptor_sha256']==sha(descriptor_path)
    movement_contract(movement,policy,sha(database),sha(netlist))
    before=rooted('before.v',design);after=rooted('after.v',design)
    assert sha(before)==sha(after)==sha(netlist)
    assert producer['artifact_sha256'].get('before.v')==sha(before)
    assert producer['artifact_sha256'].get('after.v')==sha(after)
    return files,database,descriptor_path,dict(candidate_native_producer_status='passed',
        candidate_native_producer_exit_code=0,source_reference_native_flow_status='failed',
        source_reference_native_flow_exit_code=2,source_reference_inherited_power_count=30396,
        scratch_metrics_are_provenance_only=True,checkpoint_admission_sha256=sha(manifest_path),
        source_descriptor_sha256=sha(descriptor_path),movement_gate_sha256=sha(movement_path),
        policy_sha256=sha(policy_path),fresh_native_checks_waived=False)
