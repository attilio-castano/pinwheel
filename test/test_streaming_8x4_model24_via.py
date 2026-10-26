"""Portable control fixtures only; no ignored intake, Native or solver required."""
from decimal import Decimal as D
from pathlib import Path
import copy
import json
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_model24_via as W
import streaming_8x4_model24_via_readback as R
G,O=W.G,W.O


def definitions():
    result={}
    for name,lo,cut,hi,lower,upper in [
        ('Via1_XY','Metal1','Via1','Metal2',[-145,-105,145,105],[-100,-145,100,145]),
        ('Via1_YY','Metal1','Via1','Metal2',[-105,-145,105,145],[-100,-145,100,145]),
        ('Via2_YX','Metal2','Via2','Metal3',[-105,-145,105,145],[-145,-100,145,100]),
        ('Via3_XY','Metal3','Via3','Metal4',[-145,-105,145,105],[-100,-145,100,145])]:
        result[name]=dict(kind='technology_via',layers=[lo,cut,hi],cut_count=1,source_header='DEFAULT',rectangles_dbu={lo:[lower],cut:[[-95,-95,95,95]],hi:[upper]})
    for i,(name,rows,cols,enclosure,spacing)in enumerate(zip(G.GENERATED,(1,4,4),(2,2,4),([50,125,200,50],[165,50,50,235],[50,235,235,50]),(220,290,290)),1):
        layers=['Metal'+str(i),'Via'+str(i),'Metal'+str(i+1)]
        result[name]=dict(kind='generated_DEF_via',layers=layers,cut_count=rows*cols,cut_positions_not_expanded=True,metal_enclosure_spacing_accuracy_not_qualified=True,
            parameters=dict(VIARULE='via'+str(i)+'Array',CUTSIZE=[190,190],LAYERS=layers,CUTSPACING=[spacing,spacing],ENCLOSURE=enclosure,ROWCOL=[rows,cols]))
    return result


def tech(defs):
    lines=[]
    for m in G.METALS:lines += [f'LAYER {m}', ' TYPE ROUTING ;',f' DIRECTION {G.OLD.DIRECTIONS[m]} ;',f' WIDTH {D(G.DEFAULT[m])/1000} ;',f'END {m}']
    for n in ('Via1','Via2','Via3'):lines += [f'LAYER {n}',' TYPE CUT ;',' RESISTANCE 20 ;',f'END {n}']
    for name in G.NAMED:
        lines += ['VIA '+name+' DEFAULT',' RESISTANCE 20 ;']
        for layer,boxes in G.boxes(defs[name]).items():
            lines.append(' LAYER '+layer+' ;')
            for box in boxes:lines.append(' RECT '+' '.join(str(D(v)/1000)for v in box)+' ;')
        lines.append('END '+name)
    for name in G.GENERATED:
        d=defs[name];lines.append('VIARULE '+d['parameters']['VIARULE']+' GENERATE')
        for layer in d['layers']:
            lines.append(' LAYER '+layer+' ;')
            lines.append(' RECT -.095 -.095 .095 .095 ;'if layer.startswith('Via')else' ENCLOSURE .1 .1 ;')
        lines.append('END '+d['parameters']['VIARULE'])
    return '\n'.join(lines)+'\n'


def native(defs,sheets,cuts,post):
    rows=O.globals_expected(defs,sheets,cuts)
    for case in G.cases(defs):rows+=O.events(case,post)
    return '\n'.join('\t'.join(r)for r in rows)+'\n'


class ViaTests(unittest.TestCase):
    def setUp(self):
        self.defs=definitions();self.sheets={m:'.1'for m in G.METALS};self.cuts={n:'9'for n in ('Via1','Via2','Via3')}

    def test_complete_fixed_matrix_and_scope(self):
        self.assertEqual(len(W.jobs()),6);self.assertEqual(len(G.cases(self.defs)),45)
        self.assertEqual(sum(r['family']is not None for r in G.cases(self.defs)),21)
        p=W.policy();self.assertEqual((p['seconds_per_leaf'],p['work_seconds'],p['outer_seconds']),(30,210,240))
        for k in ('model_qualified','qualified_timing','physical_fit','SPECIALNETS_extraction_qualified','full_via_coverage_qualified'):self.assertIs(p[k],False)
        self.assertIs(p['numerical_conditioning_stop_preserved'],True)

    def test_exact_integer_array_boxes(self):
        self.assertEqual(G.boxes(self.defs[G.GENERATED[0]])['Via1'],[[-300,-95,-110,95],[110,-95,300,95]])
        self.assertEqual([len(G.boxes(self.defs[n])[self.defs[n]['layers'][1]])for n in G.GENERATED],[2,8,16])
        self.assertEqual(G.boxes(self.defs[G.GENERATED[2]])['Metal4'],[[-1050,-865,1050,865]])
        wrong=copy.deepcopy(self.defs[G.GENERATED[0]]);wrong['cut_count']=1
        with self.assertRaises(ValueError):G.boxes(wrong)

    def test_complete_DEF_and_no_hidden_geometry(self):
        text=G.fixture(self.defs);self.assertEqual(G.geometry(text,tech(self.defs),self.defs)['nets'],45)
        for bad in [text.replace(' Via1_XY ( 70000 20000 0 )',' Via1_XY',1),text.replace('WIDTH 440','WIDTH 441',1),text.replace('ROWCOL 1 2','ROWCOL 1 1',1),text.replace('COMPONENTS 0','COMPONENTS 1',1)]:
            with self.assertRaises(ValueError):G.geometry(bad,tech(self.defs),self.defs)

    def test_full_public_decoder_and_terminal_projection(self):
        before=native(self.defs,self.sheets,self.cuts,False);after=native(self.defs,self.sheets,self.cuts,True)
        p=O.pair(before,after,self.defs,self.sheets,self.cuts);self.assertTrue(p['all_via_boxes_and_zero_extensions_observed'])
        self.assertEqual(len(p['after']['source_derived_body_witnesses']),45)

    def test_generated_alias_cut_and_metadata_changes_reject(self):
        before=native(self.defs,self.sheets,self.cuts,False);after=native(self.defs,self.sheets,self.cuts,True)
        mutations=[after.replace('\tBLOCK\tMetal1\tMetal2','\tTECH\tMetal1\tMetal2',1),after.replace('\tBTERM\tV0_L50_A\tV0_L50\tINPUT','\tBTERM\tV0_L50_A\tforeign\tINPUT',1),after.replace('\tPOINT_EXT\t70000\t20000\t0','\tPOINT_EXT\t70000\t20000\t1',1),after+'VIABOX\tforeign\tVia1\t0\t0\t1\t1\n']
        for bad in mutations:
            with self.assertRaises(ValueError):O.pair(before,bad,self.defs,self.sheets,self.cuts)

    def plan(self):return dict(definitions=self.defs,corner_data={c:dict(sheets=self.sheets,cuts={m:r for m in self.cuts})for c,r in zip(W.CORNERS,('5','9','20'))})

    def values(self,plan,job):
        data=plan['corner_data'][job['corner']];out={}
        for r in G.cases(self.defs):
            total=sum(D(data['sheets'][m])*r['length_um']*1000/w for m,w in zip(r['layers'],r['widths']))
            if r['family']:
                percut=D(data['cuts'][self.defs[r['family']]['layers'][1]])if job['policy']=='source_aligned'else D(20 if r['pg'] else 9)
                total+=percut/r['cut_count']
            out[r['name']]=dict(R_ohm=str(total))
        return out

    def test_all_source_predictions_and_preserved_baseline_mismatches(self):
        plan=self.plan();rows=[]
        for j in W.jobs():
            a=W.analyze(self.values(plan,j),plan,j);self.assertTrue(a['source_policy_arithmetic_passed']);rows.append(dict(job=j,analysis=a,passed=True,measurement_completed=True))
        s=W.packet_state(rows,10);self.assertTrue(s['passed']);self.assertEqual(s['baseline_ITF_via_alignment_failures'],42)
        self.assertFalse(W.packet_state(rows[:5],10)['passed']);self.assertFalse(W.packet_state(rows,210.000001)['passed'])

    def test_numeric_failure_never_promotes_candidate(self):
        p=self.plan();j=W.jobs()[3];v=self.values(p,j);v['V6_L50']['R_ohm']=str(D(v['V6_L50']['R_ohm'])+D('.1'))
        self.assertFalse(W.analyze(v,p,j)['source_policy_arithmetic_passed'])
        del v['V0_L50']
        with self.assertRaises(ValueError):W.analyze(v,p,j)

    def test_token_only_delta_and_ambiguity(self):
        text='head\n9 Via1_XY cuts 1 rest\ntail\n';pattern=r'^([0-9.]+) Via1_XY cuts 1 '
        changed,edits=W.token_replace(text,[(pattern,'5','Via1_XY')]);self.assertEqual(changed,text.replace('9 Via1_XY','5 Via1_XY'))
        self.assertEqual(edits[0]['old'],'9')
        with self.assertRaises(ValueError):W.token_replace(text+text,[(pattern,'5','Via1_XY')])

    def test_full_SPEF_graph_parser_rejects_disconnected_chain(self):
        # Exercise the unchanged actual parser, not a model of its adjacency test.
        text='*SPEF "IEEE 1481-1998"\n*R_UNIT 1 OHM\n*NAME_MAP\n*1 n\n*2 n_A\n*3 n_B\n*D_NET *1 0\n*CONN\n*P *2 I\n*P *3 O\n*CAP\n*RES\n1 *2 *3 5\n*END\n'
        self.assertEqual(G.OLD.C.parse_spef(text,{'n'})['n']['R_ohm'],'5')
        with self.assertRaises(ValueError):G.OLD.C.parse_spef(text.replace('1 *2 *3 5','1 *2 x 5\n2 y *3 5'),{'n'})

    def test_duplicate_or_reordered_jobs_cannot_pass(self):
        rows=[dict(job=j,analysis=dict(ITF_via_alignment_failures=0),passed=True,measurement_completed=True)for j in W.jobs()]
        rows[1]['job']=rows[0]['job']
        with self.assertRaises(ValueError):W.packet_state(rows,10)

    def test_actual_proposal_policy_is_inert_and_bounded(self):
        with tempfile.TemporaryDirectory()as d,patch.object(W,'verify',return_value=dict(producer_sha256={})):
            p=Path(d);r=W.proposal(p,'a'*64,p);a=r['argv']
            self.assertEqual(a[a.index('--entrypoint')+1:a.index('--entrypoint')+3],[W.S.N.C.PYTHON,W.S.N.C.IMAGE])
            self.assertEqual((a[a.index('--memory')+1],a[a.index('--memory-swap')+1],a[a.index('--cpus')+1]),('2g','2g','1'))
            self.assertEqual(r['timeout_seconds'],240);self.assertFalse(r['admitted']);self.assertFalse(r['native_executed'])

    def test_complete_prepared_seals_are_mandatory(self):
        p=Path('/owned');plan=dict(files={'fixture.def':dict(sha256='a'*64),'via-source/dbVia.cpp':dict(sha256='b'*64)})
        seals={str(p/n):v['sha256']for n,v in plan['files'].items()};self.assertEqual(R.checked_input_seals(p,plan,dict(input_sha256=seals)),2)
        with self.assertRaises(ValueError):R.checked_input_seals(p,plan,dict(input_sha256={str(p/'fixture.def'):'a'*64}))

    def test_actual_writer_cgroup_schema_and_reader_raw_contract(self):
        kernel={'cpu.max':'100000 100000','memory.max':'2147483648','memory.swap.max':'0','pids.max':'128'}
        with patch.object(Path,'read_text',lambda p:kernel[p.name]):owned=W.A.cgroups()
        self.assertEqual(set(owned),{'cpu_max','memory_max','memory_swap_max','pids_max'})
        job=W.jobs()[4];plan=self.plan();plan['token_witnesses']={job['id']:dict(actual_CUT_R=self.cuts)}
        with tempfile.TemporaryDirectory()as temp:
            base=Path(temp);inputs=base/'inputs';owner=base/'leaf';inputs.mkdir();owner.mkdir()
            contents={'tech.lef':tech(self.defs),'fixture.def':G.fixture(self.defs),'run.tcl':O.tcl(),'rules.txt':'retained source table'}
            for dst,src in W.copied(job).items():(inputs/src).write_text(contents[dst]);(owner/dst).write_text(contents[dst])
            for n in ('before.def','after.def'):(owner/n).write_text(G.fixture(self.defs))
            (owner/'before.tsv').write_text(native(self.defs,self.sheets,self.cuts,False));(owner/'after.tsv').write_text(native(self.defs,self.sheets,self.cuts,True))
            lines=['*SPEF "IEEE 1481-1998"','*R_UNIT 1 OHM','*NAME_MAP'];values=self.values(plan,job)
            for i,n in enumerate(values):lines += [f'*{3*i+1} {n}',f'*{3*i+2} {n}_A',f'*{3*i+3} {n}_B']
            for i,(n,v)in enumerate(values.items()):lines += [f'*D_NET *{3*i+1} 0','*CONN',f'*P *{3*i+2} I',f'*P *{3*i+3} O','*CAP','*RES',f'1 *{3*i+2} *{3*i+3} {v["R_ohm"]}','*END']
            (owner/'result.spef').write_text('\n'.join(lines)+'\n');(owner/'native.log').write_text('MODEL24_VIA_VERSION_BEGIN\nOpenROAD '+W.A.COMMIT+'\nMODEL24_VIA_VERSION_END\nMODEL24_VIA_TERMINAL\n')
            events=dict(low=0,high=0,max=0,oom=0,oom_kill=0);snap=dict(memory_current=1048576,memory_peak=2097152,memory_max=2147483648,memory_swap_max=0,memory_events=events,memory_events_local=events)
            row=dict(schema='pinwheel.model24-via-arithmetic-leaf.v1',plan_sha256='a'*64,job=job,argv=['/native/openroad','-no_init','-exit','run.tcl'],openroad_sha256=W.A.OPENROAD_SHA,native_executed=True,process_tree_reaped=True,inputs_sources_unchanged=True,copied_inputs_unchanged=True,openroad_unchanged=True,model_qualified=False,qualified_timing=False,
                environment=dict(PATH='/native',HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE'),cgroups=owned,cgroup_before=snap,cgroup_after=snap,cgroup_counter_deltas=W.I.counters(snap,snap),maximum_polled_memory_current=1048576,
                output_inventory=W.A.owned_inventory(owner),native_log_sha256=W.E.sha(owner/'native.log'),actual_work_seconds=1,work_budget_passed=True,exit_code=0,timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,
                analysis=W.parse_leaf(owner,plan,job),measurement_completed=True,resource_feasible=True,passed=True)
            receipt=owner/'report.json';receipt.write_text(json.dumps(row));self.assertTrue(R.read_leaf(inputs,'a'*64,plan,job,owner)['passed'])
            row['cgroups']=kernel;receipt.write_text(json.dumps(row))
            with self.assertRaises((ValueError,KeyError)):R.read_leaf(inputs,'a'*64,plan,job,owner)


if __name__=='__main__':unittest.main()
