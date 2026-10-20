"""Guard membership and public-contract checks for Source proof factoring."""
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_readback as base
import streaming_ready_readback as ready


def fixture():
    rb=ready.backend('frontend',1)
    graph=rb.Graph()
    counter=0
    def add(op,width,*args,value=None):
        nonlocal counter
        name='proposal_'+str(counter);counter+=1
        graph.nodes[name]=rb.Node(width,op,args,value)
        return name
    def lit(width,value=0):return add('lit',width,value=value)
    one=lit(1,1)
    phase=add('eq',1,'r_phase',lit(3,1));bulk=add('not',1,one)
    leaves=[add('not',1,add('and',1,one,one)) for _ in range(64)]
    level=leaves[:]
    while len(level)>1:level=[add('and',1,*level[k:k+2]) for k in range(0,len(level),2)]
    tail=level[0]
    admitted=add('and',1,one,add('and',1,one,add('and',1,tail,one)))
    admitting=add('and',1,phase,add('and',1,bulk,admitted))
    graph.next={name:name for name in rb.REGISTERS}
    graph.outputs={name:one for name in rb.OUTPUTS}
    def next_(name,raw):graph.next[name]=add('mux',rb.REGISTERS[name][0],'initialize',lit(rb.REGISTERS[name][0]),raw)
    for name in ('r_tx_left','r_tx_staging','r_rx_pending','r_work_bulk',
                 'r_export_data','r_export_start','r_export_bits','r_ack_offset'):
        next_(name,add('mux',rb.REGISTERS[name][0],admitting,lit(rb.REGISTERS[name][0]),name))
    code=add('mux',4,one,lit(4),add('mux',4,phase,
        add('mux',4,bulk,add('mux',4,tail,add('mux',4,admitted,lit(4),lit(4)),lit(4)),lit(4)),lit(4)))
    next_('r_code',code)
    next_('r_phase',add('mux',3,one,lit(3),add('mux',3,phase,
        add('mux',3,bulk,add('mux',3,admitted,lit(3),lit(3)),lit(3)),lit(3))))
    return rb,graph,dict(tail=tail,admitted=admitted,admitting=admitting,leaves=leaves)


class Factoring(unittest.TestCase):
    def test_all_public_contracts_and_closed_helpers(self):
        rb,graph,cuts=fixture();text=base.sources_source(rb,graph)
        headers=re.findall(r'(?m)^theorem source_.*? := by',text,re.S)
        expected=[]
        for operation,roots,interface in [('next',graph.next,rb.REGISTERS),('output',graph.outputs,rb.OUTPUTS)]:
            for name,node in roots.items():
                expected.append('theorem source_'+operation+'_'+name+
                    ' (i : Values '+rb.INPUT_TYPE+') (s : Values '+rb.REGISTER_TYPE+') :\n    '+
                    rb.graph_value(graph,node,'Source')+' = ('+rb.CIRCUIT+'.'+operation+
                    ' ('+interface[name][1]+')).eval i s := by')
        self.assertEqual(headers,expected);self.assertEqual(len(headers),45)
        self.assertEqual(text.count('private theorem '),3)
        self.assertEqual(text.count('congrArg context'),12)
        for token in ('sorry','axiom','native_decide','bv_decide'):
            self.assertNotIn(token,text)
        self.assertEqual(base.frontend_source_factors(rb,graph)['cuts'],{k:cuts[k] for k in ('tail','admitted','admitting')})

    def test_renumbering_preserves_cut_selection(self):
        rb,graph,cuts=fixture()
        rename={name:'renumbered_'+name for name in graph.nodes if name.startswith('proposal_')}
        graph.nodes={rename.get(name,name):rb.Node(q.width,q.op,
            tuple(rename.get(a,a) for a in q.args),q.value) for name,q in graph.nodes.items()}
        graph.next={name:rename.get(at,at) for name,at in graph.next.items()}
        graph.outputs={name:rename.get(at,at) for name,at in graph.outputs.items()}
        self.assertEqual(base.frontend_source_factors(rb,graph)['cuts'],
            {k:rename[cuts[k]] for k in ('tail','admitted','admitting')})

    def test_omissions_aliases_widths_and_wrong_root_refuse(self):
        for mutation in ('missing-next','missing-output','aliased-leaf','wrong-tail-op','wrong-width','wrong-init','wrong-code-cut','missing-admitting'):
            rb,graph,cuts=fixture()
            if mutation=='missing-next':graph.next.pop('r_crc')
            elif mutation=='missing-output':graph.outputs.pop('miso')
            elif mutation=='aliased-leaf':
                parent=next(n for n,q in graph.nodes.items() if q.args==tuple(cuts['leaves'][:2]))
                graph.nodes[parent]=rb.Node(1,'and',(cuts['leaves'][0],cuts['leaves'][0]))
            elif mutation=='wrong-tail-op':
                q=graph.nodes[cuts['tail']];graph.nodes[cuts['tail']]=rb.Node(1,'or',q.args)
            elif mutation=='wrong-width':
                q=graph.nodes[cuts['admitted']];graph.nodes[cuts['admitted']]=rb.Node(2,q.op,q.args)
            elif mutation=='wrong-init':
                at=graph.next['r_code'];q=graph.nodes[at];graph.nodes[at]=rb.Node(q.width,q.op,('sck',*q.args[1:]))
            elif mutation=='wrong-code-cut':
                at=next(n for n,q in graph.nodes.items() if q.op=='mux' and q.width==4 and q.args[0]==cuts['tail'])
                q=graph.nodes[at];graph.nodes[at]=rb.Node(q.width,q.op,(cuts['admitted'],*q.args[1:]))
            else:
                at=graph.next['r_ack_offset'];q=graph.nodes[at]
                graph.nodes[at]=rb.Node(q.width,q.op,(*q.args[:2],'r_ack_offset'))
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):base.sources_source(rb,graph)

    def test_core_source_generation_keeps_original_direct_proofs(self):
        rb=ready.backend('core',2);graph=rb.Graph()
        graph.next={name:name for name in rb.REGISTERS};graph.outputs={name:'initialize' for name in rb.OUTPUTS}
        text=base.sources_source(rb,graph)
        self.assertNotIn('source_tail_correct',text)
        self.assertEqual(text.count(' := by\n  rfl'),len(rb.REGISTERS)+len(rb.OUTPUTS))

    def sparse(self,width=16):
        variable=(width,'var',(),0)
        leaf=lambda w,op,args=(),value=None:(w,op,args,value)
        zero=lambda w:leaf(w,'lit',value=0)
        bit=lambda at:leaf(1,'slice',(variable,),at)
        def concat(a,b):return leaf(a[0]+b[0],'concat',(a,b))
        rhs=concat(concat(concat(concat(concat(zero(3),bit(12)),zero(6)),bit(5)),zero(4)),bit(0))
        lhs=leaf(16,'and',(variable,leaf(16,'lit',value=4129)))
        return dict(left=lhs,right=rhs,variables=[(16,'word',0)])

    def test_sparse_projection_class_is_semantically_exact(self):
        pair=self.sparse();proof=base.sparse_mask_proof(pair)
        self.assertIsNotNone(proof)
        self.assertIn('k = 0 ∨',proof);self.assertIn('k = 15 := by omega',proof)
        self.assertIn('decide +kernel',proof)
        self.assertNotIn('Fin.forall_fin_succ',proof)
        # Independently evaluate the proposed projection on all sixteen-bit words.
        for word in range(65536):
            actual=((word>>12)&1)<<12|((word>>5)&1)<<5|(word&1)
            self.assertEqual(word&4129,actual)
        reverse=dict(pair,left=(16,'and',tuple(reversed(pair['left'][2])),None))
        self.assertEqual(base.sparse_mask_proof(reverse),proof.replace(
            '(apply BitVec.eq_of_getLsbD_eq','(rw [BitVec.and_comm]\n     apply BitVec.eq_of_getLsbD_eq',1))
        for mutation in ('mask','shift','foreign-variable','nonzero-padding','wide','arithmetic'):
            changed=self.sparse();left,right=changed['left'],changed['right']
            if mutation=='mask':changed['left']=(16,'and',(left[2][0],(16,'lit',(),4128)),None)
            elif mutation=='shift':changed['right']=(16,'slice',(left[2][0],),1)
            elif mutation=='foreign-variable':changed['right']=(16,'slice',((16,'var',(),1),),0)
            elif mutation=='nonzero-padding':changed['right']=(16,'lit',(),4129)
            elif mutation=='wide':changed['left']=(65,'and',left[2],None)
            else:changed['left']=(16,'add',left[2],None)
            with self.subTest(mutation=mutation):self.assertIsNone(base.sparse_mask_proof(changed))

    def test_sparse_proof_generation_keeps_original_local_type(self):
        rb=ready.backend('frontend',1);pair=self.sparse()
        text=base.helper_source(rb,[pair])
        expected='theorem local_0 (x0 : BitVec 16) :\n    '+rb.render_tree(pair['left'])+' = '+rb.render_tree(pair['right'])+' := by'
        self.assertIn(expected,text)
        self.assertEqual(text.count('have range : k = 0 ∨'),1)
        self.assertIn('all_goals first\n  | (apply BitVec.eq_of_getLsbD_eq',text)
        self.assertIn('grind (splits := 128)',text)  # Original independent fallback retained.


if __name__=='__main__':unittest.main()
