import Pinwheel.Hardware.StreamingMapped.ReductionLogic

namespace Pinwheel.Hardware.StreamingMapped.Reduction

theorem Tree.reduce_and (tree : Tree width) (complete : tree.Complete) (word : BitVec width) :
    tree.evalAnd (fun i => word.getLsbD i.val) = decide (word = BitVec.allOnes width) := by
  have inputs : (fun i : Fin width => (~~~word).getLsbD i.val) =
      (fun i : Fin width => !word.getLsbD i.val) := by
    funext i
    simp only [BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
  have inverted : (~~~word = 0#width) ↔ word = BitVec.allOnes width := by
    constructor
    · intro equal
      have result := congrArg (fun value : BitVec width => ~~~value) equal
      simpa only [BitVec.not_not,BitVec.not_zero] using result
    · intro equal
      simp only [equal,BitVec.not_allOnes]
  have result := tree.logic_not complete (~~~word)
  rw [inputs] at result
  simpa only [Tree.evalAnd,inverted] using result

end Pinwheel.Hardware.StreamingMapped.Reduction
