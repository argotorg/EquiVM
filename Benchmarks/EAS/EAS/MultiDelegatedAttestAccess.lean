import Benchmarks.EAS.EAS.MultiDelegatedAttestFieldsRun
import Benchmarks.EAS.EAS.DelegatedBatchIndex

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestLoopStack (n i : Nat) (base available total groups : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat i,base,available,UInt256.ofNat n-⟨1⟩,UInt256.ofNat n,total,groups]++R

theorem easMultiDelegatedAttestAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base available total groups : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+16≤1024)
    (hi : i<n) (hn : n<UInt256.size) (hb : base.toNat+32*i<UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2777⟩ (multiDelegatedAttestLoopStack n i base available total groups R) mem aw out σ k C) :
    if delegatedBatchReferenceValid ee.calldata base i then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨2826⟩
        (multiRequestRoot ee.calldata base i::UInt256.ofNat i::groups::base::available::total::(UInt256.ofNat n-⟨1⟩)::UInt256.ofNat n::R)
        mem aw' out σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  simp only [multiDelegatedAttestLoopStack,List.cons_append,List.nil_append] at rd
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_2777_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons];omega) (by rw [ult_one (by rw [ulit_toNat' i (by omega),ulit_toNat' n hn];exact hi)];decide)
    (by rw [easPatchedValidJumpsRuntime v];jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_2809_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v];jump_dest) r1
  exact easDelegatedBatchIndex v (by simp only [List.length_cons];omega) hi hn hb
    (by rw [easPatchedValidJumps v];jump_dest) r2

end Benchmarks.EAS.EAS
