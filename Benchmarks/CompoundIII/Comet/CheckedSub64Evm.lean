import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCheckedSub64 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hx : x.toNat < 2^64) (hy : y.toNat < 2^64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11523⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    if y.toNat ≤ x.toNat then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub x y :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  split_ifs with hle
  · have r1 := cometWithExtendedAssetList_block_11523_fallthrough
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask64Clean x hx, mask64Clean y hy]; exact ult_zero hle) h
    simp only [cometWithExtendedAssetList_block_11523_fallthrough_stack,
      mask64Clean x hx, mask64Clean y hy] at r1
    have r2 := cometWithExtendedAssetList_block_11544 (immWords := wordsOf (immStore v))
      (by omega) hvalid r1
    exact ⟨_, _, r2⟩
  · have r1 := cometWithExtendedAssetList_block_11523_taken
      (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
      (by rw [mask64Clean x hx, mask64Clean y hy, ult_one (Nat.lt_of_not_ge hle)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7775 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact cometWithExtendedAssetList_block_7730 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) r2

end Benchmarks.CompoundIII.Comet
