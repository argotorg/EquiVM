import Benchmarks.CompoundIII.Comet.AbsorbDebtModel
import Benchmarks.CompoundIII.Comet.SignedSubNonnegLeftEvm
import Benchmarks.CompoundIII.Comet.Unsigned256Revert
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_078

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbDebtArithmetic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw old next price account : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hn : next.toNat < 2^255)
    (h : RD (deployedRuntime v) ee g s0 ⟨17381⟩
      (old :: next :: price :: account :: collateralBaseScale v :: R) mem aw rdata σ k C) :
    if AbsorbDebtValid v old next price then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨17410⟩
        (absorbDebtValue v old next price :: account :: absorbPaidWord old next :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_17381 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometSignedSubNonnegLeft (v := v) (a := next) (b := old)
    (by change R.length + 3 + 7 ≤ 1024; omega) hn
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  by_cases hh : signedWord next - signedWord old < (2^255 : Int)
  · rw [if_pos hh] at hr
    obtain ⟨k2, C2, r2⟩ := hr
    have r3 := cometWithExtendedAssetList_block_17390 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have hd := absorbPaidWord_signed hn hh
    by_cases h0 : 0 ≤ signedWord next - signedWord old
    · have hp : (absorbPaidWord old next).toNat < 2^255 :=
        (signedWord_nonneg_iff _).1 (by rw [hd]; exact h0)
      obtain ⟨k4, C4, r4⟩ := cometUnsigned256 (v := v)
        (by change R.length + 3 + 4 ≤ 1024; omega)
        (slt_lit_zero (by decide) (Nat.zero_le _) hp)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      have r5 := cometWithExtendedAssetList_block_17399 (immWords := wordsOf (immStore v))
        (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      have hm := cometMulPrice (v := v) (n := absorbPaidWord old next)
        (by change R.length + 2 + 7 ≤ 1024; omega) (uintCastWord_lt _ _)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
      by_cases hmV : MulPriceValid (absorbPaidWord old next) price (collateralBaseScale v)
      · rw [if_pos hmV] at hm
        rw [if_pos ⟨h0, hh, hmV⟩]
        exact hm
      · rw [if_neg hmV] at hm
        rw [if_neg (fun hv ↦ hmV hv.2.2)]
        exact hm
    · rw [if_neg (fun hv ↦ h0 hv.1)]
      have hp : ¬ (absorbPaidWord old next).toNat < 2^255 := by
        intro hp
        have hg := (signedWord_nonneg_iff _).2 hp
        rw [hd] at hg
        exact h0 hg
      apply cometUnsigned256Revert (v := v) (by change R.length + 4 + 4 ≤ 1024; omega)
        (n := absorbPaidWord old next) ?_ r3
      change UInt256.slt (absorbPaidWord old next) (UInt256.ofNat 0) ≠ UInt256.ofNat 0
      rw [slt_lit_one_high (by decide) (Nat.le_of_not_gt hp)]
      decide
  · rw [if_neg hh] at hr
    rw [if_neg (fun hv ↦ hh hv.2.1)]
    exact hr

end Benchmarks.CompoundIII.Comet
