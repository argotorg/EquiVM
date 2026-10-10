import Benchmarks.CompoundIII.Comet.SignedArithmeticWords
import Benchmarks.CompoundIII.Comet.SignedDebtWords
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_039
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_060

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSigned104SubNonneg {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw a b ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hle : signed104 b ≤ signed104 a)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨13082⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    (signed104 a - signed104 b < (2^103 : Int) ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ret
        (UInt256.sub (UInt256.signextend (UInt256.ofNat 12) a)
          (UInt256.signextend (UInt256.ofNat 12) b) :: R) mem aw rdata σ k' C') ∨
    (¬ signed104 a - signed104 b < (2^103 : Int) ∧ RDrev (deployedRuntime v) g s0) := by
  have ha := signed104_bounds a
  have hb := signed104_bounds b
  let maxWord := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 103))
    (UInt256.ofNat 1)
  have hmin : signedWord int104MinWord = -(2^103 : Int) := by decide +kernel
  have hmax : signedWord maxWord = (2^103 : Int) - 1 := by decide +kernel
  have hlow : signedWord (UInt256.signextend (UInt256.ofNat 12) b + int104MinWord) =
      signed104 b - (2^103 : Int) := by
    rw [signedWord_add_signed_of_range, signedWord_signextend104, hmin]
    · omega
    all_goals rw [signedWord_signextend104, hmin]; omega
  have hhigh : signedWord (UInt256.signextend (UInt256.ofNat 12) b + maxWord) =
      signed104 b + (2^103 : Int) - 1 := by
    rw [signedWord_add_signed_of_range, signedWord_signextend104, hmax]
    · omega
    all_goals rw [signedWord_signextend104, hmax]; omega
  have hc0 : UInt256.slt (UInt256.signextend (UInt256.ofNat 12) a)
      (UInt256.signextend (UInt256.ofNat 12) b + int104MinWord) = UInt256.ofNat 0 := by
    rw [signedWord_slt, signedWord_signextend104, hlow, decide_eq_false (by omega)]
    rfl
  have r1 := cometWithExtendedAssetList_block_13082_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 7 ≤ 1024; omega)
    (by change UInt256.land (UInt256.slt _ (_ + int104MinWord)) _ = _
        rw [hc0]; exact uint256_land_zero_left _) h
  by_cases hf : signed104 a - signed104 b < (2^103 : Int)
  · have hc1 : UInt256.sgt (UInt256.signextend (UInt256.ofNat 12) a)
        (UInt256.signextend (UInt256.ofNat 12) b + maxWord) = UInt256.ofNat 0 := by
      rw [signedWord_sgt, signedWord_signextend104, hhigh, decide_eq_false (by omega)]
      rfl
    have r2 := cometWithExtendedAssetList_block_13114_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
      (by change UInt256.land (UInt256.sgt _ (_ + maxWord)) _ = _
          rw [hc1]; exact uint256_land_zero_left _) r1
    exact Or.inl ⟨hf, _, _, cometWithExtendedAssetList_block_13132
      (immWords := wordsOf (immStore v)) (by omega) hret r2⟩
  · have hc1 : UInt256.sgt (UInt256.signextend (UInt256.ofNat 12) a)
        (UInt256.signextend (UInt256.ofNat 12) b + maxWord) = UInt256.ofNat 1 := by
      rw [signedWord_sgt, signedWord_signextend104, hhigh, decide_eq_true (by omega)]
      rfl
    have hc2 : UInt256.slt (UInt256.signextend (UInt256.ofNat 12) b) (UInt256.ofNat 0) =
        UInt256.ofNat 1 := by
      rw [signedWord_slt, signedWord_signextend104]
      change UInt256.fromBool (decide (signed104 b < 0)) = _
      rw [decide_eq_true (by omega)]; rfl
    have r2 := cometWithExtendedAssetList_block_13114_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
      (by change UInt256.land (UInt256.sgt _ (_ + maxWord))
            (UInt256.slt (UInt256.signextend (UInt256.ofNat 12) b) (UInt256.ofNat 0)) ≠ _
          rw [hc1, hc2]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have r3 := cometWithExtendedAssetList_block_7775
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    exact Or.inr ⟨hf, cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) r3⟩

end Benchmarks.CompoundIII.Comet
