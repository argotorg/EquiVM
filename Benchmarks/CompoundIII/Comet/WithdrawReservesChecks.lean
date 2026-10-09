import Benchmarks.CompoundIII.Comet.Unsigned256
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def WithdrawReservesAllowed (reserves amount : UInt256) : Prop :=
  reserves.toNat < 2^255 ∧ amount.toNat ≤ reserves.toNat

instance (reserves amount : UInt256) : Decidable (WithdrawReservesAllowed reserves amount) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem cometWithdrawReservesChecks {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {n mask recipient amount : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨6208⟩ (n :: mask :: recipient :: amount :: R)
      mem aw rdata σ k C) :
    (WithdrawReservesAllowed n amount ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨6226⟩
      (mask :: recipient :: amount :: R) mem aw rdata σ k' C') ∨
    (¬ WithdrawReservesAllowed n amount ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hn : n.toNat < 2^255
  · have hslt : UInt256.slt n (UInt256.ofNat 0) = ⟨0⟩ :=
      slt_lit_zero (by decide) (Nat.zero_le _) hn
    have r1 := cometWithExtendedAssetList_block_6208_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 4 ≤ 1024; omega)
      (by rw [hslt]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_6334
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨k3, C3, r3⟩ := cometUnsigned256 (v := v) (by change R.length + 3 + 4 ≤ 1024; omega)
      hslt (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_6344
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    by_cases ha : amount.toNat ≤ n.toNat
    · have r5 := cometWithExtendedAssetList_block_6220_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
        (ugt_zero ha) r4
      exact Or.inl ⟨⟨hn, ha⟩, _, _, r5⟩
    · have r5 := cometWithExtendedAssetList_block_6220_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
        (by rw [ugt_one (Nat.lt_of_not_ge ha)]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      exact Or.inr ⟨fun hv ↦ ha hv.2,
        cometWithExtendedAssetList_block_6316 (immWords := wordsOf (immStore v))
          (by change R.length + 3 + 3 ≤ 1024; omega) r5⟩
  · have hslt : UInt256.slt n (UInt256.ofNat 0) ≠ ⟨0⟩ :=
      u256_slt_zero_ne_zero_of_high (by change 2^255 ≤ n.toNat; omega)
    have r1 := cometWithExtendedAssetList_block_6208_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 4 ≤ 1024; omega)
      (isZero_eq_zero_of_ne hslt) h
    have r2 := cometWithExtendedAssetList_block_6220_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) hslt
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨fun hv ↦ hn hv.1,
      cometWithExtendedAssetList_block_6316 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 3 ≤ 1024; omega) r2⟩

end Benchmarks.CompoundIII.Comet
