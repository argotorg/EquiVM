import Benchmarks.CompoundIII.Comet.PrincipalWords
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_060

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSafe104 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12997⟩ (n :: ret :: R) mem aw rdata σ k C) :
    (n.toNat < 2^104 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret (n :: R)
      mem aw rdata σ k' C') ∨ (¬ n.toNat < 2^104 ∧ RDrev (deployedRuntime v) g s0) := by
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
    (UInt256.ofNat 1)
  have hm : mask.toNat = 2^104-1 := by decide
  by_cases hn : n.toNat < 2^104
  · have r1 := cometWithExtendedAssetList_block_12997_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (ugt_zero (by change n.toNat ≤ mask.toNat; rw [hm]; omega)) h
    have r2 := cometWithExtendedAssetList_block_13014
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    change RD _ _ _ _ _ (UInt256.land n mask :: R) _ _ _ _ _ _ at r2
    rw [u256LandMaskCleanOfToNat n mask hm hn] at r2
    exact Or.inl ⟨hn, _, _, r2⟩
  · have r1 := cometWithExtendedAssetList_block_12997_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [ugt_one (by change mask.toNat < n.toNat; rw [hm]; omega)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact Or.inr ⟨hn, cometWithExtendedAssetList_block_13017
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 3 ≤ 1024; omega) r1⟩

theorem cometSigned104 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hn104 : n.toNat < 2^104)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨13035⟩ (n :: ret :: R) mem aw rdata σ k C) :
    (n.toNat < 2^103 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret (n :: R)
      mem aw rdata σ k' C') ∨ (¬ n.toNat < 2^103 ∧ RDrev (deployedRuntime v) g s0) := by
  let mask := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104))
    (UInt256.ofNat 1)
  let bound := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 103))
    (UInt256.ofNat 1)
  have hm : UInt256.land mask n = n := by
    rw [u256_land_comm]; exact u256LandMaskCleanOfToNat _ _ (bits := 104) rfl hn104
  have hb : bound.toNat = 2^103-1 := by decide
  by_cases hn : n.toNat < 2^103
  · have r1 := cometWithExtendedAssetList_block_13035_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by change UInt256.gt (UInt256.land mask n) bound = UInt256.ofNat 0
          rw [hm]; exact ugt_zero (by rw [hb]; omega)) h
    change RD _ _ _ _ _ (UInt256.land mask n :: ret :: R) _ _ _ _ _ _ at r1
    rw [hm] at r1
    have r2 := cometWithExtendedAssetList_block_13059
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    simp only [cometWithExtendedAssetList_block_13059_stack, signextend104_low hn] at r2
    exact Or.inl ⟨hn, _, _, r2⟩
  · have r1 := cometWithExtendedAssetList_block_13035_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by change UInt256.gt (UInt256.land mask n) bound ≠ UInt256.ofNat 0
          rw [hm, ugt_one (by rw [hb]; omega)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact Or.inr ⟨hn, cometWithExtendedAssetList_block_13064
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega) r1⟩

end Benchmarks.CompoundIII.Comet
