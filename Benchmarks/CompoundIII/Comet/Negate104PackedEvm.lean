import Benchmarks.CompoundIII.Comet.Negate104Evm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- GENERALIZES cometNegate104 to an input that has not yet been sign-extended.
theorem cometNegate104Packed {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret basic : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hp : signed104 basic ≤ 0)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10633⟩ (basic :: ret :: R) mem aw rdata σ k C) :
    (-(2^103 : Int) < signed104 basic ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (negativePrincipal basic :: R) mem aw rdata σ k' C') ∨
    (¬ -(2^103 : Int) < signed104 basic ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hmin : -(2^103 : Int) < signed104 basic
  · have hne : UInt256.signextend (UInt256.ofNat 12) basic ≠ int104MinWord := by
      intro he; have := (signextend104_eq_min_iff basic).mp he; omega
    have r1 := cometWithExtendedAssetList_block_10633_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (uInt256_eq_zero_of_ne (fun he ↦ hne (uInt256_eq_one_eq he))) h
    have r2 := cometWithExtendedAssetList_block_10652
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    change RD _ _ _ _ _ (UInt256.sub (UInt256.ofNat 0)
      (UInt256.signextend (UInt256.ofNat 12) basic) :: R) _ _ _ _ _ _ at r2
    rw [negativePrincipal_sub hp] at r2
    exact Or.inl ⟨hmin, _, _, r2⟩
  · have hm : signed104 basic = -(2^103 : Int) := by
      have hb := signed104_bounds basic; omega
    have he := (signextend104_eq_min_iff basic).mpr hm
    have r1 := cometWithExtendedAssetList_block_10633_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by change UInt256.eq (UInt256.signextend (UInt256.ofNat 12) basic) int104MinWord ≠ _
          rw [he, uInt256_eq_self]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_10658
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact Or.inr ⟨hmin, cometWithExtendedAssetList_block_7730
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega) r2⟩

end Benchmarks.CompoundIII.Comet
