import Benchmarks.CompoundIII.Comet.NegativePrincipal
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_050

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometNegate104 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret basic : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hp : signed104 basic ≤ 0)
    (hmin : -(2^103 : Int) < signed104 basic)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨10633⟩
      (UInt256.signextend (UInt256.ofNat 12) basic :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (negativePrincipal basic :: R) mem aw rdata σ k' C' := by
  have hne : UInt256.signextend (UInt256.ofNat 12) basic ≠ int104MinWord := by
    intro he
    have := (signextend104_eq_min_iff basic).1 he
    omega
  have heq := uInt256_eq_zero_of_ne (fun he ↦ hne (uInt256_eq_one_eq he))
  have r1 := cometWithExtendedAssetList_block_10633_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
    (by rw [signextend104_idem]; exact heq) h
  simp only [cometWithExtendedAssetList_block_10633_fallthrough_stack, signextend104_idem] at r1
  have r2 := cometWithExtendedAssetList_block_10652
    (immWords := wordsOf (immStore v)) (by omega) hret r1
  simp only [cometWithExtendedAssetList_block_10652_stack, negativePrincipal_sub hp] at r2
  exact ⟨_, _, r2⟩

theorem cometNegate104_revert {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ret basic : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hmin : signed104 basic = -(2^103 : Int))
    (h : RD (deployedRuntime v) ee g s0 ⟨10633⟩
      (UInt256.signextend (UInt256.ofNat 12) basic :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have he := (signextend104_eq_min_iff basic).2 hmin
  have r1 := cometWithExtendedAssetList_block_10633_taken
    (immWords := wordsOf (immStore v)) (by simpa only [List.length_cons] using hstack)
    (by rw [signextend104_idem, he]; change UInt256.eq int104MinWord int104MinWord ≠ _
        rw [uInt256_eq_self]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_10658
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact cometWithExtendedAssetList_block_7730
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega) r2

end Benchmarks.CompoundIII.Comet
