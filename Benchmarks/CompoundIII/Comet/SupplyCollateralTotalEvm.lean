import Benchmarks.CompoundIII.Comet.SupplyCollateralRead
import Benchmarks.CompoundIII.Comet.CheckedAdd128Evm
import Benchmarks.CompoundIII.Comet.Mask128Evm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_034
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_065

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyCollateralTotal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray}
    {aw ptr free amount total reserved ret sender dst : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (asset : AccountAddress)
    (hstack : R.length + 16 ≤ 1024) (ht : total.toNat < 2^128) (ha : amount.toNat < 2^128)
    (hv : AssetValid out) (hm : TotalsCollateralMemory mem free total reserved)
    (hs : WordStructMemory mem ptr 8 (fun i ↦ calldataWord out (32 * i)))
    (hlo : 96 ≤ ptr.toNat) (hsep : ptr.toNat + 256 ≤ free.toNat)
    (h : RD (deployedRuntime v) ee g s0 ⟨13881⟩
      (free :: EVM.word asset.val :: ptr :: ⟨2^128-1⟩ :: amount :: sender :: dst :: ret :: R)
      mem aw out σ k C) :
    (total.toNat + amount.toNat < 2^128 ∧
      (total + amount).toNat ≤ (calldataWord out 224).toNat ∧
      ∃ aw' k' C',
        RD (deployedRuntime v) ee g s0 ⟨13952⟩
          (EVM.word asset.val :: ptr :: free :: amount :: sender :: dst :: ret :: R)
          (writeWord mem free.toNat (total + amount)) aw' out σ k' C') ∨
    (¬ (total.toNat + amount.toNat < 2^128 ∧
      (total + amount).toNat ≤ (calldataWord out 224).toNat) ∧ RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_13881
    (immWords := wordsOf (immStore v)) (by change R.length + 3 + 11 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_13881_stack, hm.total] at r1
  have r2 := cometMask128 (v := v) (by change R.length + 11 + 5 ≤ 1024; omega) ht
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_13899
    (immWords := wordsOf (immStore v)) (by change R.length + 12 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  rcases cometCheckedAdd128 (v := v) (by change R.length + 9 + 6 ≤ 1024; omega) ht ha
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
    ⟨hfit, k4, C4, r4⟩ | ⟨hfit, hr⟩
  · have hn : (total + amount).toNat < 2^128 := by
      rw [uadd_toNat, Nat.mod_eq_of_lt (by change total.toNat + amount.toNat < 2^256; omega)]
      exact hfit
    have r5 := cometWithExtendedAssetList_block_13904
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 9 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    simp only [cometWithExtendedAssetList_block_13904_memory, mask128Clean _ hn] at r5
    change RD _ _ _ _ ⟨13917⟩
      (⟨2^128-1⟩ :: EVM.word asset.val :: ptr :: free :: amount :: sender :: dst :: ret :: R)
      (writeWord mem free.toNat (total + amount)) _ _ _ _ _ at r5
    have hm' := hm.writeTotal (total + amount)
    have hs' := hs.preserve hlo (memoryPrefix_sparse_writeWord mem free.toNat
      (ptr.toNat + 32 * 8) (total + amount) (Or.inl hsep))
    have hcap : memLoad (ptr + UInt256.ofNat 224)
        (writeWord mem free.toNat (total + amount)) = calldataWord out 224 := hs'.word 7 (by decide)
    have r6 := cometWithExtendedAssetList_block_13917
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    simp only [cometWithExtendedAssetList_block_13917_stack, hm'.total] at r6
    have r7 := cometMask128 (v := v) (by change R.length + 8 + 5 ≤ 1024; omega) hn
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6
    have r8 := cometWithExtendedAssetList_block_13927
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 8 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
    simp only [cometWithExtendedAssetList_block_13927_stack, hcap] at r8
    have hcapw : (calldataWord out 224).toNat < 2^128 := hv.2.2.2.2.2.2.2.2
    have r9 := cometMask128 (v := v) (by change R.length + 10 + 5 ≤ 1024; omega) hcapw
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r8
    have r10 := cometWithExtendedAssetList_block_6575
      (immWords := wordsOf (immStore v)) (by change R.length + 11 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r9
    have r11 := cometMask128 (v := v) (by change R.length + 9 + 5 ≤ 1024; omega) hcapw
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r10
    have hclean : UInt256.land (total + amount) ⟨2^128-1⟩ = total + amount :=
      low128_clean _ hn
    by_cases hc : (total + amount).toNat ≤ (calldataWord out 224).toNat
    · have r12 := cometWithExtendedAssetList_block_13944_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 7 + 3 ≤ 1024; omega)
        (by rw [hclean]; exact ugt_zero hc) r11
      exact Or.inl ⟨hfit, hc, _, _, _, r12⟩
    · have r12 := cometWithExtendedAssetList_block_13944_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 7 + 3 ≤ 1024; omega)
        (by rw [hclean, ugt_one (Nat.lt_of_not_ge hc)]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r11
      exact Or.inr ⟨fun hh ↦ hc hh.2, cometWithExtendedAssetList_block_14114
        (immWords := wordsOf (immStore v)) (by change R.length + 7 + 3 ≤ 1024; omega) r12⟩
  · exact Or.inr ⟨fun hh ↦ hfit hh.1, hr⟩

end Benchmarks.CompoundIII.Comet
