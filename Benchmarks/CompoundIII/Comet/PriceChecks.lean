import Benchmarks.CompoundIII.Comet.PriceDecode
import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_044
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def priceRoundMask : UInt256 := UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨80⟩) ⟨1⟩

theorem cometRead80_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hc : (memLoad ptr mem).toNat < 2^80)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9355⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (memLoad ptr mem :: R)
      mem aw' rdata σ k' C' := by
  have hm : UInt256.land (memLoad ptr mem) priceRoundMask = memLoad ptr mem :=
    u256LandMaskCleanOfToNat _ _ (by decide : priceRoundMask.toNat = 2^80 - 1) hc
  have r1 := cometWithExtendedAssetList_block_9355_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (memLoad ptr mem) (UInt256.land (memLoad ptr mem) priceRoundMask) = ⟨0⟩
      rw [hm, u256_sub_self]) h
  have r2 := cometWithExtendedAssetList_block_9374
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 1 ≤ 1024; omega) hret r1
  exact ⟨_, _, _, r2⟩

theorem cometRead80_bad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hc : ¬ (memLoad ptr mem).toNat < 2^80)
    (h : RD (deployedRuntime v) ee g s0 ⟨9355⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hm : memLoad ptr mem ≠ UInt256.land (memLoad ptr mem) priceRoundMask := by
    intro he
    have hb := u256LandMaskToNatLtOfToNat (memLoad ptr mem) priceRoundMask
      (by decide : priceRoundMask.toNat = 2^80 - 1)
    rw [← he] at hb
    exact hc hb
  have r1 := cometWithExtendedAssetList_block_9355_taken
    (immWords := wordsOf (immStore v)) hstack (u256_sub_ne_zero_of_ne hm)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometRevert1410 (by change R.length + 2 + 2 ≤ 1024; omega) r1

theorem cometPositivePrice {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {junk price ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9426⟩ (junk :: price :: ret :: R)
      mem aw rdata σ k C) :
    if 0 < signedPrice price then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (price :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hp : 0 < signedPrice price
  · rw [if_pos hp]
    have hg : UInt256.sgt price ⟨0⟩ ≠ ⟨0⟩ := by
      intro hz
      have hn : signedPrice price ≤ 0 := sgt_zero_eq_zero_to_nonpos price hz
      omega
    have r1 := cometWithExtendedAssetList_block_9426_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
      (isZero_eq_zero_of_ne hg) h
    have r2 := cometWithExtendedAssetList_block_9437
      (immWords := wordsOf (immStore v)) (by omega) hret r1
    exact ⟨_, _, r2⟩
  · rw [if_neg hp]
    have hg : UInt256.sgt price ⟨0⟩ = ⟨0⟩ := by
      by_contra hn
      exact hp (sgt_zero_ne_zero_to_pos price hn)
    have r1 := cometWithExtendedAssetList_block_9426_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
      (by change UInt256.isZero (UInt256.sgt price ⟨0⟩) ≠ ⟨0⟩; rw [hg]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact cometWithExtendedAssetList_block_9439 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 3 ≤ 1024; omega) r1

set_option maxHeartbeats 500000 in
theorem cometPriceChecks {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h0 : memLoad ptr mem = calldataWord out 0)
    (h32 : memLoad (ptr + UInt256.ofNat 32) mem = calldataWord out 32)
    (h128 : memLoad (ptr + UInt256.ofNat 128) mem = calldataWord out 128)
    (h : RD (deployedRuntime v) ee g s0 ⟨9491⟩ (⟨0⟩ :: ptr :: ret :: R)
      mem aw out σ k C) :
    if PriceRoundCanonical out ∧ 0 < signedPrice (calldataWord out 32) then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (calldataWord out 32 :: R)
        mem aw' out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_9491
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases hc0 : (calldataWord out 0).toNat < 2^80
  · obtain ⟨aw2, k2, C2, r2⟩ := cometRead80_ok (v := v)
      (by change R.length + 2 + 5 ≤ 1024; omega) (by rw [h0]; exact hc0)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    have r3 := cometWithExtendedAssetList_block_9500
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    by_cases hc4 : (calldataWord out 128).toNat < 2^80
    · obtain ⟨aw4, k4, C4, r4⟩ := cometRead80_ok (v := v)
        (by change R.length + 2 + 5 ≤ 1024; omega) (by rw [h128]; exact hc4)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      have r5 := cometWithExtendedAssetList_block_9518
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      change RD _ _ _ _ _ (_ :: memLoad (ptr + UInt256.ofNat 32) mem :: ret :: R)
        mem _ out σ _ _ at r5
      rw [h32] at r5
      rw [Layout.runtime_size_of_bounds immutableLayout_inBounds] at r5
      have hf := cometPositivePrice (v := v) (R := R) (price := calldataWord out 32)
        (ret := ret) (by omega) hret r5
      by_cases hp : 0 < signedPrice (calldataWord out 32)
      · rw [if_pos hp] at hf
        rw [if_pos ⟨⟨hc0, hc4⟩, hp⟩]
        obtain ⟨k6, C6, r6⟩ := hf
        exact ⟨_, k6, C6, r6⟩
      · rw [if_neg hp] at hf
        rw [if_neg (by simp only [hp, and_false, not_false_eq_true])]
        exact hf
    · rw [if_neg (by rintro ⟨⟨_, h4⟩, _⟩; exact hc4 h4)]
      exact cometRead80_bad (v := v) (by change R.length + 2 + 5 ≤ 1024; omega)
        (by rw [h128]; exact hc4) r3
  · rw [if_neg (by rintro ⟨⟨hfirst, _⟩, _⟩; exact hc0 hfirst)]
    exact cometRead80_bad (v := v) (by change R.length + 2 + 5 ≤ 1024; omega)
      (by rw [h0]; exact hc0) r1

end Benchmarks.CompoundIII.Comet
