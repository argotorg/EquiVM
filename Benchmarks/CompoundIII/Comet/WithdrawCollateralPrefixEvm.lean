import Benchmarks.CompoundIII.Comet.WithdrawCollateralWrite
import Benchmarks.CompoundIII.Comet.CheckedSub128Evm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def withdrawCollateralPrefixMemory (mem : ByteArray) (src asset : AccountAddress) : ByteArray :=
  userCollateralMemory (withdrawCollateralTotalMemory (userCollateralMemory mem src asset)
    asset) src asset

theorem withdrawCollateralPrefixMemory_size {mem : ByteArray} (src asset : AccountAddress)
    (hm : 64 ≤ mem.size) : (withdrawCollateralPrefixMemory mem src asset).size = mem.size := by
  have hu := userCollateralMemory_size src asset hm
  have ht := twoWordHashMem_size_of_ge_64 (EVM.word asset.val) ⟨2⟩ (by rw [hu]; exact hm)
  rw [withdrawCollateralPrefixMemory,
    userCollateralMemory_size src asset (by
      change 64 ≤ (twoWordHashMem _ _ _).size
      rw [ht, hu]; exact hm)]
  exact ht.trans hu

theorem withdrawCollateralPrefixMemory_free {mem : ByteArray} {free : UInt256}
    (src asset : AccountAddress) (hm : 96 ≤ mem.size) (hf : memLoad ⟨64⟩ mem = free) :
    memLoad ⟨64⟩ (withdrawCollateralPrefixMemory mem src asset) = free := by
  have hu := userCollateralMemory_size src asset (by omega : 64 ≤ mem.size)
  have ht := twoWordHashMem_size_of_ge_64 (EVM.word asset.val) ⟨2⟩ (by rw [hu]; omega)
  apply userCollateralMemory_free src asset
  · change 96 ≤ (twoWordHashMem _ _ _).size
    rw [ht, hu]; exact hm
  · change memLoad ⟨64⟩ (twoWordHashMem _ _ _) = free
    rw [twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide) (by rw [hu]; exact hm)]
    exact userCollateralMemory_free src asset hm hf

theorem cometWithdrawCollateralPrefix {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient asset : AccountAddress) (hstack : R.length + 22 ≤ 1024)
    (hamount : amount.toNat < 2^128) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16281⟩
      (EVM.word src.val :: EVM.word recipient.val :: EVM.word asset.val :: amount :: ret :: R)
      mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 (withdrawCollateralPrefixMemory mem src asset)
      rdata ⟨16421⟩ (withdrawCollateralReadyStack src recipient asset amount
        (withdrawCollateralBalance evm src asset)
        (UInt256.sub (withdrawCollateralBalance evm src asset) amount) ret R)
      (withdrawCollateralPrefixOutcome evm src asset amount) := by
  obtain ⟨aw1, k1, C1, r1⟩ := cometWithdrawCollateralRead (v := v)
    src recipient asset (by omega) hs h
  rcases cometCheckedSub128 (v := v) (by change R.length + 10 + 6 ≤ 1024; omega)
      (low128_lt _) hamount
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1 with
    ⟨hb, k2, C2, r2⟩ | ⟨hb, hr⟩
  · change amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat at hb
    obtain ⟨aw3, k3, C3, r3⟩ := cometWithdrawCollateralTotalRead (v := v)
      src recipient asset (by omega) hs r2
    rcases cometCheckedSub128 (v := v) (by change R.length + 15 + 6 ≤ 1024; omega)
        (low128_lt _) hamount
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
      ⟨ht, k4, C4, r4⟩ | ⟨ht, hr⟩
    · change amount.toNat ≤ (withdrawCollateralTotal evm asset).toNat at ht
      have hw := cometWithdrawCollateralWrite (v := v) src recipient asset hstack hs r4
      simpa only [withdrawCollateralPrefixOutcome, if_pos hb, if_pos ht,
        withdrawCollateralState, withdrawCollateralPrefixMemory] using hw
    · change ¬ amount.toNat ≤ (withdrawCollateralTotal evm asset).toNat at ht
      simpa only [withdrawCollateralPrefixOutcome, if_pos hb, if_neg ht,
        internalMemoryRun] using hr
  · change ¬ amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat at hb
    simpa only [withdrawCollateralPrefixOutcome, if_neg hb, internalMemoryRun] using hr

end Benchmarks.CompoundIII.Comet
