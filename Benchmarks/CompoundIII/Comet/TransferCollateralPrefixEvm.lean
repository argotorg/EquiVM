import Benchmarks.CompoundIII.Comet.TransferCollateralRead
import Benchmarks.CompoundIII.Comet.TransferCollateralMathEvm
import Benchmarks.CompoundIII.Comet.TransferCollateralWrite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferCollateralPrefixMemory (mem : ByteArray) (src dst asset : AccountAddress) : ByteArray :=
  transferCollateralMemory (transferCollateralMemory mem src dst asset) src dst asset

theorem transferCollateralPrefixMemory_free {mem : ByteArray} {free : UInt256}
    (src dst asset : AccountAddress) (hm : 96 ≤ mem.size) (hf : memLoad ⟨64⟩ mem = free) :
    memLoad ⟨64⟩ (transferCollateralPrefixMemory mem src dst asset) = free :=
  transferCollateralMemory_free src dst asset
    (by rw [transferCollateralMemory_size _ _ _ (by omega)]; exact hm)
    (transferCollateralMemory_free src dst asset hm hf)

theorem cometTransferCollateralPrefix {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst asset : AccountAddress) (hstack : R.length + 22 ≤ 1024)
    (ha : amount.toNat < 2^128) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15329⟩
      (EVM.word src.val :: EVM.word dst.val :: EVM.word asset.val :: amount :: ret :: R)
      mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 (transferCollateralPrefixMemory mem src dst asset)
      rdata ⟨15502⟩ (transferCollateralReadyStack src dst asset amount
        (withdrawCollateralBalance evm src asset) (transferCollateralSrcNext evm src asset amount)
        (withdrawCollateralBalance evm dst asset) (transferCollateralDstNext evm dst asset amount)
        ret R) (transferCollateralPrefixOutcome evm src dst asset amount) := by
  obtain ⟨aw1, k1, C1, r1⟩ := cometTransferCollateralRead src dst asset (by omega) hs h
  rcases cometTransferCollateralMath src dst asset (by omega) ha (low128_lt _) (low128_lt _) r1 with
    ⟨hsub, hadd, k2, C2, r2⟩ | ⟨hn, hr⟩
  · change amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat at hsub
    change (withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128 at hadd
    have hw := cometTransferCollateralWrite src dst asset hstack hs r2
    simpa only [transferCollateralPrefixOutcome, if_pos hsub, if_pos hadd,
      transferCollateralState, transferCollateralPrefixMemory] using hw
  · by_cases hsub : amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat
    · have hadd : ¬ (withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128 :=
        fun hh ↦ hn ⟨hsub, hh⟩
      simpa only [transferCollateralPrefixOutcome, if_pos hsub, if_neg hadd,
        internalMemoryRun] using hr
    · simpa only [transferCollateralPrefixOutcome, if_neg hsub, internalMemoryRun] using hr

end Benchmarks.CompoundIII.Comet
