import Benchmarks.CompoundIII.Comet.AbsorbAssetModel
import Benchmarks.CompoundIII.Comet.AbsorbAfterAssetEvm
import Benchmarks.CompoundIII.Comet.AssetMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbAsset {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free i assets reserved old principal price delta basicPtr absorber : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 27 ≤ 1024) (hi : i.toNat < 256)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hbound : free.toNat + 1184 < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17578⟩
      (i :: assets :: reserved :: old :: principal :: price :: EVM.word account.val :: delta ::
        basicPtr :: absorber :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbAssetTrace v account i delta evm result ∧
      internalValuePreservingRun (deployedRuntime v) ee g s0 mem free 928 ⟨17567⟩
        (fun d ↦ i :: assets :: reserved :: old :: principal :: price :: EVM.word account.val ::
          d.delta delta :: basicPtr :: absorber :: R) result := by
  have r1 := cometWithExtendedAssetList_block_17578 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨evm', σ', z, out, hcall, hs', hh, hr⟩ := cometAssetInternal (v := v)
    (by change R.length + 12 + 13 ≤ 1024; omega) hi hfree hlo (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  have hh' : out.size < 2^255 := lt_trans hh (by decide)
  by_cases hp : z = true ∧ AssetValid out
  · rw [if_pos hp] at hr
    obtain ⟨rfl, hva⟩ := hp
    obtain ⟨aw2, k2, C2, r2⟩ := hr
    have hb : free.toNat + 1184 < UInt256.size := by
      change free.toNat + 1184 < 2^256; omega
    have h1 : (free + (⟨256⟩ : UInt256)).toNat = free.toNat + 256 :=
      uadd_word_ofNat_toNat free 256 (by omega)
    have h2 : ((free + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat = free.toNat + 512 := by
      have ha : ((free + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat =
          (free + (⟨256⟩ : UInt256)).toNat + 256 :=
        uadd_word_ofNat_toNat _ 256 (by rw [h1]; omega)
      omega
    have h3 : (((free + (⟨256⟩ : UInt256)) + ⟨256⟩) + ⟨256⟩).toNat =
        free.toNat + 768 := by
      have ha : (((free + (⟨256⟩ : UInt256)) + ⟨256⟩) + ⟨256⟩).toNat =
          ((free + (⟨256⟩ : UInt256)) + ⟨256⟩).toNat + 256 :=
        uadd_word_ofNat_toNat _ 256 (by rw [h2]; omega)
      omega
    have hhi : out.size < UInt256.size := lt_trans hh (by change 2^138 < 2^256; decide)
    have hm := assetInternalMemory_spec (mem := mem) (i := i) hlo (by omega) hva.1 hhi
    have hmSize := assetInternalMemory_size (mem := mem) (i := i) hlo (by omega) hva.1 hhi
    have hmPrefix := assetInternalMemory_prefix (mem := mem) (ptr := free) (i := i)
      (by omega) hva.1 hhi
    obtain ⟨result, ht, hr⟩ := cometAbsorbAfterAsset (v := v) account
      (by change R.length + 2 + 25 ≤ 1024; omega) hm hva.2
      (by rw [hmSize, h3]; omega) (by rw [h3]; omega) hs' r2
    refine ⟨_, AbsorbAssetTrace.assetOk hcall hh' hva ht, ?_⟩
    cases result with
    | reverted => exact hr
    | staticViolation => exact hr
    | ok evm'' p =>
        obtain ⟨σ3, mem3, free3, aw3, data3, k3, C3, hs3, hf3, hm3, hz3, hp3, r3⟩ := hr
        exact ⟨σ3, mem3, free3, aw3, data3, k3, C3, hs3, by rw [h3] at hf3; omega,
          hm3, hz3, hmPrefix.trans (hp3.mono (by rw [h3]; omega)), r3⟩
  · rw [if_neg hp] at hr
    exact ⟨.reverted, AbsorbAssetTrace.assetFailed hcall hh' hp, hr⟩

end Benchmarks.CompoundIII.Comet
