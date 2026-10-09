import Benchmarks.CompoundIII.Comet.AssetSearch
import Benchmarks.CompoundIII.Comet.AssetMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def AssetSearchRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret : UInt256) (R : List UInt256)
    (result : Option (EVM.State × ByteArray)) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some (evm', out) => ∃ σ' mem ptr free aw k C,
      SourceState s0 ee σ' evm' ∧ AssetValid out ∧ AssetMemory mem ptr free out ∧
      RD (deployedRuntime v) ee g s0 ret (ptr :: R) mem aw out σ' k C

/-- The search also retains allocation bounds for callers that query price feeds. -/
def AssetSearchRunBounded (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret : UInt256) (R : List UInt256) (limit : Nat)
    (result : Option (EVM.State × ByteArray)) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some (evm', out) => ∃ σ' mem ptr free aw k C,
      SourceState s0 ee σ' evm' ∧ AssetValid out ∧ AssetMemory mem ptr free out ∧
      free.toNat ≤ limit ∧ free.toNat ≤ mem.size ∧
      RD (deployedRuntime v) ee g s0 ret (ptr :: R) mem aw out σ' k C

theorem AssetSearchRunBounded.forget {v ee g s0 ret R limit result}
    (h : AssetSearchRunBounded v ee g s0 ret R limit result) :
    AssetSearchRun v ee g s0 ret R result := by
  cases result with
  | none => exact h
  | some pair =>
      rcases pair with ⟨evm', out⟩
      rcases h with ⟨σ', mem, ptr, free, aw, k, C, hs, hv, hm, _, _, hr⟩
      exact ⟨σ', mem, ptr, free, aw, k, C, hs, hv, hm, hr⟩

theorem cometAssetSearchLoopBounded {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {asset : AccountAddress} {evm : EVM.State} {i : Nat}
    (hstack : R.length + 18 ≤ 1024) (hi : i ≤ v.numAssets.toNat)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 768 * (v.numAssets.toNat - i) + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨7535⟩
      (UInt256.ofNat i :: EVM.word asset.val :: ret :: v.numAssets :: ⟨255⟩ :: R)
      mem aw rdata σ k C) :
    ∃ result, AssetSearch v asset i evm result ∧ AssetSearchRunBounded v ee g s0 ret R
      (ptr.toNat + 768 * (v.numAssets.toNat - i)) result := by
  have hi8 : i < 256 := lt_of_le_of_lt hi v.numAssets_lt
  have hin : (UInt256.ofNat i).toNat = i :=
    UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
  have himask : UInt256.land (UInt256.ofNat i) ⟨255⟩ = UInt256.ofNat i :=
    lowByteClean (by rw [hin]; exact hi8)
  by_cases hib : i < v.numAssets.toNat
  · have hstep : ptr.toNat + 1024 < 2^64 := by omega
    have r1 := cometWithExtendedAssetList_block_7535_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [himask, ult_one (by rw [hin]; exact hib)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7562
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨evm', σ', z, out, hc, hs', hsize, hr⟩ := cometAssetInternal (v := v)
      (by change R.length + 5 + 13 ≤ 1024; omega) (by rw [hin]; exact hi8) hfree hlo
      (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r2
    have hsiz : out.size < 2^255 := lt_trans hsize (by decide)
    by_cases hv : z = true ∧ AssetValid out
    · rw [if_pos hv] at hr
      obtain ⟨aw3, k3, C3, r3⟩ := hr
      rcases hv with ⟨rfl, hv⟩
      let mem' := assetInternalMemory mem ptr (UInt256.ofNat i) out
      let ptr' := (ptr + (⟨256⟩ : UInt256)) + ⟨256⟩
      let free' := ptr' + (⟨256⟩ : UInt256)
      have hm : AssetMemory mem' ptr' free' out :=
        assetInternalMemory_spec hlo (by change ptr.toNat + 1024 < 2^256; omega)
          hv.1 (lt_trans hsize (by change 2^138 < 2^256; decide))
      have hpn : ptr'.toNat = ptr.toNat + 512 := by
        have he : ptr' = ptr + (⟨512⟩ : UInt256) := by
          dsimp only [ptr']; rw [uadd_assoc]; rfl
        rw [he]
        exact uadd_word_ofNat_toNat ptr 512 (by change ptr.toNat + 512 < 2^256; omega)
      have hfn : free'.toNat = ptr.toNat + 768 := by
        have he : free' = ptr + (⟨768⟩ : UInt256) := by
          dsimp only [free', ptr']; rw [uadd_assoc, uadd_assoc]; rfl
        rw [he]
        exact uadd_word_ofNat_toNat ptr 768 (by change ptr.toNat + 768 < 2^256; omega)
      have hw : memLoad (ptr' + UInt256.ofNat 32) mem' = calldataWord out 32 := hm.words 1
        (by decide)
      have hmask : UInt256.land (memLoad (ptr' + UInt256.ofNat 32) mem') solcAddrMask =
          calldataWord out 32 := by rw [hw]; exact solcAddrMask_clean hv.2.2.1
      have hamask : UInt256.land solcAddrMask (EVM.word asset.val) = EVM.word asset.val :=
        solcAddrMask_clean_left (addressWord_val_canonical asset)
      by_cases ha : AccountAddress.ofNat (calldataWord out 32).toNat = asset
      · have heq : calldataWord out 32 = EVM.word asset.val := by
          rw [← ha, addressWord_eq_ofNat_address hv.2.2.1]
        have r4 := cometWithExtendedAssetList_block_7571_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 7 ≤ 1024; omega)
          (by change UInt256.eq (UInt256.land (memLoad (ptr' + UInt256.ofNat 32) mem')
              solcAddrMask) (UInt256.land solcAddrMask (EVM.word asset.val)) ≠ ⟨0⟩
              rw [hmask, hamask, heq, uInt256_eq_self]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
        have r5 := cometWithExtendedAssetList_block_7605
          (immWords := wordsOf (immStore v)) (by omega) hret r4
        exact ⟨some (evm', out), .found hib hc hsiz hv ha,
          σ', mem', ptr', free', _, _, _, hs', hv, hm,
          by rw [hfn]; omega, by have hpresent := hm.present; rw [hpn] at hpresent; rw [hfn]; omega, r5⟩
      · have hne : calldataWord out 32 ≠ EVM.word asset.val := by
          intro he
          apply ha
          rw [he, accountAddress_of_word_val]
        have r4 := cometWithExtendedAssetList_block_7571_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 7 ≤ 1024; omega)
          (by change UInt256.eq (UInt256.land (memLoad (ptr' + UInt256.ofNat 32) mem')
              solcAddrMask) (UInt256.land solcAddrMask (EVM.word asset.val)) = ⟨0⟩
              rw [hmask, hamask]
              exact uInt256_eq_zero_of_ne (fun hh ↦ hne (uInt256_eq_one_eq hh))) r3
        have r5 := cometWithExtendedAssetList_block_7595
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
        have hnext : UInt256.land (⟨255⟩ : UInt256)
            ((UInt256.ofNat 1) + UInt256.ofNat i) = UInt256.ofNat (i + 1) := by
          rw [show (UInt256.ofNat 1) + UInt256.ofNat i = UInt256.ofNat (i + 1) from
            uInt256_one_add_ofNat_of_lt (by change i + 1 < 2^256; omega), u256_land_comm]
          apply lowByteClean
          rw [UInt256.toNat_ofNat_of_lt (by change i + 1 < 2^256; omega)]
          have := v.numAssets_lt
          omega
        simp only [cometWithExtendedAssetList_block_7595_stack, hnext] at r5
        obtain ⟨result, hsearch, hrun⟩ := cometAssetSearchLoopBounded (v := v) (i := i + 1)
          hstack (by omega) hm.freeWord (by rw [hfn]; omega)
          (by rw [hfn]; omega) hret hs' r5
        have hlimit : free'.toNat + 768 * (v.numAssets.toNat - (i + 1)) =
            ptr.toNat + 768 * (v.numAssets.toNat - i) := by rw [hfn]; omega
        rw [hlimit] at hrun
        exact ⟨result, .next hib hc hsiz hv ha hsearch, hrun⟩
    · rw [if_neg hv] at hr
      exact ⟨none, .failed hib hc hsiz hv, hr⟩
  · have r1 := cometWithExtendedAssetList_block_7535_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [himask]; exact ult_zero (by rw [hin]; omega)) h
    exact ⟨none, .exhausted (by omega), cometWithExtendedAssetList_block_7545
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega) r1⟩
termination_by v.numAssets.toNat - i
decreasing_by omega

theorem cometAssetSearchLoop {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {asset : AccountAddress} {evm : EVM.State} {i : Nat}
    (hstack : R.length + 18 ≤ 1024) (hi : i ≤ v.numAssets.toNat)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 768 * (v.numAssets.toNat - i) + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨7535⟩
      (UInt256.ofNat i :: EVM.word asset.val :: ret :: v.numAssets :: ⟨255⟩ :: R)
      mem aw rdata σ k C) :
    ∃ result, AssetSearch v asset i evm result ∧ AssetSearchRun v ee g s0 ret R result := by
  obtain ⟨result, hsearch, hrun⟩ := cometAssetSearchLoopBounded hstack hi hfree hlo hptr hret hs h
  exact ⟨result, hsearch, hrun.forget⟩

theorem cometAssetSearchInternalBounded {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {asset : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 18 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat + 512 + 768 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨7482⟩ (EVM.word asset.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, AssetSearch v asset 0 evm result ∧ AssetSearchRunBounded v ee g s0 ret R
      (ptr.toNat + 256 + 768 * v.numAssets.toNat) result := by
  have r1 := cometWithExtendedAssetList_block_7482
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometAllocateAssetZero (v := v)
    (by change R.length + 2 + 8 ≤ 1024; omega) hfree (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_7491
    (immWords := wordsOf (immStore v)) (by omega) r2
  simp only [cometWithExtendedAssetList_block_7491_stack, wordsOf_immStore_numAssets,
    wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at r3
  have hmask : UInt256.land v.numAssets (UInt256.ofNat 255) = v.numAssets :=
    lowByteClean v.numAssets_lt
  rw [hmask] at r3
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by change ptr.toNat + 256 < 2^256; omega)
  obtain ⟨result, hsearch, hrun⟩ := cometAssetSearchLoopBounded (v := v) hstack (Nat.zero_le _)
    (assetZeroMemory_free hlo (by change ptr.toNat + 256 < 2^256; omega))
    (by rw [ha]; omega) (by rw [ha]; omega) hret hs r3
  refine ⟨result, hsearch, ?_⟩
  simpa only [ha, Nat.sub_zero] using hrun

theorem cometAssetSearchInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {asset : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 18 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat + 512 + 768 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨7482⟩ (EVM.word asset.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, AssetSearch v asset 0 evm result ∧ AssetSearchRun v ee g s0 ret R result := by
  obtain ⟨result, hsearch, hrun⟩ := cometAssetSearchInternalBounded hstack hfree hlo hptr hret hs h
  exact ⟨result, hsearch, hrun.forget⟩

end Benchmarks.CompoundIII.Comet
