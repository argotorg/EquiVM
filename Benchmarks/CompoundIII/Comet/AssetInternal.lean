import Benchmarks.CompoundIII.Comet.AssetResponseEvm
import Benchmarks.CompoundIII.Comet.AssetZeroMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def assetResultMemory (mem : ByteArray) (ptr i : UInt256) (out : ByteArray) : ByteArray :=
  assetStore (assetDecodeMemory (assetInputMemory mem ptr i) ptr out) (ptr + ⟨256⟩) out 8

theorem cometAssetAfterZero {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr dummy i ret : UInt256} {R : List UInt256}
    {evm : EVM.State} (hstack : R.length + 13 ≤ 1024) (hi : i.toNat < 256)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 512 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨7187⟩ (dummy :: i :: ret :: R)
      mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
      callViaEVM evm v.assetList 0 (assetPayload i) (z, evm', out) false ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      if z = true ∧ AssetValid out then
        ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret ((ptr + ⟨256⟩) :: R)
          (assetResultMemory mem ptr i out) aw' out σ' k' C'
      else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_7187
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 10 ≤ 1024; omega) h
  have hm : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (wordsOf (immStore v) "assetList") = EVM.word v.assetList.val := by
    rw [wordsOf_immStore_assetList]
    exact solcAddrMask_clean_left (addressWord_val_canonical v.assetList)
  have hi' : UInt256.land (UInt256.ofNat 255) i = i := by
    rw [u256_land_comm]; exact lowByteClean hi
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [cometWithExtendedAssetList_block_7187_stack,
    cometWithExtendedAssetList_block_7187_memory, hf, hm, hi'] at r1
  have hb : ptr.toNat + 36 < UInt256.size := by change ptr.toNat + 36 < 2^256; omega
  obtain ⟨evm', σ', z, out, k2, C2, hc, hs', r2, hsize⟩ := staticCallBridge r1 hs
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨7264⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    (assetInputMemory_payload hb) (by rw [assetPayload_size]; decide)
    (by change R.length + 3 + 1 ≤ 1024; omega)
  have hc' : callViaEVM evm v.assetList 0 (assetPayload i) (z, evm', out) false := by
    have ht : AccountAddress.ofUInt256 (EVM.word v.assetList.val) = v.assetList :=
      accountAddress_roundtrip v.assetList
    simpa only [ht] using hc
  refine ⟨evm', σ', z, out, hc', hs', hsize, ?_⟩
  exact cometAssetResponse (v := v) hstack hlo
    (by rw [assetInputMemory_size hb]; omega) hptr
    (lt_trans hsize (by change 2^138 < 2^256; decide)) hret r2

theorem cometAssetInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr i ret : UInt256} {R : List UInt256}
    {evm : EVM.State} (hstack : R.length + 13 ≤ 1024) (hi : i.toNat < 256)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat + 768 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨7179⟩ (i :: ret :: R)
      mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
      callViaEVM evm v.assetList 0 (assetPayload i) (z, evm', out) false ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      if z = true ∧ AssetValid out then
        ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (((ptr + ⟨256⟩) + ⟨256⟩) :: R)
          (assetResultMemory (assetZeroMemory mem ptr) (ptr + ⟨256⟩) i out)
          aw' out σ' k' C'
      else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_7179
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometAllocateAssetZero (v := v)
    (by change R.length + 2 + 8 ≤ 1024; omega) hfree (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have ha : (ptr + (⟨256⟩ : UInt256)).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat ptr 256 (by change ptr.toNat + 256 < 2^256; omega)
  exact cometAssetAfterZero (v := v) hstack hi
    (assetZeroMemory_free hlo (by change ptr.toNat + 256 < 2^256; omega))
    (by rw [ha]; omega) (by rw [ha]; omega) hret hs r2

end Benchmarks.CompoundIII.Comet
