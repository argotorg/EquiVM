import Benchmarks.CompoundIII.Comet.TransferOutSource
import Benchmarks.CompoundIII.Comet.TransferMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_073
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def TransferOutRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (ret ptr : UInt256) (R : List UInt256)
    (result : Option EVM.State) : Prop :=
  match result with
  | none => RDrev (deployedRuntime v) g s0
  | some evm' => ∃ σ' mem aw out k C, SourceState s0 ee σ' evm' ∧
      memLoad ⟨64⟩ mem = ptr ∧ ptr.toNat ≤ mem.size ∧
      RD (deployedRuntime v) ee g s0 ret R mem aw out σ' k C

theorem cometTransferOutInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr amount ret : UInt256} {R : List UInt256}
    {asset recipient : AccountAddress} {evm : EVM.State}
    (hstack : R.length + 17 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 68 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16113⟩
      (EVM.word asset.val :: EVM.word recipient.val :: amount :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, TransferOutTrace asset recipient amount evm result ∧
      TransferOutRun v ee g s0 ret ptr R result := by
  have ha : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (EVM.word asset.val) = EVM.word asset.val :=
    solcAddrMask_clean_left (addressWord_val_canonical asset)
  by_cases hc : extCodeSizeWord σ (EVM.word asset.val) = ⟨0⟩
  · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_16113_taken
      (immWords := wordsOf (immStore v)) (by omega) (by rw [ha, hc]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨none, .codeMissing (by simpa only [hs.accounts] using hc),
      cometWithExtendedAssetList_block_1410 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 2 ≤ 1024; omega) r1⟩
  · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_16113_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [ha]; exact isZero_eq_zero_of_ne hc) h
    simp only [cometWithExtendedAssetList_block_16113_fallthrough_stack, ha] at r1
    have r2 := cometWithExtendedAssetList_block_16132
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
    simp only [cometWithExtendedAssetList_block_16132_stack,
      cometWithExtendedAssetList_block_16132_memory, hf] at r2
    have r3 := cometWithExtendedAssetList_block_16086
      (immWords := wordsOf (immStore v)) (by change R.length + 10 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have hr : UInt256.land (EVM.word recipient.val)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) = EVM.word recipient.val := addressWord_val_clean recipient
    have hptr : (ptr + UInt256.ofNat 4) + UInt256.ofNat 32 = ptr + UInt256.ofNat 36 := by
      rw [u256_add_assoc]
      rfl
    have hend : UInt256.ofNat 64 + (ptr + UInt256.ofNat 4) = ptr + UInt256.ofNat 68 := by
      rw [u256_add_comm (UInt256.ofNat 64), u256_add_assoc]
      rfl
    simp only [cometWithExtendedAssetList_block_16086_stack,
      cometWithExtendedAssetList_block_16086_memory, hr, hptr, hend] at r3
    have r4 := cometWithExtendedAssetList_block_16171
      (immWords := wordsOf (immStore v)) (by change R.length + 6 + 5 ≤ 1024; omega) r3
    simp only [cometWithExtendedAssetList_block_16171_stack, word_add_sub_left] at r4
    change RD _ _ _ _ _ _ (transferInputMemory mem ptr recipient amount) _ _ _ _ _ at r4
    obtain ⟨evm', σ', z, out, k5, C5, hcall, hs', r5, hh⟩ := zeroCallBridge r4 hs
      (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
        wordsOf (immStore v), (⟨16175⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
        immutableLayout_inBounds, immutableTemplate_size64))
      (transferInputMemory_payload (mem := mem) (ptr := ptr)
        (recipient := recipient) (amount := amount) hb)
      (by rw [transferPayload_size]; decide)
      (by change R.length + 4 + 1 ≤ 1024; omega)
    have hcall' : callViaEVM evm asset 0 (transferPayload recipient amount) (z, evm', out) := by
      have haddr : AccountAddress.ofUInt256 (EVM.word asset.val) = asset :=
        accountAddress_roundtrip asset
      simpa only [haddr] using hcall
    have htrace := TransferOutTrace.callResult
      (by simpa only [hs.accounts] using hc) hcall' (lt_trans hh (by decide))
    change RD _ _ _ _ ⟨16176⟩ _
      (callOutputMem (transferInputMemory mem ptr recipient amount) out ptr ⟨0⟩) _ _ _ _ _ at r5
    rw [callOutputMem_zero] at r5
    rcases cometTransferResponse (by omega) (lt_trans hh (by change 2^138 < 2^256; decide))
      (by omega) hret r5 with ⟨hz, hv, aw6, k6, C6, r6⟩ | ⟨hv, r6⟩
    · rw [if_pos ⟨hz, hv⟩] at htrace
      refine ⟨some evm', htrace, σ', _, aw6, out, k6, C6, hs',
        transferOutputMemory_free hv, ?_, r6⟩
      rw [transferOutputMemory_size hlo (by change _ < 2^256; omega) hv]
      omega
    · rw [if_neg hv] at htrace
      exact ⟨none, htrace, r6⟩

end Benchmarks.CompoundIII.Comet
