import Benchmarks.CompoundIII.Comet.ApprovePayload
import Benchmarks.CompoundIII.Comet.ApproveResponseEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_073

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometApproveCall {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr amount : UInt256} {R : List UInt256}
    (manager asset : AccountAddress) (hstack : R.length + 14 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hb : ptr.toNat + 68 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨5186⟩
      (amount :: EVM.word manager.val :: EVM.word asset.val :: R) mem aw rdata σ k C) :
    ∃ evm' z out, callViaEVM evm asset 0 (approvePayload manager amount) (z, evm', out) ∧
      if z then RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty
        else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_5186 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [cometWithExtendedAssetList_block_5186_stack,
    cometWithExtendedAssetList_block_5186_memory, hf] at r1
  have r2 := cometWithExtendedAssetList_block_16086 (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have hmanager : UInt256.land (EVM.word manager.val)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = EVM.word manager.val := addressWord_val_clean manager
  have hptr : (ptr + UInt256.ofNat 4) + UInt256.ofNat 32 = ptr + UInt256.ofNat 36 := by
    rw [u256_add_assoc]
    rfl
  have hend : UInt256.ofNat 64 + (ptr + UInt256.ofNat 4) = ptr + UInt256.ofNat 68 := by
    rw [u256_add_comm (UInt256.ofNat 64), u256_add_assoc]
    rfl
  simp only [cometWithExtendedAssetList_block_16086_stack,
    cometWithExtendedAssetList_block_16086_memory, hmanager, hptr, hend] at r2
  have r3 := cometWithExtendedAssetList_block_5221 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 5 ≤ 1024; omega) r2
  simp only [cometWithExtendedAssetList_block_5221_stack, word_add_sub_left] at r3
  change RD _ _ _ _ _ _ (approveInputMemory mem ptr manager amount) _ _ _ _ _ at r3
  obtain ⟨evm', σ', z, out, k4, C4, hcall, hs', r4, _⟩ := zeroCallBridge r3 hs
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨5225⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    (approveInputMemory_payload (mem := mem) (ptr := ptr)
      (manager := manager) (amount := amount) hb)
    (by rw [approvePayload_size]; decide)
    (by change R.length + 1 + 1 ≤ 1024; omega)
  have hcall' : callViaEVM evm asset 0 (approvePayload manager amount) (z, evm', out) := by
    have haddr : AccountAddress.ofUInt256 (EVM.word asset.val) = asset :=
      accountAddress_roundtrip asset
    simpa only [haddr] using hcall
  change RD _ _ _ _ ⟨5226⟩ _
    (callOutputMem (approveInputMemory mem ptr manager amount) out ptr ⟨0⟩) _ _ _ _ _ at r4
  rw [callOutputMem_zero] at r4
  have hr := cometApproveResponse (v := v) (z := z) (ptr := ptr) (by omega) (by omega) r4
  refine ⟨evm', z, out, hcall', ?_⟩
  cases z <;> simpa only [Bool.false_eq_true, if_false, if_true, hs'.accounts] using hr

end Benchmarks.CompoundIII.Comet
