import Benchmarks.Safe.ViaIR.ExecGuardCallTrace
import Benchmarks.Safe.ViaIR.ExecGuardCalldataStack

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def ExecTransactionGuardOutcome (fork : Ethereum.Fork) (p : ExecTransactionInput) (initial current : EVM.State)
    (I : ExecutionEnv) (g : Sat256) (s0 : State) (src ptr : Nat) (R : List UInt256) : Prop :=
  (RDrev fork safeBytecode g s0 ∧ ExecBlock fork config (execSignedFrame p initial) current
    (exectransactionTransition.body.drop 6) .reverted) ∨
  ∃ locals evm' mem' aw' out k' C' scratch,
    (∀ result, ExecBlock fork config { contract := contract, locals := locals } evm'
      (exectransactionTransition.body.drop 8) result →
      ExecBlock fork config (execSignedFrame p initial) current
        (exectransactionTransition.body.drop 6) result) ∧
    ExecTransactionLocals p locals ∧
    locals["guard"]? = some (.address (AccountAddress.ofUInt256 (execGuardWord current))) ∧
    locals["txHash"]? = some (wordBytes32Value (execTransactionHash p initial)) ∧
    evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
    RD fork safeBytecode I g s0 ⟨4584⟩
      (execGuardSaved p src scratch (execGuardWord current) (execTransactionHash p initial)
        (⟨0⟩ :: R))
      mem' aw' out evm'.accountMap k' C' ∧
    memLoad ⟨64⟩ mem' = UInt256.ofNat ptr ∧ memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ 128 ≤ mem'.size

set_option maxRecDepth 2000 in
theorem safeExecTransactionGuard (initial evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr dataLen sigLen} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4534⟩
      (execSignatureSaved I.calldata dataLen ⟨128⟩
        (execTransactionHash (execTransactionCalldataInput I.calldata dataLen sigLen) initial)
        (⟨0⟩ :: R))
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hb : ExecTransactionCalldataBounds I.calldata dataLen sigLen)
    (ho : (calldataWord I.calldata 100).toNat < 2)
    (hsig : BytesMemory mem 128
      (execTransactionCalldataInput I.calldata dataLen sigLen).signatures)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hz : memLoad ⟨96⟩ mem = ⟨0⟩)
    (ha : 128 + 32 + (execTransactionCalldataInput I.calldata dataLen sigLen).signatures.size ≤ ptr)
    (hp : ptr < 2 ^ 64) (hov : R.length + 48 ≤ 1024) :
    ExecTransactionGuardOutcome fork (execTransactionCalldataInput I.calldata dataLen sigLen)
      initial evm I g s0 (execTransactionDataStart I.calldata) ptr R := by
  let p := execTransactionCalldataInput I.calldata dataLen sigLen
  have hn : p.tx.payload.size = dataLen := execTransactionPayloadSize hb
  have hsn : p.signatures.size = sigLen := execTransactionSignaturesSize hb
  have hdata : execTransactionDataStart I.calldata + p.tx.payload.size ≤ I.calldata.size := by
    rw [hn]; exact hb.dataEnd
  have hsrc : execTransactionDataStart I.calldata < UInt256.size := by
    have := hb.dataEnd
    have := lt_size_of_lt_sign hb.small
    omega
  have hwindow : ptr + 452 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size <
      UInt256.size := by
    rw [hn, hsn]
    have := hb.dataLength
    have := hb.sigLength
    change ptr + 452 + ABI.paddedSize dataLen + ABI.paddedSize sigLen < 2 ^ 256
    unfold ABI.paddedSize
    omega
  have hm : 128 ≤ mem.size := by have := hsig.available; omega
  have hload : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD guardSlot ⟨0⟩)) = execGuardWord evm := by
    simp only [execGuardWord, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      hee, hacc]
  have hs := safeExecGuardLoad (fork := fork) p initial evm
  have hl := execGuardFrame_locals p initial evm
  have hg : (execGuardFrame p initial evm).locals["guard"]? =
      some (.address (AccountAddress.ofUInt256 (execGuardWord evm))) := by
    simp [execGuardFrame]
  have hh : (execGuardFrame p initial evm).locals["txHash"]? =
      some (wordBytes32Value (execTransactionHash p initial)) := by
    simp [execGuardFrame, execSignedFrame, resumeAfterInternalCall, execHashFrame,
      Std.HashMap.getElem_insert]
  have hslot : UInt256.ofNat
      33528237782592280163068556224972516439282563014722366175641814928123294921928 =
      guardSlot := by decide +kernel
  by_cases hzero : UInt256.land (execGuardWord evm) solcAddrMask = ⟨0⟩
  · obtain ⟨_, _, h₂⟩ := safeRuntime_block_4534_fallthrough
      (by simp; omega)
      (by rw [safeAddressMask, hslot, hload, u256_land_comm]; exact hzero) h
    simp only [safeRuntime_block_4534_fallthrough_stack, safeAddressMask, hslot, hload,
      u256_land_comm solcAddrMask] at h₂
    change RD fork safeBytecode I g s0 ⟨4584⟩
      ([⟨128⟩, calldataWord I.calldata 4, UInt256.ofNat (execTransactionDataStart I.calldata),
        calldataWord I.calldata 260, UInt256.land (execGuardWord evm) solcAddrMask,
        calldataWord I.calldata 228, execTransactionHash p initial, UInt256.ofNat dataLen] ++
        (⟨0⟩ :: R)) mem aw rdata σ _ _ at h₂
    rw [← execGuardSaved_calldata hb, ← hacc] at h₂
    have hgzero : AccountAddress.ofUInt256 (execGuardWord evm) = 0 := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat, addressOfNat_eq_of_masked_word, hzero]
      rfl
    have hskip : ExecStmt fork config (execGuardFrame p initial evm) evm execGuardCheck
        (.ok (execGuardFrame p initial evm) evm) :=
      optionalCheckedCallZero (evalLocalValue (hgzero ▸ hg))
    exact .inr ⟨_, evm, mem, _, rdata, _, _, ⟨128⟩,
      fun _ ht ↦ .consNormal hs (.consNormal hskip ht), hl, hg, hh, hee, hworld,
      h₂, hf, hz, hm⟩
  obtain ⟨_, _, h₂⟩ := safeRuntime_block_4534_taken
    (by simp; omega)
    (by rw [safeAddressMask, hslot, hload, u256_land_comm]; exact hzero) (by jump_dest) h
  simp only [safeRuntime_block_4534_taken_stack, safeAddressMask, hslot, hload,
    u256_land_comm solcAddrMask] at h₂
  change RD fork safeBytecode I g s0 ⟨5454⟩
    ([⟨128⟩, calldataWord I.calldata 4, UInt256.ofNat (execTransactionDataStart I.calldata),
      calldataWord I.calldata 260, UInt256.land (execGuardWord evm) solcAddrMask,
      calldataWord I.calldata 228, execTransactionHash p initial, UInt256.ofNat dataLen] ++
      (⟨0⟩ :: R)) mem aw rdata σ _ _ at h₂
  rw [← execGuardSaved_calldata hb] at h₂
  obtain ⟨hr, hsource⟩ | ⟨evm', words, aw', out, k', C', hsource, hee', hw', hn', h₃⟩ :=
    safeExecGuardCallTrace p evm h₂ hee hacc hworld (execTransactionCalldataFields _ _ _)
      hl hg hzero hf hsig ha hp hdata (by rw [hn]; rfl) hsrc hwindow ho hov
  · exact .inl ⟨hr, .consNormal hs (.consRevert hsource)⟩
  · have hpres := execGuardCallMemory_preserves I.calldata mem ptr
      (execTransactionDataStart I.calldata) p (UInt256.ofNat I.source.val) words hdata hn'
    refine .inr ⟨_, evm', _, aw', out, k', C', ⟨0⟩,
      fun _ ht ↦ .consNormal hs (.consNormal hsource ht), hl.set _ _ (by decide),
      ?_, ?_, hee', hw', h₃, ?_, ?_, ?_⟩
    · simpa [Std.HashMap.getElem?_insert] using hg
    · simpa [Std.HashMap.getElem?_insert] using hh
    · exact memLoad_of_wordRead _ _ _ (writeWord_sparse_read_back _ _ _)
    · rw [memLoadReadWord]
      change uInt256OfByteArray ((writeWord _ 64 _).readWithPadding 96 32) = ⟨0⟩
      rw [writeWordReadAbove _ _ _ _ _ (by have := hpres.size; omega) (by decide)]
      simpa only [memLoadReadWord] using
        (hpres.load ⟨96⟩ (by decide) (by change 128 ≤ ptr; omega)
          (by change 128 ≤ mem.size; omega)).trans hz
    · rw [writeWord_sparse_size]
      have := hpres.size
      omega

end Benchmarks.Safe.ViaIR
