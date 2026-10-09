import Benchmarks.Safe.ExecGuardCallTrace
import Benchmarks.Safe.ExecGuardCalldataStack

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def ExecTransactionGuardOutcome (p : ExecTransactionInput) (initial current : EVM.State)
    (I : ExecutionEnv) (g : Sat256) (s0 : State) (src ptr : Nat) (R : List UInt256) : Prop :=
  (RDrev safeBytecode g s0 ∧ ExecBlock config (execSignedFrame p initial) current
    (exectransactionTransition.body.drop 6) .reverted) ∨
  ∃ locals evm' mem' aw' out k' C',
    (∀ result, ExecBlock config { contract := contract, locals := locals } evm'
      (exectransactionTransition.body.drop 8) result →
      ExecBlock config (execSignedFrame p initial) current
        (exectransactionTransition.body.drop 6) result) ∧
    ExecTransactionLocals p locals ∧
    locals["guard"]? = some (.address (AccountAddress.ofUInt256 (execGuardWord current))) ∧
    locals["txHash"]? = some (wordBytes32Value (execTransactionHash p initial)) ∧
    evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
    RD safeBytecode I g s0 ⟨3758⟩
      (execGuardSaved p src ⟨128⟩ (execGuardWord current) (execTransactionHash p initial) R)
      mem' aw' out evm'.accountMap k' C' ∧
    memLoad ⟨64⟩ mem' = UInt256.ofNat ptr ∧ memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ 128 ≤ mem'.size

set_option maxRecDepth 100000 in
theorem safeExecTransactionGuard (initial evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr dataLen sigLen} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3588⟩
      (execSignatureSaved I.calldata dataLen ⟨128⟩
        (execTransactionHash (execTransactionCalldataInput I.calldata dataLen sigLen) initial) R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hb : ExecTransactionCalldataBounds I.calldata dataLen sigLen)
    (ho : (calldataWord I.calldata 100).toNat < 2)
    (hsig : BytesMemory mem 128
      (execTransactionCalldataInput I.calldata dataLen sigLen).signatures)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hz : memLoad ⟨96⟩ mem = ⟨0⟩)
    (ha : 128 + 32 + (execTransactionCalldataInput I.calldata dataLen sigLen).signatures.size ≤ ptr)
    (hp : ptr < 2 ^ 220) (hov : R.length + 48 ≤ 1024) :
    ExecTransactionGuardOutcome (execTransactionCalldataInput I.calldata dataLen sigLen)
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
    simp only [execGuardWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      hee, hacc]
  obtain ⟨_, _, h₁⟩ := safeRuntime_block_3588
    (by simp [execSignatureSaved, execTransactionDecodedStack]; omega) (by jump_dest) h
  change RD safeBytecode I g s0 ⟨3629⟩
    ((σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD guardSlot ⟨0⟩)) :: ⟨0⟩ ::
      execSignatureSaved I.calldata dataLen ⟨128⟩ (execTransactionHash p initial) R)
    mem aw rdata σ _ _ at h₁
  rw [hload] at h₁
  have hs := safeExecGuardLoad p initial evm
  have hl := execGuardFrame_locals p initial evm
  have hg : (execGuardFrame p initial evm).locals["guard"]? =
      some (.address (AccountAddress.ofUInt256 (execGuardWord evm))) := by
    simp [execGuardFrame, Std.HashMap.getElem_insert]
  have hh : (execGuardFrame p initial evm).locals["txHash"]? =
      some (wordBytes32Value (execTransactionHash p initial)) := by
    simp [execGuardFrame, execSignedFrame, resumeAfterInternalCall, execHashFrame,
      Std.HashMap.getElem_insert]
  by_cases hzero : UInt256.land (execGuardWord evm) solcAddrMask = ⟨0⟩
  · have h₂ := safeRuntime_block_3629_taken
      (by simp [execSignatureSaved, execTransactionDecodedStack]; omega)
      (by rw [safeAddressMask, hzero]; decide) (by jump_dest) h₁
    change RD safeBytecode I g s0 _
      (execGuardWord evm :: execSignatureSaved I.calldata dataLen ⟨128⟩
        (execTransactionHash p initial) R) _ _ _ _ _ _ at h₂
    rw [← execGuardSaved_calldata hb, ← hacc] at h₂
    have hgzero : AccountAddress.ofUInt256 (execGuardWord evm) = 0 := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat, addressOfNat_eq_of_masked_word, hzero]
      rfl
    have hskip : ExecStmt config (execGuardFrame p initial evm) evm execGuardCheck
        (.ok (execGuardFrame p initial evm) evm) :=
      optionalCheckedCallZero (evalLocalValue (hgzero ▸ hg))
    exact .inr ⟨_, evm, mem, _, rdata, _, _,
      fun _ ht ↦ .consNormal hs (.consNormal hskip ht), hl, hg, hh, hee, hworld,
      h₂, hf, hz, hm⟩
  have h₂ := safeRuntime_block_3629_fallthrough
    (by simp [execSignatureSaved, execTransactionDecodedStack]; omega)
    (by rw [safeAddressMask]; exact isZero_eq_zero_of_ne hzero) h₁
  change RD safeBytecode I g s0 _
    (execGuardWord evm :: execSignatureSaved I.calldata dataLen ⟨128⟩
      (execTransactionHash p initial) R) _ _ _ _ _ _ at h₂
  rw [← execGuardSaved_calldata hb] at h₂
  obtain ⟨hr, hsource⟩ | ⟨evm', words, aw', out, k', C', hsource, hee', hw', hn', h₃⟩ :=
    safeExecGuardCallTrace p evm h₂ hee hacc hworld hl hg hzero hf hsig ha hm
      (by omega) hdata (by rw [hn]; rfl) hsrc hwindow ho hov
  · exact .inl ⟨hr, .consNormal hs (.consRevert hsource)⟩
  · have hpres := execGuardCallMemory_preserves I.calldata mem ptr
      (execTransactionDataStart I.calldata) p (UInt256.ofNat I.source.val) words hdata hn'
    refine .inr ⟨_, evm', _, aw', out, k', C',
      fun _ ht ↦ .consNormal hs (.consNormal hsource ht), hl.set _ _ (by decide),
      ?_, ?_, hee', hw', h₃, ?_, ?_, hm.trans hpres.size⟩
    · simpa [Std.HashMap.getElem?_insert] using hg
    · simpa [Std.HashMap.getElem?_insert] using hh
    · exact (hpres.load ⟨64⟩ (by decide) (by change 96 ≤ ptr; omega)
        (by change 96 ≤ mem.size; omega)).trans hf
    · exact (hpres.load ⟨96⟩ (by decide) (by change 128 ≤ ptr; omega)
        (by change 128 ≤ mem.size; omega)).trans hz

end Benchmarks.Safe
