import Benchmarks.Safe.ExecTransactionHashTrace
import Benchmarks.Safe.ExecTransactionSignatureSource
import Benchmarks.Safe.CheckSignaturesTrace
import Benchmarks.Safe.SignatureDecodedMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def ExecTransactionPrepareOutcome (p : ExecTransactionInput) (evm : EVM.State)
    (I : ExecutionEnv) (g : Sat256) (s0 : State) (dataLen : Nat) (R : List UInt256) : Prop :=
  (RDrev safeBytecode g s0 ∧
    ExecBlock config p.frame evm exectransactionTransition.body .reverted) ∨
  (RDstatic safeBytecode g s0 ∧
    ExecBlock config p.frame evm exectransactionTransition.body .staticViolation) ∨
  ∃ evm' mem' ptr' out aw' k' C',
    (∀ result, ExecBlock config (execSignedFrame p evm) evm'
      (exectransactionTransition.body.drop 6) result →
      ExecBlock config p.frame evm exectransactionTransition.body result) ∧
    evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
    RD safeBytecode I g s0 ⟨3588⟩
      (execSignatureSaved I.calldata dataLen ⟨128⟩ (execTransactionHash p evm) R)
      mem' aw' out evm'.accountMap k' C' ∧
    BytesMemory mem' 128 p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
    memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ 128 + 32 + p.signatures.size ≤ ptr' ∧ ptr' < 2 ^ 205

set_option maxRecDepth 100000 in
theorem safeExecTransactionPrepare (evm : EVM.State)
    {I g s0 σ k C aw rdata dataLen sigLen} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3533⟩ (execTransactionDecodedStack I.calldata dataLen ⟨128⟩ R)
      (memoryBytesDecoded (execTransactionCalldataInput I.calldata dataLen sigLen).signatures)
      aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hb : ExecTransactionCalldataBounds I.calldata dataLen sigLen)
    (ho : (calldataWord I.calldata 100).toNat < 2) (hn : sigLen ≤ 2 ^ 64 - 192)
    (hov : R.length + 64 ≤ 1024) :
    ExecTransactionPrepareOutcome (execTransactionCalldataInput I.calldata dataLen sigLen)
      evm I g s0 dataLen R := by
  let p := execTransactionCalldataInput I.calldata dataLen sigLen
  have hlen : p.signatures.size = sigLen := by
    change (I.calldata.extract (execTransactionSignaturesStart I.calldata)
      (execTransactionSignaturesStart I.calldata + sigLen)).size = sigLen
    rw [ByteArray.size_extract]; have := hb.sigEnd; omega
  have hsig : p.signatures.size ≤ 2 ^ 64 - 192 := by rw [hlen]; exact hn
  obtain ⟨_, _, h₁⟩ := safeExecNonceStart evm h hee hacc (by omega)
  by_cases hno : (execNonce evm).toNat + 1 < UInt256.size
  swap
  · exact .inl ⟨safeIncrementOverflow h₁
      (by simp [execHashStack, execHashSaved, execTransactionDecodedStack]; omega) hno,
      safeExecTransactionNonceOverflow p evm hsig ho hno⟩
  obtain ⟨_, _, h₂⟩ := safeIncrementTrace h₁
    (by simp [execHashStack, execHashSaved, execTransactionDecodedStack]; omega) hno (by jump_dest)
  cases hperm : I.perm with
  | false =>
      exact .inr (.inl ⟨safeExecNonceStatic h₂ hperm
        (by simp [execHashStack, execHashSaved, execTransactionDecodedStack]; omega),
        safeExecTransactionNonceStatic p evm hsig ho hno (by rwa [hee])⟩)
  | true =>
      obtain ⟨_, _, h₃⟩ := safeExecNonceStore evm h₂ hee hacc hperm
        (by simp [execHashStack, execHashSaved, execTransactionDecodedStack]; omega)
      let ptr := memoryBytesInitialEnd p.signatures.size
      let mem := memoryBytesDecoded p.signatures
      let tx := { p.tx with nonce := execNonce evm }
      let hashed := transactionHashMemory mem ptr I
        (UInt256.ofNat (execTransactionDataStart I.calldata)) tx
      have hp : ptr < 2 ^ 64 := memoryBytesInitialEnd_bound hsig
      have ha : 128 + 32 + p.signatures.size ≤ ptr := memoryBytesInitialEnd_contains _
      have hm : 128 ≤ mem.size := by dsimp only [mem]; rw [memoryBytesDecoded_size]; omega
      have hfree : memLoad ⟨64⟩ mem = UInt256.ofNat ptr := memoryBytesDecoded_free _
      obtain ⟨aw₄, _, _, h₄⟩ := safeExecHashTrace evm h₃ hee hb hfree
        (by change 96 ≤ mem.size; omega) (by omega)
        (by change ptr + 352 < 2 ^ 256; omega) (by omega)
      have hee₁ : (execNonceState evm).executionEnv = I := by
        simpa only [execNonceState, storageStore_executionEnv] using hee
      have hw₁ : (execNonceState evm).σ₀ = s0.σ₀ := by
        simpa only [execNonceState, storageStore_σ₀] using hworld
      have hdata : tx.payload.size = dataLen := by
        change (I.calldata.extract (execTransactionDataStart I.calldata)
          (execTransactionDataStart I.calldata + dataLen)).size = dataLen
        rw [ByteArray.size_extract]; have := hb.dataEnd; omega
      have hsrc : execTransactionDataStart I.calldata < UInt256.size := by
        have := hb.dataEnd
        have := lt_size_of_lt_sign hb.small
        omega
      have hpres : MemoryPreserves mem hashed 0 ptr := transactionHashMemory_preserves
        mem ptr I _ tx (by rw [ulit_toNat' _ hsrc, hdata]; exact hb.dataEnd)
      have hsigs : BytesMemory hashed 128 p.signatures := by
        have hh : BytesMemory mem 128 p.signatures := BytesMemory.decoded _
        apply hh.preserved (by decide) hpres.size
        intro off count hlo hhi
        exact hpres.read off count (by omega) (by omega) (by have := hh.available; omega)
      have hf : memLoad ⟨64⟩ hashed = UInt256.ofNat ptr :=
        (hpres.load ⟨64⟩ (by decide) (by change 96 ≤ ptr; omega)
          (by change 96 ≤ mem.size; omega)).trans hfree
      have hz : memLoad ⟨96⟩ hashed = ⟨0⟩ :=
        (hpres.load ⟨96⟩ (by decide) (by change 128 ≤ ptr; omega)
          (by change 128 ≤ mem.size; omega)).trans (memoryBytesDecoded_zero _)
      obtain ⟨_, _, h₅⟩ := safeExecSignatureStart h₄ (by omega)
      obtain ⟨hrev, hs⟩ | ⟨f', evm', σ', mem', ptr', aw', out, k', C', hs, hee', hacc', hw',
          h₆, hsigs', hf', hz', hptrlo, hptrhi, _⟩ :=
        safeCheckSignaturesTrace (execSignatureInput p evm) (execNonceState evm) h₅
          (by rw [accountAddress_roundtrip]; exact congrArg ExecutionEnv.source hee)
          hee₁ rfl hw₁ hsigs hf hz (by decide) ha (by omega)
          (by change p.signatures.size < 2 ^ 64; omega)
          (by simp [execSignatureSaved, execTransactionDecodedStack]; omega) (by jump_dest)
      · exact .inl ⟨hrev, safeExecSignatureRevert p evm hsig ho hno hs⟩
      · rw [← hacc'] at h₆
        have ha' : 128 + 32 + p.signatures.size ≤ ptr' := by omega
        have hp' : ptr' < 2 ^ 205 := by omega
        exact .inr (.inr ⟨evm', mem', ptr', out, aw', k', C',
          fun _ ht ↦ safeExecSignaturePrefix p evm hsig ho hno hs ht,
          hee', hw', h₆, hsigs', hf', hz', ha', hp'⟩)

end Benchmarks.Safe
