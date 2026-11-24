import Benchmarks.Safe.ViaIR.PreModuleCallPrepare
import Benchmarks.Safe.ViaIR.PreModuleReturn
import Benchmarks.Safe.ViaIR.PreModuleSource
import Benchmarks.Safe.ViaIR.PreModuleReject
import Benchmarks.Safe.ViaIR.RawValueCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
theorem safePreModuleCheckTrace (words : List UInt256) (payload : ByteArray) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {guard target value operation ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9874⟩
      (value :: operation :: UInt256.ofNat src :: ret :: ⟨0⟩ :: target :: guard :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat payload.size)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (payload.size + 31) / 32)
    (hbytes : (wordBytes words).extract 0 payload.size = payload)
    (hm : 96 ≤ mem.size) (hu : mem.size ≤ ptr + 164) (hp : 96 ≤ ptr)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr)
    (hb : ptr + 228 + 32 * words.length < UInt256.size)
    (hsmall : 196 + 32 * words.length ≤ maxReturnDataSizeByGas)
    (ho : operation.toNat < 2) (hov : R.length + 29 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev fork safeBytecode g s0 ∧
      ExecStmt fork config (preModuleCheckingFrame (AccountAddress.ofUInt256 target)
        value payload operation guard) evm preModuleCheck .reverted) ∨
    ∃ frame evm' σ' mem' aw' rdata' hash k' C',
      ExecStmt fork config (preModuleCheckingFrame (AccountAddress.ofUInt256 target)
        value payload operation guard) evm preModuleCheck (.ok frame evm') ∧
      frame.locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)) ∧
      frame.locals["guardHash"]? = some (.fixedBytes bytes32Width (EVM.Word.toBytesBE hash)) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ret (hash :: guard :: R)
        mem' aw' rdata' σ' k' C' ∧
      (mem' = mem ∨ ∃ out, out.size < 2 ^ 138 ∧ mem' = preModuleReturnMemory
        (preModuleCallMemory mem ptr payload.size target value operation
          (UInt256.ofNat I.source.val) words) out (UInt256.ofNat ptr)) := by
  by_cases hz : UInt256.land guard solcAddrMask = ⟨0⟩
  · have h₁ := safeRuntime_block_9874_fallthrough (by simp; omega)
      (by rw [safeAddressMask]; exact hz) h
    have h₂ := safeRuntime_block_9890 (by simp; omega) hret h₁
    refine Or.inr ⟨_, evm, σ, mem, _, rdata, ⟨0⟩, _, _,
      safePreModuleCheckZero evm _ value payload operation guard hz, ?_, ?_,
      hee, hacc, hworld, h₂, Or.inl rfl⟩ <;>
      simp [preModuleCheckingFrame, preModuleLocals, preModuleArgs, Std.HashMap.getElem_insert]
  have h₁ := safeRuntime_block_9874_taken (by simp; omega)
    (by rw [safeAddressMask]; exact hz) (by jump_dest) h
  simp only [safeRuntime_block_9874_taken_stack, safeAddressMask] at h₁
  obtain ⟨gasArg, aw₂, k₂, C₂, h₂⟩ := safePreModuleCallPrepare words h₁ hf hl hw hn
    hm hu hp hin ha hb ho hov
  let m := preModuleCallMemory mem ptr payload.size target value operation
    (UInt256.ofNat I.source.val) words
  obtain ⟨evm', σ', called, out, aw', k', C', hcall, he, hac, hwo, h₃, hout, hbound⟩ :=
    rawValueCallTraceFrom evm h₂ hee hacc hworld (by native_decide) (by simp; omega)
      (Or.inr rfl)
  have hpt : (UInt256.ofNat ptr).toNat = ptr := ulit_toNat' _ (by omega)
  have hnt : (UInt256.ofNat (196 + 32 * words.length)).toNat = 196 + 32 * words.length :=
    ulit_toNat' _ (by omega)
  have hbout : out.size < 2 ^ 138 := hbound (by
    rw [paddedReadSize, hnt]; exact hsmall)
  have hcopy : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size :=
    callOutputLength hout
  rw [callOutputMem, hcopy] at h₃
  have henc := safePreModuleCallEncoding target value payload operation
    (UInt256.ofNat I.source.val) (by omega)
  rw [accountAddress_roundtrip,
    ← preModuleCallMemory_read mem ptr payload target value operation
      (UInt256.ofNat I.source.val) words hu hn hbytes] at henc
  have ht : AccountAddress.ofUInt256 guard =
      AccountAddress.ofUInt256 (UInt256.land guard solcAddrMask) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      addressOfNat_eq_of_masked_word guard
  have htyped : typedCallViaEVM fork config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkModuleTransaction" 0 [.address (AccountAddress.ofUInt256 target),
        .int (Int.ofNat value.toNat), .bytes payload, .int (Int.ofNat operation.toNat),
        .address evm.executionEnv.source] (called, evm', out) := by
    refine ⟨m.readWithPadding ptr (196 + 32 * words.length), ?_, ?_⟩
    · simpa only [hee] using henc
    · simpa only [addressOfAddress, ht, hpt, hnt] using hcall
  cases called
  · exact Or.inl ⟨safePreModuleCallFailure h₃ (by simp; omega),
      safePreModuleCheckFailed hz htyped⟩
  · have hfree : memLoad ⟨64⟩ m = UInt256.ofNat ptr :=
      (preModuleCallMemory_free mem ptr payload.size target value operation
        (UInt256.ofNat I.source.val) words hm hp).trans hf
    have hsize := preModuleCallMemory_size mem ptr payload.size target value operation
      (UInt256.ofNat I.source.val) words hu hn
    rcases safePreModuleReturn h₃ hfree (by rw [hpt]; omega) (by rw [hpt]; exact hp)
      (by rw [hpt]; omega) (lt_trans hbout (by decide)) (by simp; omega) with
      hr | ⟨aw₄, k₄, C₄, h₄, hd⟩
    · exact Or.inl ⟨hr, safePreModuleCanReject evm target value operation guard payload hz
        (by omega)⟩
    · have h₅ := safeRuntime_block_10003 (by simp; omega) (by jump_dest) h₄
      obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeRuntime_block_9890_packed (by simp; omega) hret h₅
      refine Or.inr ⟨_, evm', σ', _, aw₆, out, calldataWord out 0, k₆, C₆,
        safePreModuleCheckSuccess hz htyped hd, ?_, ?_, he, hac, hwo, h₆,
        Or.inr ⟨out, hbout, rfl⟩⟩ <;>
        simp [preModuleCalledFrame, preModuleLocals, preModuleArgs, Std.HashMap.getElem_insert]

end Benchmarks.Safe.ViaIR
