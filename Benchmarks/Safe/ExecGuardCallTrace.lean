import Benchmarks.Safe.ExecGuardCallPrepare
import Benchmarks.Safe.ExecGuardSource
import Benchmarks.Safe.RawValueCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecGuardCallTrace (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src sigPtr locals} {guard hash : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3647⟩
      (execGuardSaved p src (UInt256.ofNat sigPtr) guard hash R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : ExecTransactionLocals p locals)
    (hg : locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)))
    (hz : UInt256.land guard solcAddrMask ≠ ⟨0⟩)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hsig : BytesMemory mem sigPtr p.signatures)
    (ha : sigPtr + 32 + p.signatures.size ≤ ptr) (hm : 128 ≤ mem.size) (hptr : 128 ≤ ptr)
    (hin : src + p.tx.payload.size ≤ I.calldata.size)
    (hd : I.calldata.extract src (src + p.tx.payload.size) = p.tx.payload)
    (hs : src < UInt256.size)
    (hb : ptr + 452 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size <
      UInt256.size)
    (ho : p.tx.operation.toNat < 2) (hov : R.length + 48 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecStmt config { contract := contract, locals := locals }
      evm execGuardCheck .reverted) ∨
    ∃ evm' words aw' out k' C',
      ExecStmt config { contract := contract, locals := locals } evm execGuardCheck
        (.ok { contract := contract
               locals := locals.insert "_guardChecked" (collapseReturns []) } evm') ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
      words.length = (p.signatures.size + 31) / 32 ∧
      RD safeBytecode I g s0 ⟨3758⟩
        (execGuardSaved p src (UInt256.ofNat sigPtr) guard hash R)
        (execGuardCallMemory I.calldata mem ptr src p (UInt256.ofNat I.source.val) words)
        aw' out evm'.accountMap k' C' := by
  have ht : AccountAddress.ofUInt256 guard =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask guard) := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm] using
      addressOfNat_eq_of_masked_word guard
  have hguard : AccountAddress.ofUInt256 guard ≠ 0 := by
    rw [ht]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm] using
      maskedAddress_ne_zero_of_mask_ne_zero hz
  have he : evalExpr? config { contract := contract, locals := locals } evm (.var "guard") =
      .ok (.address (AccountAddress.ofUInt256 guard)) := evalLocalValue hg
  have hargs := safeExecGuardArguments p evm hl
  obtain ⟨words, _, _, _, hn, hp, h₁⟩ :=
    safeExecGuardCallPrepare p h hf hsig ha hin hs hb ho hov
  by_cases hc : extCodeSizeWord σ (UInt256.land solcAddrMask guard) = ⟨0⟩
  · obtain ⟨_, _, h₂⟩ := safeRuntime_block_3712_fallthrough
      (by simp [execGuardSaved]; omega) (by rw [hc]; decide) h₁
    have hr := safeRuntime_block_3732 (by
      simp [safeRuntime_block_3712_fallthrough_stack, execGuardSaved]; omega) h₂
    exact .inl ⟨hr, optionalCheckedCallNoCode he hguard ht (by simpa only [hacc] using hc)⟩
  obtain ⟨_, _, h₂⟩ := safeRuntime_block_3712_taken
    (by simp [execGuardSaved]; omega)
    (by rw [isZero_eq_zero_of_ne hc]; decide) (by jump_dest) h₁
  have hpres := execGuardCallMemory_preserves I.calldata mem ptr src p
    (UInt256.ofNat I.source.val) words hin hn
  have hfree : memLoad (UInt256.ofNat 64)
      (execGuardCallMemory I.calldata mem ptr src p (UInt256.ofNat I.source.val) words) =
      UInt256.ofNat ptr :=
    (hpres.load ⟨64⟩ (by decide) (by change 96 ≤ ptr; omega)
      (by change 96 ≤ mem.size; omega)).trans hf
  simp only [safeRuntime_block_3712_taken_stack, hfree] at h₂
  let count := 420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size
  have hsub : UInt256.sub (UInt256.ofNat (ptr + 420 + ABI.paddedSize p.tx.payload.size +
      ABI.paddedSize p.signatures.size)) (UInt256.ofNat ptr) = UInt256.ofNat count := by
    have he : UInt256.ofNat (ptr + count) = UInt256.ofNat ptr + UInt256.ofNat count := by
      apply u256_inj
      rw [ulit_toNat' _ (by dsimp [count]; omega)]
      exact (uadd_ofNat_toNat (by omega) (by dsimp [count]; omega)
        (by dsimp [count]; omega)).symm
    rw [show ptr + 420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size =
      ptr + count by dsimp [count]; omega, he, word_add_sub_left]
  rw [hsub] at h₂
  have h₃ := safeRuntime_block_3735 (by simp [execGuardSaved]; omega) h₂
  obtain ⟨evm', σ', called, out, aw', k', C', hcall, hee', hacc', hw', h₄, _⟩ :=
    rawValueCallTraceFrom evm h₃ hee hacc hworld (by native_decide)
      (by simp [execGuardSaved]; omega) (Or.inr rfl)
  rw [callOutputMem_zero] at h₄
  have htyped : typedCallViaEVM config evm (EVM.address (AccountAddress.ofUInt256 guard))
      "checkTransaction" 0 (execGuardArguments p evm.executionEnv.source)
      (called, evm', out) := by
    refine ⟨(execGuardCallMemory I.calldata mem ptr src p
      (UInt256.ofNat I.source.val) words).readWithPadding ptr count, ?_, ?_⟩
    · rw [hee, safeExecGuardCallEncoding p I.source (by omega)]
      congr 1
      exact (execGuardCallMemory_read I.calldata mem ptr src p
        (UInt256.ofNat I.source.val) words hin hd hn hp).symm
    · simpa only [addressOfAddress, ht, ulit_toNat' ptr (by omega),
        ulit_toNat' count (by dsimp [count]; omega)] using hcall
  cases called
  · have h₅ := safeRuntime_block_3739_fallthrough (by simp [execGuardSaved]; omega)
      (by decide) h₄
    have hr := safeRuntime_block_3746 (by
      simp [safeRuntime_block_3739_fallthrough_stack, execGuardSaved]; omega) h₅
    exact .inl ⟨hr, optionalCheckedCallFailure he hguard ht
      (by simpa only [hacc] using hc) hargs htyped⟩
  · have h₅ := safeRuntime_block_3739_taken (by simp [execGuardSaved]; omega)
      (by decide) (by jump_dest) h₄
    have h₆ := safeRuntime_block_3753 (by simp [execGuardSaved]; omega) h₅
    rw [← hacc'] at h₆
    exact .inr ⟨evm', words, aw', out, _, _, optionalCheckedCallSuccess he hguard ht
      (by simpa only [hacc] using hc) hargs htyped rfl, hee', hw', hn, h₆⟩

end Benchmarks.Safe
