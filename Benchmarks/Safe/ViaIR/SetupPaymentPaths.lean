import Benchmarks.Safe.ViaIR.SetupPaymentPrepare
import Benchmarks.Safe.ViaIR.SetupTokenTransfer
import Benchmarks.Safe.ViaIR.PaymentNativeReturn
import Benchmarks.Safe.ViaIR.CallNonemptyReject

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000

def SetupPaymentOutcome (fork : Ethereum.Fork) (p : PaymentInput) (evm : State) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (ret : UInt256) (R : List UInt256) : Prop :=
  (RDrev fork safeBytecode g s0 ∧
    ExecFuncBody fork config p.frame evm handlePaymentFunction.body .reverted) ∨
  ∃ (f' : Frame) (evm' : State) (mem' : ByteArray) (out : ByteArray)
    (aw' : UInt256) (k' C' : Nat),
    ExecFuncBody fork config p.frame evm handlePaymentFunction.body
      (.returned f' evm' (some [uint256Value (UInt256.mul p.gasTotal (paymentPrice p I))])) ∧
    RD fork safeBytecode I g s0 ret (UInt256.mul p.gasTotal (paymentPrice p I) :: R)
      mem' aw' out evm'.accountMap k' C'

theorem safeSetupPaymentTokenFinish {I g s0 σ k C aw mem out}
    {ret payment : UInt256} {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 ⟨10644⟩
      (z.toUInt256 :: ret :: payment :: R) mem aw out σ k C)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    if z then ∃ k' C', RD fork safeBytecode I g s0 ret
      (payment :: R) mem aw out σ k' C' else RDrev fork safeBytecode g s0 := by
  cases z
  · have h₁ := safeRuntime_block_10644_taken (by simp; omega) (by decide) (by jump_dest) h
    simp only [safeRuntime_block_10644_taken_stack] at h₁
    have h₂ := safeRuntime_block_5243 (by simp; omega) (by jump_dest) h₁
    exact safeRuntime_block_9727 (by simp; omega) h₂
  · have h₁ := safeRuntime_block_10644_fallthrough (by simp; omega) (by decide) h
    exact ⟨_, _, safeRuntime_block_10650 (by simp; omega) hret h₁⟩

theorem safeSetupPaymentTokenTrace (p : PaymentInput) (evm : State)
    {I g s0 σ k C aw mem rdata ptr} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10565⟩
      (UInt256.mul p.gasTotal p.gasPrice :: UInt256.ofNat p.gasToken.val :: ⟨0⟩ :: ⟨32⟩ ::
        ret :: UInt256.ofNat (p.receiver I).val :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * p.gasPrice.toNat < UInt256.size)
    (htoken : p.gasToken ≠ EVM.address 0)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 128 ≤ ptr)
    (hb : ptr + 128 < 2 ^ 64) (hov : R.length + 28 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    SetupPaymentOutcome fork p evm I g s0 ret R := by
  obtain ⟨evm', σ', z, out, aw₂, k₂, C₂, hsource, hee', hacc', hw', h₂⟩ :=
    safeSetupTokenTransferTrace (p.tokenInput I) evm h hee hacc hworld hf hp hb (by omega)
  have hcallee : ExecFuncBody fork config (p.tokenInput evm.executionEnv).frame evm
      transferTokenFunction.body
      (.returned ((p.tokenInput I).finalFrame z out) evm'
        (some [.bool (tokenTransferResult z out)])) := by simpa only [hee] using hsource
  have hbody := safePaymentTokenSource hsum hprod htoken hcallee
  have hfinish := safeSetupPaymentTokenFinish (tokenTransferResult z out) h₂ (by omega) hret
  cases he : tokenTransferResult z out
  · simp only [he, Bool.false_eq_true, ite_false] at hbody hfinish
    exact .inl ⟨hfinish, hbody⟩
  · simp only [he, ite_true] at hbody hfinish
    obtain ⟨k₃, C₃, h₃⟩ := hfinish
    refine .inr ⟨p.tokenFinal evm.executionEnv true, evm',
      tokenTransferOutputMemory mem ptr (p.tokenInput I) out, out, aw₂, k₃, C₃, ?_, ?_⟩
    · simpa only [paymentPrice, htoken, ite_false] using hbody
    · simpa only [paymentPrice, htoken, ite_false, hacc', PaymentInput.tokenInput] using h₃

theorem safeSetupPaymentNativeFinish {I g s0 σ k C aw mem out}
    {buf ret payment : UInt256} {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 ⟨10521⟩
      (buf :: z.toUInt256 :: ret :: payment :: R) mem aw out σ k C)
    (hov : R.length + 12 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    if z then ∃ k' C', RD fork safeBytecode I g s0 ret
      (payment :: R) mem aw out σ k' C' else RDrev fork safeBytecode g s0 := by
  cases z
  · have h₁ := safeRuntime_block_10521_taken (by simp; omega) (by decide) (by jump_dest) h
    simp only [safeRuntime_block_10521_taken_stack] at h₁
    have h₂ := safeRuntime_block_5106 (by simp; omega) (by jump_dest) h₁
    exact safeRuntime_block_9772 (by simp; omega) h₂
  · have h₁ := safeRuntime_block_10521_fallthrough (by simp; omega) (by decide) h
    exact ⟨_, _, safeRuntime_block_10528 (by simp; omega) hret h₁⟩

theorem safeSetupPaymentReturnBuffer {I g s0 σ k C aw mem ptr out}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10382⟩ (ret :: R) mem aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + out.size + 64 < UInt256.size) (hov : R.length + 11 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev fork safeBytecode g s0 ∧ out ≠ ByteArray.empty) ∨
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      ((if out.size = 0 then ⟨96⟩ else UInt256.ofNat ptr) :: R)
      (paymentReturnMemory mem ptr out) aw' out σ k' C' := by
  by_cases hz : out = ByteArray.empty
  · have hs : out.size = 0 := by rw [hz]; rfl
    have h₁ := safeRuntime_block_10382_taken (by simp; omega)
      (by rw [hs]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_10424 (by simp; omega) hret h₁
    exact .inr ⟨_, _, _, by simpa only [paymentReturnMemory, hs, if_true] using h₂⟩
  · obtain hr | ⟨aw', k', C', h', _⟩ := safePaymentReturnBuffer h hf hb hov hret
    · exact .inl ⟨hr, hz⟩
    · exact .inr ⟨aw', k', C', h'⟩

theorem safeSetupPaymentNativeTrace (p : PaymentInput) (evm : State)
    {I g s0 σ k C aw mem rdata ptr} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10499⟩
      (UInt256.mul p.gasTotal (p.nativePrice I) ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ret ::
        UInt256.ofNat (p.receiver I).val :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hsum : p.gasUsed.toNat + p.baseGas.toNat < UInt256.size)
    (hprod : p.gasTotal.toNat * (p.nativePrice I).toNat < UInt256.size)
    (htoken : p.gasToken = EVM.address 0)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr < 2 ^ 64)
    (hperm : I.perm = true) (hov : R.length + 28 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    SetupPaymentOutcome fork p evm I g s0 ret R := by
  have h₁ := safeRuntime_block_10499 (by simp; omega) h
  simp only [safeRuntime_block_10499_stack, safeAddressMask,
    solcAddrMask_clean_left (safePaymentReceiverWord p I)] at h₁
  obtain ⟨evm', σ', z, out, aw₂, k₂, C₂, hc, hee', hacc', hw', h₂, hout, hbound⟩ :=
    rawValueCallTraceFrom evm h₁ hee hacc hworld (by native_decide) (by simp; omega)
      (.inl hperm)
  have hc' : callViaEVM fork evm (EVM.address (p.receiver evm.executionEnv))
      (Int.ofNat (UInt256.mul p.gasTotal (p.nativePrice evm.executionEnv)).toNat)
      ByteArray.empty (z, evm', out) := by
    simpa only [hee, accountAddress_roundtrip, addressOfAddress,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hc
  have hout138 : out.size < 2 ^ 138 := hbound (by
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero]
    exact Nat.zero_le _)
  have hbz : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
  rw [hbz, callOutputMem_zero] at h₂
  have h₂' := safeRuntime_block_10514 (by simp; omega) (by jump_dest) h₂
  obtain ⟨hrev, hne⟩ | ⟨aw₃, k₃, C₃, h₃⟩ := safeSetupPaymentReturnBuffer h₂' hf
    (by change ptr + out.size + 64 < 2 ^ 256; omega) (by simp; omega) (by jump_dest)
  · obtain ⟨failed, failedOut, hcFail⟩ := callNonemptyCanReject hc' (by decide) hne
    exact .inl ⟨hrev, safePaymentNativeSource (hperm := Or.inr (by simpa only [hee] using hperm)) hsum
      (by simpa only [hee] using hprod) htoken hcFail⟩
  have hbody := safePaymentNativeSource (fork := fork) (hperm := Or.inr (by simpa only [hee] using hperm)) hsum (by simpa only [hee] using hprod) htoken hc'
  have hfinish := safeSetupPaymentNativeFinish z h₃ (by omega) hret
  cases z
  · exact .inl ⟨hfinish, hbody⟩
  · obtain ⟨k₄, C₄, h₄⟩ := hfinish
    refine .inr ⟨p.nativeFinal evm.executionEnv true out, evm',
      paymentReturnMemory mem ptr out, out, aw₃, k₄, C₄, ?_, ?_⟩
    · simpa only [paymentPrice, htoken, ite_true, hee] using hbody
    · simpa only [paymentPrice, htoken, ite_true, hacc'] using h₄

end Benchmarks.Safe.ViaIR
