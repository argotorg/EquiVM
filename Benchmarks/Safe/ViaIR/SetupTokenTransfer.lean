import Benchmarks.Safe.ViaIR.TokenTransferTrace
import Benchmarks.Safe.ViaIR.Blocks.Runtime_048

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeSetupTokenTransferMemory {mem : ByteArray} {ptr : Nat} {receiver amount : UInt256}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + 100 < UInt256.size) (hc : receiver.toNat < EVM.addressModulus) :
    safeRuntime_block_10565_memory (mem := mem) (x0 := amount) (x3 := ⟨32⟩)
      (x5 := receiver) = tokenTransferHeaderMemory mem ptr receiver amount := by
  exact safeTokenTransferMemory hf hb hc

set_option maxRecDepth 5000 in
theorem safeSetupTokenTransferPrepare {I g s0 σ k C aw mem rdata ptr}
    {amount receiver token ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10565⟩
      (amount :: token :: ⟨0⟩ :: ⟨32⟩ :: ret :: receiver :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 96 ≤ ptr)
    (hb : ptr + 128 < 2 ^ 64) (hc : receiver.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ gasArg aw' k' C', RD fork safeBytecode I g s0 ⟨10627⟩
      (gasArg :: token :: ⟨0⟩ :: UInt256.ofNat (ptr + 32) :: ⟨68⟩ :: ⟨0⟩ :: ⟨32⟩ ::
        ret :: amount :: R) (tokenTransferMemory mem ptr receiver amount) aw' rdata σ k' C' := by
  have hbword : ptr + 128 < UInt256.size := by change ptr + 128 < 2 ^ 256; omega
  have hmemory := safeSetupTokenTransferMemory (amount := amount) hf (by omega) hc
  obtain ⟨aw₁, k₁, C₁, h₁⟩ :=
    safeRuntime_block_10565_packed (by simp; omega) (by jump_dest) h
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have h32 : UInt256.ofNat ptr + (⟨32⟩ : UInt256) = UInt256.ofNat (ptr + 32) :=
    tokenTransferPointerAdd (by omega) 32 (by decide)
  simp only [safeRuntime_block_10565_stack, hf, h32] at h₁
  rw [hmemory] at h₁
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeIRAllocateValidTrace h₁ (by decide)
    (by simpa only [show ABI.paddedSize 100 = 128 from rfl] using hb)
    (by simp; omega) (by jump_dest)
  change RD fork safeBytecode I g s0 (UInt256.ofNat 10618)
    (UInt256.ofNat ptr :: ⟨0⟩ :: UInt256.ofNat (ptr + 32) :: token :: ⟨0⟩ :: ⟨32⟩ ::
      ret :: amount :: R) (tokenTransferMemory mem ptr receiver amount) aw₂ rdata σ k₂ C₂
    at h₂
  have hlen : memLoad (UInt256.ofNat ptr) (tokenTransferMemory mem ptr receiver amount) =
      ⟨68⟩ := by
    apply memLoad_of_wordRead
    rw [ulit_toNat' ptr (by omega)]
    exact tokenTransferMemory_length _ _ _ _ hp
  have h₃ := safeRuntime_block_10618 (by simp; omega) h₂
  simp only [safeRuntime_block_10618_stack, hlen] at h₃
  exact ⟨_, _, _, _, h₃⟩

set_option maxRecDepth 2000 in
theorem safeSetupTokenTransferAllocationRevert {I g s0 σ k C aw mem rdata ptr}
    {amount receiver token ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10565⟩
      (amount :: token :: ⟨0⟩ :: ⟨32⟩ :: ret :: receiver :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr < 2 ^ 64)
    (hn : ¬ptr + 128 < 2 ^ 64) (hov : R.length + 16 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have hbword : ptr + 128 < UInt256.size := by change ptr + 128 < 2 ^ 256; omega
  obtain ⟨aw₁, k₁, C₁, h₁⟩ :=
    safeRuntime_block_10565_packed (by simp; omega) (by jump_dest) h
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have h32 : UInt256.ofNat ptr + (⟨32⟩ : UInt256) = UInt256.ofNat (ptr + 32) :=
    tokenTransferPointerAdd (by omega) 32 (by decide)
  simp only [safeRuntime_block_10565_stack, hf, h32] at h₁
  obtain hr | ⟨_, _, _, hfit, _⟩ := safeIRAllocateTrace h₁ (by decide)
    (by simpa only [show ABI.paddedSize 100 = 128 from rfl] using hbword)
    (by simp; omega) (by jump_dest)
  · exact hr
  · exact False.elim (hn hfit)


set_option maxRecDepth 5000 in
theorem safeSetupTokenTransferReturn {I g s0 σ k C aw mem out}
    {amount ret : UInt256} {R : List UInt256} (z : Bool)
    (h : RD fork safeBytecode I g s0 ⟨10628⟩ (z.toUInt256 :: ret :: amount :: R)
      (callOutputMem mem out ⟨0⟩ ⟨32⟩) aw out σ k C)
    (hb : out.size < UInt256.size) (hov : R.length + 12 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨10644⟩
      ((tokenTransferResult z out).toUInt256 :: ret :: amount :: R)
      (callOutputMem mem out ⟨0⟩ ⟨32⟩) aw' out σ k' C' := by
  by_cases hz : out.size = 0
  · have h₁ := safeRuntime_block_10628_taken (by simp; omega)
      (by rw [hz]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_10663 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, _, by simpa only [safeRuntime_block_10663_stack,
      tokenTransferResult, hz, ite_true] using h₂⟩
  have hnz : UInt256.ofNat out.size ≠ ⟨0⟩ := by
    intro he
    have he' := congrArg UInt256.toNat he
    rw [ulit_toNat' out.size hb] at he'
    exact hz he'
  have h₁ := safeRuntime_block_10628_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne hnz) h
  by_cases hs : out.size = 32
  · have h₂ := safeRuntime_block_10635_taken (by simp; omega)
      (by rw [hs]; decide) (by jump_dest) h₁
    have h₃ := safeRuntime_block_10651 (by simp; omega) (by jump_dest) h₂
    have hw : memLoad ⟨0⟩ (callOutputMem mem out ⟨0⟩ ⟨32⟩) = calldataWord out 0 := by
      apply memLoad_of_wordRead
      exact callOutput32_read_word _ _ _ hb (by omega) (by exact Nat.zero_le _)
    exact ⟨_, _, _, by simpa only [safeRuntime_block_10651_stack, hw,
      callSuccessNonzeroWord, tokenTransferResult, hz, hs, ite_false, ite_true] using h₃⟩
  · have hns : UInt256.ofNat 32 ≠ UInt256.ofNat out.size := by
      intro he
      have he' := congrArg UInt256.toNat he
      rw [ulit_toNat' out.size hb] at he'
      exact hs he'.symm
    have h₂ := safeRuntime_block_10635_fallthrough (by simp; omega)
      (u256_eq_of_ne hns) h₁
    have h₃ := safeRuntime_block_10642 (by simp; omega) h₂
    exact ⟨_, _, _, by simpa only [safeRuntime_block_10642_stack,
      tokenTransferResult, hz, hs, ite_false] using h₃⟩


set_option maxRecDepth 2000 in
theorem safeSetupTokenTransferTrace (p : TokenTransferInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10565⟩
      (p.amount :: UInt256.ofNat p.token.val :: ⟨0⟩ :: ⟨32⟩ :: ret ::
        UInt256.ofNat p.receiver.val :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 128 ≤ ptr)
    (hb : ptr + 128 < 2 ^ 64) (hov : R.length + 24 ≤ 1024) :
    ∃ evm' σ' z out aw' k' C',
      ExecFuncBody fork config p.frame evm transferTokenFunction.body
        (.returned (p.finalFrame z out) evm' (some [.bool (tokenTransferResult z out)])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨10644⟩
        ((tokenTransferResult z out).toUInt256 :: ret :: p.amount :: R)
        (tokenTransferOutputMemory mem ptr p out) aw' out σ' k' C' := by
  have hbword : ptr + 128 < UInt256.size := by change ptr + 128 < 2 ^ 256; omega
  obtain ⟨gasArg, aw₁, k₁, C₁, h₁⟩ := safeSetupTokenTransferPrepare h hf (by omega)
    hb (addressWord_canonical _) (by omega)
  obtain ⟨evm', σ', z, out, aw₂, k₂, C₂, hc, hee', hacc', hw', h₂, hout, _⟩ :=
    rawValueCallTraceFrom evm h₁ hee hacc hworld (by native_decide)
      (by simp; omega) (.inr rfl)
  have hread := tokenTransferMemory_read mem ptr (UInt256.ofNat p.receiver.val) p.amount
    (by omega)
  have hc' : callViaEVM fork evm (EVM.address p.token) 0 p.callBytes (z, evm', out) := by
    simpa only [accountAddress_roundtrip, addressOfAddress, ulit_toNat' (ptr + 32) (by omega),
      show (⟨68⟩ : UInt256).toNat = 68 from rfl, hread, TokenTransferInput.callBytes] using hc
  have hbz : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
  rw [hbz] at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeSetupTokenTransferReturn z h₂ hout (by omega)
  exact ⟨evm', σ', z, out, aw₃, k₃, C₃,
    safeTokenTransferSource hc', hee', hacc', hw', h₃⟩

end Benchmarks.Safe.ViaIR
