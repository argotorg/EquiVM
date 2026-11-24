import Benchmarks.Safe.ViaIR.ReturnDataMemory
import Benchmarks.Safe.ViaIR.ContractSignatureSource
import Benchmarks.Safe.ViaIR.IRMemoryAllocation
import Benchmarks.Safe.ViaIR.Blocks.Runtime_037
import Benchmarks.Safe.ViaIR.Blocks.Runtime_038
import Benchmarks.Safe.ViaIR.Blocks.Runtime_046

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def signatureReturnMemory (mem : ByteArray) (ptr : Nat) (out : ByteArray) : ByteArray :=
  if out.size = 0 then mem else returnDataMemory mem ptr out

def signatureReturnDataPtr (ptr : Nat) (out : ByteArray) : UInt256 :=
  if out.size = 0 then ⟨96⟩ else UInt256.ofNat ptr

set_option maxRecDepth 2000

theorem safeContractSignatureReturnBuffer {I g s0 σ k C aw mem ptr}
    {out : ByteArray} {z : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7777⟩ (z :: R) mem aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + out.size + 64 < UInt256.size) (hov : R.length + 12 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
      ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7784⟩
        (signatureReturnDataPtr ptr out :: z :: R)
        (signatureReturnMemory mem ptr out) aw' out σ k' C' ∧
        (ptr < 2 ^ 64 → (if out.size = 0 then ptr else
          ptr + 32 + ABI.paddedSize out.size) < 2 ^ 64) := by
  have h₀ := safeRuntime_block_7777 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_7777_stack] at h₀
  simpa only [signatureReturnDataPtr, signatureReturnMemory] using
    safeIRReturnBufferTrace h₀ hf hb (by simp; omega) (by jump_dest)

private theorem safeContractSignatureRequire {I g s0 σ k C aw mem out}
    {scratch : UInt256} {valid : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7796⟩
      (scratch :: (if valid then ⟨1⟩ else ⟨0⟩) :: R) mem aw out σ k C)
    (hov : R.length + 6 ≤ 1024) :
    if valid then ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7803⟩ R mem aw' out σ k' C'
    else RDrev fork safeBytecode g s0 := by
  cases valid with
  | false =>
    have h₁ := safeRuntime_block_7796_taken (by simp; omega) (by decide) (by jump_dest) h
    exact safeRuntime_block_7939 (by simp only [safeRuntime_block_7796_taken_stack]; omega) h₁
  | true =>
    exact safeRuntime_block_7796_fallthrough_packed (by simp; omega) (by decide) h

theorem safeContractSignatureFinish {I g s0 σ k C aw mem} {out : ByteArray}
    {buf : UInt256} {z : Bool} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7784⟩
      (buf :: (if z then ⟨1⟩ else ⟨0⟩) :: R) mem aw out σ k C)
    (hl : memLoad buf mem = UInt256.ofNat out.size)
    (hw : out.size = 32 → memLoad (buf + UInt256.ofNat 32) mem = calldataWord out 0)
    (hb : out.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    if contractSignatureResult z out then
      ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7803⟩ R mem aw' out σ k' C'
    else RDrev fork safeBytecode g s0 := by
  cases z with
  | false =>
    have h₁ := safeRuntime_block_7784_fallthrough (by simp; omega) (by rfl) h
    have h₂ := safeRuntime_block_7790_fallthrough (by simp; omega) (by rfl) h₁
    exact safeContractSignatureRequire (valid := false) h₂ (by omega)
  | true =>
    have h₁ := safeRuntime_block_7784_taken (by simp; omega) (by decide) (by jump_dest) h
    have h₂ := safeRuntime_block_8021 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_8021_stack, hl] at h₂
    by_cases ho : out.size = 32
    · have h₃ := safeRuntime_block_7790_taken (by simp; omega)
        (by rw [ho]; decide) (by jump_dest) h₂
      have h₄ := safeRuntime_block_7984_fallthrough (by simp; omega)
        (by rw [hl, ho, word_add_sub_left]; decide) h₃
      have h₅ := safeRuntime_block_8006 (by simp; omega) (by jump_dest) h₄
      have hm : UInt256.shiftLeft (UInt256.ofNat 185818431) (UInt256.ofNat 225) =
          signatureMagicWord := by decide +kernel
      simp only [safeRuntime_block_8006_stack, hw ho, hm] at h₅
      have hcond : UInt256.eq signatureMagicWord (calldataWord out 0) =
          (if contractSignatureResult true out then ⟨1⟩ else ⟨0⟩) := by
        simp only [contractSignatureResult, ho, decide_true, Bool.true_and, UInt256.eq,
          eq_comm (a := signatureMagicWord) (b := calldataWord out 0)]
        rfl
      rw [hcond] at h₅
      exact safeContractSignatureRequire h₅ (by omega)
    · have hn : UInt256.ofNat 32 ≠ UInt256.ofNat out.size := by
        intro he
        have he' := congrArg UInt256.toNat he
        rw [ulit_toNat' out.size hb] at he'
        exact ho he'.symm
      have hcond : UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat out.size) = ⟨0⟩ := by
        simp [UInt256.eq, UInt256.fromBool, hn]
        rfl
      rw [hcond] at h₂
      have h₃ := safeRuntime_block_7790_fallthrough (by simp; omega) rfl h₂
      have hr := safeContractSignatureRequire (valid := false) h₃ (by omega)
      simpa only [contractSignatureResult, ho, decide_false, Bool.false_and,
        Bool.and_false, Bool.false_eq_true, if_false] using hr

end Benchmarks.Safe.ViaIR
