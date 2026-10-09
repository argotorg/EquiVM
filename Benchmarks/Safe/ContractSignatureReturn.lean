import Benchmarks.Safe.ReturnDataMemory
import Benchmarks.Safe.ContractSignatureSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def signatureReturnMemory (mem : ByteArray) (ptr : Nat) (out : ByteArray) : ByteArray :=
  if out.size = 0 then mem else returnDataMemory mem ptr out

def signatureReturnDataPtr (ptr : Nat) (out : ByteArray) : UInt256 :=
  if out.size = 0 then ⟨96⟩ else UInt256.ofNat ptr

set_option maxRecDepth 100000 in
theorem safeContractSignatureReturnBuffer {I g s0 σ k C aw mem ptr}
    {out : ByteArray} {z x y : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8797⟩ (z :: x :: y :: R) mem aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + out.size + 64 < UInt256.size) (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨8846⟩
      (UInt256.ofNat out.size :: signatureReturnDataPtr ptr out :: z :: R)
      (signatureReturnMemory mem ptr out) aw' out σ k' C' := by
  by_cases hz : out.size = 0
  · have h₁ := safeRuntime_block_8797_taken (by omega) (by rw [hz]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_8841 (by simp; omega) h₁
    exact ⟨_, _, _, by simpa only [safeRuntime_block_8841_stack,
      safeRuntime_block_8797_taken_stack, signatureReturnDataPtr, signatureReturnMemory,
      hz, if_true] using h₂⟩
  · have hne : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have he' := congrArg UInt256.toNat he
      rw [ulit_toNat' out.size (by omega)] at he'
      exact hz he'
    have hcond : UInt256.eq (UInt256.ofNat out.size) ⟨0⟩ = UInt256.ofNat 0 := by
      simp [UInt256.eq, UInt256.fromBool, hne]
    have h₁ := safeRuntime_block_8797_fallthrough (by omega) hcond h
    obtain ⟨aw', k', C', h₂⟩ := safeRuntime_block_8809_packed (by simp; omega)
      (by rw [ulit_toNat' out.size (by omega)]; change 0 + out.size ≤ out.size; omega)
      (by jump_dest) h₁
    rw [safeReturnDataMemory hf hb] at h₂
    change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
    simp only [safeRuntime_block_8809_stack, safeRuntime_block_8797_fallthrough_stack,
      hf] at h₂
    exact ⟨aw', k', C', by simpa only [signatureReturnDataPtr,
      signatureReturnMemory, if_neg hz] using h₂⟩

set_option maxRecDepth 100000 in
theorem safeContractSignatureFinish {I g s0 σ k C aw mem} {out : ByteArray}
    {buf x y d0 d1 d2 d3 d4 ret : UInt256} {z : Bool} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8846⟩
      (UInt256.ofNat out.size :: buf :: (if z then ⟨1⟩ else ⟨0⟩) :: x :: y ::
        d0 :: d1 :: d2 :: d3 :: d4 :: ret :: R) mem aw out σ k C)
    (hl : memLoad buf mem = UInt256.ofNat out.size)
    (hw : out.size = 32 → memLoad (buf + UInt256.ofNat 32) mem = calldataWord out 0)
    (hb : out.size < UInt256.size) (hov : R.length + 16 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      ((if contractSignatureResult z out then ⟨1⟩ else ⟨0⟩) :: R) mem aw' out σ k' C' := by
  cases z with
  | false =>
      have h₁ := safeRuntime_block_8846_taken (by simp; omega) (by decide) (by jump_dest) h
      have h₂ := safeRuntime_block_8865_taken (by simp; omega) (by decide) (by jump_dest) h₁
      have h₃ := safeRuntime_block_8904 (by omega) hret h₂
      exact ⟨_, _, _, by simpa only [safeRuntime_block_8904_stack,
        safeRuntime_block_8846_taken_stack, contractSignatureResult, Bool.false_and,
        Bool.false_eq_true, if_false] using h₃⟩
  | true =>
      have h₁ := safeRuntime_block_8846_fallthrough (by simp; omega) (by decide) h
      have h₂ := safeRuntime_block_8859 (by simp; omega) h₁
      simp only [safeRuntime_block_8859_stack, safeRuntime_block_8846_fallthrough_stack,
        hl] at h₂
      by_cases ho : out.size = 32
      · have h₃ := safeRuntime_block_8865_fallthrough (by simp; omega) (by rw [ho]; decide) h₂
        have h₄ := safeRuntime_block_8872 (by simp; omega) (by jump_dest) h₃
        simp only [safeRuntime_block_8872_stack, hl, ho] at h₄
        rw [u256_add_comm (UInt256.ofNat 32) (buf + UInt256.ofNat 32)] at h₄
        obtain ⟨_, _, _, h₅⟩ := safeBytes32DecoderValid h₄ (by simp; omega)
          (by decide) (by decide) (by jump_dest)
        rw [hw ho] at h₅
        have h₆ := safeRuntime_block_8902 (by simp; omega) h₅
        have h₇ := safeRuntime_block_8904 (by omega) hret h₆
        have hm : UInt256.shiftLeft (UInt256.ofNat 185818431) (UInt256.ofNat 225) =
            signatureMagicWord := by decide +kernel
        exact ⟨_, _, _, by simpa only [safeRuntime_block_8904_stack,
          safeRuntime_block_8902_stack, hm, contractSignatureResult, ho, decide_true,
          Bool.true_and, UInt256.eq] using h₇⟩
      · have hn : UInt256.ofNat 32 ≠ UInt256.ofNat out.size := by
          intro he
          have he' := congrArg UInt256.toNat he
          rw [ulit_toNat' out.size hb] at he'
          exact ho he'.symm
        have hcond : UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat out.size) = ⟨0⟩ := by
          simp [UInt256.eq, UInt256.fromBool, hn]
          rfl
        rw [hcond] at h₂
        have h₃ := safeRuntime_block_8865_taken (by simp; omega) (by decide) (by jump_dest) h₂
        have h₄ := safeRuntime_block_8904 (by omega) hret h₃
        exact ⟨_, _, _, by simpa only [safeRuntime_block_8904_stack,
          contractSignatureResult, ho, decide_false, Bool.false_and, Bool.and_false,
          Bool.false_eq_true, if_false] using h₄⟩

end Benchmarks.Safe
