import Benchmarks.Safe.V3_77901a5.ReturnDataMemory
import Benchmarks.Safe.V3_77901a5.ContractSignatureSource
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_030
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_031
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_038

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V3_77901a5.RuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000

def signatureReturnMemory (mem : ByteArray) (ptr : Nat) (out : ByteArray) : ByteArray :=
  if out.size = 0 then mem else returnDataMemory mem ptr out

def signatureReturnPtr (ptr : Nat) (out : ByteArray) : Nat :=
  if out.size = 0 then 96 else ptr

theorem signatureReturnMemory_length (mem out : ByteArray) (ptr : Nat)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hb : ptr < UInt256.size) :
    memLoad (UInt256.ofNat (signatureReturnPtr ptr out)) (signatureReturnMemory mem ptr out) =
      UInt256.ofNat out.size := by
  by_cases he : out.size = 0
  · simpa only [signatureReturnMemory, signatureReturnPtr, he, if_true] using hz
  · simp only [signatureReturnMemory, signatureReturnPtr, he, if_false]
    apply memLoad_of_wordRead
    rw [ulit_toNat' _ hb]
    exact returnDataMemory_length mem out ptr

theorem signatureReturnMemory_word (mem out : ByteArray) (ptr : Nat)
    (hs : out.size = 32) (hb : ptr + 32 < UInt256.size) :
    memLoad (UInt256.ofNat (signatureReturnPtr ptr out) + UInt256.ofNat 32)
      (signatureReturnMemory mem ptr out) = calldataWord out 0 := by
  simp only [signatureReturnPtr, signatureReturnMemory, hs, show ¬32 = 0 by decide, if_false]
  apply memLoad_of_wordRead
  have hadd : (UInt256.ofNat ptr + UInt256.ofNat 32).toNat = ptr + 32 :=
    uadd_ofNat_toNat (by omega) (by decide) hb
  rw [hadd]
  exact returnDataMemory_word mem out ptr (by omega)

theorem safeContractSignatureReturnBuffer {I g s0 σ k C aw mem ptr}
    {out : ByteArray} {a b c : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8797⟩ (a :: b :: c :: R) mem aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + out.size + 64 < UInt256.size) (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨8846⟩
      (UInt256.ofNat out.size :: UInt256.ofNat (signatureReturnPtr ptr out) :: a :: R)
      (signatureReturnMemory mem ptr out) aw' out σ k' C' := by
  by_cases hz : out.size = 0
  · have h₁ := safeRuntime_block_8797_taken (by omega)
      (by rw [hz]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_8841 (by simp only [safeRuntime_block_8797_taken_stack, List.length_cons]; omega) h₁
    exact ⟨_, _, _, by simpa only [safeRuntime_block_8841_stack,
      safeRuntime_block_8797_taken_stack, signatureReturnMemory, signatureReturnPtr, hz,
      if_true] using h₂⟩
  · have hn : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have hh := congrArg UInt256.toNat he
      rw [ulit_toNat' _ (by omega)] at hh
      exact hz hh
    have h₁ := safeRuntime_block_8797_fallthrough (by omega) (u256_eq_of_ne hn) h
    have h₂ := safeRuntime_block_8809 (by simp only [safeRuntime_block_8797_fallthrough_stack, List.length_cons]; omega) (by change 0 + out.size % UInt256.size ≤ out.size; simpa only [Nat.zero_add] using Nat.mod_le out.size UInt256.size)
      (by jump_dest) h₁
    have hm : safeRuntime_block_8809_memory (mem := mem) (rdata := out) =
        returnDataMemory mem ptr out := by
      exact safeReturnDataMemory hf hb
    change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
    exact ⟨_, _, _, by simpa only [safeRuntime_block_8809_stack,
      safeRuntime_block_8797_fallthrough_stack, hm, hf, signatureReturnMemory,
      signatureReturnPtr, hz, if_false] using h₂⟩

theorem safeContractSignatureCallFailure {I g s0 σ k C aw mem out}
    {size ptr d0 d1 d2 d3 d4 d5 d6 ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8846⟩
      (size :: ptr :: ⟨0⟩ :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: ret :: R)
      mem aw out σ k C)
    (hov : R.length + 13 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret (⟨0⟩ :: R) mem aw' out σ k' C' := by
  have h₁ := safeRuntime_block_8846_taken (by simp; omega) (by decide) (by jump_dest) h
  have h₂ := safeRuntime_block_8865_taken (by simp only [safeRuntime_block_8846_taken_stack, List.length_cons]; omega) (by decide) (by jump_dest) h₁
  exact safeRuntime_block_8904_packed (by omega) hret h₂

theorem safeContractSignatureFinish {I g s0 σ k C aw mem} {out : ByteArray} {z : Bool}
    {size ptr d0 d1 d2 d3 d4 d5 d6 ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8846⟩
      (size :: ptr :: z.toUInt256 :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: ret :: R)
      mem aw out σ k C)
    (hl : memLoad ptr mem = UInt256.ofNat out.size)
    (hw : out.size = 32 → memLoad (ptr + UInt256.ofNat 32) mem = calldataWord out 0)
    (hb : out.size < UInt256.size) (hov : R.length + 16 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      ((contractSignatureResult z out).toUInt256 :: R) mem aw' out σ k' C' := by
  cases z with
  | false => exact safeContractSignatureCallFailure h (by omega) hret
  | true =>
    have h₁ := safeRuntime_block_8846_fallthrough (by simp; omega) (by decide) h
    have h₂ := safeRuntime_block_8859 (by simp only [safeRuntime_block_8846_fallthrough_stack, List.length_cons]; omega) h₁
    simp only [safeRuntime_block_8859_stack, safeRuntime_block_8846_fallthrough_stack, hl] at h₂
    by_cases hs : out.size = 32
    · rw [hs, show UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat 32) = ⟨1⟩ by decide] at h₂
      have h₃ := safeRuntime_block_8865_fallthrough (by simp; omega) (by decide) h₂
      have h₄ := safeRuntime_block_8872 (by simp; omega) (by jump_dest) h₃
      have hmagic : UInt256.shiftLeft (UInt256.ofNat 185818431) (UInt256.ofNat 225) =
          signatureMagicWord := by decide +kernel
      have hadd : UInt256.ofNat 32 + (ptr + UInt256.ofNat 32) =
          (ptr + UInt256.ofNat 32) + UInt256.ofNat 32 := u256_add_comm _ _
      simp only [safeRuntime_block_8872_stack, hl, hs, hmagic, hadd] at h₄
      obtain ⟨_, _, _, h₅⟩ := safeBytes32DecoderValid h₄ (by simp; omega)
        (by decide) (by decide) (by jump_dest)
      rw [hw hs] at h₅
      have h₆ := safeRuntime_block_8902 (by simp; omega) h₅
      obtain ⟨_, _, _, h₇⟩ := safeRuntime_block_8904_packed (by omega) hret h₆
      have heq : UInt256.eq (calldataWord out 0) signatureMagicWord =
          (contractSignatureResult true out).toUInt256 := by
        by_cases he : calldataWord out 0 = signatureMagicWord
        · simp only [contractSignatureResult, hs, he, decide_true, Bool.and_self,
            uInt256_eq_self]
          rfl
        · rw [u256_eq_of_ne he]
          simp only [contractSignatureResult, he, decide_false, Bool.and_false]
          rfl
      exact ⟨_, _, _, by simpa only [safeRuntime_block_8904_stack,
        safeRuntime_block_8902_stack, heq] using h₇⟩
    · have hn : UInt256.ofNat 32 ≠ UInt256.ofNat out.size := by
        intro he
        have hh := congrArg UInt256.toNat he
        rw [ulit_toNat' _ hb] at hh
        exact hs hh.symm
      rw [u256_eq_of_ne hn] at h₂
      have h₃ := safeRuntime_block_8865_taken (by simp; omega) (by decide) (by jump_dest) h₂
      obtain ⟨_, _, _, h₄⟩ := safeRuntime_block_8904_packed (by omega) hret h₃
      exact ⟨_, _, _, by simpa only [safeRuntime_block_8904_stack,
        contractSignatureResult, hs, decide_false, Bool.false_and, Bool.and_false] using h₄⟩

-- The caller enforces GS024 after the secured helper returns its Boolean.
theorem safeContractSignatureRequire {I g s0 σ k C aw mem out} {z : Bool}
    {d0 d1 d2 d3 d4 d5 ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7053⟩
      (z.toUInt256 :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: ret :: R) mem aw out σ k C)
    (hov : R.length + 13 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev fork safeBytecode g s0 ∧ z = false) ∨
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret R mem aw' out σ k' C' ∧ z = true := by
  cases z
  · have h₁ := safeRuntime_block_7053_fallthrough (by simp; omega) rfl h
    have h₂ := safeRuntime_block_7058 (by simp only [safeRuntime_block_7053_fallthrough_stack, List.length_cons]; omega) (by jump_dest) h₁
    exact Or.inl ⟨safeRuntime_block_6898 (by simp only [safeRuntime_block_7058_stack,
      safeRuntime_block_7053_fallthrough_stack, List.length_cons]; omega) h₂, rfl⟩
  · have h₁ := safeRuntime_block_7053_taken (by simp; omega) (by decide) (by jump_dest) h
    have h₂ := safeRuntime_block_7074 (by omega) hret h₁
    exact Or.inr ⟨_, _, _, h₂, rfl⟩

end Benchmarks.Safe.V3_77901a5
