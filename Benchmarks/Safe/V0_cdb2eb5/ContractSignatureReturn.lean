import Benchmarks.Safe.V0_cdb2eb5.PreModuleReturnMemory
import Benchmarks.Safe.V0_cdb2eb5.ContractSignatureSource
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_030
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

def signatureReturnMemory (mem : ByteArray) (ptr : Nat) (out : ByteArray) : ByteArray :=
  preModuleReturnMemory mem out (UInt256.ofNat ptr)

theorem safeContractSignatureCallFailure {I g s0 σ k C aw mem out} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7250⟩ (⟨0⟩ :: R) mem aw out σ k C)
    (hov : R.length + 4 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_7250_fallthrough (by omega) (by decide) h
  exact safeRuntime_block_7257 (by
    simp only [safeRuntime_block_7250_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeContractSignatureReturnBuffer {I g s0 σ k C aw mem ptr}
    {out : ByteArray} {a b c : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7250⟩ (⟨1⟩ :: a :: b :: c :: R)
      (preModuleOutputMemory mem out (UInt256.ofNat ptr)) aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hm : ptr + 32 ≤ mem.size) (hp : 96 ≤ ptr) (hptr : ptr < UInt256.size)
    (hb : out.size < 2 ^ 255) (hov : R.length + 8 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ contractSignatureDecoded true out = false) ∨
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7300⟩ (calldataWord out 0 :: R)
      (signatureReturnMemory mem ptr out) aw' out σ k' C' ∧
      contractSignatureDecoded true out = true := by
  have h₁ := safeRuntime_block_7250_taken (by simp; omega) (by decide) (by jump_dest) h
  have h₂ := safeRuntime_block_7264 (by simp; omega) (by jump_dest) h₁
  have hfree : memLoad (UInt256.ofNat 64)
      (preModuleOutputMemory mem out (UInt256.ofNat ptr)) = UInt256.ofNat ptr :=
    preModuleOutputFree hf (by rw [ulit_toNat' ptr hptr]; omega)
      (by rw [ulit_toNat' ptr hptr]; exact hp)
  simp only [safeRuntime_block_7264_stack, safeRuntime_block_7264_memory, hfree] at h₂
  change RD fork safeBytecode I g s0 _
    (UInt256.ofNat ptr :: (UInt256.ofNat ptr + UInt256.ofNat out.size) :: ⟨7300⟩ :: R)
    (signatureReturnMemory mem ptr out) _ out σ _ _ at h₂
  by_cases hl : 32 ≤ out.size
  · have hword : memLoad (UInt256.ofNat ptr) (signatureReturnMemory mem ptr out) =
        calldataWord out 0 := preModuleReturnWord
      (by rw [ulit_toNat' ptr hptr]; exact hm) (by rw [ulit_toNat' ptr hptr]; exact hp) hl
    by_cases hd : calldataWord out 0 = UInt256.land (calldataWord out 0) bytes4Mask
    · obtain ⟨aw', k', C', h₃⟩ := safeBytes4DecoderValid h₂ hov hl hb hword hd (by jump_dest)
      exact Or.inr ⟨aw', k', C', h₃, by
        simp only [contractSignatureDecoded, hl, decide_true, decide_eq_true hd, Bool.and_self]⟩
    · exact Or.inl ⟨safeBytes4DecoderNoncanon h₂ hov hl hb hword hd, by
        simp only [contractSignatureDecoded, hd, decide_false, Bool.and_false]⟩
  · exact Or.inl ⟨safeBytes4DecoderShort h₂ (by omega) (by omega), by
      simp only [contractSignatureDecoded, hl, decide_false, Bool.false_and, Bool.and_false]⟩

theorem safeContractSignatureFinish {I g s0 σ k C aw mem} {out : ByteArray}
    {d0 d1 d2 d3 d4 d5 ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7300⟩
      (calldataWord out 0 :: signatureMagicWord :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: ret :: R)
      mem aw out σ k C)
    (hd : contractSignatureDecoded true out = true) (hov : R.length + 13 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev fork safeBytecode g s0 ∧ contractSignatureResult true out = false) ∨
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret R mem aw' out σ k' C' ∧
      contractSignatureResult true out = true := by
  have hh : 32 ≤ out.size ∧ calldataWord out 0 = UInt256.land (calldataWord out 0) bytes4Mask := by
    simpa only [contractSignatureDecoded, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
      using hd
  have hclean : UInt256.land bytes4Mask (calldataWord out 0) = calldataWord out 0 := by
    rw [u256_land_comm]
    exact hh.2.symm
  by_cases hv : calldataWord out 0 = signatureMagicWord
  · have h₁ := safeRuntime_block_7300_taken (by simp; omega)
      (by change UInt256.eq (UInt256.land bytes4Mask (calldataWord out 0)) signatureMagicWord ≠ ⟨0⟩
          rw [hclean, hv, uInt256_eq_self]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_7332 (by omega) hret h₁
    exact Or.inr ⟨_, _, _, h₂, by
      simp only [contractSignatureResult, hh.1, hv, decide_true, Bool.and_self]⟩
  · have h₁ := safeRuntime_block_7300_fallthrough (by simp; omega)
      (by change UInt256.eq (UInt256.land bytes4Mask (calldataWord out 0)) signatureMagicWord = ⟨0⟩
          rw [hclean]
          exact uInt256_eq_zero_of_ne (fun he ↦ hv (uInt256_eq_one_eq he))) h
    simp only [safeRuntime_block_7300_fallthrough_stack] at h₁
    have h₂ := safeRuntime_block_7316 (by simp; omega) (by jump_dest) h₁
    refine Or.inl ⟨safeRuntime_block_6990 (by
      simp only [safeRuntime_block_7316_stack, safeRuntime_block_7300_fallthrough_stack,
        List.length_cons]; omega) h₂, ?_⟩
    simp only [contractSignatureResult, hv, decide_false, Bool.and_false]

end Benchmarks.Safe.V0_cdb2eb5
