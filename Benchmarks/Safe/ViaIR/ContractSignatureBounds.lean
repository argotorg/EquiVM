import Benchmarks.Safe.ViaIR.ContractSignatureCheckSource
import Benchmarks.Safe.ViaIR.BytesMemory
import Benchmarks.Safe.ViaIR.SafeAddTrace
import Benchmarks.Safe.ViaIR.Blocks.Runtime_037
import Benchmarks.Safe.ViaIR.Blocks.Runtime_038

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

open ContractSignatureInput

set_option maxRecDepth 2000

theorem safeCheckContractBounds (p : ContractSignatureInput)
    {I g s0 σ k C aw mem rdata src} {last owner : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7635⟩
      (p.offset :: last :: owner :: UInt256.ofNat src :: p.hash :: R) mem aw rdata σ k C)
    (hm : BytesMemory mem src p.signatures)
    (hb : src + 64 + p.signatures.size < UInt256.size) (hov : R.length + 20 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬(p.start ≤ p.signatures.size ∧ p.finish ≤ p.signatures.size)) ∨
      ∃ aw' k' C', p.start ≤ p.signatures.size ∧ p.finish ≤ p.signatures.size ∧
        RD fork safeBytecode I g s0 ⟨7707⟩
          (UInt256.ofNat (src + 32 + p.offset.toNat) :: last :: owner ::
            UInt256.ofNat src :: p.hash :: R)
          mem aw' rdata σ k' C' := by
  have hlen := hm.length
  have h₁ := safeRuntime_block_7635 (by simp; omega) (by jump_dest) h
  by_cases hsfit : p.start < UInt256.size
  swap
  · exact Or.inl ⟨safeAdd32Overflow h₁ (Nat.le_of_not_gt hsfit) (by simp; omega), by omega⟩
  obtain ⟨_, _, h₂⟩ := safeAdd32Trace h₁ hsfit (by simp; omega) (by jump_dest)
  have hstart : (p.offset + UInt256.ofNat 32).toNat = p.start :=
    addWord_toNat _ _ hsfit
  have hn : (UInt256.ofNat p.signatures.size).toNat = p.signatures.size :=
    ulit_toNat' _ (by omega)
  have hle : UInt256.lt (p.offset + UInt256.ofNat 32) p.offset = ⟨0⟩ :=
    ult_zero (by rw [hstart]; dsimp [start]; omega)
  have h₂' := safeRuntime_block_7643_fallthrough (by simp; omega) hle h₂
  by_cases hs : p.start ≤ p.signatures.size
  swap
  · have hcond : UInt256.lt (memLoad (UInt256.ofNat src) mem)
        (p.offset + UInt256.ofNat 32) = ⟨1⟩ := ult_one (by rw [hlen, hstart, hn]; omega)
    have h₃ := safeRuntime_block_7651_taken (by simp; omega)
      (by rw [hcond]; decide) (by jump_dest) h₂'
    exact Or.inl ⟨safeRuntime_block_8078 (by
      simp only [safeRuntime_block_7651_taken_stack, List.length_cons]; omega) h₃, by omega⟩
  have hcond : UInt256.lt (memLoad (UInt256.ofNat src) mem)
      (p.offset + UInt256.ofNat 32) = ⟨0⟩ := ult_zero (by rw [hlen, hstart, hn]; exact hs)
  have h₃ := safeRuntime_block_7651_fallthrough (by simp; omega) hcond h₂'
  have haddr : (UInt256.ofNat src + p.offset) + UInt256.ofNat 32 =
      UInt256.ofNat (src + 32 + p.offset.toNat) := by
    apply u256_inj
    change ((src % UInt256.size + p.offset.toNat) % UInt256.size + 32) % UInt256.size =
      (src + 32 + p.offset.toNat) % UInt256.size
    have hs' : p.offset.toNat + 32 ≤ p.signatures.size := hs
    rw [Nat.mod_eq_of_lt (by omega : src < UInt256.size),
      Nat.mod_eq_of_lt (by omega : src + p.offset.toNat < UInt256.size)]
    congr 1
    omega
  have hread : memLoad ((UInt256.ofNat src + p.offset) + UInt256.ofNat 32) mem = p.len := by
    rw [haddr]
    exact hm.word hs (by have hs' : p.offset.toNat + 32 ≤ p.signatures.size := hs; omega)
  have h₄ := safeRuntime_block_7658 (by simp; omega) (by jump_dest) h₃
  simp only [safeRuntime_block_7658_stack] at h₄
  rw [hread, haddr] at h₄
  obtain ⟨_, _, h₅⟩ := safeAdd32Trace h₄ hsfit (by simp; omega) (by jump_dest)
  have h₅' := safeRuntime_block_7675_fallthrough (by simp; omega) hle h₅
  have h₆ := safeRuntime_block_7683 (by simp; omega) (by jump_dest) h₅'
  by_cases hefit : p.finish < UInt256.size
  swap
  · exact Or.inl ⟨safeAddOverflow h₆ (by rw [hstart]; exact Nat.le_of_not_gt hefit)
      (by simp; omega), by omega⟩
  obtain ⟨_, _, h₇⟩ := safeAddTrace h₆ (by rw [hstart]; exact hefit)
    (by simp; omega) (by jump_dest)
  have hend : (p.offset + UInt256.ofNat 32 + p.len).toNat = p.finish := by
    have he := addWord_toNat (p.offset + UInt256.ofNat 32) p.len
      (by rw [hstart]; exact hefit)
    simpa only [hstart] using he
  have hle' : UInt256.lt (p.offset + UInt256.ofNat 32 + p.len)
      (p.offset + UInt256.ofNat 32) = ⟨0⟩ :=
    ult_zero (by rw [hend, hstart]; dsimp [finish]; omega)
  have h₇' := safeRuntime_block_7692_fallthrough (by simp; omega) hle' h₇
  by_cases he : p.finish ≤ p.signatures.size
  · have hcond : UInt256.lt (memLoad (UInt256.ofNat src) mem)
        (p.offset + UInt256.ofNat 32 + p.len) = ⟨0⟩ :=
      ult_zero (by rw [hlen, hend, hn]; exact he)
    have h₈ := safeRuntime_block_7700_fallthrough (by simp; omega) hcond h₇'
    exact Or.inr ⟨_, _, _, hs, he, h₈⟩
  · have hcond : UInt256.lt (memLoad (UInt256.ofNat src) mem)
        (p.offset + UInt256.ofNat 32 + p.len) = ⟨1⟩ :=
      ult_one (by rw [hlen, hend, hn]; omega)
    have h₈ := safeRuntime_block_7700_taken (by simp; omega)
      (by rw [hcond]; decide) (by jump_dest) h₇'
    exact Or.inl ⟨safeRuntime_block_8033 (by
      simp only [safeRuntime_block_7700_taken_stack, List.length_cons]; omega) h₈, by omega⟩

end Benchmarks.Safe.ViaIR
