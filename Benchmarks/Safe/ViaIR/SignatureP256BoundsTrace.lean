import Benchmarks.Safe.ViaIR.SignatureP256BoundsSource
import Benchmarks.Safe.ViaIR.BytesMemory
import Benchmarks.Safe.ViaIR.SafeMulTrace
import Benchmarks.Safe.ViaIR.Blocks.Runtime_038
import Benchmarks.Safe.ViaIR.Blocks.Runtime_039
import Benchmarks.Safe.ViaIR.Blocks.Runtime_040
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeSignatureP256Bounds (p : SignatureInput)
    {I g s0 σ k C aw mem rdata src} {i s r v hash executor last : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8265⟩
      (v :: r :: last :: s :: UInt256.ofNat src :: hash :: i :: executor :: p.required :: R)
      mem aw rdata σ k C)
    (hm : BytesMemory mem src p.signatures) (hn : p.signatures.size < UInt256.size)
    (hreq : p.requiredBytes ≤ p.signatures.size) (hov : R.length + 21 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ¬(p.requiredBytes ≤ s.toNat ∧ s.toNat + 128 ≤ p.signatures.size)) ∨
    ∃ aw' k' C', p.requiredBytes ≤ s.toNat ∧ s.toNat + 128 ≤ p.signatures.size ∧
      RD fork safeBytecode I g s0 ⟨8316⟩
        (s :: last :: UInt256.land solcAddrMask r :: UInt256.ofNat src :: hash ::
          i :: executor :: p.required :: R)
        mem aw' rdata σ k' C' := by
  have hfit : p.requiredBytes < UInt256.size := lt_of_le_of_lt hreq hn
  have hmul : (UInt256.mul p.required (UInt256.ofNat 65)).toNat = p.requiredBytes := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hfit
  have h₁ := safeRuntime_block_8265 (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, h₂⟩ := safeMul65Trace h₁ hfit (by simp; omega) (by jump_dest)
  by_cases hl : p.requiredBytes ≤ s.toNat
  swap
  · have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨1⟩ :=
      ult_one (by rw [hmul]; omega)
    have h₃ := safeRuntime_block_8284_taken (by simp; omega)
      (by rw [hlt]; decide) (by jump_dest) h₂
    have h₄ := safeRuntime_block_8123 (by
      simp only [safeRuntime_block_8284_taken_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact .inl ⟨safeRuntime_block_9682 (by
      simp only [safeRuntime_block_8284_taken_stack, List.length_cons]; omega) h₄,
      fun hh ↦ hl hh.1⟩
  have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨0⟩ :=
    ult_zero (by rw [hmul]; exact hl)
  have h₃ := safeRuntime_block_8284_fallthrough (by simp; omega) hlt h₂
  by_cases hb : s.toNat + 128 < UInt256.size
  swap
  · have hg : UInt256.gt s (s + UInt256.ofNat 128) = ⟨1⟩ := by
      rw [u256_add_comm s]
      exact checkedAddOverflowGt s (UInt256.ofNat 128) (by
        change UInt256.size ≤ s.toNat + 128; omega)
    have h₄ := safeRuntime_block_8291_taken (by simp; omega)
      (by rw [hg]; decide) (by jump_dest) h₃
    exact .inl ⟨safeRuntime_block_7511 (by
      simp [safeRuntime_block_8291_taken_stack]; omega) h₄, fun hh ↦ hb (by omega)⟩
  have hg : UInt256.gt s (s + UInt256.ofNat 128) = ⟨0⟩ := by
    rw [u256_add_comm s]
    exact checkedAddNoOverflowGt s (UInt256.ofNat 128) hb
  have h₄ := safeRuntime_block_8291_fallthrough (by simp; omega) hg h₃
  have hsum : (s + UInt256.ofNat 128).toNat = s.toNat + 128 := addWord_toNat _ _ hb
  have hle : UInt256.lt (s + UInt256.ofNat 128) s = ⟨0⟩ :=
    ult_zero (by rw [hsum]; omega)
  have h₅ := safeRuntime_block_8302_fallthrough (by simp; omega) hle h₄
  by_cases hh : s.toNat + 128 ≤ p.signatures.size
  · have hlt : UInt256.lt (memLoad (UInt256.ofNat src) mem) (s + UInt256.ofNat 128) =
        ⟨0⟩ := ult_zero (by rw [hm.length, ulit_toNat' _ hn, hsum]; exact hh)
    obtain ⟨aw', k', C', h₆⟩ := safeRuntime_block_8309_fallthrough_packed
      (by simp; omega) hlt h₅
    refine .inr ⟨aw', k', C', hl, hh, ?_⟩
    simpa only [safeRuntime_block_8309_fallthrough_stack, safeAddressMask] using h₆
  · have hlt : UInt256.lt (memLoad (UInt256.ofNat src) mem) (s + UInt256.ofNat 128) =
        ⟨1⟩ := ult_one (by rw [hm.length, ulit_toNat' _ hn, hsum]; omega)
    have h₆ := safeRuntime_block_8309_taken (by simp; omega)
      (by rw [hlt]; decide) (by jump_dest) h₅
    exact .inl ⟨safeRuntime_block_8481 (by
      simp [safeRuntime_block_8309_taken_stack]; omega) h₆, fun hbad ↦ hh hbad.2⟩

end Benchmarks.Safe.ViaIR
