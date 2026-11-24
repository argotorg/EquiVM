import Benchmarks.Safe.ViaIR.CalldataLengthRounding
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeIRAllocateValidTrace {I g s0 σ k C aw mem rdata ptr len}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7128⟩
      (UInt256.ofNat ptr :: UInt256.ofNat len :: ret :: R) mem aw rdata σ k C)
    (hlen : len + 31 < UInt256.size) (hb : ptr + ABI.paddedSize len < 2 ^ 64)
    (hov : R.length + 6 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret R
      (writeWord mem 64 (UInt256.ofNat (ptr + ABI.paddedSize len))) aw' rdata σ k' C' := by
  have hfit : ptr + ABI.paddedSize len < UInt256.size := lt_trans hb (by decide)
  have hadd : UInt256.ofNat ptr + UInt256.ofNat (ABI.paddedSize len) =
      UInt256.ofNat (ptr + ABI.paddedSize len) := wordOfNatAdd _ _ hfit
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hl : UInt256.lt (UInt256.ofNat (ptr + ABI.paddedSize len)) (UInt256.ofNat ptr) =
      ⟨0⟩ := ult_zero (by rw [ulit_toNat' _ hfit, ulit_toNat' _ (by omega)]; omega)
  have hg : UInt256.gt (UInt256.ofNat (ptr + ABI.paddedSize len))
      (UInt256.ofNat (2 ^ 64 - 1)) = ⟨0⟩ := ugt_zero (by
    rw [ulit_toNat' _ hfit, ulit_toNat' _ (by decide)]; omega)
  have h₁ := safeRuntime_block_7128_fallthrough (by simp; omega)
    (by rw [roundedCalldataLengthMask len hlen, hadd, hmax, hg, hl]; rfl) h
  simp only [safeRuntime_block_7128_fallthrough_stack,
    roundedCalldataLengthMask len hlen, hadd] at h₁
  exact safeRuntime_block_7157_packed (by simp; omega) hret h₁

theorem safeIRAllocateTrace {I g s0 σ k C aw mem rdata ptr len}
    {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7128⟩
      (UInt256.ofNat ptr :: UInt256.ofNat len :: ret :: R) mem aw rdata σ k C)
    (hlen : len + 31 < UInt256.size) (hb : ptr + ABI.paddedSize len < UInt256.size)
    (hov : R.length + 6 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨
      ∃ aw' k' C', ptr + ABI.paddedSize len < 2 ^ 64 ∧
        RD fork safeBytecode I g s0 ret R
          (writeWord mem 64 (UInt256.ofNat (ptr + ABI.paddedSize len))) aw' rdata σ k' C' := by
  have hadd : UInt256.ofNat ptr + UInt256.ofNat (ABI.paddedSize len) =
      UInt256.ofNat (ptr + ABI.paddedSize len) := wordOfNatAdd _ _ hb
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hl : UInt256.lt (UInt256.ofNat (ptr + ABI.paddedSize len)) (UInt256.ofNat ptr) =
      ⟨0⟩ := ult_zero (by rw [ulit_toNat' _ hb, ulit_toNat' _ (by omega)]; omega)
  by_cases ha : ptr + ABI.paddedSize len < 2 ^ 64
  swap
  · have hg : UInt256.gt (UInt256.ofNat (ptr + ABI.paddedSize len))
        (UInt256.ofNat (2 ^ 64 - 1)) = ⟨1⟩ := ugt_one (by
      rw [ulit_toNat' _ hb, ulit_toNat' _ (by decide)]; omega)
    have h₁ := safeRuntime_block_7128_taken (by simp; omega)
      (by rw [roundedCalldataLengthMask len hlen, hadd, hmax, hg, hl]; decide)
      (by jump_dest) h
    exact .inl (safeRuntime_block_7161 (by
      simp only [safeRuntime_block_7128_taken_stack, List.length_cons]; omega) h₁)
  obtain ⟨aw', k', C', h₂⟩ := safeIRAllocateValidTrace h hlen ha hov hret
  exact .inr ⟨aw', k', C', ha, h₂⟩

end Benchmarks.Safe.ViaIR
