import Benchmarks.Safe.ViaIR.Common
import Reasoning.WordArithmetic
import Benchmarks.Safe.ViaIR.Blocks.Runtime_022
import Benchmarks.Safe.ViaIR.Blocks.Runtime_026

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

-- The IR pipeline inlines checked subtraction in execTransaction's gas-used calculation.
theorem safeSubtractTrace {I g s0 σ k C aw mem rdata}
    {a b x0 x1 x2 x3 x4 x5 ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4719⟩
      (b :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: a :: ptr :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hle : b.toNat ≤ a.toNat) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨4728⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: UInt256.sub a b :: ptr :: R)
      mem aw rdata σ k' C' := by
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    ugt_zero (by rw [usub_toNat hle]; omega)
  exact ⟨_, _, safeRuntime_block_4719_fallthrough (by simp; omega) hgt h⟩

theorem safeSubtractUnderflow {I g s0 σ k C aw mem rdata}
    {a b x0 x1 x2 x3 x4 x5 ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4719⟩
      (b :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: a :: ptr :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hlt : a.toNat < b.toNat) : RDrev fork safeBytecode g s0 := by
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    apply ugt_one
    rw [usub_toNat_underflow hlt]
    have := b.val.isLt
    change b.toNat < UInt256.size at this
    omega
  have h₁ := safeRuntime_block_4719_taken (by simp; omega)
    (by rw [hgt]; decide) (by jump_dest) h
  exact safeRuntime_block_5301 hov h₁

theorem safeSubtractZeroOne {I g s0 σ k C aw mem rdata}
    {x0 x1 x2 x3 x4 x5 ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4719⟩
      (⟨1⟩ :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: ⟨0⟩ :: ptr :: R)
      mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) : RDrev fork safeBytecode g s0 :=
  safeSubtractUnderflow h hov (by decide)

end Benchmarks.Safe.ViaIR
