import Benchmarks.Safe.ViaIR.CheckedSubtract

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

-- SafeMath.sub is inlined after the IR bytecode reads the remaining gas.
set_option maxRecDepth 100000

theorem safeSubTrace {I g s0 σ k C aw mem rdata}
    {a x0 x1 x2 x3 x4 x5 ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4710⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: a :: ptr :: R) mem aw rdata σ k C)
    (hle : (g.subNat (C + 1 + 2)).toUInt256.toNat ≤ a.toNat)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨4728⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 ::
        UInt256.sub a (g.subNat (C + 1 + 2)).toUInt256 :: ptr :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_4710_fallthrough (by simp; omega) (ugt_zero hle) h
  exact safeSubtractTrace h₁ (by omega) hle

theorem safeSubUnderflow {I g s0 σ k C aw mem rdata}
    {a x0 x1 x2 x3 x4 x5 ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4710⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: a :: ptr :: R) mem aw rdata σ k C)
    (hlt : a.toNat < (g.subNat (C + 1 + 2)).toUInt256.toNat)
    (hov : R.length + 11 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_4710_taken (by simp; omega)
    (by rw [ugt_one hlt]; decide) (by jump_dest) h
  exact safeRuntime_block_5321 hov h₁

end Benchmarks.Safe.ViaIR
