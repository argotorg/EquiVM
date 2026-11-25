import Benchmarks.Midnight.CheckedArithmetic

variable {fork : Ethereum.Fork}

/-! Checked multiplication preserves the accumulated execution cost. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightCheckedMul_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hno : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨20413⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ret (UInt256.mul a b :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_20413_fallthrough hstack (checkedMulGuard hno) rd
  simp only [midnightBlocks.midnight_block_20413_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_20431 (by simp; omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

end Benchmarks.Midnight
