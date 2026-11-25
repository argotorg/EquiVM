import Benchmarks.Midnight.CheckedArithmetic

variable {fork : Ethereum.Fork}

/-! Checked subtraction retains previously paid execution costs. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightCheckedSub_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hle : b.toNat ≤ a.toNat)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨19447⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    ugt_zero (by rw [usub_toNat hle]; omega)
  have rd1 := midnightBlocks.midnight_block_19447_fallthrough hstack hc rd
  simp only [midnightBlocks.midnight_block_19447_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_19459 (by simp; omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

end Benchmarks.Midnight
