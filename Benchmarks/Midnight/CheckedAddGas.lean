import Benchmarks.Midnight.CheckedArithmeticRevert

variable {fork : Ethereum.Fork}

/-! The checked addition helper retains cumulative gas. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCheckedAdd_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hno : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨19536⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hn : (a + b).toNat = a.toNat + b.toNat := addWord_toNat a b hno
  have hc : UInt256.gt a (a + b) = ⟨0⟩ := ugt_zero (by rw [hn]; omega)
  have rd1 := midnightBlocks.midnight_block_19536_fallthrough hstack hc rd
  simp only [midnightBlocks.midnight_block_19536_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_19548 (by simp; omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

end Benchmarks.Midnight
