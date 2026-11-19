import Benchmarks.Midnight.Common
import Benchmarks.Midnight.RuntimeBlocks_029
import Benchmarks.Midnight.RuntimeBlocks_073
import Benchmarks.Midnight.RuntimeBlocks_074
import Benchmarks.Midnight.RuntimeBlocks_077

/-! Midnight's checked arithmetic routines, with arbitrary stack tails and return PCs. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: Solidity's checked multiplication guard on a bounded product.
theorem checkedMulGuard {a b : UInt256} (hno : a.toNat * b.toNat < UInt256.size) :
    UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul a b) a) b)
      (UInt256.isZero a)) = ⟨0⟩ := by
  by_cases hz : a = ⟨0⟩
  · rw [hz, show UInt256.isZero ⟨0⟩ = ⟨1⟩ from rfl, u256_lor_comm]
    exact isZero_eq_zero_of_ne (u256_lor_one_ne_zero _)
  · rw [mulDiv_cancel hz hno, uInt256_eq_self]
    exact isZero_eq_zero_of_ne (u256_lor_one_ne_zero _)

theorem checkedMulGuardInline {a b : UInt256} (hno : a.toNat * b.toNat < UInt256.size) :
    UInt256.isZero (UInt256.lor (UInt256.isZero a)
      (UInt256.eq b (UInt256.div (UInt256.mul a b) a))) = ⟨0⟩ := by
  rw [u256_lor_comm, uInt256_eq_comm b]
  exact checkedMulGuard hno

theorem midnightCheckedSub {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hle : b.toNat ≤ a.toNat)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19447⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    ugt_zero (by rw [usub_toNat hle]; omega)
  have rd1 := midnightBlocks.midnight_block_19447_fallthrough hstack hc rd
  simp only [midnightBlocks.midnight_block_19447_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_19459 (by simp; omega) hret rd1
  exact ⟨_, _, rd2⟩

theorem midnightCheckedSubRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hlt : a.toNat < b.toNat)
    (rd : RD midnightBytecode I g s0 ⟨19447⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have hc : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    apply ugt_one
    rw [usub_toNat_underflow hlt]
    have hb := b.val.isLt
    change b.toNat < UInt256.size at hb
    omega
  have rd1 := midnightBlocks.midnight_block_19447_taken hstack
    (by rw [hc]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_7302
    (by simp only [midnightBlocks.midnight_block_19447_taken_stack, List.length_cons]; omega) rd1

theorem midnightCheckedAdd {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hno : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19536⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hn : (a + b).toNat = a.toNat + b.toNat := addWord_toNat a b hno
  have hc : UInt256.gt a (a + b) = ⟨0⟩ := ugt_zero (by rw [hn]; omega)
  have rd1 := midnightBlocks.midnight_block_19536_fallthrough hstack hc rd
  simp only [midnightBlocks.midnight_block_19536_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_19548 (by simp; omega) hret rd1
  exact ⟨_, _, rd2⟩

theorem midnightCheckedMul {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hno : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20413⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret (UInt256.mul a b :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_20413_fallthrough hstack (checkedMulGuard hno) rd
  simp only [midnightBlocks.midnight_block_20413_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_20431 (by simp; omega) hret rd1
  exact ⟨_, _, rd2⟩

theorem midnightCheckedDiv {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hnz : b ≠ ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19391⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret (UInt256.div a b :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19391_fallthrough
    (by simp; omega) (isZero_eq_zero_of_ne hnz) rd
  have rd2 := midnightBlocks.midnight_block_19398 (by omega) hret rd1
  exact ⟨_, _, rd2⟩

end Benchmarks.Midnight
