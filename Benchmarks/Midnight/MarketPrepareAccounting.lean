import Benchmarks.Midnight.MarketFirstFieldsAccounting
import Benchmarks.Midnight.AllocationAccounting
import Benchmarks.Midnight.AllocationArithmetic

/-! Allocating a market record and copying its first calldata fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketCalldataPrepare_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head ret finish : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 15 ≤ 1024)
    (hhead : head.toNat + 256 < UInt256.size) (hptr : ptr.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18589⟩ (head :: ret :: finish :: R)
      mem aw rdata σ k C) :
    (¬ ptr.toNat + 256 < 2^64 ∧ RDrev midnightBytecode g s0) ∨
    (decodeMarketData I.calldata head.toNat = none ∧ RDrev midnightBytecode g s0) ∨
    (ptr.toNat + 256 < 2^64 ∧
      (calldataWord I.calldata (head.toNat + 32)).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata (head.toNat + 64)).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata (head.toNat + 96)).toNat < 2^64 ∧ ∃ aw' k' C',
      MemoryAccounting
        (marketFirstMemory (writeWord mem 64 (ptr + UInt256.ofNat 256)) ptr I.calldata head.toNat)
        aw' C' ∧
      RD midnightBytecode I g s0 ⟨18661⟩
        (calldataWord I.calldata (head.toNat + 96) :: finish :: head :: ptr :: ret :: ptr :: R)
        (marketFirstMemory (writeWord mem 64 (ptr + UInt256.ofNat 256)) ptr I.calldata head.toNat)
        aw' rdata σ k' C') := by
  have hp : (ptr + UInt256.ofNat 256).toNat = ptr.toNat + 256 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have rd1 := midnightBlocks.midnight_block_18589 (by
    simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_18589_stack, hfree] at rd1
  have ha1 := memoryAccountingAt rd1 (by memory_account ha)
  by_cases hfit : ptr.toNat + 256 < 2^64
  · obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightAllocate256_accounted
      (by simp only [List.length_cons]; omega)
      (allocationCheck_ok (by rw [hp]; exact hfit) (by rw [hp]; omega)) (by jump_dest) ha1 rd1
    rcases midnightMarketCalldataFirstFields_accounted (by omega) hhead
        (by change _ < 2^256; omega) ha2 rd2 with
      ⟨hnone, hr⟩ | ⟨hm, hl, hoff, aw3, k3, C3, ha3, rd3⟩
    · exact Or.inr (Or.inl ⟨hnone, hr⟩)
    · exact Or.inr (Or.inr ⟨hfit, hm, hl, hoff, aw3, k3, C3, ha3, rd3⟩)
  · left
    refine ⟨hfit, midnightAllocate256Revert (by simp only [List.length_cons]; omega) ?_ rd1⟩
    exact allocationCheck_large (by rw [hp]; omega) (by rw [hp]; omega)

end Benchmarks.Midnight
