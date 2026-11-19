import Benchmarks.Midnight.AllocationFunding
import Benchmarks.Midnight.AllocationArithmetic
import Benchmarks.Midnight.BoolMemoryDecode
import Benchmarks.Midnight.RuntimeBlocks_033

/-! Shared allocation and decoding of a fixed Boolean reply. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 10000

theorem midnightBoolReplyShort {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hshort : out.size < 32) (hroot : root.toNat + 32 < 2^64)
    (rd : RD midnightBytecode I g s0 ⟨8404⟩ (UInt256.ofNat 32 :: root :: ret :: R)
      mem aw out σ k C) : RDrev midnightBytecode g s0 := by
  have hn : (UInt256.ofNat out.size).toNat = out.size :=
    UInt256.toNat_ofNat_of_lt (by change out.size < 2^256; omega)
  have rd1 := midnight_block_8404 (by simp only [List.length_cons]; omega) (by jump_dest) rd
  have rd2 := midnight_block_8380 (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := midnightAllocate
    (by simp only [List.length_cons]; omega)
    (allocationCheck_bounded (by rw [hn]; change _ < 2^256; omega)
      (by rw [hn]; omega)) (by jump_dest) rd2
  have rd4 := midnight_block_8390 (by simp only [List.length_cons]; omega) (by jump_dest) rd3
  apply midnightBoolMemory_short (by simp only [List.length_cons]; omega) ?_ rd4
  rw [word_add_sub_left]
  have hlo : ¬ (UInt256.ofNat out.size).toNat ≥ 2^255 := by rw [hn]; omega
  simp only [UInt256.slt, UInt256.sltBool, hlo, if_false,
    show ¬ (UInt256.ofNat 32).toNat ≥ 2^255 from by decide]
  have hl : UInt256.ofNat out.size < UInt256.ofNat 32 := by
    change (UInt256.ofNat out.size).toNat < 32
    rw [hn]
    exact hshort
  rw [decide_eq_true hl]
  decide

theorem midnightBoolReplyFull {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw root ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hroot : root.toNat + 32 < 2^64)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hword : memLoad root (writeWord mem 64 (root + UInt256.ofNat 32)) = calldataWord out 0)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18444⟩
      (root :: UInt256.ofNat 32 :: UInt256.ofNat 8390 :: UInt256.ofNat 32 :: root :: ret :: R)
      mem aw out σ k C) :
    (¬ (calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) ∧
      RDrev midnightBytecode g s0) ∨
    ((calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩) ∧ ∃ aw' k' C',
      MemoryFunding credit (writeWord mem 64 (root + UInt256.ofNat 32)) aw' C' ∧
      RD midnightBytecode I g s0 ret (calldataWord out 0 :: R)
        (writeWord mem 64 (root + UInt256.ofNat 32)) aw' out σ k' C') := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightAllocate_funded
    (by simp only [List.length_cons]; omega)
    (allocationCheck_bounded (by decide) hroot) (by jump_dest) ha rd
  have he : allocationEnd root (UInt256.ofNat 32) = root + UInt256.ofNat 32 := rfl
  rw [he] at rd1 ha1
  have rd2 := midnight_block_8390 (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
  have hlen : UInt256.slt (UInt256.sub (root + UInt256.ofNat 32) root) ⟨32⟩ = ⟨0⟩ := by
    rw [word_add_sub_left]
    decide
  by_cases hc : calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩
  · obtain ⟨aw3, k3, C3, hc3, rd3⟩ := midnightBoolMemory_cleanCharge
      (by omega) hlen (by rw [hword]; exact hc) hret rd2
    rw [hword] at rd3
    refine Or.inr ⟨hc, aw3, k3, C3, ?_, rd3⟩
    simpa only [Nat.add_zero] using
      hc3.funding ha2 (ha2.covered.mono hc3.active_le)
  · exact Or.inl ⟨hc, midnightBoolMemory_dirty
      (by simp only [List.length_cons]; omega) hlen (by rw [hword]; exact hc) rd2⟩

end Benchmarks.Midnight
