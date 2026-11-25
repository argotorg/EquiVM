import Benchmarks.Midnight.TakeAuthorizationRead
import Benchmarks.Midnight.RuntimeBlocks_042

variable {fork : Ethereum.Fork}

/-! Take's caller-or-delegate guard after saving its callback-data pointer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeAuthorization {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw user takerPtr : UInt256}
    {k C : Nat} {R : List UInt256} (evm : EVM.State) (henv : evm.executionEnv = I)
    (hstack : R.length + 6 ≤ 1024) (hmem : 576 ≤ mem.size)
    (huser : memLoad (UInt256.ofNat 544) mem = user)
    (hcanon : user.toNat < EVM.addressModulus) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10925⟩ (takerPtr :: R)
      mem aw rdata evm.accountMap k C) :
    (¬ onBehalfAllowed evm user ∧ RDrev fork midnightBytecode g s0) ∨
    (onBehalfAllowed evm user ∧ ∃ mem' aw' k' C',
      MemoryPrefix (writeWord mem 320 takerPtr) mem' mem.size ∧ mem'.size = mem.size ∧
      memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
      MemoryFunding credit mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨10957⟩ R mem' aw' rdata evm.accountMap k' C') := by
  let base := writeWord mem 320 takerPtr
  have hbsize : base.size = mem.size := by rw [writeWord_sparse_size]; omega
  have hbuser : memLoad (UInt256.ofNat 544) base = user := by
    rw [memLoad_writeWord_preserved _ 320 (UInt256.ofNat 544) _ hmem (Or.inr (by decide)), huser]
  have hbfree : memLoad (UInt256.ofNat 64) base = memLoad (UInt256.ofNat 64) mem :=
    memLoad_writeWord_preserved _ 320 (UInt256.ofNat 64) _
      (by change 96 ≤ mem.size; omega) (Or.inl (by decide))
  have finish {mem' aw' k' C' check}
      (hp : MemoryPrefix base mem' mem.size) (hs : mem'.size = mem.size)
      (hf : memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem)
      (ha' : MemoryFunding credit mem' aw' C')
      (hc : check ≠ ⟨0⟩ ↔ onBehalfAllowed evm user)
      (rd' : RD fork midnightBytecode I g s0 ⟨10951⟩ (check :: R)
        mem' aw' rdata evm.accountMap k' C') :
      (¬ onBehalfAllowed evm user ∧ RDrev fork midnightBytecode g s0) ∨
      (onBehalfAllowed evm user ∧ ∃ mem' aw' k' C',
        MemoryPrefix base mem' mem.size ∧ mem'.size = mem.size ∧
        memLoad (UInt256.ofNat 64) mem' = memLoad (UInt256.ofNat 64) mem ∧
        MemoryFunding credit mem' aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨10957⟩ R mem' aw' rdata evm.accountMap k' C') := by
    by_cases hz : check = ⟨0⟩
    · have rr := midnightBlocks.midnight_block_10951_taken (by omega)
        (by rw [hz]; decide) (by jump_dest) rd'
      exact Or.inl ⟨fun h ↦ (hc.mpr h) hz,
        midnightBlocks.midnight_block_15013 (by
          change R.length + 2 ≤ 1024; omega) rr⟩
    · have rr := midnightBlocks.midnight_block_10951_fallthrough (by omega)
        (isZero_eq_zero_of_ne hz) rd'
      exact Or.inr ⟨hc.mp hz, _, _, _, _, hp, hs, hf, by memory_fund ha', rr⟩
  have hload : memLoad (UInt256.ofNat 544)
      (takerPtr.toByteArray.write 0 mem (UInt256.ofNat 320).toNat 32) = user := hbuser
  by_cases hself : user = solcSourceWord I
  · have heq : UInt256.eq user (solcSourceWord I) = ⟨1⟩ := by
      rw [hself, uInt256_eq_self]
    have rd1 := midnightBlocks.midnight_block_10925_fallthrough (by omega) (by
      rw [hload, addressMask_computed, solcAddrMask_clean hcanon]
      change UInt256.isZero (UInt256.eq user (solcSourceWord I)) = _
      rw [heq]; rfl) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by
      unfold midnightBlocks.midnight_block_10925_fallthrough_memory
      memory_fund ha)
    simp only [midnightBlocks.midnight_block_10925_fallthrough_stack, hload,
      addressMask_computed, solcAddrMask_clean hcanon] at rd1
    apply finish (MemoryPrefix.refl _ _) hbsize hbfree ha1 _ rd1
    change UInt256.eq user (solcSourceWord I) ≠ ⟨0⟩ ↔ _
    simp only [onBehalfAllowed, henv, hself, true_or, uInt256_eq_self]
    decide
  · have heq : UInt256.eq user (solcSourceWord I) = ⟨0⟩ := u256_eq_of_ne hself
    have rd1 := midnightBlocks.midnight_block_10925_taken (by omega) (by
      rw [hload, addressMask_computed, solcAddrMask_clean hcanon]
      change UInt256.isZero (UInt256.eq user (solcSourceWord I)) ≠ _
      rw [heq]; decide) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by
      unfold midnightBlocks.midnight_block_10925_taken_memory
      memory_fund ha)
    simp only [midnightBlocks.midnight_block_10925_taken_stack, hload,
      addressMask_computed, solcAddrMask_clean hcanon] at rd1
    obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakeAuthorizationRead_funded (by omega)
      (by change 64 ≤ base.size; rw [hbsize]; omega) hbuser hcanon ha1 rd1
    have hs1 : (twoWordHashMem user ⟨3⟩ base).size = base.size :=
      twoWordHashMem_size_of_ge_64 _ _ (by rw [hbsize]; omega)
    apply finish ((twoWordHashMem_prefix base user ⟨3⟩ mem.size).trans
      (twoWordHashMem_prefix _ _ _ mem.size))
      ((supplyAuthorizationMemory_size base I user (by rw [hbsize]; omega)).trans hbsize)
      ?_ ha2 ?_ rd2
    · change memLoad (UInt256.ofNat 64) (supplyAuthorizationMemory base I user) = _
      rw [supplyAuthorizationMemory, memLoad_twoWordHashMem _ _ _ (by decide)
        (by change 96 ≤ _; rw [hs1, hbsize]; omega),
        memLoad_twoWordHashMem user ⟨3⟩ (UInt256.ofNat 64) (by decide)
          (by change 96 ≤ base.size; rw [hbsize]; omega), hbfree]
    · simp only [onBehalfAllowed, henv, hself, false_or, authorizationWord, henv]
      rfl

end Benchmarks.Midnight
