import Benchmarks.Midnight.LiquidatePositionMemory
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.RuntimeBlocks_022

/-! Normalized memory and stack for the liquidation position lookup. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem liquidatePositionBlock_normalize {ee : ExecutionEnv} {mem : ByteArray}
    {id borrower dl dp : UInt256} {R : List UInt256}
    (hm : 832 ≤ mem.size) (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hc : borrower.toNat < EVM.addressModulus) :
    midnight_block_5161_fallthrough_memory (mem := mem) (x0 := id) (x2 := borrower) =
      liquidatePositionMemory mem id borrower ∧
    midnight_block_5161_fallthrough_stack (ee := ee) (mem := mem)
      (x0 := id) (x1 := dl) (x2 := borrower) (x3 := dp) (R := R) =
      [UInt256.isZero (calldataWord ee.calldata 100),
        UInt256.isZero (UInt256.isZero (calldataWord ee.calldata 100)),
        positionSlot id borrower, dp, dl, borrower,
        UInt256.isZero (calldataWord ee.calldata 100)] ++ R := by
  have hs1 : 832 ≤ (liquidateIdMemory mem id).size := by
    rw [liquidateIdMemory_size id hm]; exact hm
  have hs2 : 832 ≤ (twoWordHashMem id ⟨1⟩ (liquidateIdMemory mem id)).size := by
    rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hs1
  have hs3 : 832 ≤ (liquidateMarketMemory mem id).size := by
    rw [liquidateMarketMemory_size id hm]; exact hm
  have hs4 : 832 ≤ (twoWordHashMem id ⟨0⟩ (liquidateMarketMemory mem id)).size := by
    rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hs3
  have hz1 : memLoad (UInt256.ofNat 800) (liquidateIdMemory mem id) = ⟨0⟩ := by
    rw [liquidateIdMemory_load _ (UInt256.ofNat 800) hm (Or.inr (by decide)), hz]
  have hz2 : memLoad (UInt256.ofNat 800)
      (twoWordHashMem id ⟨1⟩ (liquidateIdMemory mem id)) = ⟨0⟩ := by
    rw [memLoad_twoWordHashMem _ _ (UInt256.ofNat 800) (by decide) hs1, hz1]
  have hz3 : memLoad (UInt256.ofNat 800) (liquidateMarketMemory mem id) = ⟨0⟩ := by
    rw [liquidateMarketMemory_load _ (UInt256.ofNat 800) hm (by decide) hm
      (Or.inr (by decide)) (Or.inr (by decide)), hz]
  have hzw : memLoad (UInt256.ofNat 800)
      (wordAt0Mem id (liquidateMarketMemory mem id)) = ⟨0⟩ := by
    rw [memLoad_wordAt0Mem _ (UInt256.ofNat 800) (by decide) hs3, hz3]
  have hz4 : memLoad (UInt256.ofNat 800)
      (twoWordHashMem id ⟨0⟩ (liquidateMarketMemory mem id)) = ⟨0⟩ := by
    rw [memLoad_twoWordHashMem _ _ (UInt256.ofNat 800) (by decide) hs3, hz3]
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem id ⟨1⟩ (liquidateIdMemory mem id)) = solcMappingSlot ⟨1⟩ id :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem id ⟨0⟩ (liquidateMarketMemory mem id)) = solcMappingSlot ⟨0⟩ id :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hh3 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (liquidatePositionMemory mem id borrower) = positionSlot id borrower :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hf1 : id.toByteArray.write 0 mem 768 32 = liquidateIdMemory mem id := rfl
  have hf2 : (solcMappingSlot ⟨1⟩ id).toByteArray.write 0
      (twoWordHashMem id ⟨1⟩ (liquidateIdMemory mem id)) 672 32 =
      liquidateMarketMemory mem id := rfl
  have hf3 : twoWordHashMem borrower (solcMappingSlot ⟨0⟩ id)
      (twoWordHashMem id ⟨0⟩ (liquidateMarketMemory mem id)) =
      liquidatePositionMemory mem id borrower := rfl
  constructor <;> simp only [midnight_block_5161_fallthrough_memory,
    midnight_block_5161_fallthrough_stack, addressMask_computed, solcAddrMask_clean hc] <;>
    simp only [show (UInt256.ofNat 768).toNat = 768 from rfl,
    show (UInt256.ofNat 672).toNat = 672 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, hf1, hf2, hf3,
    liquidateIdMemory_id, liquidateMarketMemory_id id hm, hz1, hz2, hz3, hzw, hz4,
    wordAt0_fold, twoWordHash_fold, hh1, hh2, hh3, List.cons_append, List.nil_append] <;> rfl

end Benchmarks.Midnight
