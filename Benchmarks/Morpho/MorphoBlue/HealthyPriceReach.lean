import Benchmarks.Morpho.MorphoBlue.HealthyPriceSource
import Benchmarks.Morpho.MorphoBlue.RepayMathReach
import Benchmarks.Morpho.MorphoBlue.SupplyPositionRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def healthyBorrowMem (id account : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem id (UInt256.ofNat 3) (supplyPositionMem id account mem)

def healthyPriceMem (id account : UInt256) (mem : ByteArray) : ByteArray :=
  supplyPositionMem id account (healthyBorrowMem id account mem)

theorem supplyPositionMem_hash (id account : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyPositionMem id account mem) =
      positionSlot id account := twoWordHashMem_solcMappingSlot_any _ _ _


theorem supplyPositionMem_prefix (id account : UInt256) (mem : ByteArray) (limit : Nat) :
    MemoryPrefix mem (supplyPositionMem id account mem) limit :=
  (twoWordHashMem_prefix id (UInt256.ofNat 2) mem limit).trans
    (twoWordHashMem_prefix account (solcMappingSlot ⟨2⟩ id) _ limit)

theorem MorphoHeap.positionHash {mem fp spare} (hm : MorphoHeap mem fp spare) (id account : UInt256) :
    MorphoHeap (supplyPositionMem id account mem) fp spare :=
  (hm.hash id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ id)

theorem healthyPriceMem_prefix (id account : UInt256) (mem : ByteArray) (limit : Nat) :
    MemoryPrefix mem (healthyPriceMem id account mem) limit :=
  ((supplyPositionMem_prefix id account mem limit).trans (twoWordHashMem_prefix id (UInt256.ofNat 3) _ limit)).trans
    (supplyPositionMem_prefix id account _ limit)

theorem MorphoHeap.healthyPrice {mem fp spare} (hm : MorphoHeap mem fp spare) (id account : UInt256) :
    MorphoHeap (healthyPriceMem id account mem) fp spare :=
  ((hm.positionHash id account).hash id (UInt256.ofNat 3)).positionHash id account

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id account price borrowed mpos ret : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem morphoHealthyPriceReachAssets (hstack : R.length + 28 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14189)
      ([mpos, id, account, price, ret] ++ R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15445)
      ([positionFieldWord σ ee id account 1, marketFieldWord σ ee id 2, marketFieldWord σ ee id 3,
        UInt256.ofNat 14328, account, UInt256.ofNat 0, UInt256.ofNat 64, UInt256.ofNat 1, price,
        UInt256.ofNat 14355, oraclePriceScale, UInt256.ofNat 128, mpos, UInt256.ofNat 14365, wad, id, ret] ++ R)
      (healthyBorrowMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_14189_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 19 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_14189_stack, morphoBlocks.morpho_block_14189_memory] at rd1
  have hmask : UInt256.land account (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = account := solcAddrMask_clean hc
  rw [hmask] at rd1
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem) =
      solcMappingSlot ⟨2⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 2) mem)) (twoWordHashMem id (UInt256.ofNat 2) mem)) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3)
          (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            (twoWordHashMem id (UInt256.ofNat 2) mem)) (twoWordHashMem id (UInt256.ofNat 2) mem))) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3)
          (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            (twoWordHashMem id (UInt256.ofNat 2) mem)) (twoWordHashMem id (UInt256.ofNat 2) mem))) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128),
      UInt256.ofNat 14328, account, UInt256.ofNat 0, UInt256.ofNat 64, UInt256.ofNat 1, price,
      UInt256.ofNat 14355, oraclePriceScale, UInt256.ofNat 128, mpos, UInt256.ofNat 14365, wad, id, ret] ++ R)
    (twoWordHashMem id (UInt256.ofNat 3)
      (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 2) mem)) (twoWordHashMem id (UInt256.ofNat 2) mem))) _ _ _ _ _ at rd1
  rw [hh1] at rd1
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (supplyPositionMem id account mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (healthyBorrowMem id account mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (healthyBorrowMem id account mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128),
      UInt256.ofNat 14328, account, UInt256.ofNat 0, UInt256.ofNat 64, UInt256.ofNat 1, price,
      UInt256.ofNat 14355, oraclePriceScale, UInt256.ofNat 128, mpos, UInt256.ofNat 14365, wad, id, ret] ++ R)
    (healthyBorrowMem id account mem) _ _ _ _ _ at rd1
  rw [supplyPositionMem_hash] at rd1
  have hh3 := marketBorrowSlot_hash id (supplyPositionMem id account mem)
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (healthyBorrowMem id account mem) + UInt256.ofNat 1 = _ at hh3
  rw [hh3] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoHealthyPriceReachCollateral (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14328)
      ([borrowed, account, UInt256.ofNat 0, UInt256.ofNat 64, UInt256.ofNat 1, price,
        UInt256.ofNat 14355, oraclePriceScale, UInt256.ofNat 128, mpos, UInt256.ofNat 14365, wad, id, ret] ++ R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([positionFieldWord σ ee id account 2, price, UInt256.ofNat 14355, oraclePriceScale, UInt256.ofNat 128,
        mpos, UInt256.ofNat 14365, wad, borrowed, ret] ++ R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_14328_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 14 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem) =
      solcMappingSlot ⟨2⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 2) mem)) (twoWordHashMem id (UInt256.ofNat 2) mem)) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128),
      price, UInt256.ofNat 14355, oraclePriceScale, UInt256.ofNat 128, mpos, UInt256.ofNat 14365, wad, borrowed, ret] ++ R)
    (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 2) mem)) (twoWordHashMem id (UInt256.ofNat 2) mem)) _ _ _ _ _ at rd1
  rw [hh1] at rd1
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (supplyPositionMem id account mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128),
      price, UInt256.ofNat 14355, oraclePriceScale, UInt256.ofNat 128, mpos, UInt256.ofNat 14365, wad, borrowed, ret] ++ R)
    (supplyPositionMem id account mem) _ _ _ _ _ at rd1
  rw [supplyPositionMem_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
