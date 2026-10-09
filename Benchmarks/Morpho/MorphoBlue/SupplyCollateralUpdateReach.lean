import Benchmarks.Morpho.MorphoBlue.SupplyCollateralGuardPrepare
import Benchmarks.Morpho.MorphoBlue.PositionPackedWrites
import Benchmarks.Morpho.MorphoBlue.StoreHighStatic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyCollateralPositionMem (p : MarketParamsWords) (account : UInt256) : ByteArray :=
  twoWordHashMem account (solcMappingSlot ⟨2⟩ p.id) (twoWordHashMem p.id (UInt256.ofNat 2) (supplyCollateralCastMem p))

theorem supplyCollateralPositionHeap (p : MarketParamsWords) (account : UInt256) :
    CreateMarketHeap p 544 (supplyCollateralPositionMem p account) :=
  (((supplyCollateralCastHeap p).1.hash (by decide) p.id (UInt256.ofNat 2)).hash (by decide)
    account (solcMappingSlot ⟨2⟩ p.id))

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {aw assets account srcOff len : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoSupplyCollateralReachCast (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10184)
      (supplyCollateralUpdateTail p.id assets account srcOff len R) (supplyCollateralGuardMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([assets, UInt256.ofNat 10196, UInt256.ofNat 10235] ++ supplyCollateralUpdateTail p.id assets account srcOff len R)
      (supplyCollateralGuardMem p) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10184_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoSupplyCollateralReachAdd (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10196)
      ([assets, UInt256.ofNat 10235] ++ supplyCollateralUpdateTail p.id assets account srcOff len R)
      (supplyCollateralCastMem p) aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([positionFieldWord σ ee p.id account 2, assets, UInt256.ofNat 2278,
        positionSlot p.id account + ⟨1⟩, UInt256.ofNat 10235] ++ supplyCollateralUpdateTail p.id assets account srcOff len R)
      (supplyCollateralPositionMem p account) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10196_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 13 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  let mem := supplyCollateralCastMem p
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem p.id (UInt256.ofNat 2) mem) =
      solcMappingSlot ⟨2⟩ p.id := twoWordHashMem_solcMappingSlot_any _ _ _
  have hh2 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyCollateralPositionMem p account) =
      positionSlot p.id account := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem p.id (UInt256.ofNat 2) mem))
          (twoWordHashMem p.id (UInt256.ofNat 2) mem)) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), assets,
      UInt256.ofNat 2278, keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem p.id (UInt256.ofNat 2) mem))
          (twoWordHashMem p.id (UInt256.ofNat 2) mem)) + UInt256.ofNat 1,
      UInt256.ofNat 10235] ++ supplyCollateralUpdateTail p.id assets account srcOff len R)
    (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem p.id (UInt256.ofNat 2) mem))
      (twoWordHashMem p.id (UInt256.ofNat 2) mem)) _ _ _ _ _ at rd1
  rw [hh1] at rd1
  dsimp only [supplyCollateralPositionMem] at hh2
  rw [hh2] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
