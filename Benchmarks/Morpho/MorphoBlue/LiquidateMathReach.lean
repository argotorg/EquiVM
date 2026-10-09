import Benchmarks.Morpho.MorphoBlue.LiquidateQuotedReach
import Benchmarks.Morpho.MorphoBlue.RepayMathReach
import Benchmarks.Morpho.MorphoBlue.AssetsDownRoutines
import Benchmarks.Morpho.MorphoBlue.SharesUpRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateDebtTail (id shares price srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [price, srcOff, len, UInt256.ofNat 0, shares, id, UInt256.ofNat 128] ++ R

def liquidateFinishMathTail (id seized shares srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [id, srcOff, len, UInt256.ofNat 0, shares, seized, UInt256.ofNat 128] ++ R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {id seized shares price lltv srcOff len quote : UInt256} {R : List UInt256}

theorem morphoLiquidateReachShares (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2009)
      ([quote, UInt256.ofNat 2055] ++ liquidateAmountTail id seized srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15411)
      ([quote, marketFieldWord σ ee id 2, marketFieldWord σ ee id 3, UInt256.ofNat 2055] ++
        liquidateAmountTail id seized srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2009_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 10 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hh := marketBorrowSlot_hash id mem
  dsimp only [morphoBlocks.morpho_block_2009_stack, morphoBlocks.morpho_block_2009_memory] at rd1
  change RD _ _ _ _ _
    ([quote, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), UInt256.ofNat 2055] ++
        liquidateAmountTail id seized srcOff len R) _ _ _ _ _ _ at rd1
  rw [hh] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoLiquidateReachDebt (hstack : R.length + 24 ≤ 1024) (hz : seized = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
      (liquidateMathStack id seized shares price (liquidationDenom lltv) srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15373)
      ([shares, marketFieldWord σ ee id 2, marketFieldWord σ ee id 3, UInt256.ofNat 3443,
        liquidationFactor lltv, UInt256.ofNat 3448, wad] ++ liquidateDebtTail id shares price srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd0 := morphoBlocks.morpho_block_1743_taken (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 10 ≤ 1024; omega) (by rw [hz]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_3324_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 15 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd0
  have hf := liquidationFactor_evm_alt lltv
  dsimp only [liquidationCap, oraclePriceScale] at hf
  dsimp only [morphoBlocks.morpho_block_3324_stack, morphoBlocks.morpho_block_3324_memory] at rd1
  rw [hf] at rd1
  change RD _ _ _ _ _
    ([shares, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), UInt256.ofNat 3443,
        liquidationFactor lltv, UInt256.ofNat 3448, wad] ++ liquidateDebtTail id shares price srcOff len R) _ _ _ _ _ _ at rd1
  rw [marketBorrowSlot_hash id mem] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoLiquidateReachAssets (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2057)
      (liquidateFinishMathTail id seized shares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15445)
      ([shares, marketFieldWord σ ee id 2, marketFieldWord σ ee id 3, UInt256.ofNat 2105] ++
        liquidateFinishMathTail id seized shares srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2057_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 10 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_2057_stack, morphoBlocks.morpho_block_2057_memory] at rd1
  change RD _ _ _ _ _
    ([shares, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), UInt256.ofNat 2105] ++
        liquidateFinishMathTail id seized shares srcOff len R) _ _ _ _ _ _ at rd1
  rw [marketBorrowSlot_hash id mem] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
