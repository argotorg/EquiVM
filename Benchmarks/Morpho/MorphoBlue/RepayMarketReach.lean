import Benchmarks.Morpho.MorphoBlue.RepayPositionRefine
import Benchmarks.Morpho.MorphoBlue.ZeroFloorSub
import Benchmarks.Morpho.MorphoBlue.MarketSubtract

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw id assets shares account srcOff len : UInt256} {out : ByteArray}
  {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoRepayMarketSharesReachSub (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10709)
      ([shares, UInt256.ofNat 10736] ++ repayMarketTail id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([marketFieldWord σ ee id 3, shares, UInt256.ofNat 2278, marketFieldSlot id 3, UInt256.ofNat 10736] ++
        repayMarketTail id assets shares account srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10709_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), shares, UInt256.ofNat 2278,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1, UInt256.ofNat 10736] ++
      repayMarketTail id assets shares account srcOff len R) (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [marketBorrowSlot_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoRepayDebtReachCast (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10736)
      (repayMarketTail id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([zeroFloorSubWord (marketFieldWord σ ee id 2) assets, UInt256.ofNat 10767] ++
        repayMarketTail id assets shares account srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10736_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 17 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  let m1 := twoWordHashMem id (UInt256.ofNat 3) mem
  let old := UInt256.land (solcSlotWordAt
    (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 + UInt256.ofNat 1) σ ee) uint128Mask
  change RD _ _ _ _ _
    ([UInt256.mul (UInt256.gt old assets) (UInt256.sub old assets), UInt256.ofNat 10767] ++
      repayMarketTail id assets shares account srcOff len R) m1 _ _ _ _ _ at rd1
  have hold : old = marketFieldWord σ ee id 2 := by
    dsimp only [old, m1]
    rw [marketBorrowSlot_hash]
    rfl
  rw [hold, zeroFloorSubWord_evm] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
