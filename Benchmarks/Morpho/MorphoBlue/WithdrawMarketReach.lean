import Benchmarks.Morpho.MorphoBlue.WithdrawPositionRefine
import Benchmarks.Morpho.MorphoBlue.MarketSubtract
import Benchmarks.Morpho.MorphoBlue.RepayMathReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def withdrawStoreTail (σ : AccountMap) (ee : ExecutionEnv) (id assets shares account receiver : UInt256)
    (R : List UInt256) : List UInt256 :=
  [uint128Mask, UInt256.lnot uint128Mask, solcSlotWordAt (marketFieldSlot id 0) σ ee,
    marketFieldSlot id 0] ++ withdrawUpdateTail id assets shares account receiver R

def withdrawEventTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [id, account, receiver, UInt256.ofNat 128, solcAddrMask, receiver, assets,
    UInt256.ofNat 2752, shares, assets, UInt256.ofNat 64] ++ R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw id assets shares account receiver : UInt256} {out : ByteArray}
  {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoWithdrawMarketSharesReachSub (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7788)
      ([shares, UInt256.ofNat 7813] ++ withdrawUpdateTail id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([marketFieldWord σ ee id 1, shares, UInt256.ofNat 2278, marketFieldSlot id 1, UInt256.ofNat 7813] ++
        withdrawUpdateTail id assets shares account receiver R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_7788_packed (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 10 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee) (UInt256.ofNat 128), shares, UInt256.ofNat 2278,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem), UInt256.ofNat 7813] ++
      withdrawUpdateTail id assets shares account receiver R) (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [marketSupplySlot_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoWithdrawMarketAssetsReachSub (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7822)
      (assets :: withdrawUpdateTail id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([marketFieldWord σ ee id 0, assets, UInt256.ofNat 7898] ++
        withdrawStoreTail σ ee id assets shares account receiver R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_7822_packed (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 12 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee) uint128Mask, assets, UInt256.ofNat 7898,
      uint128Mask, UInt256.lnot uint128Mask,
      solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem)] ++
      withdrawUpdateTail id assets shares account receiver R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [marketSupplySlot_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoWithdrawStoreLiquidity (hstack : R.length + 28 ≤ 1024)
    (hp : ee.perm = true) (value : UInt256) (hc : value.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7898)
      (value :: withdrawStoreTail σ ee id assets shares account receiver R) mem aw out σ k C) :
    let σ' := storeMarketFieldAccounts σ ee id ⟨0, by decide⟩ value
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12880)
      ([UInt256.ofNat 585, UInt256.isZero (UInt256.lt (marketFieldWord σ' ee id 0)
        (marketFieldWord σ' ee id 2)), UInt256.ofNat 7950] ++
        withdrawEventTail id assets shares account receiver R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ' k' C' := by
  have hc' : UInt256.land value uint128Mask = value := halfWord_low_clean _ hc
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_7898_packed (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 9 ≤ 1024; omega) hp
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_7898_stack] at rd1
  change RD _ _ _ _ _
    ([UInt256.ofNat 585, UInt256.isZero (UInt256.lt
      (UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem))
        (storeMarketFieldAccounts σ ee id ⟨0, by decide⟩ (UInt256.land value uint128Mask)) ee) uint128Mask)
      (UInt256.land (solcSlotWordAt ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem)) + UInt256.ofNat 1)
        (storeMarketFieldAccounts σ ee id ⟨0, by decide⟩ (UInt256.land value uint128Mask)) ee) uint128Mask)),
      UInt256.ofNat 7950] ++ withdrawEventTail id assets shares account receiver R)
    (twoWordHashMem id (UInt256.ofNat 3) mem) _ _
    (storeMarketFieldAccounts σ ee id ⟨0, by decide⟩ (UInt256.land value uint128Mask)) _ _ at rd1
  rw [hc', marketBorrowSlot_hash, marketSupplySlot_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
