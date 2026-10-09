import Benchmarks.Morpho.MorphoBlue.SupplyMathReach
import Benchmarks.Morpho.MorphoBlue.WithdrawAccrueRefine
import Benchmarks.Morpho.MorphoBlue.SharesUpRoutines
import Benchmarks.Morpho.MorphoBlue.AssetsDownRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def withdrawUpdateTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 0, UInt256.ofNat 64, UInt256.ofNat 7950, id, account, receiver, UInt256.ofNat 128,
    solcAddrMask, receiver, assets, UInt256.ofNat 2752, shares, assets, UInt256.ofNat 64] ++ R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw assets shares account receiver : UInt256} {out : ByteArray}
  {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoWithdrawReachShares (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (hn : assets ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7651)
      (withdrawAccrueTail p.id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15411)
      ([assets, marketFieldWord σ ee p.id 0, marketFieldWord σ ee p.id 1, UInt256.ofNat 7735,
        UInt256.ofNat 64, UInt256.ofNat 7950, p.id, account, receiver, UInt256.ofNat 128, solcAddrMask,
        receiver, assets, UInt256.ofNat 2752, UInt256.ofNat 0, assets, UInt256.ofNat 64] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_7651_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 2 ≤ 1024; omega) (isZero_eq_zero_of_ne hn) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_7656_packed (immWords := wordsOf (immStore v))
    (by change R.length + 18 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := marketSupplySlot_hash p.id mem
  dsimp only [morphoBlocks.morpho_block_7656_stack, morphoBlocks.morpho_block_7656_memory] at rd2
  change RD _ _ _ _ _
    ([assets, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem)) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem)) σ ee) (UInt256.ofNat 128), UInt256.ofNat 7735,
      UInt256.ofNat 64, UInt256.ofNat 7950, p.id, account, receiver, UInt256.ofNat 128, solcAddrMask,
      receiver, assets, UInt256.ofNat 2752, UInt256.ofNat 0, assets, UInt256.ofNat 64] ++ R) _ _ _ _ _ _ at rd2
  rw [hh] at rd2
  exact ⟨a2, k2, C2, rd2⟩

theorem morphoWithdrawReachAssets (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (hz : assets = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7651)
      (withdrawAccrueTail p.id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15373)
      ([shares, marketFieldWord σ ee p.id 0, marketFieldWord σ ee p.id 1, UInt256.ofNat 8097,
        UInt256.ofNat 7950, p.id, account, receiver, UInt256.ofNat 128, solcAddrMask,
        receiver, UInt256.ofNat 0, UInt256.ofNat 2752, shares, UInt256.ofNat 64, UInt256.ofNat 64] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_7651_taken (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 2 ≤ 1024; omega) (by rw [hz]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_8014_packed (immWords := wordsOf (immStore v))
    (by change R.length + 18 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := marketSupplySlot_hash p.id mem
  dsimp only [morphoBlocks.morpho_block_8014_stack, morphoBlocks.morpho_block_8014_memory] at rd2
  change RD _ _ _ _ _
    ([shares, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem)) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem)) σ ee) (UInt256.ofNat 128), UInt256.ofNat 8097,
      UInt256.ofNat 7950, p.id, account, receiver, UInt256.ofNat 128, solcAddrMask,
      receiver, UInt256.ofNat 0, UInt256.ofNat 2752, shares, UInt256.ofNat 64, UInt256.ofNat 64] ++ R) _ _ _ _ _ _ at rd2
  rw [hh] at rd2
  exact ⟨a2, k2, C2, rd2⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
