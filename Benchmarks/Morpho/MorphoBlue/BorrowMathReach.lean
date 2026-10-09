import Benchmarks.Morpho.MorphoBlue.RepayMathReach
import Benchmarks.Morpho.MorphoBlue.BorrowAccrueRefine
import Benchmarks.Morpho.MorphoBlue.SharesUpRoutines
import Benchmarks.Morpho.MorphoBlue.AssetsDownRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def borrowUpdateTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [account, UInt256.ofNat 3, UInt256.ofNat 0, uint128Mask, id, shares, receiver,
    UInt256.ofNat 128, solcAddrMask, assets, receiver, UInt256.ofNat 32, shares, assets] ++ R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw assets shares account receiver : UInt256} {out : ByteArray}
  {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoBorrowReachShares (p : MarketParamsWords) (hstack : R.length + 30 ≤ 1024)
    (hn : assets ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8491)
      (borrowAccrueTail p.id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15411)
      ([assets, marketFieldWord σ ee p.id 2, marketFieldWord σ ee p.id 3, UInt256.ofNat 8534,
        UInt256.ofNat 0, uint128Mask, p.id, account, receiver, UInt256.ofNat 128, solcAddrMask,
        assets, receiver, UInt256.ofNat 32, UInt256.ofNat 3, assets] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_8491_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) (isZero_eq_zero_of_ne hn) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_8496_packed (immWords := wordsOf (immStore v))
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := marketBorrowSlot_hash p.id mem
  dsimp only [morphoBlocks.morpho_block_8496_stack, morphoBlocks.morpho_block_8496_memory] at rd2
  change RD _ _ _ _ _
    ([assets, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), UInt256.ofNat 8534,
      UInt256.ofNat 0, uint128Mask, p.id, account, receiver, UInt256.ofNat 128, solcAddrMask,
      assets, receiver, UInt256.ofNat 32, UInt256.ofNat 3, assets] ++ R) _ _ _ _ _ _ at rd2
  rw [hh] at rd2
  exact ⟨a2, k2, C2, rd2⟩

theorem morphoBorrowReachAssets (p : MarketParamsWords) (hstack : R.length + 30 ≤ 1024)
    (hz : assets = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8491)
      (borrowAccrueTail p.id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15373)
      ([shares, marketFieldWord σ ee p.id 2, marketFieldWord σ ee p.id 3, UInt256.ofNat 8973,
        UInt256.ofNat 0, uint128Mask, p.id, shares, receiver, UInt256.ofNat 128, solcAddrMask,
        account, receiver, UInt256.ofNat 32, shares, UInt256.ofNat 3] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_8491_taken (immWords := wordsOf (immStore v))
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) (by rw [hz]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_8934_packed (immWords := wordsOf (immStore v))
    (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := marketBorrowSlot_hash p.id mem
  dsimp only [morphoBlocks.morpho_block_8934_stack, morphoBlocks.morpho_block_8934_memory] at rd2
  change RD _ _ _ _ _
    ([shares, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), UInt256.ofNat 8973,
      UInt256.ofNat 0, uint128Mask, p.id, shares, receiver, UInt256.ofNat 128, solcAddrMask,
      account, receiver, UInt256.ofNat 32, shares, UInt256.ofNat 3] ++ R) _ _ _ _ _ _ at rd2
  rw [hh] at rd2
  exact ⟨a2, k2, C2, rd2⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
