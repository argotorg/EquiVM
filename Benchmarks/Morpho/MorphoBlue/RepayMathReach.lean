import Benchmarks.Morpho.MorphoBlue.RepayAccrueRefine
import Benchmarks.Morpho.MorphoBlue.AssetsUpRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def repayUpdateTail (id assets shares account srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [uint128Mask, UInt256.ofNat 3, id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128,
    UInt256.ofNat 32, shares, assets, solcAddrMask] ++ R

theorem marketBorrowSlot_hash (id : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1 =
      marketFieldSlot id 2 := by
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hh]
  rfl

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw assets shares account srcOff len : UInt256} {out : ByteArray}
  {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoRepayReachShares (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (hn : assets ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10571)
      (repayAccrueTail p.id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15336)
      ([assets, marketFieldWord σ ee p.id 2, marketFieldWord σ ee p.id 3, UInt256.ofNat 10607,
        UInt256.ofNat 3, p.id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
        uint128Mask, assets, solcAddrMask] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_10571_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 13 + 2 ≤ 1024; omega) (isZero_eq_zero_of_ne hn) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_10576_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 15 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := marketBorrowSlot_hash p.id mem
  simp only [morphoBlocks.morpho_block_10576_stack, morphoBlocks.morpho_block_10576_memory] at rd2
  change RD _ _ _ _ _
    ([assets, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), UInt256.ofNat 10607,
      UInt256.ofNat 3, p.id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
      uint128Mask, assets, solcAddrMask] ++ R) _ _ _ _ _ _ at rd2
  rw [hh] at rd2
  exact ⟨a2, k2, C2, rd2⟩

theorem morphoRepayReachAssets (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (hz : assets = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10571)
      (repayAccrueTail p.id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15445)
      ([shares, marketFieldWord σ ee p.id 2, marketFieldWord σ ee p.id 3, UInt256.ofNat 11034,
        UInt256.ofNat 3, p.id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
        shares, uint128Mask, solcAddrMask] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_10571_taken (immWords := wordsOf (immStore v))
    (by change R.length + 13 + 2 ≤ 1024; omega) (by rw [hz]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_10999_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := marketBorrowSlot_hash p.id mem
  simp only [morphoBlocks.morpho_block_10999_stack, morphoBlocks.morpho_block_10999_memory] at rd2
  change RD _ _ _ _ _
    ([shares, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128), UInt256.ofNat 11034,
      UInt256.ofNat 3, p.id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
      shares, uint128Mask, solcAddrMask] ++ R) _ _ _ _ _ _ at rd2
  rw [hh] at rd2
  exact ⟨a2, k2, C2, rd2⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
