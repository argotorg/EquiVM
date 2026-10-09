import Benchmarks.Morpho.MorphoBlue.SupplyAccrueRefine
import Benchmarks.Morpho.MorphoBlue.AssetsUpRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyUpdateTail (id assets shares account srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [uint128Mask, id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128,
    UInt256.ofNat 32, shares, assets, solcAddrMask] ++ R

theorem marketSupplySlot_hash (id : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) =
      marketFieldSlot id 0 := by
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  simpa only [marketFieldSlot, Nat.zero_div, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    u256_add_zero] using hh

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw assets shares account srcOff len : UInt256} {out : ByteArray}
  {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoSupplyReachShares (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (hn : assets ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3948)
      (supplyAccrueTail p.id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15336)
      ([assets, marketFieldWord σ ee p.id 0, marketFieldWord σ ee p.id 1, UInt256.ofNat 3982,
        p.id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
        uint128Mask, assets, solcAddrMask] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_3948_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 12 + 2 ≤ 1024; omega) (isZero_eq_zero_of_ne hn) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_3953_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 14 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := marketSupplySlot_hash p.id mem
  simp only [morphoBlocks.morpho_block_3953_stack, morphoBlocks.morpho_block_3953_memory] at rd2
  change RD _ _ _ _ _
    ([assets, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem)) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem)) σ ee) (UInt256.ofNat 128), UInt256.ofNat 3982,
      p.id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
      uint128Mask, assets, solcAddrMask] ++ R) _ _ _ _ _ _ at rd2
  rw [hh] at rd2
  exact ⟨a2, k2, C2, rd2⟩

theorem morphoSupplyReachAssets (p : MarketParamsWords) (hstack : R.length + 28 ≤ 1024)
    (hz : assets = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3948)
      (supplyAccrueTail p.id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15445)
      ([shares, marketFieldWord σ ee p.id 0, marketFieldWord σ ee p.id 1, UInt256.ofNat 4360,
        p.id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
        shares, uint128Mask, solcAddrMask] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_3948_taken (immWords := wordsOf (immStore v))
    (by change R.length + 12 + 2 ≤ 1024; omega) (by rw [hz]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_4327_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 15 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hh := marketSupplySlot_hash p.id mem
  simp only [morphoBlocks.morpho_block_4327_stack, morphoBlocks.morpho_block_4327_memory] at rd2
  change RD _ _ _ _ _
    ([shares, UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem)) σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem)) σ ee) (UInt256.ofNat 128), UInt256.ofNat 4360,
      p.id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
      shares, uint128Mask, solcAddrMask] ++ R) _ _ _ _ _ _ at rd2
  rw [hh] at rd2
  exact ⟨a2, k2, C2, rd2⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
