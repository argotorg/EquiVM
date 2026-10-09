import Benchmarks.Morpho.MorphoBlue.SupplyPositionRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def supplyStoreTail (σ : AccountMap) (ee : ExecutionEnv) (id assets shares account srcOff len : UInt256)
    (R : List UInt256) : List UInt256 :=
  [uint128Mask, UInt256.lnot uint128Mask, solcSlotWordAt (marketFieldSlot id 0) σ ee,
    marketFieldSlot id 0, id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128,
    UInt256.ofNat 32, shares, assets, solcAddrMask] ++ R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw id assets shares account srcOff len : UInt256} {out : ByteArray}
  {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoSupplyMarketSharesReachAdd (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4031)
      ([shares, UInt256.ofNat 4056] ++ supplyUpdateTail id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([marketFieldWord σ ee id 1, shares, UInt256.ofNat 2278, marketFieldSlot id 1, UInt256.ofNat 4056] ++
        supplyUpdateTail id assets shares account srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4031_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 14 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee) (UInt256.ofNat 128), shares, UInt256.ofNat 2278,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem), UInt256.ofNat 4056] ++
      supplyUpdateTail id assets shares account srcOff len R) (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [marketSupplySlot_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoSupplyMarketAssetsReachAdd (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4065)
      (assets :: supplyUpdateTail id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([marketFieldWord σ ee id 0, assets, UInt256.ofNat 4124] ++
        supplyStoreTail σ ee id assets shares account srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_4065_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 15 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee) uint128Mask, assets, UInt256.ofNat 4124,
      uint128Mask, UInt256.lnot uint128Mask,
      solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem)) σ ee,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem),
      id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
      shares, assets, solcAddrMask] ++ R) (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [marketSupplySlot_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
