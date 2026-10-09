import Benchmarks.Morpho.MorphoBlue.LiquidateCollateralRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateEventTail (trash id assets seized shares badAssets badShares srcOff len : UInt256)
    (R : List UInt256) : List UInt256 :=
  [trash, badAssets, badShares] ++ liquidateUpdateTail id assets seized shares srcOff len R

def liquidateBadTail (id assets seized shares badAssets badShares srcOff len : UInt256)
    (R : List UInt256) : List UInt256 :=
  liquidateEventTail (UInt256.lnot uint128Mask) id assets seized shares badAssets badShares srcOff len R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets seized shares account srcOff len : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem morphoLiquidateBadDebtGuard (hstack : R.length + 40 ≤ 1024)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2509)
      (liquidateMarketTail id assets seized shares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if positionFieldWord σ ee id account 2 = ⟨0⟩ then UInt256.ofNat 2873 else UInt256.ofNat 2574)
      (liquidateBadTail id assets seized shares (UInt256.ofNat 0) (UInt256.ofNat 0) srcOff len R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  have haddr : UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = account := by
    change UInt256.land (calldataWord ee.calldata 164) solcAddrMask = account
    rw [haccount, solcAddrMask_clean ha]
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  have hh2 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyPositionMem id account mem) =
      positionSlot id account := supplyPositionMem_hash _ _ _
  have hc : UInt256.shiftRight (solcSlotWordAt
      (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee)
      (UInt256.ofNat 128) = positionFieldWord σ ee id account 2 := by rw [hm2, hh2]; rfl
  by_cases hz : positionFieldWord σ ee id account 2 = ⟨0⟩
  · rw [if_pos hz]
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2509_taken_packed (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 11 ≤ 1024; omega)
      (by rw [haddr]; change UInt256.isZero (UInt256.shiftRight (solcSlotWordAt
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128)) ≠ _
          rw [hc, hz]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_2509_taken_memory] at rd1
    rw [haddr] at rd1
    change RD _ _ _ _ _ _ m2 _ _ _ _ _ at rd1
    rw [hm2] at rd1
    exact ⟨a1, k1, C1, rd1⟩
  · rw [if_neg hz]
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2509_fallthrough_packed (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 11 ≤ 1024; omega)
      (by rw [haddr]; change UInt256.isZero (UInt256.shiftRight (solcSlotWordAt
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128)) = _
          rw [hc]; exact isZero_eq_zero_of_ne hz) h
    dsimp only [morphoBlocks.morpho_block_2509_fallthrough_memory] at rd1
    rw [haddr] at rd1
    change RD _ _ _ _ _ _ m2 _ _ _ _ _ at rd1
    rw [hm2] at rd1
    exact ⟨a1, k1, C1, rd1⟩

theorem morphoLiquidateBadDebtReachAssets (hstack : R.length + 40 ≤ 1024)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2873)
      (liquidateBadTail id assets seized shares (UInt256.ofNat 0) (UInt256.ofNat 0) srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15445)
      ([positionFieldWord σ ee id account 1, marketFieldWord σ ee id 2, marketFieldWord σ ee id 3,
        UInt256.ofNat 2996, marketFieldWord σ ee id 2, UInt256.lnot uint128Mask,
        positionFieldWord σ ee id account 1] ++ liquidateUpdateTail id assets seized shares srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) (supplyPositionMem id account mem)) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2873_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 13 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have haddr : UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = account := by
    change UInt256.land (calldataWord ee.calldata 164) solcAddrMask = account
    rw [haccount, solcAddrMask_clean ha]
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  let m3 := twoWordHashMem id (UInt256.ofNat 3) m2
  let ps := keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1
  let ms := keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m3 + UInt256.ofNat 1
  dsimp only [morphoBlocks.morpho_block_2873_stack, morphoBlocks.morpho_block_2873_memory] at rd1
  rw [haddr] at rd1
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt ps σ ee) uint128Mask, UInt256.land (solcSlotWordAt ms σ ee) uint128Mask,
      UInt256.shiftRight (solcSlotWordAt ms σ ee) (UInt256.ofNat 128), UInt256.ofNat 2996,
      UInt256.land (solcSlotWordAt ms σ ee) uint128Mask, UInt256.lnot uint128Mask,
      UInt256.land (solcSlotWordAt ps σ ee) uint128Mask] ++ liquidateUpdateTail id assets seized shares srcOff len R)
      m3 _ _ _ _ _ at rd1
  have hps : ps = positionSlot id account + UInt256.ofNat 1 := by dsimp only [ps]; rw [hm2, supplyPositionMem_hash]
  have hms : ms = marketFieldSlot id 2 := marketBorrowSlot_hash id m2
  rw [hps, hms] at rd1
  dsimp only [m3] at rd1
  rw [hm2] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
