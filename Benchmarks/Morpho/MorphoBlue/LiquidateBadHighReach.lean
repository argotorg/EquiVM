import Benchmarks.Morpho.MorphoBlue.LiquidateBadLowRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets seized shares account badAssets badShares srcOff len : UInt256}
  {σ : AccountMap} {k C : Nat} {R : List UInt256}

theorem morphoLiquidateBadHighReachSub (hstack : R.length + 40 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3140)
      ([badShares, UInt256.ofNat 3169] ++ liquidateBadTail id assets seized shares badAssets badShares srcOff len R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([marketFieldWord σ ee id 3, badShares, UInt256.ofNat 2278, marketFieldSlot id 3, UInt256.ofNat 3169] ++
        liquidateBadTail id assets seized shares badAssets badShares srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_3140_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 14 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) (UInt256.ofNat 128),
      badShares, UInt256.ofNat 2278,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1,
      UInt256.ofNat 3169] ++ liquidateBadTail id assets seized shares badAssets badShares srcOff len R)
    (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [marketBorrowSlot_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoLiquidateBadClear (hstack : R.length + 40 ≤ 1024) (hperm : ee.perm = true)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3169)
      (liquidateBadTail id assets seized shares badAssets badShares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2574)
      (liquidateEventTail (UInt256.ofNat (deployedRuntime v).size) id assets seized shares badAssets badShares srcOff len R)
      (supplyPositionMem id account mem) aw' out
      (storePositionPackedAccounts σ ee id account false (UInt256.ofNat 0)) k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_3169_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 11 ≤ 1024; omega) hperm
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have haddr : UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = account := by
    change UInt256.land (calldataWord ee.calldata 164) solcAddrMask = account
    rw [haccount, solcAddrMask_clean ha]
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  dsimp only [morphoBlocks.morpho_block_3169_memory] at rd1
  rw [haddr] at rd1
  change RD _ _ _ _ _ _ m2 _ _
    (sstoreAccountMap ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1)
      (UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee)
        (UInt256.lnot uint128Mask))) _ _ at rd1
  rw [hm2, supplyPositionMem_hash] at rd1
  have hz : storePositionPackedAccounts σ ee id account false (UInt256.ofNat 0) =
      sstoreAccountMap ee.codeOwner σ (positionSlot id account + UInt256.ofNat 1)
        (UInt256.land (solcSlotWordAt (positionSlot id account + UInt256.ofNat 1) σ ee) (UInt256.lnot uint128Mask)) := by
    dsimp only [storePositionPackedAccounts, setUint128HalfWord, setUint128LowWord]
    simp only [Bool.false_eq_true, ↓reduceIte,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_lor_zero]
    rfl
  rw [← hz] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
