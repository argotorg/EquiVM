import Benchmarks.Morpho.MorphoBlue.LiquidateMarketRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets seized shares account srcOff len debt : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem morphoLiquidateDebtStore (hstack : R.length + 30 ≤ 1024) (hperm : ee.perm = true)
    (hc : debt.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2391)
      (debt :: liquidateMarketTail id assets seized shares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([seized, UInt256.ofNat 2444, UInt256.ofNat 2509] ++ liquidateMarketTail id assets seized shares srcOff len R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' out
      (storeMarketFieldAccounts σ ee id ⟨2, by decide⟩ debt) k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2391_packed (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 13 ≤ 1024; omega) hperm (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _ _ (twoWordHashMem id (UInt256.ofNat 3) mem) _ _
    (sstoreAccountMap ee.codeOwner σ
      (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1)
      (UInt256.lor (UInt256.land (solcSlotWordAt
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee)
        (UInt256.lnot uint128Mask)) (UInt256.land debt uint128Mask))) _ _ at rd1
  have hc' : UInt256.land debt uint128Mask = debt := halfWord_low_clean debt hc
  rw [marketBorrowSlot_hash, hc'] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoLiquidateCollateralReachSub (hstack : R.length + 30 ≤ 1024)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2444)
      ([seized, UInt256.ofNat 2509] ++ liquidateMarketTail id assets seized shares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([positionFieldWord σ ee id account 2, seized, UInt256.ofNat 2278,
        positionSlot id account + UInt256.ofNat 1, UInt256.ofNat 2509] ++ liquidateMarketTail id assets seized shares srcOff len R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2444_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 12 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have haddr : UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = account := by
    change UInt256.land (calldataWord ee.calldata 164) solcAddrMask = account
    rw [haccount, solcAddrMask_clean ha]
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  dsimp only [morphoBlocks.morpho_block_2444_stack, morphoBlocks.morpho_block_2444_memory] at rd1
  rw [haddr] at rd1
  change RD _ _ _ _ _
    ([UInt256.shiftRight (solcSlotWordAt
      (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee)
      (UInt256.ofNat 128), seized, UInt256.ofNat 2278,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1, UInt256.ofNat 2509] ++
      liquidateMarketTail id assets seized shares srcOff len R) m2 _ _ _ _ _ at rd1
  rw [hm2, supplyPositionMem_hash] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
end Benchmarks.Morpho.MorphoBlue
