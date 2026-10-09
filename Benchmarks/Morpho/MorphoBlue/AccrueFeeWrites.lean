import Benchmarks.Morpho.MorphoBlue.AccrueHeap
import Benchmarks.Morpho.MorphoBlue.AccrueSourceFeeWrites
import Benchmarks.Morpho.MorphoBlue.AccrueSupplyShares

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem accrueFeePositionState_env (evm : EVM.State) (id shares : UInt256) :
    (accrueFeePositionState evm id shares).executionEnv = evm.executionEnv :=
  storePositionSupplyShares_executionEnv _ _ _ _

theorem accrueFeePositionState_accounts (evm : EVM.State) (id shares : UInt256) :
    (accrueFeePositionState evm id shares).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
        (accrueFeePositionSlot evm.accountMap evm.executionEnv id)
        (solcSlotWordAt (accrueFeePositionSlot evm.accountMap evm.executionEnv id)
          evm.accountMap evm.executionEnv + shares) := by
  rw [accrueFeePositionState, storePositionSupplyShares, storageStore_accountMap]
  rfl

theorem accrueFeePositionState_bridge {s0 : State} {I : ExecutionEnv} {σ : AccountMap} {evm : State}
    (hs : SourceState s0 I σ evm) (id shares : UInt256) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ (accrueFeePositionSlot σ I id)
        (solcSlotWordAt (accrueFeePositionSlot σ I id) σ I + shares))
      (accrueFeePositionState evm id shares) := by
  have hb := storePositionSupplyShares_bridge hs id (accrueFeeRecipient σ I)
    (solcSlotWordAt (accrueFeePositionSlot σ I id) σ I + shares)
  simpa only [accrueFeePositionState, hs.env, ← hs.accounts] using hb

def accrueFeeWritesMem (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem id (UInt256.ofNat 3) (uint128ErrorMem (accrueFeePositionMem σ I id mem))

theorem MorphoHeap.feePosition {mem fp spare} (h : MorphoHeap mem fp spare)
    (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    MorphoHeap (accrueFeePositionMem σ I id mem) fp spare :=
  (h.hash id (UInt256.ofNat 2)).hash (accrueFeeRecipient σ I) (solcMappingSlot ⟨2⟩ id)

theorem MorphoHeap.feeWrites {mem fp spare} (h : MorphoHeap mem fp spare)
    (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) (hb : 64 ≤ spare) :
    MorphoHeap (accrueFeeWritesMem σ I id mem) (fp + UInt256.ofNat 64) (spare - 64) :=
  ((h.feePosition σ I id).narrow hb).hash id (UInt256.ofNat 3)

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 evm : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {id rate interest shares ret fp : UInt256} {R : List UInt256} {spare : Nat}

theorem morphoAccrueFeeWritesOk (hstack : R.length + 32 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hfit : AccrueFeeWritesFit evm id shares)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13793)
      ([shares, interest, solcAddrMask] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ σ' aw' k' C', SourceState s0 ee σ' (accrueFeeSharesState evm id shares) ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13863)
        ([interest, shares] ++ accrueMathTail id rate ret R)
        (accrueFeeWritesMem σ ee id mem) aw' rdata σ' k' C' := by
  have hpos : (solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee).toNat + shares.toNat < UInt256.size := by
    simpa only [hs.env, ← hs.accounts] using hfit.1
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccruePositionAddOk (v := v) (by omega) hpos h
  obtain ⟨k2, C2, rd2⟩ := morphoAccruePositionStore (v := v) (by omega) hp rd1
  have hm1 := hm.feePosition σ ee id
  have hs1 := accrueFeePositionState_bridge hs id shares
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoToUint128Ok (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (hm1.alloc64Guard hb) hfit.2.1 rd2
  let σ1 := sstoreAccountMap ee.codeOwner σ (accrueFeePositionSlot σ ee id)
    (solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee + shares)
  have hsum : (marketFieldWord σ1 ee id 1).toNat + shares.toNat < 2 ^ 128 := by
    simpa only [hs1.env, ← hs1.accounts] using hfit.2.2
  obtain ⟨aw4, k4, C4, rd4⟩ := morphoAccrueSharesStore (v := v) (by omega) hp hfit.2.1 hsum rd3
  have hs2 := storeMarketField_bridge hs1 id ⟨1, by decide⟩ (marketFieldWord σ1 ee id 1 + shares)
  refine ⟨_, aw4, k4, C4, ?_, rd4⟩
  simpa only [accrueFeeSharesState, hs1.env, ← hs1.accounts] using hs2

theorem morphoAccrueFeeWritesReverts (hstack : R.length + 32 ≤ 1024) (hp : ee.perm = true)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp spare) (hb : 64 ≤ spare)
    (hbad : ¬ AccrueFeeWritesFit evm id shares)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13793)
      ([shares, interest, solcAddrMask] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases hpos : (solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee).toNat + shares.toNat < UInt256.size
  · obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccruePositionAddOk (v := v) (by omega) hpos h
    obtain ⟨k2, C2, rd2⟩ := morphoAccruePositionStore (v := v) (by omega) hp rd1
    have hm1 := hm.feePosition σ ee id
    have hs1 := accrueFeePositionState_bridge hs id shares
    by_cases hc : shares.toNat < 2 ^ 128
    · obtain ⟨aw3, k3, C3, rd3⟩ := morphoToUint128Ok (v := v)
        (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
        (by rw [morphoPatchedValidJumps v]; jump_dest) (hm1.alloc64Guard hb) hc rd2
      apply morphoAccrueSharesAddReverts (v := v) (by omega) hc _ rd3
      apply Nat.le_of_not_gt
      intro hsum
      apply hbad
      refine ⟨?_, hc, ?_⟩
      · simpa only [hs.env, ← hs.accounts] using hpos
      · simpa only [hs1.env, ← hs1.accounts] using hsum
    · exact morphoToUint128Reverts (v := v)
        (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
        (hm1.alloc64Guard hb) hm1.size (by rw [hm1.free]; exact hm1.lower)
        hm1.errorGap hm1.errorHi (Nat.le_of_not_gt hc) rd2
  · exact morphoAccruePositionAddReverts (v := v) (by omega) (Nat.le_of_not_gt hpos) h

end Routines
end Benchmarks.Morpho.MorphoBlue
