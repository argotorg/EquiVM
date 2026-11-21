import Benchmarks.Midnight.PositionViewTrace
import Benchmarks.Midnight.PositionUpdateDecrease

/-! The internal position update's call to the position-view routine. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionUpdateView {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr id user ret maturity : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 27 ≤ 1024)
    (hcanon : user.toNat < EVM.addressModulus)
    (hlo : 64 ≤ (ptr + UInt256.ofNat 128).toNat)
    (hhi : (ptr + UInt256.ofNat 128).toNat + 32 ≤ mem.size)
    (hmaturity : memLoad (ptr + UInt256.ofNat 128) mem = maturity)
    (rd : RD midnightBytecode I g s0 ⟨23599⟩ (ptr :: id :: user :: ret :: R)
      mem aw rdata σ k C) :
    let w0 := solcSlotWordAt (positionSlot id user) σ I
    let w1 := solcSlotWordAt (positionSlot id user + ⟨1⟩) σ I
    let credit := low128 w0
    let pending := UInt256.shiftRight w0 (UInt256.ofNat 128)
    let lastLoss := low128 w1
    let loss := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)
    let lastAccrual := UInt256.shiftRight w1 (UInt256.ofNat 128)
    let time := UInt256.ofNat I.header.timestamp
    let pc := slashCredit credit lastLoss loss
    let pp := slashPending credit pending pc
    let fee := positionAccruedFee pp lastAccrual maturity time
    (¬ PositionViewSafe credit pending lastLoss loss lastAccrual maturity time ∧ RDrev midnightBytecode g s0) ∨
    (PositionViewSafe credit pending lastLoss loss lastAccrual maturity time ∧ ∃ aw' k' C',
      RD midnightBytecode I g s0 ⟨23680⟩
        ([fee, UInt256.sub (low128 pp) fee, UInt256.sub (low128 pc) fee,
          updatePositionTopic, id, positionSlot id user, solcAddrMask, ret, ⟨96⟩, user] ++ R)
        (positionSlashMemory (positionReadMemory mem id user) id user lastLoss) aw' rdata σ k' C') := by
  have hs : 64 ≤ mem.size := by omega
  have hh0 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) =
      solcMappingSlot ⟨0⟩ id := twoWordHashMem_mapSlot_of_ge64 id ⟨0⟩ hs
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem user (solcMappingSlot ⟨0⟩ id) (twoWordHashMem id ⟨0⟩ mem)) = positionSlot id user :=
    twoWordHashMem_mapSlot_of_ge64 user (solcMappingSlot ⟨0⟩ id) (by
      rw [twoWordHashMem_size_of_ge_64 _ _ hs]; exact hs)
  have rd1 := midnightBlocks.midnight_block_23599 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_23599_stack, midnightBlocks.midnight_block_23599_memory,
    addressMask_computed, solcAddrMask_clean hcanon,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl,
    wordAt0_fold, twoWordHash_fold, hh0, hh1] at rd1
  have hm : memLoad (ptr + UInt256.ofNat 128) (positionReadMemory mem id user) = maturity := by
    rw [positionReadMemory, memLoad_twoWordHashMem _ _ _ hlo (by
      rw [twoWordHashMem_size_of_ge_64 _ _ hs]; exact hhi),
      memLoad_twoWordHashMem _ _ _ hlo hhi, hmaturity]
  exact midnightPositionViewInternal (by simp only [List.append, List.length_cons]; omega) hcanon hlo
    (by rw [positionReadMemory_size _ _ _ hs]; exact hhi) hm (by jump_dest) rd1

end Benchmarks.Midnight
