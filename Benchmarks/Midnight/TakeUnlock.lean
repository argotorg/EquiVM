import Benchmarks.Midnight.TakeUnlockSource
import Benchmarks.Midnight.DynamicLockTrace

variable {fork : Ethereum.Fork}

/-! Restore the captured lock state before the final health check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeUnlock {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw root id seller wasLocked ignored : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hsel : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hw : frame.locals.get? "wasLocked" = some (wordToElem .bool wasLocked))
    (hroot : root.toNat + 128 < 2^64) (hlo : 832 ≤ root.toNat) (hperm : I.perm = true)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (ha : MemoryFunding credit mem aw C) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I g s0 ⟨13336⟩
      (ignored :: wasLocked :: R) mem aw rdata σ k C) :
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' : ByteArray)
      (root' aw' : UInt256) (k' C' : Nat),
      ExecStmt fork config frame evm takeTransition.body[71]! (.ok frame' evm') ∧
      frame'.contract = frame.contract ∧
      (∀ name, name ≠ "__c31" → frame'.locals.get? name = frame.locals.get? name) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      (root' = root ∨ root' = root + UInt256.ofNat 128) ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧ MemoryFunding credit mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨13343⟩ R mem' aw' rdata σ' k' C' := by
  have he := takeUnlockCondition_eval (evm := evm) hw
  rw [takeUnlock_shape]
  by_cases hz : wasLocked = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_13336_taken (by omega)
      (by rw [hz]; decide) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (ha.mono (by omega))
    have rd2 := midnightBlocks.midnight_block_13434 (R := R) (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_13434_stack, hid, hseller] at rd2
    obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightDynamicLock true hstack hcanon hroot
      (by omega) (fun _ ↦ hperm) hfree (by jump_dest) ha2 rd2
    have rd4 := midnightBlocks.midnight_block_13450 (by omega) (by jump_dest) rd3
    have ha4 := memoryFundingAt (credit := credit) rd4 (ha3.mono (by omega))
    refine ⟨takeUnlockFrame frame evm id seller, lockExchangeState evm liquidationLockBase id seller
      false, _, _, root + UInt256.ofNat 128, _, _, _, ?_, rfl, ?_,
      sourceState_transientWrite hs _ ⟨0⟩, dynamicLockMemory_prefix .., Or.inr rfl,
      dynamicLockMemory_free .., ha4, rd4⟩
    · exact ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using he)
        (ExecBlock.consNormal (takeUnlockSource hc hcanon hi hsel (by rw [hs.env]; exact hperm))
          ExecBlock.nil)
    · intro name hn
      exact store_get_ne _ _ (by simpa using hn.symm)
  · have rd1 := midnightBlocks.midnight_block_13336_fallthrough (by omega)
      (isZero_eq_zero_of_ne hz) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (ha.mono (by omega))
    exact ⟨frame, evm, σ, mem, root, _, _, _,
      ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using he) ExecBlock.nil,
      rfl, fun _ _ ↦ rfl, hs, MemoryPrefix.refl _ _, Or.inl rfl, hfree, ha1, rd1⟩

theorem midnightTakeReadLock {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw root id seller : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hc : frame.contract = contract) (hcanon : seller.toNat < EVM.addressModulus)
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hsel : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat seller.toNat)))
    (hroot : root.toNat + 128 < 2^64) (hlo : 832 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (ha : MemoryFunding credit mem aw C) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I g s0 ⟨13343⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C',
      ExecStmt fork config frame evm takeTransition.body[72]!
        (.ok (takeLockedFrame frame evm id seller) evm) ∧
      MemoryFunding credit (dynamicLockMemory mem root id seller) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨13359⟩
        (Stele.EVM.transientLoad evm evm.executionEnv.codeOwner
          (lockSlot liquidationLockBase id seller) :: R)
        (dynamicLockMemory mem root id seller) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_13343 (by omega) (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
  simp only [midnightBlocks.midnight_block_13343_stack, hid, hseller] at rd1
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightDynamicLock false hstack hcanon hroot
    (by omega) (by simp) hfree (by jump_dest) ha1 rd1
  rw [← sourceState_transientRead hs] at rd2
  exact ⟨_, _, _, takeLockedSource hc hcanon hi hsel, ha2, rd2⟩

end Benchmarks.Midnight
