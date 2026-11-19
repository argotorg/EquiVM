import Benchmarks.Midnight.WithdrawUnitsRead
import Benchmarks.Midnight.WithdrawUnitsPendingSource
import Reasoning.ExternalCall

/-! Coupling withdrawal's position read and pending-fee branch to source execution. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightWithdrawUnitsPending {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw root fee pending credit id user market units ret saved : UInt256}
    {receiver : AccountAddress} {gasCredit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : WithdrawUnitsSourceFrame frame m id user units receiver)
    (hcanon : user.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 25 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hz : frame.locals.get? "pendingFeeDecrease" = some (.int 0))
    (hb : TransferBudget root gasCredit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨3909⟩
      ([fee, pending, credit, id, user, solcMappingSlot ⟨1⟩ id, market, UInt256.ofNat 64,
        solcAddrMask, UInt256.ofNat receiver.val, units, ret, saved] ++ R)
      mem aw rdata evm.accountMap k C) :
    (RDrev midnightBytecode g s0 ∧
      ExecBlock config frame evm (withdrawTransition.body.drop 9) .reverted) ∨
    ∃ frame' evm' decrease aw' k' C',
      SourceState s0 I evm'.accountMap evm' ∧
      WithdrawUnitsSourceFrame frame' m id user units receiver ∧
      decrease.toNat < 2^128 ∧
      frame'.locals.get? "pendingFeeDecrease" = some (.int decrease.toNat) ∧
      ExecStmt config frame evm (withdrawTransition.body[9]!) (.ok frame' evm') ∧
      TransferBudget root gasCredit (positionReadMemory mem id user) aw' C' ∧
      RD midnightBytecode I g s0 ⟨23403⟩
        ([units, UInt256.ofNat 3993, UInt256.ofNat 4002, uint128Mask,
          positionSlot id user, solcMappingSlot ⟨1⟩ id, id, user, decrease,
          market, UInt256.ofNat 64, solcAddrMask, UInt256.ofNat receiver.val, units, ret, saved] ++ R)
        (positionReadMemory mem id user) aw' rdata evm'.accountMap k' C' := by
  have hload : solcSlotWordAt (positionSlot id user) evm.accountMap I =
      EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user) :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I _
      (congrArg ExecutionEnv.codeOwner hs.env)).symm
  simp only [List.cons_append, List.nil_append] at rd
  obtain ⟨aw1, k1, C1, hb1, hcases⟩ := midnightWithdrawUnitsRead
    (by simp only [List.length_cons]; omega) hmem hzero hb rd
  rw [hload] at hcases
  rcases hcases with ⟨hc, rd1⟩ | ⟨hc, rd1⟩
  · simp only [List.cons_append, List.nil_append] at rd1
    have rd2 := midnightBlocks.midnight_block_3971
      (by simp only [List.length_cons]; omega) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_3971_stack, uint128Mask_computed] at rd2
    refine Or.inr ⟨frame, evm, ⟨0⟩, _, _, _, hs, hf, by decide, hz, ?_, ?_, rd2⟩
    · apply withdrawUnitsPendingZero hf hcanon
      exact congrArg UInt256.toNat hc
    · exact hb1.mono (by omega)
  · simp only [List.cons_append, List.nil_append] at rd1
    have hpos : 0 < (positionFieldWord evm id user 0).toNat := by
      by_contra hn
      apply hc
      apply u256_inj
      change (positionFieldWord evm id user 0).toNat = 0
      omega
    rcases midnightWithdrawPendingReduction
        (by simp only [List.length_cons]; omega) hperm rd1 with
      ⟨hbad, hr⟩ | ⟨hsafe, k2, C2, hc2, rd2⟩
    · exact Or.inl ⟨hr, ExecBlock.consRevert
        (withdrawUnitsPendingReverts hf hcanon hz hpos hbad)⟩
    · let decrease := mulDivUp (positionFieldWord evm id user 1) units
        (positionFieldWord evm id user 0)
      let evm2 := storeHigh128 evm (positionSlot id user)
        (UInt256.sub (positionFieldWord evm id user 1) decrease)
      let frame2 := withdrawUnitsPendingFrame frame decrease
      have hs2 : SourceState s0 I evm2.accountMap evm2 := by
        refine ⟨?_, (storeHigh128_env ..).trans hs.env, rfl⟩
        simpa only [evm2, storeHigh128, storageStore_σ₀] using hs.world
      have hf2 : WithdrawUnitsSourceFrame frame2 m id user units receiver :=
        ((hf.insert "__c2" (.int decrease.toNat) (by decide)).insert
          "__c3" (.int decrease.toNat) (by decide)).insert
            "pendingFeeDecrease" (.int decrease.toNat) (by decide)
      have ha : evm2.accountMap = storeHigh128Accounts evm.accountMap I (positionSlot id user)
          (UInt256.sub (positionFieldWord evm id user 1) decrease) := by
        dsimp only [evm2]
        rw [storeHigh128_accounts, hs.env]
      change RD _ _ _ _ _ _ _ _ _
        (storeHigh128Accounts evm.accountMap I (positionSlot id user)
          (UInt256.sub (positionFieldWord evm id user 1) decrease)) _ _ at rd2
      rw [← ha] at rd2
      simp only [List.cons_append, List.nil_append] at rd2
      have rd3 := midnightBlocks.midnight_block_4248 (by omega) (by jump_dest) rd2
      have rd4 := midnightBlocks.midnight_block_3971
        (by simp only [List.length_cons]; omega)
        (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_3971_stack, uint128Mask_computed] at rd4
      refine Or.inr ⟨frame2, evm2, decrease, _, _, _, hs2, hf2, hsafe.2.1,
        wordLocal_get .., ?_, ?_, rd4⟩
      · exact withdrawUnitsPendingReturns hf hcanon hz hpos hsafe
          (by rw [hs.env]; exact hperm)
      · exact hb1.mono (by omega)

end Benchmarks.Midnight
