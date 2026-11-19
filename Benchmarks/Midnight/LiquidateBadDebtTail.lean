import Benchmarks.Midnight.LiquidateTotalTrace
import Benchmarks.Midnight.LiquidateFees

/-! The loss-factor, total-unit, and continuous-fee writes complete bad-debt recognition. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateBadDebtTail {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root newLoss oldWord reverseRep rep maxDebt price id pos dp dl borrower badDebt : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256} (hstack : R.length + 21 ≤ 1024)
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hl : frame.locals.get? "__c13" = some (.int newLoss.toNat))
    (ho : frame.locals.get? "_lossFactor" = some (.int (UInt256.shiftRight oldWord ⟨128⟩).toNat))
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hp : I.perm = true) (hs : SourceState s0 I σ evm)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨7541⟩
      ([newLoss, ⟨7571⟩, oldWord, reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
      mem aw rdata σ k C) :
    let evm1 := liquidateTotalState evm id newLoss badDebt
    let oldLoss := UInt256.shiftRight oldWord ⟨128⟩
    let amount := liquidateFeeValue evm1 id oldLoss
    let frame1 := wordLocal frame "__c14" badDebt
    (ExecBlock config frame evm (liquidateBadDebtBody.drop 5) .reverted ∧
      RDrev midnightBytecode g s0) ∨
    (∃ σ' aw' k' C',
      SourceState s0 I σ' (marketBalanceStore evm1 id 2 amount) ∧
      ExecBlock config frame evm (liquidateBadDebtBody.drop 5)
        (.ok (liquidateFeeFrame frame1 oldLoss amount) (marketBalanceStore evm1 id 2 amount)) ∧
      TransferBudget root credit mem aw' C' ∧ RD midnightBytecode I g s0 ⟨7768⟩
        ([reverseRep, rep, maxDebt, price, pos, dp, dl, borrower, badDebt] ++ R)
        mem aw' rdata σ' k' C') := by
  dsimp only
  let evm0 := liquidateLossState evm id newLoss
  let evm1 := liquidateTotalState evm id newLoss badDebt
  let σ0 := storeHigh128Accounts σ I (solcMappingSlot ⟨1⟩ id) newLoss
  let total := marketBalanceWord evm0 id 0
  let frame1 := wordLocal frame "__c14" badDebt
  have hs0 : SourceState s0 I σ0 evm0 := SourceState.storeHigh128 hs _ _
  have htotal : total = low128 (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ0 I) := by
    change low128 (Stele.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
      (solcMappingSlot ⟨1⟩ id)) = _
    rw [hs0.storageRead]
    rfl
  have hsource := liquidateTotalSource hc hm hl hd (by rw [hs.env]; exact hp)
  have hrun := midnightLiquidateTotal (R := R) (by omega) hp hb rd
  dsimp only at hrun hsource
  simp only [hslot] at hrun
  dsimp only [σ0] at htotal
  rw [← htotal] at hrun
  have hlist : (liquidateBadDebtBody.drop 5).take 3 ++ liquidateBadDebtBody.drop 8 =
      liquidateBadDebtBody.drop 5 := by
    simpa only [List.drop_drop] using List.take_append_drop 3 (liquidateBadDebtBody.drop 5)
  rcases hrun with ⟨hbad, hrev⟩ | ⟨hfit, hle, aw1, k1, C1, hb1, rd1⟩
  · obtain ⟨_, hex⟩ := hsource.resolve_right (fun h ↦ hbad ⟨h.1, h.2.1⟩)
    refine Or.inl ⟨?_, hrev⟩
    have hfull := execBlockAppendReverted (suff := liquidateBadDebtBody.drop 8) hex
    simpa only [hlist] using hfull
  · obtain ⟨_, _, hex⟩ := hsource.resolve_left (fun h ↦ h.1 ⟨hfit, hle⟩)
    have hs1 : SourceState s0 I (storeLow128Accounts σ0 I (solcMappingSlot ⟨1⟩ id)
        (UInt256.sub total badDebt)) evm1 :=
      SourceState.storeLow128 hs0 _ _
    have hm1 : frame1.locals.get? "_marketState" =
        some (.storageRef (marketStateRef id) marketStateType) := by
      simpa only [frame1, wordLocal_get_ne _ _ _ _ (show "__c14" ≠ "_marketState" by decide)] using hm
    have ho1 : frame1.locals.get? "_lossFactor" =
        some (.int (UInt256.shiftRight oldWord ⟨128⟩).toNat) := by
      simpa only [frame1, wordLocal_get_ne _ _ _ _ (show "__c14" ≠ "_lossFactor" by decide)] using ho
    rcases midnightLiquidateFees (frame := frame1)
      (R := reverseRep :: rep :: maxDebt :: price :: pos :: dp :: dl :: borrower :: badDebt :: R)
      (by simp only [List.length_cons]; omega) hp hzero hslot hc hm1 ho1 hs1 hb1 rd1 with
      ⟨hex1, hrev⟩ | ⟨σ2, aw2, k2, C2, hs2, hex1, hb2, rd2⟩
    · refine Or.inl ⟨?_, hrev⟩
      have hfull := execBlock_append_ok hex hex1
      simpa only [hlist] using hfull
    · refine Or.inr ⟨σ2, aw2, k2, C2, hs2, ?_, hb2, rd2⟩
      have hfull := execBlock_append_ok hex hex1
      simpa only [hlist] using hfull

end Benchmarks.Midnight
