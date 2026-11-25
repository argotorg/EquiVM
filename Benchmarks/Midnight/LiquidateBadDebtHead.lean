import Benchmarks.Midnight.LiquidateBadDebtWrite
import Benchmarks.Midnight.LiquidateLossSource
import Benchmarks.Midnight.LiquidateLossTrace
import Benchmarks.Midnight.PackedStorageSourceState
import Benchmarks.Midnight.TransferBudget

variable {fork : Ethereum.Fork}

/-! The initial position-debt write and loss-factor calculation agree with the source. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def liquidateBadDebtMarketWord (evm : State) (id borrower badDebt : UInt256) : UInt256 :=
  let evm' := liquidateBadDebtState evm id borrower badDebt
  Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ id)

theorem midnightLiquidateBadDebtHead {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root debtWord reverseRep rep maxDebt price id dp dl borrower badDebt : UInt256}
    {σ : AccountMap} {k C credit : Nat} {R : List UInt256} (hstack : R.length + 23 ≤ 1024)
    (hcanon : borrower.toNat < EVM.addressModulus) (hc : frame.contract = contract)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id borrower) positionType))
    (hm : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType))
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hdebt : healthPositionWord evm id borrower = debtWord)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨7431⟩
      ([debtWord, reverseRep, rep, maxDebt, price, positionSlot id borrower, dp, dl, borrower, badDebt] ++ R)
      mem aw rdata σ k C) :
    let evm' := liquidateBadDebtState evm id borrower badDebt
    let word := liquidateBadDebtMarketWord evm id borrower badDebt
    let total := low128 word
    let loss := UInt256.shiftRight word ⟨128⟩
    (ExecBlock fork config frame evm (liquidateBadDebtBody.take 5) .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    (ExecBlock fork config frame evm (liquidateBadDebtBody.take 5) .staticViolation ∧
      RDstatic fork midnightBytecode g s0) ∨
    (I.perm = true ∧ ∃ σ' aw' k' C', SourceState s0 I σ' evm' ∧
      ExecBlock fork config frame evm (liquidateBadDebtBody.take 5)
        (.ok (liquidateLossFrame frame total loss badDebt) evm') ∧
      TransferBudget root credit mem aw' C' ∧ RD fork midnightBytecode I g s0 ⟨7541⟩
        ([liquidateNextLoss total loss badDebt, ⟨7571⟩, word, reverseRep, rep, maxDebt,
          price, positionSlot id borrower, dp, dl, borrower, badDebt] ++ R)
        mem aw' rdata σ' k' C') := by
  dsimp only
  rcases midnightLiquidateBadDebtSubtract (R := R) (by omega) rd with
    ⟨hlt, hrev⟩ | ⟨hle, k1, C1, hc1, rd1⟩
  · refine Or.inl ⟨ExecBlock.consRevert (liquidateBadDebtWriteUnderflow hcanon hp hd ?_), hrev⟩
    rw [hdebt]
    exact hlt
  · rcases midnightLiquidateBadDebtWrite (R := R) (by omega) rd1 with
      ⟨hfalse, hstatic⟩ | ⟨htrue, k2, C2, hc2, rd2⟩
    · refine Or.inr (Or.inl ⟨ExecBlock.consStatic
        (liquidateBadDebtWriteStatic hcanon hp hd ?_ ?_), hstatic⟩)
      · rw [hdebt]; exact hle
      · rw [hs.env]; exact hfalse
    · let evm1 := liquidateBadDebtState evm id borrower badDebt
      let word := liquidateBadDebtMarketWord evm id borrower badDebt
      let total := low128 word
      let loss := UInt256.shiftRight word ⟨128⟩
      let σ1 := storeLow128Accounts σ I (positionSlot id borrower + ⟨2⟩)
        (UInt256.sub (low128 debtWord) (low128 badDebt))
      have hs1 : SourceState s0 I σ1 evm1 := by
        simpa only [evm1, σ1, liquidateBadDebtState, hdebt] using
          SourceState.storeLow128 hs (positionSlot id borrower + ⟨2⟩)
            (UInt256.sub (low128 debtWord) (low128 badDebt))
      have hex1 : ExecStmt fork config frame evm (liquidateBadDebtBody[0]!) (.ok frame evm1) :=
        liquidateBadDebtWriteSource hcanon hp hd (by rw [hdebt]; exact hle)
          (by rw [hs.env]; exact htrue)
      have hw : word = solcSlotWordAt (memLoad (UInt256.ofNat 672) mem) σ1 I := by
        rw [hslot]
        exact hs1.storageRead _
      have htotal : marketBalanceWord evm1 id 0 = total := rfl
      have hloss : marketLossWord evm1 id = loss := rfl
      have hsrc := liquidateLossSource (fork := fork) (evm := evm1) hc hm hd []
      simp only [htotal, hloss, List.append_nil] at hsrc
      have hb1 := hb.mono hc1
      have hb2 : TransferBudget root credit mem (M aw (UInt256.ofNat 672) ⟨32⟩) C2 := by
        simp only [memExpansionCost] at hc2
        transfer_budget hb1
      dsimp only [σ1] at hw
      rw [← hw] at rd2
      rcases midnightLiquidateLoss
        (R := ⟨7571⟩ :: word :: reverseRep :: rep :: maxDebt :: price ::
          positionSlot id borrower :: dp :: dl :: borrower :: badDebt :: R)
        (by simp only [List.length_cons]; omega) (low128_lt _) (shiftRight128_lt _) rd2 with
        ⟨hbad, hrev⟩ | ⟨hbd, hnz, k3, C3, hc3, rd3⟩
      · obtain ⟨_, hex⟩ := hsrc.resolve_right (fun h ↦ hbad ⟨h.1, h.2.1⟩)
        exact Or.inl ⟨ExecBlock.consNormal hex1 hex, hrev⟩
      · obtain ⟨_, _, hab⟩ := hsrc.resolve_left (fun h ↦ h.1 ⟨hbd, hnz⟩)
        exact Or.inr (Or.inr ⟨htrue, σ1, _, k3, C3, hs1,
          ExecBlock.consNormal hex1 (hab.run ExecBlock.nil), hb2.mono hc3, rd3⟩)

end Benchmarks.Midnight
