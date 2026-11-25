import Benchmarks.Midnight.LiquidateThresholdSource
import Benchmarks.Midnight.LiquidateThresholdTrace
import Benchmarks.Midnight.LiquidateRecoverableTrace
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-! Paired execution of the recovery-threshold branch after repayment exceeds the cap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateThresholdStep {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw id index seized repaid borrower mode bitmap maxDebt price
      originalDebt badDebt lif cap flag dp dl receiverWord selector root : UInt256} {credit : Nat}
    {receiver callback : AccountAddress} {data : ByteArray} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 22 ≤ 1024)
    (hf : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt)
    (hl : frame.locals.get? "lif" = some (.int lif.toNat))
    (hcap : frame.locals.get? "maxRepaid" = some (.int cap.toNat))
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hd : decodeCalldataMarket I.calldata 4 = some m) (hi : calldataWord I.calldata 36 = index)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨7188⟩
      ([price, lif, cap, flag, positionSlot id borrower, dp, dl, borrower, badDebt,
        receiverWord, mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm liquidateThresholdBody .reverted ∧ RDrev fork midnightBytecode g s0) ∨
    ∃ frame' k' C', ExecBlock fork config frame evm liquidateThresholdBody (.ok frame' evm) ∧
      LiquidateSourceFrame frame' m id index seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' bitmap maxDebt price originalDebt badDebt ∧
      TransferBudget root credit mem aw C' ∧
      RD fork midnightBytecode I g s0 ⟨6744⟩
        ([selector, selector, selector, selector, positionSlot id borrower, dp, dl, borrower,
          badDebt, receiverWord, mode, selector] ++ R) mem aw rdata σ k' C' := by
  have htrace := midnightLiquidateRecoverable
    (R := [dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hi rd
  have hload : (fun slot ↦ solcSlotWordAt slot σ I) =
      Stele.EVM.storageLoad evm evm.executionEnv.codeOwner := funext (fun slot ↦ (hs.storageRead slot).symm)
  rw [hload] at htrace
  have hsource := liquidateRecoverableSource (fork := fork) (evm := evm)
    hf.contract hcanon hf.position hf.index ha.price hl
  rcases htrace with ⟨hbad, hrev⟩ | ⟨hidx, hsafe, k1, C1, hc1, rd1⟩
  · rcases hsource with ⟨_, hsrev⟩ | ⟨hi', hs', _⟩
    · refine Or.inl ⟨?_, hrev⟩
      simpa only [List.take_append_drop] using
        (execBlockAppendReverted (suff := liquidateThresholdBody.drop 2) hsrev)
    · exact (hbad ⟨hi', hs'⟩).elim
  · rcases hsource with ⟨hbad, _⟩ | ⟨_, _, hprefix⟩
    · exact (hbad ⟨hidx, hsafe⟩).elim
    · let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
        (positionSlot id borrower + ⟨3⟩) index
      let f1 := liquidateRecoverableFrame frame collateral price lif
      have hf1 : LiquidateSourceFrame f1 m id index seized repaid borrower mode receiver callback data :=
        (hf.insert _ _ (by decide)).insert _ _ (by decide)
      have ha1 : LiquidateAccumulators f1 bitmap maxDebt price originalDebt badDebt :=
        (ha.insert _ _ (by decide)).insert _ _ (by decide)
      have hcap1 : f1.locals.get? "maxRepaid" = some (.int cap.toNat) := by
        simpa only [f1, liquidateRecoverableFrame,
          wordLocal_get_ne _ _ _ _ (show "repayable" ≠ "maxRepaid" by decide),
          wordLocal_get_ne _ _ _ _ (show "value" ≠ "maxRepaid" by decide)] using hcap
      have hrep1 : f1.locals.get? "repayable" =
          some (.int (liquidateRecoverable collateral price lif).toNat) := wordLocal_get _ _ _
      have hs1 := liquidateThresholdSource (fork := fork) (evm := evm) hf1.contract hf1.market hrep1 hcap1
      rcases midnightLiquidateThreshold (R := R) (by omega) hd rd1 with
        ⟨hbad, hrev⟩ | ⟨hsafe, k2, C2, hc2, rd2⟩
      · rcases hs1 with ⟨_, hsrev⟩ | ⟨hsafe, _⟩
        · refine Or.inl ⟨?_, hrev⟩
          simpa only [List.take_append_drop] using execBlockAppendRevert hprefix hsrev
        · exact (hbad hsafe).elim
      · rcases hs1 with ⟨hbad, _⟩ | ⟨_, hsok⟩
        · exact (hbad hsafe).elim
        · refine Or.inr ⟨_, k2, C2, ?_,
            hf1.insert "remainder"
              (.int (zeroFloorSubWord (liquidateRecoverable collateral price lif) cap).toNat) (by decide),
            ha1.insert "remainder"
              (.int (zeroFloorSubWord (liquidateRecoverable collateral price lif) cap).toNat) (by decide),
            hb.mono (by omega), rd2⟩
          simpa only [List.take_append_drop] using execBlockAppendOk hprefix hsok

end Benchmarks.Midnight
