import Benchmarks.Midnight.WithdrawCollateralRead
import Benchmarks.Midnight.WithdrawCollateralArithmetic
import Benchmarks.Midnight.WithdrawBitmapPhase
import Benchmarks.Midnight.WithdrawReadSource

variable {fork : Ethereum.Fork}

/-! Collateral withdrawal through its balance update, ending at the health check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem withdrawBeforeHealth {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw market array limit root user index assets extra : UInt256}
    {receiver : AccountAddress} {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : SupplyTouchSourceFrame frame m user index assets)
    (hreceiver : frame.locals.get? "receiver" = some (.address receiver))
    (hcanon : user.toNat < EVM.addressModulus)
    (hstack : R.length + 28 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hm : MarketStored mem market array limit m) (hb : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨4472⟩
      ([m.id, user, UInt256.ofNat 4643, user, index, UInt256.ofNat receiver.val, assets,
        market, extra] ++ R) mem aw rdata evm.accountMap k C) :
    (RDrev fork midnightBytecode g s0 ∧
      ExecBlock fork config frame evm (withdrawCollateralTransition.body.drop 5) .reverted) ∨
    (RDstatic fork midnightBytecode g s0 ∧
      ExecBlock fork config frame evm (withdrawCollateralTransition.body.drop 5) .staticViolation) ∨
    ∃ hi : index.toNat < m.collaterals.length, I.perm = true ∧
      ∃ frame' evm' aw' k' C',
        SourceState s0 I evm'.accountMap evm' ∧
        WithdrawSourceFrame frame' m m.id user index assets m.collaterals[index.toNat].token receiver ∧
        TransferBudget root credit (positionReadMemory mem m.id user) aw' C' ∧
        (∀ result, ExecBlock fork config frame' evm' (withdrawCollateralTransition.body.drop 11) result →
          ExecBlock fork config frame evm (withdrawCollateralTransition.body.drop 5) result) ∧
        RD fork midnightBytecode I g s0 ⟨19775⟩
          ([market, m.id, user, UInt256.ofNat 4643, user,
            UInt256.ofNat m.collaterals[index.toNat].token.val, UInt256.ofNat receiver.val,
            assets, m.id, extra] ++ R)
          (positionReadMemory mem m.id user) aw' rdata evm'.accountMap k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  rcases midnightWithdrawCollateralRead (R := extra :: R)
      (by simp only [List.length_cons]; omega) hmem hzero hm hb rd with
    ⟨hbad, hr⟩ | ⟨hi, hi128, aw1, k1, C1, hb1, rd1⟩
  · exact Or.inl ⟨hr, withdrawReadRevert hf hbad⟩
  · have hload : (fun slot ↦ solcSlotWordAt slot evm.accountMap I) =
        EVM.storageLoad evm evm.executionEnv.codeOwner := by
      funext slot
      exact (storageLoad_codeOwner_eq_solcSlotWordAt evm I slot
        (congrArg ExecutionEnv.codeOwner hs.env)).symm
    rw [hload] at rd1
    let old := collateralWord (EVM.storageLoad evm evm.executionEnv.codeOwner) m.id user index
    let token := m.collaterals[index.toNat].token
    let frame1 := supplyPositionFrame frame m.id user token
    have hf1 : WithdrawSourceFrame frame1 m m.id user index assets token receiver :=
      withdrawReadFrame_get hf hreceiver token
    have hread : evalExpr? config frame1 evm (positionCollateralExpr "collateralIndex") =
        .ok (.int old.toNat) :=
      evalPositionCollateral "collateralIndex" hf1.contract hcanon hf1.position hf1.index hi128
    have hold : old.toNat < 2^128 := low128_lt _
    simp only [List.cons_append, List.nil_append] at rd1
    rcases withdrawCollateralArithmetic hs.env (by simp only [List.length_cons]; omega)
        hi128 hold (by jump_dest) rd1 with ⟨hlt, hr⟩ | ⟨hle, hperm, hr⟩ |
          ⟨hle, hperm, k2, C2, hc2, rd2⟩
    · exact Or.inl ⟨hr, withdrawReadSource hf hi (withdrawSubRevert hf1 hread hlt)⟩
    · exact Or.inr (Or.inl ⟨hr, withdrawReadSource hf hi
        (withdrawSubStatic hf1 hread hle hold hcanon hi128 (by rw [hs.env]; exact hperm))⟩)
    · let evm2 := collateralWriteState evm m.id user index (UInt256.sub old assets)
      let frame2 := withdrawSubFrame frame1 (UInt256.sub old assets)
      have hf2 : WithdrawSourceFrame frame2 m m.id user index assets token receiver := hf1.subFrame _
      have hs2 : SourceState s0 I evm2.accountMap evm2 := by
        refine ⟨?_, (collateralWriteState_env ..).trans hs.env, rfl⟩
        simpa only [evm2, collateralWriteState, storageStore_σ₀] using hs.world
      have hnew : frame2.locals.get? "newCollateral" = some (.int (UInt256.sub old assets).toNat) := by
        simp only [frame2, withdrawSubFrame,
          wordLocal_get_ne _ "__c1" "newCollateral" _ (by decide), wordLocal_get]
      obtain ⟨frame3, evm3, k3, C3, hc3, hs3, hf3, hif, rd3⟩ :=
        withdrawBitmapPhase (R := R) hs2 hf2 hnew hcanon hi128 hperm (by omega) rd2
      refine Or.inr (Or.inr ⟨hi, hperm, frame3, evm3, aw1, k3, C3, hs3, hf3,
        (hb1.mono hc2).mono hc3, ?_, rd3⟩)
      intro result htail
      apply withdrawReadSource hf hi
      apply withdrawSubSource hf1 hread hle hold hcanon hi128 (by rw [hs.env]; exact hperm)
      exact ExecBlock.consNormal hif htail

end Benchmarks.Midnight
