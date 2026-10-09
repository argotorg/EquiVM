import Benchmarks.Morpho.MorphoBlue.AccrueSourceMath
import Benchmarks.Morpho.MorphoBlue.AccrueFeePosition
import Benchmarks.Morpho.MorphoBlue.SharesDownSource
import Benchmarks.Morpho.MorphoBlue.StateBlock

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev accrueFeeBody : List Stmt :=
  match accrueIrmBody[10]! with
  | .ite _ yes _ => yes
  | _ => []

theorem morphoAccrueFeeAmountStep (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (interest : UInt256) (hl : MarketLocals p locals)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "interest") = .ok (.int (Int.ofNat interest.toNat)))
    (hf : interest.toNat * (marketFieldWord evm.accountMap evm.executionEnv p.id 5).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[0]!
      (.ok { contract := contract, locals := locals.insert "feeAmount" (.int (Int.ofNat
        (wMulDownResult interest (marketFieldWord evm.accountMap evm.executionEnv p.id 5)).toNat)), immutables := imms } evm) :=
  morphoWMulDownCallOk _ _ evm locals imms _ _ _ hi (hl.evalField imms evm ⟨5, by decide⟩) hf

theorem morphoAccrueFeeAmountReverts (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (interest : UInt256) (hl : MarketLocals p locals)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "interest") = .ok (.int (Int.ofNat interest.toNat)))
    (hf : UInt256.size ≤ interest.toNat * (marketFieldWord evm.accountMap evm.executionEnv p.id 5).toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[0]! .reverted :=
  morphoWMulDownCallReverts _ _ evm locals imms _ _ _ hi (hl.evalField imms evm ⟨5, by decide⟩) hf

theorem morphoAccrueFeeSharesStep (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (fee : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "feeAmount") = .ok (.int (Int.ofNat fee.toNat)))
    (hsub : fee.toNat ≤ (marketFieldWord evm.accountMap evm.executionEnv p.id 0).toNat)
    (hfit : SharesDownFits fee (UInt256.sub (marketFieldWord evm.accountMap evm.executionEnv p.id 0) fee)
      (marketFieldWord evm.accountMap evm.executionEnv p.id 1)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[1]!
      (.ok { contract := contract, locals := locals.insert "__c6" (.int (Int.ofNat
        (sharesDownWord fee (UInt256.sub (marketFieldWord evm.accountMap evm.executionEnv p.id 0) fee)
          (marketFieldWord evm.accountMap evm.executionEnv p.id 1)).toNat)), immutables := imms } evm) :=
  morphoSharesDownCallOk _ _ _ evm locals imms _ _ _ _ he
    (evalExpr_uint256_sub (hl.evalField imms evm ⟨0, by decide⟩) he hsub)
    (hl.evalField imms evm ⟨1, by decide⟩) hfit

theorem morphoAccrueFeeSharesUnderflow (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (fee : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "feeAmount") = .ok (.int (Int.ofNat fee.toNat)))
    (hsub : (marketFieldWord evm.accountMap evm.executionEnv p.id 0).toNat < fee.toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[1]! .reverted := by
  apply ExecStmt.internalCallArgsRevert
  have hbad := evalCheckedSubUnderflow (hl.evalField imms evm ⟨0, by decide⟩) he hsub
  simp only [marketFieldName] at hbad
  simp only [evalExprs?, he, hbad, pure, bind, EvalResult.bind]

theorem morphoAccrueFeeSharesReverts (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (fee : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "feeAmount") = .ok (.int (Int.ofNat fee.toNat)))
    (hsub : fee.toNat ≤ (marketFieldWord evm.accountMap evm.executionEnv p.id 0).toNat)
    (hbad : ¬ SharesDownFits fee (UInt256.sub (marketFieldWord evm.accountMap evm.executionEnv p.id 0) fee)
      (marketFieldWord evm.accountMap evm.executionEnv p.id 1)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[1]! .reverted :=
  morphoSharesDownCallReverts _ _ _ evm locals imms _ _ _ _ he
    (evalExpr_uint256_sub (hl.evalField imms evm ⟨0, by decide⟩) he hsub)
    (hl.evalField imms evm ⟨1, by decide⟩) hbad

theorem morphoAccrueFeeAssignLocal (locals imms : Store) (evm : EVM.State) (shares : UInt256) (old : Value)
    (hg : locals.get? "feeShares" = some old)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "__c6") = .ok (.int (Int.ofNat shares.toNat))) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[2]!
      (.ok { contract := contract, locals := locals.insert "feeShares" (.int (Int.ofNat shares.toNat)), immutables := imms } evm) :=
  ExecStmt.assign he (assignLocalWord hg)

theorem MarketLocals.evalFeeRecipient {p : MarketParamsWords} {locals : Store}
    (hl : MarketLocals p locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"feeRecipient", []⟩) =
      .ok (.address (AccountAddress.ofNat (accrueFeeRecipient evm.accountMap evm.executionEnv).toNat)) :=
  evalMorphoAddress evm locals imms "feeRecipient" ⟨1⟩ hl.feeRecipient rfl rfl

theorem MarketLocals.evalFeePosition {p : MarketParamsWords} {locals : Store}
    (hl : MarketLocals p locals) (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"position", [.mindex (.var "id"), .mindex (.storage ⟨"feeRecipient", []⟩), .field "supplyShares"]⟩) =
      .ok (.int (Int.ofNat (solcSlotWordAt (accrueFeePositionSlot evm.accountMap evm.executionEnv p.id)
        evm.accountMap evm.executionEnv).toNat)) :=
  evalMorphoPositionField evm locals imms _ _ p.id _ ⟨0, by decide⟩ hl.position
    (hl.evalId imms evm) (hl.evalFeeRecipient imms evm) (solcAddrMask_result_canonical _)

theorem morphoAccrueFeePositionAssign (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (shares : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "feeShares") = .ok (.int (Int.ofNat shares.toNat)))
    (hfit : (solcSlotWordAt (accrueFeePositionSlot evm.accountMap evm.executionEnv p.id)
      evm.accountMap evm.executionEnv).toNat + shares.toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[3]!
      (.ok { contract := contract, locals := locals, immutables := imms }
        (storePositionSupplyShares evm p.id (accrueFeeRecipient evm.accountMap evm.executionEnv)
          (solcSlotWordAt (accrueFeePositionSlot evm.accountMap evm.executionEnv p.id) evm.accountMap evm.executionEnv + shares))) := by
  apply ExecStmt.assign (checkedAddSourceOk (hl.evalFeePosition imms evm) he hfit)
  exact assignPositionSupplyShares evm locals imms _ _ p.id _ _ (solcAddrMask_result_canonical _)
    hl.position (hl.evalId imms evm) (hl.evalFeeRecipient imms evm)

theorem morphoAccrueFeePositionReverts (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (shares : UInt256) (hl : MarketLocals p locals)
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "feeShares") = .ok (.int (Int.ofNat shares.toNat)))
    (hover : UInt256.size ≤ (solcSlotWordAt (accrueFeePositionSlot evm.accountMap evm.executionEnv p.id)
      evm.accountMap evm.executionEnv).toNat + shares.toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueFeeBody[3]! .reverted :=
  ExecStmt.assignExprRevert (checkedAddSourceOverflow (hl.evalFeePosition imms evm) he hover)

end Benchmarks.Morpho.MorphoBlue
