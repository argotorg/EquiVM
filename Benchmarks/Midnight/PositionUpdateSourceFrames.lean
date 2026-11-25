import Benchmarks.Midnight.PositionViewSource
import Benchmarks.Midnight.PositionUpdateStorage

variable {fork : Ethereum.Fork}

/-! Source frames through the view call and the two decrease calculations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def positionUpdateFunction : FunctionDecl := contract.functions[10]!

def positionNewCredit (evm : EVM.State) (m : MarketData) (id user : UInt256) : UInt256 :=
  UInt256.sub (low128 (positionPostCredit evm id user)) (positionViewFee evm m id user)

def positionNewPending (evm : EVM.State) (m : MarketData) (id user : UInt256) : UInt256 :=
  UInt256.sub (low128 (positionPostPending evm id user)) (positionViewFee evm m id user)

def positionUpdateTupleFrame (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  resumeAfterInternalCall (positionViewAliasFrame imms m id user) "__c0"
    (some (positionViewReturnValues (positionPostCredit evm id user) (positionPostPending evm id user)
      (positionViewFee evm m id user)))

def positionUpdateValuesFrame (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (positionUpdateTupleFrame evm imms m id user)
    "newCredit" (positionNewCredit evm m id user)) "newPendingFee" (positionNewPending evm m id user))
    "accruedFee" (positionViewFee evm m id user)

def positionCreditDecrease (evm : EVM.State) (m : MarketData) (id user : UInt256) : UInt256 :=
  UInt256.sub (positionFieldWord evm id user 0) (positionNewCredit evm m id user)

def positionPendingDecrease (evm : EVM.State) (m : MarketData) (id user : UInt256) : UInt256 :=
  UInt256.sub (positionFieldWord evm id user 1) (positionNewPending evm m id user)

def positionUpdateCreditFrame (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  wordLocal (positionUpdateValuesFrame evm imms m id user) "creditDecrease" (positionCreditDecrease evm m id user)

def positionUpdateWritesFrame (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) : Frame :=
  wordLocal (positionUpdateCreditFrame evm imms m id user) "pendingFeeDecrease" (positionPendingDecrease evm m id user)

theorem positionUpdateAliasPrefix (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    ABlock fork config evm (positionViewCallFrame imms m id user) positionUpdateFunction.body
      (positionViewAliasFrame imms m id user) (positionUpdateFunction.body.drop 1) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
  apply resolvePositionRef rfl
  · simp [positionViewCallFrame, positionViewArguments]
  · simp [positionViewCallFrame, positionViewArguments, Std.HashMap.getElem_insert]
  · simp [positionViewCallFrame, positionViewArguments, Std.HashMap.getElem_insert]

theorem evalPositionUpdateViewArgs (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256) :
    evalExprs? config (positionViewAliasFrame imms m id user) evm
      [.var "market", .var "id", .var "user"] =
      .ok [Model.marketValue m.value, wordBytes32Value id, .address (AccountAddress.ofNat user.toNat)] := by
  simp [evalExprs?, evalExpr?, positionViewAliasFrame, positionViewCallFrame, positionViewArguments,
    EvalResult.ofOption, EvalResult.bind, pure, bind, Std.HashMap.getElem_insert]

theorem positionUpdateValuesPrefix (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hsafe : PositionViewSourceSafe evm m id user) :
    ABlock fork config evm (positionViewCallFrame imms m id user) positionUpdateFunction.body
      (positionUpdateValuesFrame evm imms m id user) (positionUpdateFunction.body.drop 5) := by
  have hp := sourceNormalStep (fork := fork) (positionUpdateAliasPrefix (fork := fork) evm imms m id user)
    (internalCallFunctionReturn (fork := fork) (callee := positionViewFunction) (locals := positionViewArguments m id user)
      (evalPositionUpdateViewArgs evm imms m id user) rfl rfl
      (positionViewInternalReturns (fork := fork) evm imms m id user hcanon hsafe))
  have ht0 : evalExpr? config (positionUpdateTupleFrame evm imms m id user) evm
      (.tupleGet (.var "__c0") 0) = .ok (.int (positionNewCredit evm m id user).toNat) := by
    simp only [positionUpdateTupleFrame, resumeAfterInternalCall, collapseReturns,
      positionViewReturnValues, evalExpr?, store_get_self, EvalResult.ofOption, EvalResult.bind,
      bind, pure, tupleGetValue?, List.getElem?_cons_zero, positionNewCredit]
  have hp1 := hp.letStep ht0
  have ht1 : evalExpr? config
      (wordLocal (positionUpdateTupleFrame evm imms m id user) "newCredit" (positionNewCredit evm m id user))
      evm (.tupleGet (.var "__c0") 1) = .ok (.int (positionNewPending evm m id user).toNat) := by
    simp [wordLocal, positionUpdateTupleFrame, resumeAfterInternalCall, collapseReturns,
      positionViewReturnValues, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      tupleGetValue?, positionNewPending, Std.HashMap.getElem_insert]
  have hp2 := hp1.letStep ht1
  apply hp2.letStep
  simp [evalExpr?, wordLocal, positionUpdateTupleFrame, resumeAfterInternalCall, collapseReturns,
    positionViewReturnValues, tupleGetValue?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    Std.HashMap.getElem_insert]

theorem positionUpdateViewReverts (evm : EVM.State) (imms : Store) (m : MarketData) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hbad : ¬ PositionViewSourceSafe evm m id user) :
    ExecFuncBody fork config (positionViewCallFrame imms m id user) evm positionUpdateFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply (positionUpdateAliasPrefix evm imms m id user).run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := positionViewFunction)
    (locals := positionViewArguments m id user) (evalPositionUpdateViewArgs evm imms m id user) rfl rfl
    (positionViewInternalReverts evm imms m id user hcanon hbad))

end Benchmarks.Midnight
