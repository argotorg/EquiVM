import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesAllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl

/-! Elapsed time, the accrual condition, and the balance reader's final return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def marketElapsedExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩)
    (.binary .sub (.env .timestamp) (.field (.var "market") "lastUpdate"))

def marketAccrualCondition : Expr :=
  .binary .and
    (.binary .and (.binary .ne (.var "elapsed") (.intLit 0))
      (.binary .ne (.field (.var "market") "totalBorrowAssets") (.intLit 0)))
    (.binary .ne (.field (.var "marketParams") "irm") (.cast (.intLit 0) (.elem .address)))

def marketBalanceFields : List Expr :=
  [.field (.var "market") "totalSupplyAssets", .field (.var "market") "totalSupplyShares",
   .field (.var "market") "totalBorrowAssets", .field (.var "market") "totalBorrowShares"]

def marketAccrualSourceBody : List Stmt :=
  match (Syntax.contractSyntax.functions[55]!).body[3]! with
  | .ite _ yes _ => yes
  | _ => []

def marketAccrualBody : List Stmt :=
  allocationBody marketBalancesAllocationCalls
    (fun name ↦ if name == "market" then 384 else if name == "borrowRateView" then 32 else 0)
    marketAccrualSourceBody

theorem allocatedMarketBalances_tail :
    allocatedMarketBalancesFunction.body.drop 3 =
      [.letDecl "elapsed" (some abiUInt256) marketElapsedExpr,
       .ite marketAccrualCondition marketAccrualBody [],
       .return [.tupleLit marketBalanceFields, .var cursorName]] := by
  let reserves := fun name ↦
    if name == "market" then 384 else if name == "borrowRateView" then 32 else 0
  have hsplit (yes : List Stmt) :
      allocationBody marketBalancesAllocationCalls reserves
        [.internalCall "MarketParamsLib_id" [.var "marketParams"] "id",
         .externalCall (.var "morpho") "market" (.intLit 0) [.var "id"] "market" false,
         .letDecl "elapsed" (some abiUInt256) marketElapsedExpr,
         .ite marketAccrualCondition yes [], .return marketBalanceFields] =
        [.internalCall "MarketParamsLib_id" [.var "marketParams"] "id",
         .externalCall (.var "morpho") "market" (.intLit 0) [.var "id"] "market" false,
         reserveBytes 384, .letDecl "elapsed" (some abiUInt256) marketElapsedExpr,
         .ite marketAccrualCondition (allocationBody marketBalancesAllocationCalls reserves yes) [],
         .return [.tupleLit marketBalanceFields, .var cursorName]] := by
    simp [allocationBody, allocationStatement, marketBalancesAllocationCalls, reserves,
      returnValueExpr, marketBalanceFields]
  have hb := hsplit marketAccrualSourceBody
  change allocatedMarketBalancesFunction.body = _ at hb
  rw [hb]
  rfl

-- GENERALIZES Reasoning.SolmArithmetic.evalExpr_ne_int_true/false to arbitrary frames.
theorem wordNeSource {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg frame evm (.binary .ne lhs rhs) = .ok (.bool (decide (a ≠ b))) := by
  have hinj : a.toNat = b.toNat ↔ a = b := ⟨u256_inj, fun h ↦ congrArg UInt256.toNat h⟩
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp [ha, hb, bind, EvalResult.bind, uint256Value, evalBinaryOp?, BEq.beq, hinj]

def marketBalancesElapsed (evm : State) (out : ByteArray) : UInt256 :=
  UInt256.sub (UInt256.ofNat evm.executionEnv.header.timestamp) (calldataWord out 128)

def marketAccrues (p : MarketParamsData) (elapsed : UInt256) (out : ByteArray) : Prop :=
  elapsed ≠ ⟨0⟩ ∧ calldataWord out 64 ≠ ⟨0⟩ ∧ p.irm ≠ AccountAddress.ofNat 0

instance (p : MarketParamsData) (elapsed : UInt256) (out : ByteArray) :
    Decidable (marketAccrues p elapsed out) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def marketBalancesElapsedFrame (frame : Frame) (elapsed : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "elapsed" (uint256Value elapsed) }

theorem marketFieldSource {cfg : Config} {frame : Frame} {evm : State}
    {out : ByteArray} {name : Ident} {value : Value}
    (hmarket : frame.locals.get? "market" = some (marketValue out))
    (hfield : lookupField? (marketValue out) name = some value) :
    evalExpr? cfg frame evm (.field (.var "market") name) = .ok value := by
  have he : evalExpr? cfg frame evm (.var "market") = .ok (marketValue out) := by
    simp only [evalExpr?, hmarket, EvalResult.ofOption]
  exact evalExpr_structField he hfield

-- LIBRARY CANDIDATE: the source timestamp uses the EVM's word truncation.
theorem timestampSource (cfg : Config) (frame : Frame) (evm : State) :
    evalExpr? cfg frame evm (.env .timestamp) =
      .ok (uint256Value (UInt256.ofNat evm.executionEnv.header.timestamp)) := by
  simp only [evalExpr?, pure, envValue, uint256Value]

theorem marketElapsedSource {cfg : Config} {frame : Frame} {evm : State} {out : ByteArray}
    (hmarket : frame.locals.get? "market" = some (marketValue out))
    (hle : (calldataWord out 128).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? cfg frame evm marketElapsedExpr =
      .ok (uint256Value (marketBalancesElapsed evm out)) :=
  evalExpr_uint256_sub (timestampSource cfg frame evm) (marketFieldSource hmarket rfl) hle

theorem marketElapsedSourceRevert {cfg : Config} {frame : Frame} {evm : State}
    {out : ByteArray} (hmarket : frame.locals.get? "market" = some (marketValue out))
    (hlt : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (calldataWord out 128).toNat) :
    evalExpr? cfg frame evm marketElapsedExpr = .revert :=
  checkedSubSourceUnderflow (timestampSource cfg frame evm) (marketFieldSource hmarket rfl) hlt

theorem marketAccrualSource {cfg : Config} {frame : Frame} {evm : State}
    {p : MarketParamsData} {out : ByteArray} {elapsed : UInt256}
    (hmarket : frame.locals.get? "market" = some (marketValue out))
    (hparams : frame.locals.get? "marketParams" = some p.value)
    (helapsed : frame.locals.get? "elapsed" = some (uint256Value elapsed)) :
    evalExpr? cfg frame evm marketAccrualCondition =
      .ok (.bool (decide (marketAccrues p elapsed out))) := by
  have he := wordNeSource
    (show evalExpr? cfg frame evm (.var "elapsed") = .ok (uint256Value elapsed) by
      simp only [evalExpr?, helapsed, EvalResult.ofOption])
    (show evalExpr? cfg frame evm (.intLit 0) = .ok (uint256Value ⟨0⟩) by
      simp only [evalExpr?, pure]; rfl)
  have hm := wordNeSource (evalExpr_structField
    (show evalExpr? cfg frame evm (.var "market") = .ok (marketValue out) by
      simp only [evalExpr?, hmarket, EvalResult.ofOption])
    (show lookupField? (marketValue out) "totalBorrowAssets" =
      some (uint256Value (calldataWord out 64)) from rfl))
    (show evalExpr? cfg frame evm (.intLit 0) = .ok (uint256Value ⟨0⟩) by
      simp only [evalExpr?, pure]; rfl)
  have hp := evalExpr_addressNe (evalExpr_structField
    (show evalExpr? cfg frame evm (.var "marketParams") = .ok p.value by
      simp only [evalExpr?, hparams, EvalResult.ofOption])
    (show lookupField? p.value "irm" = some (.address p.irm) from rfl))
    (show evalExpr? cfg frame evm (.cast (.intLit 0) (.elem .address)) =
      .ok (.address (AccountAddress.ofNat 0)) by
        simp only [evalExpr?, bind, EvalResult.bind, pure]; rfl)
  simpa only [marketAccrues, Bool.decide_and, Bool.and_assoc, marketAccrualCondition] using
    boolAndSource (boolAndSource he hm) hp

def marketBalancesValue (out : ByteArray) : Value :=
  .tuple [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32),
    uint256Value (calldataWord out 64), uint256Value (calldataWord out 96)]

theorem marketBalancesReturn {cfg : Config} {frame : Frame} {evm : State}
    {out : ByteArray} {cursor : UInt256}
    (hmarket : frame.locals.get? "market" = some (marketValue out))
    (hcursor : frame.locals.get? cursorName = some (uint256Value cursor)) :
    ExecBlock cfg frame evm [.return [.tupleLit marketBalanceFields, .var cursorName]]
      (.returned frame evm [marketBalancesValue out, uint256Value cursor]) := by
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, evalExprList?, marketBalanceFields,
    hmarket, hcursor, EvalResult.ofOption,
    bind, EvalResult.bind, marketValue, marketFields, lookupField?,
    pure, marketBalancesValue]
  rfl

def marketBalancesAfterElapsed : List Stmt :=
  [.ite marketAccrualCondition marketAccrualBody [],
   .return [.tupleLit marketBalanceFields, .var cursorName]]

theorem marketBalancesElapsedPrefix {cfg : Config} {frame : Frame} {evm : State}
    {out : ByteArray} (hmarket : frame.locals.get? "market" = some (marketValue out))
    (hle : (calldataWord out 128).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    ABlock cfg evm frame (allocatedMarketBalancesFunction.body.drop 3)
      (marketBalancesElapsedFrame frame (marketBalancesElapsed evm out))
      marketBalancesAfterElapsed := by
  constructor
  intro result htail
  rw [allocatedMarketBalances_tail]
  exact ExecBlock.consNormal (ExecStmt.letDecl (marketElapsedSource hmarket hle)) htail

theorem marketBalancesTailNoAccrual {cfg : Config} {frame : Frame} {evm : State}
    {p : MarketParamsData} {out : ByteArray} {cursor : UInt256}
    (hmarket : frame.locals.get? "market" = some (marketValue out))
    (hparams : frame.locals.get? "marketParams" = some p.value)
    (hcursor : frame.locals.get? cursorName = some (uint256Value cursor))
    (hle : (calldataWord out 128).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hno : ¬ marketAccrues p (marketBalancesElapsed evm out) out) :
    ExecBlock cfg frame evm (allocatedMarketBalancesFunction.body.drop 3)
      (.returned (marketBalancesElapsedFrame frame (marketBalancesElapsed evm out)) evm
        [marketBalancesValue out, uint256Value cursor]) := by
  apply (marketBalancesElapsedPrefix hmarket hle).run
  have hm : (marketBalancesElapsedFrame frame (marketBalancesElapsed evm out)).locals.get?
      "market" = some (marketValue out) := by
    rw [marketBalancesElapsedFrame, store_get_ne _ _ (by decide)]; exact hmarket
  have hp : (marketBalancesElapsedFrame frame (marketBalancesElapsed evm out)).locals.get?
      "marketParams" = some p.value := by
    rw [marketBalancesElapsedFrame, store_get_ne _ _ (by decide)]; exact hparams
  have hc : (marketBalancesElapsedFrame frame (marketBalancesElapsed evm out)).locals.get?
      cursorName = some (uint256Value cursor) := by
    rw [marketBalancesElapsedFrame, store_get_ne _ _ (by decide)]; exact hcursor
  apply ExecBlock.consNormal (ExecStmt.iteFalse
    (by rw [marketAccrualSource hm hp (store_get_self _ _ _)]; simp only [hno, decide_false])
    ExecBlock.nil)
  exact marketBalancesReturn hm hc

theorem marketBalancesTailUnderflow {cfg : Config} {frame : Frame} {evm : State}
    {out : ByteArray} (hmarket : frame.locals.get? "market" = some (marketValue out))
    (hlt : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (calldataWord out 128).toNat) :
    ExecBlock cfg frame evm (allocatedMarketBalancesFunction.body.drop 3) .reverted := by
  rw [allocatedMarketBalances_tail]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert (marketElapsedSourceRevert hmarket hlt))

theorem allocatedMarketBalancesReserveFrame_market (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) (out : ByteArray) :
    (allocatedMarketBalancesReserveFrame imms morpho p ptr out).locals.get? "market" =
      some (marketValue out) := by
  rw [allocatedMarketBalancesReserveFrame, store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem allocatedMarketBalancesReserveFrame_params (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (ptr : UInt256) (out : ByteArray) :
    (allocatedMarketBalancesReserveFrame imms morpho p ptr out).locals.get? "marketParams" =
      some p.value := by
  simp only [allocatedMarketBalancesReserveFrame, allocatedMarketBalancesDecodedFrame,
    allocatedMarketBalancesCallFrame, allocatedMarketBalancesFrame,
    store_get_ne _ _ (by decide : (cursorName == "marketParams") = false),
    store_get_ne _ _ (by decide : ("market" == "marketParams") = false),
    store_get_ne _ _ (by decide : ("id" == "marketParams") = false),
    store_get_ne _ _ (by decide : ("morpho" == "marketParams") = false), store_get_self]

theorem allocatedMarketBalancesBodyNoAccrual {imms : Store} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr : UInt256} {evm evm' : State} {out : ByteArray}
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value p.id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "market" out = some [marketValue out])
    (hfit : allocationFits ptr ⟨384⟩)
    (hle : (calldataWord out 128).toNat ≤
      (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat)
    (hno : ¬ marketAccrues p (marketBalancesElapsed evm' out) out) :
    ExecFuncBody config (allocatedMarketBalancesFrame imms morpho p ptr) evm
      allocatedMarketBalancesFunction.body
      (.returned (marketBalancesElapsedFrame
        (allocatedMarketBalancesReserveFrame imms morpho p ptr out)
        (marketBalancesElapsed evm' out)) evm'
        (some [marketBalancesValue out, uint256Value (nextCursor ptr ⟨384⟩)])) := by
  apply ExecFuncBody.execBlockRet
  apply allocatedMarketBalancesAllocationPrefix hcall hdecode hfit
  exact marketBalancesTailNoAccrual
    (allocatedMarketBalancesReserveFrame_market imms morpho p ptr out)
    (allocatedMarketBalancesReserveFrame_params imms morpho p ptr out)
    (store_get_self _ _ _) hle hno

theorem allocatedMarketBalancesBodyTimeUnderflow {imms : Store} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr : UInt256} {evm evm' : State} {out : ByteArray}
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value p.id]
      (true, evm', out) false)
    (hdecode : config.externalABI.decode? "market" out = some [marketValue out])
    (hfit : allocationFits ptr ⟨384⟩)
    (hlt : (UInt256.ofNat evm'.executionEnv.header.timestamp).toNat <
      (calldataWord out 128).toNat) :
    ExecFuncBody config (allocatedMarketBalancesFrame imms morpho p ptr) evm
      allocatedMarketBalancesFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply allocatedMarketBalancesAllocationPrefix hcall hdecode hfit
  exact marketBalancesTailUnderflow
    (allocatedMarketBalancesReserveFrame_market imms morpho p ptr out) hlt

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
