import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStorage
import Benchmarks.Morpho.MetaMorphoV1_1.CuratorRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.DomainSource

/-! Source frames and guard expressions for submitting market removal. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def marketRemovalStructExpr : Expr :=
  .structLit "MarketParams"
    [("loanToken", .tupleGet (.var "marketParams") 0),
      ("collateralToken", .tupleGet (.var "marketParams") 1),
      ("oracle", .tupleGet (.var "marketParams") 2),
      ("irm", .tupleGet (.var "marketParams") 3),
      ("lltv", .tupleGet (.var "marketParams") 4)]

def marketRemovalTimeExpr : Expr :=
  .cast (.inRange (.uint ⟨256, by decide⟩)
    (.binary .add (.env .timestamp) (.storage ⟨"timelock", []⟩)))
    (.elem (.int (.uint ⟨64, by decide⟩)))

def marketRemovalTimeCondition (pending : Bool) : Expr :=
  .binary .eq (.storage ⟨if pending then "pendingCap" else "config",
    [.mindex (.var "id"), .field (if pending then "validAt" else "removableAt")]⟩) (.intLit 0)

def marketRemovalCapCondition : Expr :=
  .binary .eq (.storage ⟨"config", [.mindex (.var "id"), .field "cap"]⟩) (.intLit 0)

def marketRemovalEnabledExpr : Expr :=
  .storage ⟨"config", [.mindex (.var "id"), .field "enabled"]⟩

def marketRemovalGuards : List Stmt :=
  [.require (marketRemovalTimeCondition false), .require marketRemovalCapCondition,
    .require marketRemovalEnabledExpr, .require (marketRemovalTimeCondition true)]

def marketRemovalTail : List Stmt :=
  [.assign .storage ⟨"config", [.mindex (.var "id"), .field "removableAt"]⟩
      marketRemovalTimeExpr,
    .internalCall "_msgSender" [] "__c3", .emit "SubmitMarketRemoval" [.var "__c3", .var "id"]]

def marketRemovalBody : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
    .letDecl "__calldata" (some .bytes) (.env .msgData),
    .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
      (.intLit (Int.ofNat (2 ^ 255 + 4)))),
    .letDecl "marketParams" none marketRemovalStructExpr,
    .internalCall "_checkCuratorRole" [] "__role",
    .internalCall "MarketParamsLib_id" [.var "marketParams"] "id"] ++
      marketRemovalGuards ++ marketRemovalTail

theorem marketRemovalBody_eq : submitMarketRemovalTransition.body = marketRemovalBody := rfl

def marketRemovalCalldataFrame (evm : State) (imms : Store) (out : ByteArray) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))).insert
      "__calldata" (.bytes evm.executionEnv.calldata)
    immutables := imms }

def marketRemovalParamsFrame (evm : State) (imms : Store) (out : ByteArray) : Frame :=
  { (marketRemovalCalldataFrame evm imms out) with
    locals := (marketRemovalCalldataFrame evm imms out).locals.insert "marketParams"
      (marketParamsData out).value }

def marketRemovalRoleFrame (evm : State) (imms : Store) (out : ByteArray) : Frame :=
  { (marketRemovalParamsFrame evm imms out) with
    locals := (marketRemovalParamsFrame evm imms out).locals.insert "__role" .unit }

def marketRemovalFrame (evm : State) (imms : Store) (out : ByteArray) : Frame :=
  { (marketRemovalRoleFrame evm imms out) with
    locals := (marketRemovalRoleFrame evm imms out).locals.insert "id"
      (wordBytes32Value (marketParamsData out).id) }

theorem marketParamsTupleStructSource {evm : State} {frame : Frame} (out : ByteArray)
    (hvar : evalExpr? config frame evm (.var "marketParams") =
      .ok (.tuple (marketParamsFields out))) :
    evalExpr? config frame evm marketRemovalStructExpr =
      .ok (marketParamsData out).value := by
  simp [marketRemovalStructExpr, evalExpr?, evalStructFields?, hvar,
    tupleGetValue?, marketParamsFields, marketParamsData, MarketParamsData.value,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem marketRemovalStructSource (evm : State) (imms : Store) (out : ByteArray) :
    evalExpr? config (marketRemovalCalldataFrame evm imms out) evm marketRemovalStructExpr =
      .ok (marketParamsData out).value := by
  have hvar : evalExpr? config (marketRemovalCalldataFrame evm imms out) evm
      (.var "marketParams") = .ok (.tuple (marketParamsFields out)) := by
    simp only [evalExpr?, marketRemovalCalldataFrame,
      store_get_ne _ _ (by decide : ("__calldata" == "marketParams") = false),
      store_get_self, EvalResult.ofOption]
  exact marketParamsTupleStructSource out hvar

theorem marketRemovalPrefix (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm
      { contract := contract
        locals := (∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))
        immutables := imms }
      marketRemovalBody (marketRemovalParamsFrame evm imms out)
      ([.internalCall "_checkCuratorRole" [] "__role",
        .internalCall "MarketParamsLib_id" [.var "marketParams"] "id"] ++
        marketRemovalGuards ++ marketRemovalTail) := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consNormal (ExecStmt.letDecl (marketRemovalStructSource evm imms out)) htail

theorem marketRemovalRolePrefix (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm) :
    ABlock config evm
      { contract := contract
        locals := (∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))
        immutables := imms }
      marketRemovalBody (marketRemovalFrame evm imms out)
      (marketRemovalGuards ++ marketRemovalTail) := by
  constructor
  intro result htail
  apply (marketRemovalPrefix evm imms out hwv hhi).run
  apply ExecBlock.consNormal (curatorRoleCall evm _ imms "__role" hrole)
  apply ExecBlock.consNormal (marketParamsIdCall evm _ imms (marketParamsData out) "id"
    (.var "marketParams") ?_) htail
  simp only [evalExpr?, marketRemovalRoleFrame, marketRemovalParamsFrame,
    store_get_ne _ _ (by decide : ("__role" == "marketParams") = false),
    store_get_self, EvalResult.ofOption]

end Benchmarks.Morpho.MetaMorphoV1_1
