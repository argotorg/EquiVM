import Benchmarks.Morpho.MetaMorphoV1_1.AllocatorRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource

/-! Source loop and continuation for supply-queue replacement. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def supplyQueueLoopCondition : Expr := .binary .lt (.var "i") (.var "length")

def supplyQueueCapCondition : Expr :=
  .binary .ne (.storage ⟨"config",
    [.mindex (.index (.var "newSupplyQueue") (.var "i")), .field "cap"]⟩) (.intLit 0)

def supplyQueueLoopBody : List Stmt := [.require supplyQueueCapCondition]

def supplyQueueLoop : Stmt :=
  .for [.letDecl "i" (some abiUInt256) (.intLit 0)]
    supplyQueueLoopCondition maxDepositPost supplyQueueLoopBody

def supplyQueueLengthCondition : Expr := .binary .le (.var "length") (.intLit 30)

def supplyQueueTail : List Stmt :=
  [.assign .storage ⟨"supplyQueue", []⟩ (.var "newSupplyQueue"),
    .internalCall "_msgSender" [] "__c2",
    .emit "SetSupplyQueue" [.var "__c2", .var "newSupplyQueue"]]

def supplyQueueBody : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
    .letDecl "__calldata" (some .bytes) (.env .msgData),
    .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
      (.intLit (Int.ofNat (2 ^ 255 + 4)))),
    .internalCall "_checkAllocatorRole" [] "__role",
    .letDecl "length" (some abiUInt256) (.arrayLength .localVar ⟨"newSupplyQueue", []⟩),
    .require supplyQueueLengthCondition, supplyQueueLoop] ++ supplyQueueTail

theorem supplyQueueBody_eq : setSupplyQueueTransition.body = supplyQueueBody := rfl

def supplyQueuePrefixFrame (evm : State) (imms : Store) (values : List Value) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert "newSupplyQueue" (.array values)).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).insert "__role" .unit).insert "length"
        (.int (Int.ofNat values.length))
    immutables := imms }

def supplyQueueIndexFrame (frame : Frame) (i : Nat) : Frame :=
  { frame with locals := frame.locals.insert "i" (.int (Int.ofNat i)) }

structure SupplyQueueReady (frame : Frame) (values : List Value) (i : Nat) : Prop where
  contract : frame.contract = MetaMorphoV1_1.contract
  config : frame.locals.get? "config" = none
  supplyQueue : frame.locals.get? "supplyQueue" = none
  array : frame.locals.get? "newSupplyQueue" = some (.array values)
  length : frame.locals.get? "length" = some (.int (Int.ofNat values.length))
  index : frame.locals.get? "i" = some (.int (Int.ofNat i))

theorem supplyQueueIndexFrame_ready {frame : Frame} {values : List Value} {i : Nat}
    (h : SupplyQueueReady frame values i) (j : Nat) :
    SupplyQueueReady (supplyQueueIndexFrame frame j) values j := by
  constructor
  · exact h.contract
  · rw [supplyQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.config
  · rw [supplyQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.supplyQueue
  · rw [supplyQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.array
  · rw [supplyQueueIndexFrame, store_get_ne _ _ (by decide)]; exact h.length
  · exact store_get_self _ _ _

theorem supplyQueueInitialReady (evm : State) (imms : Store) (values : List Value) :
    SupplyQueueReady (supplyQueueIndexFrame (supplyQueuePrefixFrame evm imms values) 0)
      values 0 := by
  constructor <;> simp only [supplyQueueIndexFrame, supplyQueuePrefixFrame,
    store_get_ne _ _ (by decide : ("i" == "config") = false),
    store_get_ne _ _ (by decide : ("length" == "config") = false),
    store_get_ne _ _ (by decide : ("__role" == "config") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "config") = false),
    store_get_ne _ _ (by decide : ("newSupplyQueue" == "config") = false),
    store_get_ne _ _ (by decide : ("i" == "supplyQueue") = false),
    store_get_ne _ _ (by decide : ("length" == "supplyQueue") = false),
    store_get_ne _ _ (by decide : ("__role" == "supplyQueue") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "supplyQueue") = false),
    store_get_ne _ _ (by decide : ("newSupplyQueue" == "supplyQueue") = false),
    store_get_ne _ _ (by decide : ("i" == "newSupplyQueue") = false),
    store_get_ne _ _ (by decide : ("length" == "newSupplyQueue") = false),
    store_get_ne _ _ (by decide : ("__role" == "newSupplyQueue") = false),
    store_get_ne _ _ (by decide : ("__calldata" == "newSupplyQueue") = false),
    store_get_ne _ _ (by decide : ("i" == "length") = false),
    store_get_self, store_get_empty]

theorem supplyQueuePrefix (evm : State) (imms : Store) (values : List Value)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : allocatorRoleAllowed evm) :
    ABlock config evm
      { contract := contract
        locals := (∅ : Store).insert "newSupplyQueue" (.array values)
        immutables := imms }
      supplyQueueBody (supplyQueuePrefixFrame evm imms values)
      ([.require supplyQueueLengthCondition, supplyQueueLoop] ++ supplyQueueTail) := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (allocatorRoleCall evm _ imms "__role" hrole)
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalLocalArrayLength (by
    simp only [store_get_ne _ _ (by decide : ("__role" == "newSupplyQueue") = false),
      store_get_ne _ _ (by decide : ("__calldata" == "newSupplyQueue") = false),
      store_get_self]))) htail

theorem supplyQueueLengthSource {frame : Frame} {evm : State} {values : List Value}
    (hlen : frame.locals.get? "length" = some (.int (Int.ofNat values.length))) :
    evalExpr? config frame evm supplyQueueLengthCondition =
      .ok (.bool (decide (values.length ≤ 30))) := by
  simp only [supplyQueueLengthCondition, evalExpr?, hlen, EvalResult.ofOption, bind,
    EvalResult.bind, evalBinaryOp?, pure, Int.ofNat_eq_natCast]
  congr 3
  apply propext
  omega

theorem supplyQueueConditionSource {frame : Frame} {evm : State}
    {values : List Value} {i : Nat} (h : SupplyQueueReady frame values i) :
    evalExpr? config frame evm supplyQueueLoopCondition =
      .ok (.bool (decide (i < values.length))) := evalLocalNatLt h.index h.length

theorem supplyQueueCapSource {frame : Frame} {evm : State} {values : List Value}
    {i : Nat} {id : UInt256} (h : SupplyQueueReady frame values i)
    (hid : values[i]? = some (wordBytes32Value id)) :
    evalExpr? config frame evm supplyQueueCapCondition =
      .ok (.bool (decide (maxDepositCapWord evm.executionEnv evm.accountMap id ≠ ⟨0⟩))) := by
  exact wordNeSource (configCapRead h.contract h.config
    (evalLocalArrayIndex h.array h.index hid (by rfl))) (by simp only [evalExpr?, pure]; rfl)

theorem supplyQueuePostSource {frame : Frame} {evm : State} {values : List Value} {i : Nat}
    (h : SupplyQueueReady frame values i) (hfit : i + 1 < UInt256.size) :
    ExecBlock config frame evm maxDepositPost
      (.ok (supplyQueueIndexFrame frame (i + 1)) evm) := execLocalIncrement h.index hfit

end Benchmarks.Morpho.MetaMorphoV1_1
