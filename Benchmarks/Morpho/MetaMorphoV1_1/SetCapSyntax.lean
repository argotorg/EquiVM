import Benchmarks.Morpho.MetaMorphoV1_1.StorageAlias
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStorage
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsHashSource

/-! The cap setter's source body, arguments, and local storage alias. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def marketConfigType : StorageType :=
  .struct "MarketConfig"
    [("cap", .elem (.int (.uint ⟨184, by decide⟩))), ("enabled", .elem .bool),
      ("removableAt", .elem (.int (.uint ⟨64, by decide⟩)))]

def marketConfigRef (id : UInt256) : EvaledStorageRef :=
  ⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))]⟩

def setCapCondition : Expr := .binary .gt (.var "supplyCap") (.intLit 0)

def setCapDisabledCondition : Expr :=
  .unary .not (.storage ⟨"marketConfig", [.field "enabled"]⟩)

def setCapQueueCondition (limit : Nat) : Expr :=
  .binary .le (.arrayLength .storage ⟨"withdrawQueue", []⟩) (.intLit (Int.ofNat limit))

def setCapEnableBody : List Stmt :=
  [.require (setCapQueueCondition (2 ^ 64 - 1)),
    .push ⟨"withdrawQueue", []⟩ (some (.var "id")),
    .require (setCapQueueCondition 30),
    .assign .storage ⟨"marketConfig", [.field "enabled"]⟩ (.boolLit true),
    .letDecl "previousTotalAssets" (some abiUInt256) (.storage ⟨"lastTotalAssets", []⟩)] ++
  cursorCall allocatedSupplyAssetsFunction.name
    [.immutable "MORPHO", .var "marketParams", .env .this] "__c0" ++
  [.internalCall "_updateLastTotalAssets"
      [.inRange (.uint ⟨256, by decide⟩)
        (.binary .add (.var "previousTotalAssets") (.var "__c0"))] "__c1",
    .emit "SetWithdrawQueue" [.env .caller, .storage ⟨"withdrawQueue", []⟩]]

def setCapPositiveBody : List Stmt :=
  [.ite setCapDisabledCondition setCapEnableBody [],
    .assign .storage ⟨"marketConfig", [.field "removableAt"]⟩ (.intLit 0)]

def setCapTail : List Stmt :=
  [.assign .storage ⟨"marketConfig", [.field "cap"]⟩ (.var "supplyCap"),
    .internalCall "_msgSender" [] "__c2",
    .emit "SetCap" [.var "__c2", .var "id", .var "supplyCap"],
    .delete ⟨"pendingCap", [.mindex (.var "id")]⟩, .return [.var cursorName]]

theorem allocatedSetCapFunction_body : allocatedSetCapFunction.body =
    [.letStorage "marketConfig" ⟨"config", [.mindex (.var "id")]⟩,
      .ite setCapCondition setCapPositiveBody []] ++ setCapTail := by decide +kernel

theorem allocatedSetCapFunction_lookup :
    lookupCallable? contract allocatedSetCapFunction.name =
      some allocatedSetCapFunction.toCallable := rfl

def setCapFrame (imms : Store) (p : MarketParamsData) (id cap ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((((∅ : Store).insert cursorName (uint256Value ptr)).insert "supplyCap"
      (uint256Value cap)).insert "id" (wordBytes32Value id)).insert "marketParams" p.value
    immutables := imms }

def setCapAliasFrame (frame : Frame) (id : UInt256) : Frame :=
  { frame with
    locals := frame.locals.insert "marketConfig"
      (.storageRef (marketConfigRef id) marketConfigType) }

structure SetCapReady (frame : Frame) (p : MarketParamsData) (id cap ptr : UInt256) : Prop where
  contract : frame.contract = MetaMorphoV1_1.contract
  reference : frame.locals.get? "marketConfig" =
    some (.storageRef (marketConfigRef id) marketConfigType)
  pending : frame.locals.get? "pendingCap" = none
  queue : frame.locals.get? "withdrawQueue" = none
  lastAssets : frame.locals.get? "lastTotalAssets" = none
  params : frame.locals.get? "marketParams" = some p.value
  id : frame.locals.get? "id" = some (wordBytes32Value id)
  cap : frame.locals.get? "supplyCap" = some (uint256Value cap)
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)

theorem setCapFrame_ready (imms : Store) (p : MarketParamsData) (id cap ptr : UInt256) :
    SetCapReady (setCapAliasFrame (setCapFrame imms p id cap ptr) id) p id cap ptr := by
  constructor <;> simp [setCapAliasFrame, setCapFrame, cursorName, Std.HashMap.getElem_insert]

theorem setCapAliasPrefix (evm : State) (imms : Store) (p : MarketParamsData)
    (id cap ptr : UInt256) :
    ABlock config evm (setCapFrame imms p id cap ptr) allocatedSetCapFunction.body
      (setCapAliasFrame (setCapFrame imms p id cap ptr) id)
      ([.ite setCapCondition setCapPositiveBody []] ++ setCapTail) := by
  constructor
  intro result htail
  rw [allocatedSetCapFunction_body]
  apply ExecBlock.consNormal (ExecStmt.letStorage ?_) htail
  apply resolveStorageRef?_ok
  · simp [setCapFrame, cursorName]
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      setCapFrame, store_get_ne _ _ (by decide : ("marketParams" == "id") = false),
      store_get_self, EvalResult.ofOption,
      valueToKey_bytes32_of_length (word_toBytesBE_length_32 id),
      bind, EvalResult.bind, pure, wordBytes32Value, marketConfigRef]
  · rfl

theorem marketConfigFieldResolve {frame : Frame} {evm : State} {id : UInt256}
    (halias : frame.locals.get? "marketConfig" =
      some (.storageRef (marketConfigRef id) marketConfigType)) (field : Ident)
    (t : ElemType) (hfield : storageTypeStep? marketConfigType (.field field) = some (.elem t)) :
    resolveStorageRef? config frame evm ⟨"marketConfig", [.field field]⟩ =
      .ok (⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
        .field field]⟩, .elem t) :=
  resolveStorageAliasField halias hfield

theorem setCapConditionSource {frame : Frame} {evm : State} {cap : UInt256}
    (hcap : frame.locals.get? "supplyCap" = some (uint256Value cap)) :
    evalExpr? config frame evm setCapCondition = .ok (.bool (decide (cap ≠ ⟨0⟩))) := by
  rw [show setCapCondition = .binary .gt (.var "supplyCap") (.intLit 0) from rfl,
    evalExpr_uint256_var_positive evm "supplyCap" cap hcap]
  congr 3
  apply propext
  exact ⟨fun hp hz ↦ by subst cap; contradiction,
    fun hz ↦ Nat.pos_of_ne_zero (fun hzero ↦ hz (uint256_toNat_eq_zero hzero))⟩

theorem setCapDisabledSource {frame : Frame} {evm : State} {id : UInt256}
    (halias : frame.locals.get? "marketConfig" =
      some (.storageRef (marketConfigRef id) marketConfigType)) :
    evalExpr? config frame evm setCapDisabledCondition =
      .ok (.bool (decide (marketRemovalEnabledWord evm id = ⟨0⟩))) := by
  have hr := marketConfigFieldResolve (evm := evm) halias "enabled" .bool rfl
  have he : evalExpr? config frame evm (.storage ⟨"marketConfig", [.field "enabled"]⟩) =
      .ok (wordToElem .bool (marketRemovalEnabledWord evm id)) := by
    apply evalStorageResolved
      (loc :=
        { slot := solcMappingSlot ⟨13⟩ id, offset := 23, size := 1,
          hbound := by decide, type := .bool }) hr rfl
    · change some (StorageAddr.leaf
        { slot := solcMappingSlot ⟨13⟩
            (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
          offset := 23, size := 1, hbound := by decide, type := .bool }) = _
      rw [show keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)) = id from
        keyValueToWord_fixedBytes32 id]
    · exact storageLocLoad_bool_shift evm _ 23
  rw [setCapDisabledCondition, evalExpr?, he, wordToElemBool]
  simp only [bind, EvalResult.bind, evalUnaryOp?, EvalResult.ofOption, Bool.not_not]

end Benchmarks.Morpho.MetaMorphoV1_1
