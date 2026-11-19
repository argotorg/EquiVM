import Benchmarks.Midnight.PositionFields
import Benchmarks.Midnight.PositionViewValues
import Benchmarks.Midnight.SourceControl
import Benchmarks.Midnight.MarketData
import Benchmarks.Midnight.MulDivCall

/-! Source expressions and composition used by the position-view body. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def positionViewFunction : FunctionDecl := contract.functions[25]!

-- LIBRARY CANDIDATE: advance a source block through any normally completing statement.
theorem sourceNormalStep {cfg : Config} {evm : EVM.State} {start frame frame' : Frame}
    {body rest : List Stmt} {stmt : Stmt}
    (prev : ABlock cfg evm start body frame (stmt :: rest))
    (hstmt : ExecStmt cfg frame evm stmt (.ok frame' evm)) :
    ABlock cfg evm start body frame' rest :=
  ⟨fun h ↦ prev.run (ExecBlock.consNormal hstmt h)⟩

def wordLocal (frame : Frame) (name : Ident) (word : UInt256) : Frame :=
  { frame with locals := frame.locals.insert name (.int word.toNat) }

theorem wordLocal_get (frame : Frame) (name : Ident) (word : UInt256) :
    (wordLocal frame name word).locals.get? name = some (.int word.toNat) :=
  store_get_self _ _ _

theorem wordLocal_get_ne (frame : Frame) (name other : Ident) (word : UInt256)
    (hne : name ≠ other) :
    (wordLocal frame name word).locals.get? other = frame.locals.get? other := by
  exact store_get_ne _ _ (by simpa using hne)

theorem evalWordLocal {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {word : UInt256}
    (hget : frame.locals.get? name = some (.int word.toNat)) :
    evalExpr? cfg frame evm (.var name) = .ok (.int word.toNat) := by
  simp only [evalExpr?, hget, EvalResult.ofOption]

theorem evalMarketMaturity {cfg : Config} {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hget : frame.locals.get? "market" = some (Model.marketValue m.value)) :
    evalExpr? cfg frame evm (.field (.var "market") "maturity") = .ok (.int m.maturity.toNat) := by
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

def marketLossWord (evm : EVM.State) (id : UInt256) : UInt256 :=
  UInt256.shiftRight (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
    (solcMappingSlot ⟨1⟩ id)) (UInt256.ofNat 128)

theorem evalMarketLoss {frame : Frame} {evm : EVM.State} {id : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm (.storage { base := "marketState", steps :=
      [.mindex (.var "id"), .field "lossFactor"] }) = .ok (.int (marketLossWord evm id).toNat) := by
  apply evalExpr_storage_scalar_value (loc := {
      slot := solcMappingSlot ⟨1⟩ id, offset := 16, size := 16,
      hbound := by decide, type := .int packedUInt128Int })
    (er := { base := "marketState", steps :=
      [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)), .field "lossFactor"] })
    (t := .int packedUInt128Int) hbase
  · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hid,
      EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
  · rw [hc]; rfl
  · rfl
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
      offset := 16, size := 16, hbound := _, type := .int packedUInt128Int }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact storageLocLoad_uint128_high evm _

theorem evalComplement128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {word : UInt256}
    (he : evalExpr? cfg frame evm expr = .ok (.int word.toNat)) (hw : word.toNat < 2 ^ 128) :
    evalExpr? cfg frame evm (.inRange packedUInt128Int
      (.binary .sub (.intLit (2 ^ 128 - 1)) expr)) = .ok (.int (complement128 word).toNat) := by
  exact evalCheckedSub128 (a := uint128Mask)
    (by norm_num [evalExpr?, pure,
      show uint128Mask.toNat = 340282366920938463463374607431768211455 from rfl]) he (by decide)
    (by change word.toNat ≤ 340282366920938463463374607431768211455; omega)

end Benchmarks.Midnight
