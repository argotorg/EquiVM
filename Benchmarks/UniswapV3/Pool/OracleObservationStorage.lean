import Benchmarks.UniswapV3.Pool.ObservationStorage
import Benchmarks.UniswapV3.Pool.OracleTransformSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: read an array element after the bounds check.
theorem evalStorageRef_aindex_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {base : Ident} {index : Expr} {value : Value} {key : KeyValue}
    (heval : evalExpr? cfg frame evm index = .ok value)
    (hkey : valueToKey? value = some key)
    (hbound : arrayIndexInBounds? cfg evm frame.contract.storage base [] key = .ok ()) :
    evalStorageRef cfg frame evm ⟨base, [.aindex index]⟩ =
      .ok ⟨base, [.aindex key]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, heval,
    hkey, hbound, EvalResult.bind, bind, pure, EvalResult.ofOption]

theorem evalStorageRef_aindex_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {base : Ident} {index : Expr} {value : Value} {key : KeyValue}
    (heval : evalExpr? cfg frame evm index = .ok value)
    (hkey : valueToKey? value = some key)
    (hbound : arrayIndexInBounds? cfg evm frame.contract.storage base [] key = .revert) :
    evalStorageRef cfg frame evm ⟨base, [.aindex index]⟩ = .revert := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, heval,
    hkey, hbound, EvalResult.bind, bind, pure, EvalResult.ofOption]

def oracleStoredObservation (index : UInt256) (σ : AccountMap) (I : ExecutionEnv) : OracleObservation :=
  { timestamp := observationFieldWord index 0 4 σ I
    tickCumulative := observationTickValue index σ I
    secondsPerLiquidity := observationFieldWord index 11 20 σ I
    initialized := !decide (observationFieldWord index 31 1 σ I = ⟨0⟩) }

def observationStorageType : StorageType :=
  .struct "Observation" [
    ("blockTimestamp", .elem (.int (.uint ⟨32, by decide⟩))),
    ("tickCumulative", .elem (.int (.sint ⟨56, by decide⟩))),
    ("secondsPerLiquidityCumulativeX128", .elem (.int (.uint ⟨160, by decide⟩))),
    ("initialized", .elem .bool)]

theorem readObservationFieldOfGetter (evm : EVM.State) (index : UInt256)
    (name : Ident) (ty : ABI.ElemType) (value : Value) (hin : index.toNat < 65535)
    (htype : storageTypeAt? contract.storage
      ⟨"observations", [.aindex (.int (Int.ofNat index.toNat)), .field name]⟩ = some (.elem ty))
    (heval : evalExpr? config
      {contract := contract, locals := (∅ : Store).insert "arg0" (.int (Int.ofNat index.toNat))}
      evm (.storage ⟨"observations", [.aindex (.var "arg0"), .field name]⟩) = .ok value) :
    solidityReadStorage? storageBackend.locate? evm
      ⟨"observations", [.aindex (.int (Int.ofNat index.toNat)), .field name]⟩ (.elem ty) = .ok value := by
  have hresolve : resolveStorageRef? config
      {contract := contract, locals := (∅ : Store).insert "arg0" (.int (Int.ofNat index.toNat))}
      evm ⟨"observations", [.aindex (.var "arg0"), .field name]⟩ =
      .ok (⟨"observations", [.aindex (.int (Int.ofNat index.toNat)), .field name]⟩, .elem ty) :=
    resolveStorageRef?_ok (by simp)
      (evalStorageRef_aindex_field_ok (evalExpr_var_get (value := .int (Int.ofNat index.toNat)) (by simp)) rfl
        (by rw [observationArrayBounds, if_pos hin])) htype
  simpa only [evalExpr?, hresolve, bind, EvalResult.bind] using heval

theorem readOracleObservation (evm : EVM.State) (index : UInt256) (hin : index.toNat < 65535) :
    solidityReadStorage? storageBackend.locate? evm
      ⟨"observations", [.aindex (.int (Int.ofNat index.toNat))]⟩ observationStorageType =
      .ok (oracleStoredObservation index evm.accountMap evm.executionEnv).value := by
  let locals : Store := (∅ : Store).insert "arg0" (.int (Int.ofNat index.toNat))
  have hbase : locals.get? "observations" = none := by simp [locals]
  have hindex : locals.get? "arg0" = some (.int (Int.ofNat index.toNat)) := by simp [locals]
  have ht := readObservationFieldOfGetter evm index "blockTimestamp" (.int (.uint ⟨32, by decide⟩))
    _ hin rfl (evalObservationBlockTimestamp locals ∅ evm index hbase hindex hin)
  have hc := readObservationFieldOfGetter evm index "tickCumulative" (.int (.sint ⟨56, by decide⟩))
    _ hin rfl (evalObservationTickCumulative locals ∅ evm index hbase hindex hin)
  have hs := readObservationFieldOfGetter evm index "secondsPerLiquidityCumulativeX128" (.int (.uint ⟨160, by decide⟩))
    _ hin rfl (evalObservationSecondsPerLiquidityCumulativeX128 locals ∅ evm index hbase hindex hin)
  have hi := readObservationFieldOfGetter evm index "initialized" .bool
    _ hin rfl (evalObservationInitialized locals ∅ evm index hbase hindex hin)
  rw [observationStorageType, solidityReadStorage?]
  simp only [solidityReadFields?, List.cons_append, List.nil_append, ht, hc, hs, hi]
  simp only [bind, EvalResult.bind, pure, wordToElemBool]
  simp only [oracleStoredObservation, OracleObservation.value]

theorem evalOracleObservationExpr (locals imms : Store) (evm : EVM.State)
    (expr : Expr) (index : UInt256) (hbase : locals.get? "observations" = none)
    (he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm expr =
      .ok (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex expr]⟩) =
      .ok (oracleStoredObservation index evm.accountMap evm.executionEnv).value := by
  have hb : arrayIndexInBounds? config evm contract.storage "observations" []
      (.int (Int.ofNat index.toNat)) = .ok () := by rw [observationArrayBounds, if_pos hin]
  have hr := evalStorageRef_aindex_ok he rfl hb
  have hty : storageTypeAt? contract.storage
      ⟨"observations", [.aindex (.int (Int.ofNat index.toNat))]⟩ = some observationStorageType := rfl
  have hresolve := resolveStorageRef?_ok hbase hr hty
  rw [evalExpr?]
  simp only [hresolve, bind, EvalResult.bind]
  exact readOracleObservation evm index hin

theorem evalOracleObservation (locals imms : Store) (evm : EVM.State)
    (name : Ident) (index : UInt256) (hbase : locals.get? "observations" = none)
    (hindex : locals.get? name = some (.int (Int.ofNat index.toNat))) (hin : index.toNat < 65535) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex (.var name)]⟩) =
      .ok (oracleStoredObservation index evm.accountMap evm.executionEnv).value := by
  exact evalOracleObservationExpr locals imms evm (.var name) index hbase
    (evalExpr_var_get hindex) hin

theorem evalOracleObservationRevert (locals imms : Store) (evm : EVM.State)
    (name : Ident) (index : UInt256) (hbase : locals.get? "observations" = none)
    (hindex : locals.get? name = some (.int (Int.ofNat index.toNat))) (hin : ¬ index.toNat < 65535) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨"observations", [.aindex (.var name)]⟩) = .revert := by
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hindex
  have hb : arrayIndexInBounds? config evm contract.storage "observations" [] (.int (Int.ofNat index.toNat)) =
      .revert := by rw [observationArrayBounds, if_neg hin]
  exact evalExpr_storage_ref_revert hbase (evalStorageRef_aindex_revert he rfl hb)

theorem evalOracleTimestamp {frame : Frame} {evm : EVM.State} {name : Ident}
    (last : OracleObservation) (h : frame.locals.get? name = some last.value) :
    evalExpr? config frame evm (.field (.var name) "blockTimestamp") =
      .ok (.int (Int.ofNat last.timestamp.toNat)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) h
  simp only [evalExpr?, he, OracleObservation.value, lookupField?, lookupAssoc,
    EvalResult.ofOption, bind, EvalResult.bind, ↓reduceIte]

end Benchmarks.UniswapV3.Pool
