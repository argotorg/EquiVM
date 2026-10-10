import Benchmarks.UniswapV3.Pool.PositionOwedStorage
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def positionStructValue (key : UInt256) (σ : AccountMap) (ee : ExecutionEnv) : Value :=
  .struct "PositionInfo"
    [("liquidity", .int (Int.ofNat (positionFieldWord key 0 0 16 σ ee).toNat)),
     ("feeGrowthInside0LastX128", .int (Int.ofNat (positionFieldWord key 1 0 32 σ ee).toNat)),
     ("feeGrowthInside1LastX128", .int (Int.ofNat (positionFieldWord key 2 0 32 σ ee).toNat)),
     ("tokensOwed0", .int (Int.ofNat (positionOwedWord key false σ ee).toNat)),
     ("tokensOwed1", .int (Int.ofNat (positionOwedWord key true σ ee).toNat))]

theorem resolvePositionReference (locals imms : Store) (evm : EVM.State) (name : Ident)
    (key : UInt256) (hbase : locals.get? "positions" = none)
    (hkey : locals.get? name = some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))) :
    resolveStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      ⟨"positions", [.mindex (.var name)]⟩ = .ok (positionReference key, positionStorageType) := by
  apply resolveStorageRef?_ok hbase
  · have hlen : (EVM.Word.toBytesBE key).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size key
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr_var_get (frame := {contract := contract, locals := locals, immutables := imms})
        (cfg := config) (evm := evm) hkey, valueToKey?, hlen, positionReference,
      if_true, bind, EvalResult.bind, EvalResult.ofOption, pure]
  · rfl

def positionGetterLocals (key : UInt256) : Store :=
  (∅ : Store).insert "arg0" (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))

theorem readPositionFieldOfGetter (evm : EVM.State) (key : UInt256) (name : Ident)
    (ty : ABI.ElemType) (value : Value)
    (htype : storageTypeStep? positionStorageType (.field name) = some (.elem ty))
    (heval : evalExpr? config {contract := contract, locals := positionGetterLocals key} evm
      (.storage ⟨"positions", [.mindex (.var "arg0"), .field name]⟩) = .ok value) :
    solidityReadStorage? storageBackend.locate? evm
      ⟨"positions", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)), .field name]⟩
      (.elem ty) = .ok value := by
  let frame : Frame := {contract := contract, locals := positionGetterLocals key}
  have hlen : (EVM.Word.toBytesBE key).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size key
  have hr : resolveStorageRef? config frame evm
      ⟨"positions", [.mindex (.var "arg0"), .field name]⟩ = .ok
      (⟨"positions", [.mindex (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)), .field name]⟩,
        .elem ty) := by
    apply resolveStorageRef?_ok (by simp [frame, positionGetterLocals])
    · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, frame,
        positionGetterLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self,
        valueToKey?, hlen, if_true,
        bind, EvalResult.bind,
        EvalResult.ofOption, pure]
    · change (storageTypeStep? positionStorageType (.field name) >>= fun t ↦ some t) = _
      rw [htype]
      rfl
  change evalExpr? config frame evm _ = .ok value at heval
  simpa only [evalExpr?, hr, bind, EvalResult.bind] using heval

theorem readPositionStruct (evm : EVM.State) (key : UInt256) :
    solidityReadStorage? storageBackend.locate? evm (positionReference key) positionStorageType =
      .ok (positionStructValue key evm.accountMap evm.executionEnv) := by
  let locals := (∅ : Store).insert "arg0" (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key))
  have hbase : locals.get? "positions" = none := by simp [locals]
  have hkey : locals.get? "arg0" =
      some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)) := Std.HashMap.getElem?_insert_self
  have h0 := readPositionFieldOfGetter evm key "liquidity" (.int (.uint ⟨128, by decide⟩)) _ rfl
    (evalPositionLiquidity locals ∅ evm key hbase hkey)
  have h1 := readPositionFieldOfGetter evm key "feeGrowthInside0LastX128"
    (.int (.uint ⟨256, by decide⟩)) _ rfl (evalPositionFeeGrowthInside0LastX128 locals ∅ evm key hbase hkey)
  have h2 := readPositionFieldOfGetter evm key "feeGrowthInside1LastX128"
    (.int (.uint ⟨256, by decide⟩)) _ rfl (evalPositionFeeGrowthInside1LastX128 locals ∅ evm key hbase hkey)
  have h3 := readPositionFieldOfGetter evm key "tokensOwed0" (.int (.uint ⟨128, by decide⟩)) _ rfl
    (evalPositionTokensOwed0 locals ∅ evm key hbase hkey)
  have h4 := readPositionFieldOfGetter evm key "tokensOwed1" (.int (.uint ⟨128, by decide⟩)) _ rfl
    (evalPositionTokensOwed1 locals ∅ evm key hbase hkey)
  rw [positionStorageType, solidityReadStorage?]
  simp only [positionReference, solidityReadFields?, List.cons_append, List.nil_append,
    h0, h1, h2, h3, h4, bind, EvalResult.bind, pure, positionStructValue, positionOwedWord]
  rfl

theorem evalPositionStruct (locals imms : Store) (evm : EVM.State) (name : Ident) (key : UInt256)
    (hget : locals.get? name = some (positionAlias key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage ⟨name, []⟩) = .ok (positionStructValue key evm.accountMap evm.executionEnv) := by
  rw [evalExpr?]
  simp only [resolveStorageRef?, hget, positionAlias, evalStorageRefFrom?, pure, bind, EvalResult.bind]
  exact readPositionStruct evm key

end Benchmarks.UniswapV3.Pool
