import Benchmarks.Midnight.NestedStorage
import Benchmarks.Midnight.PackedFields
import Reasoning.VyperBounded

variable {fork : Ethereum.Fork}

/-! Fixed-array bounds and packed-array reads for public getters. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: evaluate a mapping followed by a bounded fixed-array index.
theorem evalMappingArrayRef {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name arg0 arg1 : Ident} {value : Value} {key : KeyValue} {index length : Nat}
    {ty : StorageType}
    (hget0 : frame.locals.get? arg0 = some value)
    (hget1 : frame.locals.get? arg1 = some (.int (Int.ofNat index)))
    (hkey : valueToKey? value = some key)
    (hty : storageTypeAt? frame.contract.storage { base := name, steps := [.mindex key] } =
      some (.array ty length)) :
    evalStorageRef cfg frame evm
      { base := name, steps := [.mindex (.var arg0), .aindex (.var arg1)] } =
      if index < length then
        .ok { base := name, steps := [.mindex key, .aindex (.int (Int.ofNat index))] }
      else .revert := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget0, hget1,
    EvalResult.bind, EvalResult.ofOption, hkey,
    show valueToKey? (.int (Int.ofNat index)) = some (.int (Int.ofNat index)) from rfl, pure, bind,
    List.nil_append, arrayIndexInBounds?, hty]
  simp only [Int.ofNat_eq_natCast, Int.natCast_nonneg, Nat.cast_lt, true_and]
  by_cases hi : index < length <;> simp only [hi, if_true, if_false] <;> rfl

theorem guardedMappingArrayGetter {cfg : Config} {C : ContractDecl} {layout : StorageLayout}
    {name : Ident} {t : ElemType} {loc : StorageLoc} {result : Value} {length : Nat}
    (evm : EVM.State) (arg0 : Value) (key : KeyValue) (index : Nat)
    (hkey : valueToKey? arg0 = some key)
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? C.storage { base := name, steps := [.mindex key] } =
      some (.array (.elem t) length))
    (hleaf : storageTypeAt? C.storage
      { base := name, steps := [.mindex key, .aindex (.int (Int.ofNat index))] } =
      some (.elem t))
    (hloc : layout { base := name, steps := [.mindex key, .aindex (.int (Int.ofNat index))] } =
      some (.leaf loc))
    (hload : storageLocLoad evm loc = result)
    (hname : name ≠ "__calldata") (harg0 : name ≠ "arg0") (harg1 : name ≠ "arg1")
    (hi : index < length) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork cfg C evm (nestedMappingArguments arg0 (.int (Int.ofNat index)))
      (entryPrefix ++ [.return [.storage
        { base := name, steps := [.mindex (.var "arg0"), .aindex (.var "arg1")] }]])
      (.returned (calldataFrame C (nestedMappingArguments arg0 (.int (Int.ofNat index))) ∅ evm)
        evm (some [result])) := by
  apply guardedReturnBody hwv hhi
  apply evalExpr_storage_scalar_value (loc := loc)
    (er := { base := name, steps := [.mindex key, .aindex (.int (Int.ofNat index))] }) (t := t)
  · simp [calldataFrame, nestedMappingArguments, Ne.symm hname, Ne.symm harg0, Ne.symm harg1]
  · rw [evalMappingArrayRef (calldataNestedArg0 _ _ _ _) (calldataNestedArg1 _ _ _ _) hkey hty,
      if_pos hi]
  · exact hleaf
  · exact hbackend
  · exact hloc
  · exact hload

theorem guardedMappingArrayRevert {cfg : Config} {C : ContractDecl}
    {name : Ident} {ty : StorageType} {length : Nat}
    (evm : EVM.State) (arg0 : Value) (key : KeyValue) (index : Nat)
    (hkey : valueToKey? arg0 = some key)
    (hty : storageTypeAt? C.storage { base := name, steps := [.mindex key] } =
      some (.array ty length))
    (hname : name ≠ "__calldata") (harg0 : name ≠ "arg0") (harg1 : name ≠ "arg1")
    (hi : ¬ index < length) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork cfg C evm (nestedMappingArguments arg0 (.int (Int.ofNat index)))
      (entryPrefix ++ [.return [.storage
        { base := name, steps := [.mindex (.var "arg0"), .aindex (.var "arg1")] }]])
      .reverted := by
  apply guardedReturnReverts hwv hhi
  apply Reasoning.VyperBounded.evalExpr_storage_revert
  · simp [calldataFrame, nestedMappingArguments, Ne.symm hname, Ne.symm harg0, Ne.symm harg1]
  · rw [evalMappingArrayRef (calldataNestedArg0 _ _ _ _) (calldataNestedArg1 _ _ _ _) hkey hty,
      if_neg hi]

end Benchmarks.Midnight
