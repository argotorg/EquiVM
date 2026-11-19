import Benchmarks.Midnight.Storage

/-! Source evaluation for two-key public mapping getters. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def nestedMappingArguments (arg0 arg1 : Value) : Store :=
  ((∅ : Store).insert "arg0" arg0).insert "arg1" arg1

theorem calldataNestedArg0 (C : ContractDecl) (arg0 arg1 : Value) (evm : EVM.State) :
    (calldataFrame C (nestedMappingArguments arg0 arg1) ∅ evm).locals.get? "arg0" =
      some arg0 := by
  change ((((∅ : Store).insert "arg0" arg0).insert "arg1" arg1).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "arg0" = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem calldataNestedArg1 (C : ContractDecl) (arg0 arg1 : Value) (evm : EVM.State) :
    (calldataFrame C (nestedMappingArguments arg0 arg1) ∅ evm).locals.get? "arg1" =
      some arg1 := by
  change ((((∅ : Store).insert "arg0" arg0).insert "arg1" arg1).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "arg1" = _
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem guardedNestedMappingGetter
    {cfg : Config} {C : ContractDecl} {layout : StorageLayout}
    {name : Ident} {t : ElemType} {loc : StorageLoc} {value : Value}
    (evm : EVM.State) (arg0 arg1 : Value) (key0 key1 : KeyValue)
    (hkey0 : valueToKey? arg0 = some key0) (hkey1 : valueToKey? arg1 = some key1)
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hty : storageTypeAt? C.storage
      { base := name, steps := [.mindex key0, .mindex key1] } = some (.elem t))
    (hloc : layout { base := name, steps := [.mindex key0, .mindex key1] } = some (.leaf loc))
    (hload : storageLocLoad evm loc = value)
    (hname : name ≠ "__calldata") (harg0 : name ≠ "arg0") (harg1 : name ≠ "arg1")
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody cfg C evm (nestedMappingArguments arg0 arg1)
      (entryPrefix ++ [.return [.storage
        { base := name, steps := [.mindex (.var "arg0"), .mindex (.var "arg1")] }]])
      (.returned (calldataFrame C (nestedMappingArguments arg0 arg1) ∅ evm) evm
        (some [value])) := by
  apply guardedReturnBody hwv hhi
  apply evalExpr_storage_scalar_value (loc := loc)
    (er := { base := name, steps := [.mindex key0, .mindex key1] }) (t := t)
  · simp [calldataFrame, nestedMappingArguments, Ne.symm hname, Ne.symm harg0, Ne.symm harg1]
  · have hget0 := calldataNestedArg0 C arg0 arg1 evm
    have hget1 := calldataNestedArg1 C arg0 arg1 evm
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget0, hget1,
      EvalResult.bind, EvalResult.ofOption, hkey0, hkey1, pure, bind]
  · exact hty
  · exact hbackend
  · exact hloc
  · exact hload

end Benchmarks.Midnight
