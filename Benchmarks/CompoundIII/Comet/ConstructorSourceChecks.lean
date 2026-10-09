import Benchmarks.CompoundIII.Comet.ConstructorDecimalsCheck

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem constructorSource_storeFront (c : ConstructorConfig) (w : UInt256) (evm : EVM.State) :
    evalExpr? config (constructorSourceDecimals c w) evm
      (.field (.var "config") "storeFrontPriceFactor") =
      .ok (.int (Int.ofNat c.storeFrontPriceFactor.val)) := by
  simp only [evalExpr?, constructorSourceDecimals, constructorSourceConfig,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
    bind, EvalResult.bind]
  rfl

theorem constructorSource_assetCount (c : ConstructorConfig) (w : UInt256) (evm : EVM.State) :
    evalExpr? config (constructorSourceDecimals c w) evm
      (.arrayLength .localVar ⟨"config", [.field "assetConfigs"]⟩) =
      .ok (.int (Int.ofNat c.assetConfigs.length)) := by
  have hfield : lookupField? (constructorConfigValue c) "assetConfigs" =
      some (.array (c.assetConfigs.map ConstructorAsset.value)) := rfl
  have hpath : readLocalPath? config (constructorSourceDecimals c w) evm
      (constructorConfigValue c) [.field "assetConfigs"] =
      .ok (.array (c.assetConfigs.map ConstructorAsset.value)) := by
    simp only [readLocalPath?, hfield, EvalResult.ofOption, bind, EvalResult.bind, pure]
  simp only [evalExpr?, constructorSourceDecimals, constructorSourceConfig,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    pure, bind, EvalResult.bind]
  change (show EvalResult Value from do
    let v ← readLocalPath? config (constructorSourceDecimals c w) evm
      (constructorConfigValue c) [.field "assetConfigs"]
    match v with
    | .array vs => pure (.int vs.length)
    | .bytes b => pure (.int (Int.ofNat b.size))
    | .fixedBytes n _ => pure (.int (fixedBytesSize n))
    | _ => .error .typeError) = _
  rw [hpath]
  simp only [bind, EvalResult.bind, pure, List.length_map, Int.ofNat_eq_natCast]

theorem constructorSource_storeFrontGuard (c : ConstructorConfig) (w : UInt256) (evm : EVM.State) :
    evalExpr? config (constructorSourceDecimals c w) evm
      (.binary .le (.field (.var "config") "storeFrontPriceFactor") (.intLit 1000000000000000000)) =
      .ok (.bool (decide (c.storeFrontPriceFactor.val ≤ 1000000000000000000))) := by
  simp only [evalExpr?, constructorSource_storeFront, pure, bind, EvalResult.bind, evalBinaryOp?]
  simp

theorem constructorSource_assetCountGuard (c : ConstructorConfig) (w : UInt256) (evm : EVM.State) :
    evalExpr? config (constructorSourceDecimals c w) evm
      (.binary .le (.arrayLength .localVar ⟨"config", [.field "assetConfigs"]⟩) (.intLit 24)) =
      .ok (.bool (decide (c.assetConfigs.length ≤ 24))) := by
  simp only [evalExpr?, constructorSource_assetCount, pure, bind, EvalResult.bind, evalBinaryOp?]
  simp

/-- Every outcome of the base-token call leads to a source revert for an oversized asset array. -/
theorem constructorSourceOversized_revert {c : ConstructorConfig} {evm evm' : EVM.State}
    {z : Bool} {out : ByteArray} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hc : callViaEVM evm c.baseToken 0 decimalsPayload (z, evm', out) false)
    (hhi : out.size < 2^255) (hn : 24 < c.assetConfigs.length) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body .reverted := by
  by_cases hvalid : z = true ∧ 32 ≤ out.size ∧ (calldataWord out 0).toNat ≤ 18
  · rcases hvalid with ⟨rfl, hlo, hword⟩
    have hd := constructorSourceDecimalsChecked_exec hv hc hhi hlo hword
    rw [← List.take_append_drop 4 contract.ctor.body]
    apply execBlockAppendOk hd
    by_cases hfactor : c.storeFrontPriceFactor.val ≤ 1000000000000000000
    · apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
      · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        rw [constructorSource_assetCountGuard, decide_eq_false (by omega)]
      · rw [constructorSource_storeFrontGuard, decide_eq_true hfactor]
    · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      rw [constructorSource_storeFrontGuard, decide_eq_false hfactor]
  · exact constructorSourceDecimalsChecked_revert hv hc hhi hvalid

end Benchmarks.CompoundIII.Comet
