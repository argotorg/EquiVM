import Benchmarks.CompoundIII.Comet.ConstructorInput
import Benchmarks.CompoundIII.Comet.DecimalsCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorConfigNames : List Ident :=
  ["governor", "pauseGuardian", "baseToken", "baseTokenPriceFeed", "extensionDelegate",
    "supplyKink", "supplyPerYearInterestRateSlopeLow", "supplyPerYearInterestRateSlopeHigh",
    "supplyPerYearInterestRateBase", "borrowKink", "borrowPerYearInterestRateSlopeLow",
    "borrowPerYearInterestRateSlopeHigh", "borrowPerYearInterestRateBase", "storeFrontPriceFactor",
    "trackingIndexScale", "baseTrackingSupplySpeed", "baseTrackingBorrowSpeed", "baseMinForRewards",
    "baseBorrowMin", "targetReserves", "assetConfigs"]

def constructorConfigExpr : Expr := .structLit "Configuration"
  (constructorConfigNames.zipIdx.map fun (name, i) ↦ (name, .tupleGet (.var "configTuple") i))

def constructorConfigValue (c : ConstructorConfig) : Value :=
  .struct "Configuration" (constructorConfigNames.zip
    (c.scalars.map ScalarReturn.value ++ [.array (c.assetConfigs.map ConstructorAsset.value)]))

def constructorSourceArgs (c : ConstructorConfig) : Store :=
  (∅ : Store).insert "configTuple" c.value

def constructorSourceEntry (c : ConstructorConfig) : Frame :=
  { contract := contract, locals := constructorSourceArgs c,
    immutables := initialImmutables contract }

def constructorSourceConfig (c : ConstructorConfig) : Frame :=
  let f := constructorSourceEntry c
  { f with locals := f.locals.insert "config" (constructorConfigValue c) }

def constructorSourceDecimals (c : ConstructorConfig) (w : UInt256) : Frame :=
  let f := constructorSourceConfig c
  { f with locals := f.locals.insert "decimals_" (.int (Int.ofNat w.toNat)) }

theorem constructorSourceArgs_bind (c : ConstructorConfig) :
    constructorSourceArgs c = Std.HashMap.ofList ((contract.ctor.params.map Param.name).zip
      [c.value]) := rfl

theorem constructorSourcePrefix_shape : contract.ctor.body.take 3 =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "config" (some ConstructorConfig.abiType) constructorConfigExpr,
      .externalCall (.field (.var "config") "baseToken") "decimals" (.intLit 0) []
        "decimals_" (perm := false)] := rfl

theorem constructorConfigExpr_eval (c : ConstructorConfig) (evm : EVM.State) :
    evalExpr? config (constructorSourceEntry c) evm constructorConfigExpr =
      .ok (constructorConfigValue c) := by
  simp only [constructorConfigExpr, constructorConfigNames, List.zipIdx_cons, List.zipIdx_nil,
    List.map_cons, List.map_nil, evalExpr?, evalStructFields?, constructorSourceEntry,
    constructorSourceArgs, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    EvalResult.ofOption, ConstructorConfig.value, ConstructorConfig.scalars, List.cons_append,
    List.nil_append, tupleGetValue?, bind, EvalResult.bind, pure]
  rfl

theorem constructorSourceConfig_exec (c : ConstructorConfig) (evm : EVM.State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 2)
      (.ok (constructorSourceConfig c) evm) := by
  change ExecBlock config _ _
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "config" (some ConstructorConfig.abiType) constructorConfigExpr] _
  exact .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.letDecl (constructorConfigExpr_eval _ _)) .nil)

theorem constructorSource_baseToken (c : ConstructorConfig) (evm : EVM.State) :
    evalExpr? config (constructorSourceConfig c) evm (.field (.var "config") "baseToken") =
      .ok (.address c.baseToken) := by
  simp only [evalExpr?, constructorSourceConfig, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem constructorSourceDecimals_exec {c : ConstructorConfig} {evm evm' : EVM.State}
    {out : ByteArray} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hc : callViaEVM evm c.baseToken 0 decimalsPayload (true, evm', out) false)
    (hhi : out.size < 2^255) (hvalid : DecimalsReturnValid out) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 3)
      (.ok (constructorSourceDecimals c (calldataWord out 0)) evm') := by
  change ExecBlock config _ _ (contract.ctor.body.take 2 ++ [contract.ctor.body[2]!]) _
  apply execBlockAppendOk (constructorSourceConfig_exec c evm hv)
  exact .consNormal (decimals_source_ok (constructorSource_baseToken c evm) hc hhi hvalid) .nil

theorem constructorSourceDecimals_revert {c : ConstructorConfig} {evm evm' : EVM.State}
    {z : Bool} {out : ByteArray} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hc : callViaEVM evm c.baseToken 0 decimalsPayload (z, evm', out) false)
    (hhi : out.size < 2^255) (hvalid : ¬ (z = true ∧ DecimalsReturnValid out)) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body .reverted := by
  rw [← List.take_append_drop 2 contract.ctor.body]
  apply execBlockAppendOk (constructorSourceConfig_exec c evm hv)
  exact .consRevert (decimals_source_revert (constructorSource_baseToken c evm) hc hhi hvalid)

end Benchmarks.CompoundIII.Comet
