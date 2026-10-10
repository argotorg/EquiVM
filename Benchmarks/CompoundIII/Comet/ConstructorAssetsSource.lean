import Benchmarks.CompoundIII.Comet.CreateAssetListInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorFinalImms (c : ConstructorConfig) (w assetList : UInt256) : Store :=
  (constructorRemainingImms c w).insert "assetList" (.address (AccountAddress.ofUInt256 assetList))

def constructorSourceFinal (c : ConstructorConfig) (w feed factory assetList : UInt256) : Frame :=
  let frame := constructorSourceFactory c w feed factory
  { frame with
    locals := frame.locals.insert "__c3" (.address (AccountAddress.ofUInt256 assetList))
    immutables := constructorFinalImms c w assetList }

theorem constructorSourceFactory_args {c : ConstructorConfig} {w feed factory : UInt256}
    {evm : EVM.State} :
    evalExpr? config (constructorSourceFactory c w feed factory) evm (.var "__c2") =
      .ok (.address (AccountAddress.ofUInt256 factory)) ∧
    evalExpr? config (constructorSourceFactory c w feed factory) evm
      (.field (.var "config") "assetConfigs") =
      .ok (.array (c.assetConfigs.map ConstructorAsset.value)) := by
  constructor
  · simp only [evalExpr?, constructorSourceFactory, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  · apply constructorSourceField (c := c) ?_ rfl
    simp only [constructorSourceFactory, constructorSourceDelegate, constructorSourceRemainingImms,
      constructorSourceScale, constructorSourceInitialImms, constructorSourcePriceFeed,
      constructorSourceDecimals, constructorSourceConfig, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl

theorem constructorSourceAssets_exec {c : ConstructorConfig} {w feed factory : UInt256}
    {evm evm' evm'' : EVM.State} {out : ByteArray}
    (hn : c.assetConfigs.length < UInt256.size)
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 36)
      (.ok (constructorSourceFactory c w feed factory) evm'))
    (hc : callViaEVM evm' (AccountAddress.ofUInt256 factory) 0
      (createAssetListPayload c.assetConfigs c.assetConfigs.length) (true, evm'', out))
    (hhi : out.size < 2^255) (hv : ConstructorFactoryReturnValid out) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body
      (.ok (constructorSourceFinal c w feed factory (calldataWord out 0)) evm'') := by
  change ExecBlock config _ _ (contract.ctor.body.take 36 ++
    [.internalCall "createAssetList_call"
      [.var "__c2", .field (.var "config") "assetConfigs"] "__c3",
      .setImmutable "assetList" (.var "__c3")]) _
  apply execBlockAppendOk hp
  refine .consNormal (createAssetList_call_ok rfl hn constructorSourceFactory_args.1
    constructorSourceFactory_args.2 hc hhi hv) ?_
  refine .consNormal (.setImmutable (ty := .address)
    (value := .address (AccountAddress.ofUInt256 (calldataWord out 0))) ?_ rfl rfl) .nil
  simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    EvalResult.ofOption]
  rfl

theorem constructorSourceAssets_revert {c : ConstructorConfig} {w feed factory : UInt256}
    {evm evm' evm'' : EVM.State} {z : Bool} {out : ByteArray}
    (hn : c.assetConfigs.length < UInt256.size)
    (hp : ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 36)
      (.ok (constructorSourceFactory c w feed factory) evm'))
    (hc : callViaEVM evm' (AccountAddress.ofUInt256 factory) 0
      (createAssetListPayload c.assetConfigs c.assetConfigs.length) (z, evm'', out))
    (hhi : out.size < 2^255) (hv : ¬ (z = true ∧ ConstructorFactoryReturnValid out)) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body .reverted := by
  rw [← List.take_append_drop 36 contract.ctor.body]
  apply execBlockAppendOk hp
  exact .consRevert (createAssetList_call_revert rfl hn constructorSourceFactory_args.1
    constructorSourceFactory_args.2 hc hhi hv)

end Benchmarks.CompoundIII.Comet
