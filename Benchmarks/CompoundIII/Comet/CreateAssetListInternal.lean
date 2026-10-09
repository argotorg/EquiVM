import Benchmarks.CompoundIII.Comet.CreateAssetListSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem createAssetList_call_ok {frame : Frame} {evm evm' : EVM.State}
    {factory : AccountAddress} {assets : List ConstructorAsset} {out : ByteArray}
    {factoryExpr assetsExpr : Expr} {ret : Ident}
    (hf : frame.contract = contract) (hn : assets.length < UInt256.size)
    (hfactory : evalExpr? config frame evm factoryExpr = .ok (.address factory))
    (hassets : evalExpr? config frame evm assetsExpr =
      .ok (.array (assets.map ConstructorAsset.value)))
    (hc : callViaEVM evm factory 0 (createAssetListPayload assets assets.length) (true, evm', out))
    (hhi : out.size < 2^255) (hv : ConstructorFactoryReturnValid out) :
    ExecStmt config frame evm (.internalCall "createAssetList_call" [factoryExpr, assetsExpr] ret)
      (.ok { frame with locals := (frame.locals.insert ret
        (.address (AccountAddress.ofUInt256 (calldataWord out 0)))) } evm') := by
  obtain ⟨final, hb⟩ := createAssetListBody_ok frame.immutables factory assets hn hc hhi hv
  exact ExecStmt.internalCallReturn (callee := createAssetListCallable)
    (locals := ((∅ : Store).insert "assets" (.array (assets.map ConstructorAsset.value))).insert
      "factory" (.address factory))
    (cfg := config) (solm := frame) (evm := evm)
    (args := [factoryExpr, assetsExpr])
    (argVals := [.address factory, .array (assets.map ConstructorAsset.value)])
    (by simp only [evalExprs?, hfactory, hassets, pure, bind, EvalResult.bind])
    (by rw [hf]; exact createAssetListCallable_lookup) rfl
    (by simpa only [createAssetListEntry, hf] using hb)

theorem createAssetList_call_revert {frame : Frame} {evm evm' : EVM.State}
    {factory : AccountAddress} {assets : List ConstructorAsset} {out : ByteArray} {z : Bool}
    {factoryExpr assetsExpr : Expr} {ret : Ident}
    (hf : frame.contract = contract) (hn : assets.length < UInt256.size)
    (hfactory : evalExpr? config frame evm factoryExpr = .ok (.address factory))
    (hassets : evalExpr? config frame evm assetsExpr =
      .ok (.array (assets.map ConstructorAsset.value)))
    (hc : callViaEVM evm factory 0 (createAssetListPayload assets assets.length) (z, evm', out))
    (hhi : out.size < 2^255) (hv : ¬ (z = true ∧ ConstructorFactoryReturnValid out)) :
    ExecStmt config frame evm (.internalCall "createAssetList_call" [factoryExpr, assetsExpr] ret)
      .reverted := by
  apply ExecStmt.internalCallRevert (callee := createAssetListCallable)
    (locals := ((∅ : Store).insert "assets" (.array (assets.map ConstructorAsset.value))).insert
      "factory" (.address factory))
    (cfg := config) (solm := frame) (evm := evm)
    (args := [factoryExpr, assetsExpr])
    (argVals := [.address factory, .array (assets.map ConstructorAsset.value)])
    (by simp only [evalExprs?, hfactory, hassets, pure, bind, EvalResult.bind])
    (by rw [hf]; exact createAssetListCallable_lookup) rfl
  simpa only [createAssetListEntry, hf] using
    createAssetListBody_revert frame.immutables factory assets hn hc hhi hv

end Benchmarks.CompoundIII.Comet
