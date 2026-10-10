import Benchmarks.CompoundIII.Comet.CreateAssetListLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def createAssetListStartFrame (imms : Store) (factory : AccountAddress)
    (assets : List ConstructorAsset) : Frame :=
  let frame := createAssetListEntry imms factory assets
  let locals := frame.locals.insert "payload" (.bytes (createAssetListHeader assets.length))
  { frame with locals := locals.insert "index" (.int 0) }

theorem createAssetListStartFrame_state (imms : Store) (factory : AccountAddress)
    (assets : List ConstructorAsset) :
    CreateAssetListLoopState factory assets 0 (createAssetListStartFrame imms factory assets) := by
  constructor <;>
    simp only [createAssetListStartFrame, createAssetListEntry, createAssetListPayload_zero,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl

theorem createAssetListPrefix_exec (imms : Store) (factory : AccountAddress)
    (assets : List ConstructorAsset) (evm : EVM.State) (hn : assets.length < UInt256.size) :
    ∃ frame, ExecBlock config (createAssetListEntry imms factory assets) evm createAssetListPrefix
      (.ok frame evm) ∧ CreateAssetListLoopState factory assets assets.length frame := by
  obtain ⟨frame, hw, hi⟩ := createAssetListLoop_exec
    (createAssetListStartFrame_state imms factory assets) evm (Nat.zero_le _)
  refine ⟨frame, ?_, hi⟩
  refine .consNormal (.letDecl (createAssetListHeader_eval ?_ hn)) ?_
  · simp only [createAssetListEntry, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  refine .consNormal (.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  exact .consNormal hw .nil

theorem createAssetListReturn_decode {out : ByteArray} (hhi : out.size < 2^255) :
    decodeReturnValueWithMode? config.abiDecodeMode abiAddress out =
      if ConstructorFactoryReturnValid out then
        some (.address (AccountAddress.ofUInt256 (calldataWord out 0))) else none := by
  have hd := constructorFactory_decode hhi
  change (decodeReturnValueWithMode? config.abiDecodeMode abiAddress out).map
    (fun v ↦ [v]) = _ at hd
  cases he : decodeReturnValueWithMode? config.abiDecodeMode abiAddress out <;>
    by_cases hv : ConstructorFactoryReturnValid out <;> simp_all

def createAssetListCallFrame (frame : Frame) (z : Bool) (out : ByteArray) : Frame :=
  { frame with locals := (frame.locals.insert "ok" (.bool z)).insert "result" (.bytes out) }

def createAssetListDecodedFrame (frame : Frame) (out : ByteArray) : Frame :=
  let frame := createAssetListCallFrame frame true out
  { frame with locals := (frame.locals.insert "resultAddress"
    (.address (AccountAddress.ofUInt256 (calldataWord out 0)))) }

theorem createAssetListCall_exec {factory : AccountAddress} {assets : List ConstructorAsset}
    {frame : Frame} {evm evm' : EVM.State} {z : Bool} {out : ByteArray}
    (h : CreateAssetListLoopState factory assets assets.length frame)
    (hc : callViaEVM evm factory 0 (createAssetListPayload assets assets.length) (z, evm', out)) :
    ExecStmt config frame evm
      (.lowLevelCall (.var "factory") (.intLit 0) (.var "payload") "ok" "result")
      (.ok (createAssetListCallFrame frame z out) evm') := by
  exact lowLevelCallSourceWithPerm (target := factory) (value := 0)
    (calldata := createAssetListPayload assets assets.length)
    (by simp only [evalExpr?, h.factory, EvalResult.ofOption])
    (by simp only [evalExpr?, pure])
    (by simp only [evalExpr?, h.payload, EvalResult.ofOption]) hc

theorem createAssetListRemainder_ok {factory : AccountAddress} {assets : List ConstructorAsset}
    {frame : Frame} {evm evm' : EVM.State} {out : ByteArray}
    (h : CreateAssetListLoopState factory assets assets.length frame)
    (hc : callViaEVM evm factory 0 (createAssetListPayload assets assets.length) (true, evm', out))
    (hhi : out.size < 2^255) (hv : ConstructorFactoryReturnValid out) :
    ExecBlock config frame evm createAssetListRemainder
      (.returned (createAssetListDecodedFrame frame out) evm'
        (some [.address (AccountAddress.ofUInt256 (calldataWord out 0))])) := by
  refine .consNormal (createAssetListCall_exec h hc) ?_
  refine .consNormal (.requireTrue ?_) ?_
  · simp only [evalExpr?, createAssetListCallFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  refine .consNormal (.letDecl (value := .address (AccountAddress.ofUInt256 (calldataWord out 0)))
    ?_) ?_
  · simp only [evalExpr?, createAssetListCallFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
    change (match decodeReturnValueWithMode? config.abiDecodeMode abiAddress out with
      | some value => EvalResult.ok value | none => .revert) = _
    rw [createAssetListReturn_decode hhi, if_pos hv]
  apply ABlock.returns ABlock.start
  simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    EvalResult.ofOption]
  rfl

theorem createAssetListRemainder_revert {factory : AccountAddress} {assets : List ConstructorAsset}
    {frame : Frame} {evm evm' : EVM.State} {z : Bool} {out : ByteArray}
    (h : CreateAssetListLoopState factory assets assets.length frame)
    (hc : callViaEVM evm factory 0 (createAssetListPayload assets assets.length) (z, evm', out))
    (hhi : out.size < 2^255) (hv : ¬ (z = true ∧ ConstructorFactoryReturnValid out)) :
    ExecBlock config frame evm createAssetListRemainder .reverted := by
  refine .consNormal (createAssetListCall_exec h hc) ?_
  cases z with
  | false =>
    apply ExecBlock.consRevert (.requireFalse ?_)
    simp only [evalExpr?, createAssetListCallFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  | true =>
    refine .consNormal (.requireTrue ?_) ?_
    · simp only [evalExpr?, createAssetListCallFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl
    apply ExecBlock.consRevert (.letDeclRevert ?_)
    simp only [evalExpr?, createAssetListCallFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
    change (match decodeReturnValueWithMode? config.abiDecodeMode abiAddress out with
      | some value => EvalResult.ok value | none => .revert) = _
    rw [createAssetListReturn_decode hhi, if_neg (fun hh ↦ hv ⟨rfl, hh⟩)]

theorem createAssetListBody_ok (imms : Store) (factory : AccountAddress)
    (assets : List ConstructorAsset) {evm evm' : EVM.State} {out : ByteArray}
    (hn : assets.length < UInt256.size)
    (hc : callViaEVM evm factory 0 (createAssetListPayload assets assets.length) (true, evm', out))
    (hhi : out.size < 2^255) (hv : ConstructorFactoryReturnValid out) :
    ∃ final, ExecFuncBody config (createAssetListEntry imms factory assets) evm
      createAssetListCallable.body
      (.returned final evm' (some [.address (AccountAddress.ofUInt256 (calldataWord out 0))])) := by
  obtain ⟨frame, hp, hs⟩ := createAssetListPrefix_exec imms factory assets evm hn
  exact ⟨_, .execBlockRet (execBlockAppendOk hp (createAssetListRemainder_ok hs hc hhi hv))⟩

theorem createAssetListBody_revert (imms : Store) (factory : AccountAddress)
    (assets : List ConstructorAsset) {evm evm' : EVM.State} {z : Bool} {out : ByteArray}
    (hn : assets.length < UInt256.size)
    (hc : callViaEVM evm factory 0 (createAssetListPayload assets assets.length) (z, evm', out))
    (hhi : out.size < 2^255) (hv : ¬ (z = true ∧ ConstructorFactoryReturnValid out)) :
    ExecFuncBody config (createAssetListEntry imms factory assets) evm
      createAssetListCallable.body .reverted := by
  obtain ⟨frame, hp, hs⟩ := createAssetListPrefix_exec imms factory assets evm hn
  exact .execBlockRevert (execBlockAppendOk hp (createAssetListRemainder_revert hs hc hhi hv))

end Benchmarks.CompoundIII.Comet
