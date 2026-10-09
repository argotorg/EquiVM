import Benchmarks.CompoundIII.Comet.AssetDecode
import Benchmarks.CompoundIII.Comet.StaticCallBridge
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def assetPayload (i : UInt256) : ByteArray :=
  ⟨([200, 199, 254, 107] ++ EVM.Word.toBytesBE i).toArray⟩

theorem assetPayload_size (i : UInt256) : (assetPayload i).size = 36 := by
  have hl : (EVM.Word.toBytesBE i).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size i
  change ([200, 199, 254, 107] ++ EVM.Word.toBytesBE i).toArray.size = 36
  simp only [List.size_toArray, List.length_append, List.length_cons, List.length_nil, hl]

def assetPayloadExpr : Expr :=
  .abiEncodePacked [(.elem (.bytes ⟨3, by decide⟩),
    .fixedBytesLit ⟨3, by decide⟩ [200, 199, 254, 107]),
    (abiUInt256, .var "i")]

def assetPrefix : List Stmt :=
  [.letDecl "receiver" (some abiAddress) (.immutable "assetList"),
    .letDecl "payload" (some .bytes) assetPayloadExpr,
    .lowLevelCall (.var "receiver") (.intLit 0) (.var "payload") "ok" "result"
      (perm := false)]

def assetStructExpr : Expr :=
  .structLit "AssetInfo" [("offset", .tupleGet (.var "decoded") 0),
    ("asset", .tupleGet (.var "decoded") 1), ("priceFeed", .tupleGet (.var "decoded") 2),
    ("scale", .tupleGet (.var "decoded") 3),
    ("borrowCollateralFactor", .tupleGet (.var "decoded") 4),
    ("liquidateCollateralFactor", .tupleGet (.var "decoded") 5),
    ("liquidationFactor", .tupleGet (.var "decoded") 6),
    ("supplyCap", .tupleGet (.var "decoded") 7)]

def assetRemainder : List Stmt :=
  [.require (.var "ok"), .letDecl "decoded" none (.abiDecode assetInfoType (.var "result")),
    .return [assetStructExpr]]

def assetCallable : CallableDecl :=
  { params := [⟨"i", .elem (.int (.uint ⟨8, by decide⟩))⟩]
    returnType := [assetInfoType]
    body := assetPrefix ++ assetRemainder }

theorem assetCallable_lookup :
    lookupCallable? contract "getAssetInfo_body" = some assetCallable := rfl

def assetEntry (imms : Store) (i : UInt256) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "i" (.int (Int.ofNat i.toNat)),
    immutables := imms }

def assetCallFrame (imms : Store) (i : UInt256) (addr : AccountAddress)
    (z : Bool) (out : ByteArray) : Frame :=
  let f := assetEntry imms i
  { f with locals := (((f.locals.insert "receiver" (.address addr)).insert "payload"
    (.bytes (assetPayload i))).insert "ok" (.bool z)).insert "result" (.bytes out) }

def assetDecodedFrame (imms : Store) (i : UInt256) (addr : AccountAddress)
    (out : ByteArray) : Frame :=
  let f := assetCallFrame imms i addr true out
  { f with locals := f.locals.insert "decoded" (assetTuple out) }

def assetValue (out : ByteArray) : Value :=
  .struct "AssetInfo" [("offset", .int (calldataWord out 0).toNat),
    ("asset", .address (AccountAddress.ofNat (calldataWord out 32).toNat)),
    ("priceFeed", .address (AccountAddress.ofNat (calldataWord out 64).toNat)),
    ("scale", .int (calldataWord out 96).toNat),
    ("borrowCollateralFactor", .int (calldataWord out 128).toNat),
    ("liquidateCollateralFactor", .int (calldataWord out 160).toNat),
    ("liquidationFactor", .int (calldataWord out 192).toNat),
    ("supplyCap", .int (calldataWord out 224).toNat)]

def AssetValid (out : ByteArray) : Prop := 256 ≤ out.size ∧ AssetCanonical out

instance (out : ByteArray) : Decidable (AssetValid out) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem assetPayload_eval (frame : Frame) (evm : EVM.State) (i : UInt256)
    (hi : evalExpr? config frame evm (.var "i") = .ok (.int (Int.ofNat i.toNat))) :
    evalExpr? config frame evm assetPayloadExpr = .ok (.bytes (assetPayload i)) := by
  have hf : encodePackedValue? (.elem (.bytes ⟨3, by decide⟩))
      (.fixedBytes ⟨3, by decide⟩ [200, 199, 254, 107]) =
      some [200, 199, 254, 107] := by decide
  have hp := evalPackedArgs_cons (show evalExpr? config frame evm
    (.fixedBytesLit ⟨3, by decide⟩ [200, 199, 254, 107]) =
      .ok (.fixedBytes ⟨3, by decide⟩ [200, 199, 254, 107]) by
        simp only [evalExpr?, pure]) hf (evalPackedArgs_single hi (encodePacked_uint256 i))
  rw [assetPayloadExpr, evalExpr?, hp]
  rfl

theorem assetPrefix_exec (imms : Store) (i : UInt256) (addr : AccountAddress)
    (evm evm' : EVM.State) (z : Bool) (out : ByteArray)
    (ha : imms.get? "assetList" = some (.address addr))
    (hc : callViaEVM evm addr 0 (assetPayload i) (z, evm', out) false) :
    ExecBlock config (assetEntry imms i) evm assetPrefix
      (.ok (assetCallFrame imms i addr z out) evm') := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .address addr) ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl (assetPayload_eval _ _ i ?_))
    · apply ExecBlock.consNormal (lowLevelCallSourceWithPerm (target := addr)
        (value := 0) (calldata := assetPayload i) ?_ (by simp only [evalExpr?, pure]) ?_ hc)
      · exact ExecBlock.nil
      all_goals
        simp only [evalExpr?, assetEntry, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl
    · simp only [evalExpr?, assetEntry, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl
  · simp only [evalExpr?, assetEntry, ha, EvalResult.ofOption]

theorem assetDecoded_exec (imms : Store) (i : UInt256) (addr : AccountAddress)
    (evm : EVM.State) (out : ByteArray) (hhi : out.size < 2^255) (hv : AssetValid out) :
    ExecBlock config (assetCallFrame imms i addr true out) evm
      (assetRemainder.take 2) (.ok (assetDecodedFrame imms i addr out) evm) := by
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl (value := assetTuple out) ?_) ExecBlock.nil
    have hd := assetDecode_result hv.1 hhi
    rw [if_pos hv.2] at hd
    simp only [evalExpr?, assetCallFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
    change (match decodeReturnValueWithMode? .modern assetInfoType out with
      | some value => EvalResult.ok value | none => .revert) = _
    rw [hd]
  · simp only [evalExpr?, assetCallFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl

theorem assetRemainder_returns (imms : Store) (i : UInt256) (addr : AccountAddress)
    (evm : EVM.State) (out : ByteArray) (hhi : out.size < 2^255) (hv : AssetValid out) :
    ExecBlock config (assetCallFrame imms i addr true out) evm assetRemainder
      (.returned (assetDecodedFrame imms i addr out) evm (some [assetValue out])) := by
  change ExecBlock config _ _ (assetRemainder.take 2 ++ assetRemainder.drop 2) _
  apply execBlockAppendOk (assetDecoded_exec imms i addr evm out hhi hv)
  apply ABlock.returns ABlock.start
  simp only [assetStructExpr, evalExpr?, evalStructFields?, assetDecodedFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
    pure, bind, EvalResult.bind, assetTuple, tupleGetValue?]
  rfl

theorem assetRemainder_reverts (imms : Store) (i : UInt256) (addr : AccountAddress)
    (evm : EVM.State) (out : ByteArray) (z : Bool) (hhi : out.size < 2^255)
    (hv : ¬ (z = true ∧ AssetValid out)) :
    ExecBlock config (assetCallFrame imms i addr z out) evm assetRemainder .reverted := by
  cases z with
  | false =>
      apply ABlock.start.requireRevert
      simp only [evalExpr?, assetCallFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, EvalResult.ofOption]
      rfl
  | true =>
      have hd : decodeReturnValueWithMode? .modern assetInfoType out = none := by
        by_cases hlo : 256 ≤ out.size
        · rw [assetDecode_result hlo hhi, if_neg (fun h ↦ hv ⟨rfl, hlo, h⟩)]
        · exact assetDecode_short (Nat.lt_of_not_ge hlo)
      apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
      · apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
        simp only [evalExpr?, assetCallFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
        change (match decodeReturnValueWithMode? .modern assetInfoType out with
          | some value => EvalResult.ok value | none => .revert) = _
        rw [hd]
      · simp only [evalExpr?, assetCallFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption]
        rfl

theorem asset_call_ok (frame : Frame) (evm evm' : EVM.State) (i : UInt256)
    (addr : AccountAddress) (expr : Expr) (ret : Ident) (out : ByteArray)
    (hf : frame.contract = contract)
    (ha : frame.immutables.get? "assetList" = some (.address addr))
    (he : evalExpr? config frame evm expr = .ok (.int (Int.ofNat i.toNat)))
    (hc : callViaEVM evm addr 0 (assetPayload i) (true, evm', out) false)
    (hhi : out.size < 2^255) (hv : AssetValid out) :
    ExecStmt config frame evm (.internalCall "getAssetInfo_body" [expr] ret)
      (.ok { frame with locals := frame.locals.insert ret (assetValue out) } evm') := by
  have hb : ExecFuncBody config (assetEntry frame.immutables i) evm assetCallable.body
      (.returned (assetDecodedFrame frame.immutables i addr out) evm'
        (some [assetValue out])) :=
    .execBlockRet (execBlockAppendOk (assetPrefix_exec _ _ _ _ _ _ _ ha hc)
      (assetRemainder_returns _ _ _ _ _ hhi hv))
  exact ExecStmt.internalCallReturn (callee := assetCallable)
    (locals := (∅ : Store).insert "i" (.int (Int.ofNat i.toNat)))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr])
    (argVals := [.int (Int.ofNat i.toNat)])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hf]; exact assetCallable_lookup) rfl (by simpa only [hf] using hb)

theorem asset_call_revert (frame : Frame) (evm evm' : EVM.State) (i : UInt256)
    (addr : AccountAddress) (expr : Expr) (ret : Ident) (out : ByteArray) (z : Bool)
    (hf : frame.contract = contract)
    (ha : frame.immutables.get? "assetList" = some (.address addr))
    (he : evalExpr? config frame evm expr = .ok (.int (Int.ofNat i.toNat)))
    (hc : callViaEVM evm addr 0 (assetPayload i) (z, evm', out) false)
    (hhi : out.size < 2^255) (hv : ¬ (z = true ∧ AssetValid out)) :
    ExecStmt config frame evm (.internalCall "getAssetInfo_body" [expr] ret) .reverted := by
  apply ExecStmt.internalCallRevert (callee := assetCallable)
    (locals := (∅ : Store).insert "i" (.int (Int.ofNat i.toNat)))
    (cfg := config) (solm := frame) (evm := evm) (args := [expr])
    (argVals := [.int (Int.ofNat i.toNat)])
    (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
    (by rw [hf]; exact assetCallable_lookup) rfl
  have hb : ExecFuncBody config (assetEntry frame.immutables i) evm assetCallable.body
      .reverted :=
    .execBlockRevert (execBlockAppendOk (assetPrefix_exec _ _ _ _ _ _ _ ha hc)
      (assetRemainder_reverts _ _ _ _ _ _ hhi hv))
  simpa only [hf] using hb

end Benchmarks.CompoundIII.Comet
