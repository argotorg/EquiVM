import Benchmarks.CompoundIII.Comet.AssetSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

/-- The external-call trace of the asset-address search, including every revert case. -/
inductive AssetSearch (v : CometWithExtendedAssetListImmutables) (asset : AccountAddress) :
    Nat → EVM.State → Option (EVM.State × ByteArray) → Prop where
  | exhausted {i evm} (h : v.numAssets.toNat ≤ i) : AssetSearch v asset i evm none
  | failed {i evm evm' z out} (hi : i < v.numAssets.toNat)
      (hc : callViaEVM evm v.assetList 0 (assetPayload (UInt256.ofNat i))
        (z, evm', out) false)
      (hsize : out.size < 2^255) (hv : ¬ (z = true ∧ AssetValid out)) :
      AssetSearch v asset i evm none
  | found {i evm evm' out} (hi : i < v.numAssets.toNat)
      (hc : callViaEVM evm v.assetList 0 (assetPayload (UInt256.ofNat i))
        (true, evm', out) false)
      (hsize : out.size < 2^255) (hv : AssetValid out)
      (ha : AccountAddress.ofNat (calldataWord out 32).toNat = asset) :
      AssetSearch v asset i evm (some (evm', out))
  | next {i evm evm' out result} (hi : i < v.numAssets.toNat)
      (hc : callViaEVM evm v.assetList 0 (assetPayload (UInt256.ofNat i))
        (true, evm', out) false)
      (hsize : out.size < 2^255) (hv : AssetValid out)
      (ha : AccountAddress.ofNat (calldataWord out 32).toNat ≠ asset)
      (tail : AssetSearch v asset (i + 1) evm' result) : AssetSearch v asset i evm result

def assetSearchCond : Expr := .binary .lt (.var "i") (.immutable "numAssets")

def assetSearchMatch : Expr := .binary .eq (.field (.var "assetInfo") "asset") (.var "asset")

def assetSearchIncrement : Stmt := .assign .localVar ⟨"i", []⟩
  (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int (.uint ⟨8, by decide⟩))))

def assetSearchBody : List Stmt :=
  [.internalCall "getAssetInfo_body" [.var "i"] "assetInfo",
    .ite assetSearchMatch [.return [.var "assetInfo"]] [], assetSearchIncrement]

def assetSearchTail : List Stmt :=
  [.while assetSearchCond assetSearchBody, .require (.boolLit false)]

def assetSearchCallable : CallableDecl :=
  { params := [⟨"asset", abiAddress⟩], returnType := [assetInfoType],
    body := .letDecl "i" (some (.elem (.int (.uint ⟨8, by decide⟩)))) (.intLit 0) ::
      assetSearchTail }

theorem assetSearchCallable_lookup :
    lookupCallable? contract "getAssetInfoByAddress_body" = some assetSearchCallable := rfl

-- LIBRARY CANDIDATE: prepend one normal iteration to a while loop and its continuation.
theorem execBlock_while_step {cfg : Config} {f f' : Frame} {e e' : EVM.State}
    {cond : Expr} {body tail : List Stmt} {result : ExecResult}
    (hc : evalExpr? cfg f e cond = .ok (.bool true))
    (hb : ExecBlock cfg f e body (.ok f' e'))
    (ht : ExecBlock cfg f' e' (.while cond body :: tail) result) :
    ExecBlock cfg f e (.while cond body :: tail) result := by
  cases ht with
  | consNormal hw ht => exact .consNormal (.whileTrue hc hb hw) ht
  | consReturn hw => exact .consReturn (.whileTrue hc hb hw)
  | consRevert hw => exact .consRevert (.whileTrue hc hb hw)
  | consBreak hw => exact .consBreak (.whileTrue hc hb hw)
  | consContinue hw => exact .consContinue (.whileTrue hc hb hw)
  | consStatic hw => exact .consStatic (.whileTrue hc hb hw)

theorem assetSearchCond_eval {v : CometWithExtendedAssetListImmutables}
    {frame : Frame} {evm : EVM.State} {i : Nat}
    (him : frame.immutables = immStore v) (hi : frame.locals.get? "i" = some (.int i)) :
    evalExpr? config frame evm assetSearchCond = .ok (.bool (decide (i < v.numAssets.toNat))) := by
  simp only [assetSearchCond, evalExpr?, hi, him, immStore_get_numAssets,
    EvalResult.ofOption, bind, EvalResult.bind, evalBinaryOp_lt_int_ok,
    Int.ofNat_eq_natCast]
  simp only [Int.ofNat_lt]

theorem assetSearchMatch_eval {frame : Frame} {evm : EVM.State} {out : ByteArray}
    {asset : AccountAddress}
    (hi : frame.locals.get? "assetInfo" = some (assetValue out))
    (ha : frame.locals.get? "asset" = some (.address asset)) :
    evalExpr? config frame evm assetSearchMatch =
      .ok (.bool (decide (AccountAddress.ofNat (calldataWord out 32).toNat = asset))) := by
  simp only [assetSearchMatch, evalExpr?, hi, ha, EvalResult.ofOption, bind, EvalResult.bind,
    assetValue, lookupField?]
  simp [lookupAssoc, evalBinaryOp?, beq_eq_decide]

theorem assetSearchIncrement_exec {frame : Frame} {evm : EVM.State} {i : Nat}
    (hi : frame.locals.get? "i" = some (.int i)) (hb : i + 1 < 256) :
    ExecStmt config frame evm assetSearchIncrement
      (.ok { frame with locals := frame.locals.insert "i" (.int (i + 1)) } evm) := by
  apply ExecStmt.assign (value := .int (i + 1))
  · simp only [evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind, pure,
      evalBinaryOp_add_int_ok, castValue?]
    rw [normalizeInt_uint_eq_self _ _ (by omega) (by change (i : Int) + 1 < 256; omega)]
  · simp only [assignStorageRef?, hi, updateLocalPath?, pure, bind, EvalResult.bind]

theorem assetSearch_exec {v : CometWithExtendedAssetListImmutables}
    {asset : AccountAddress} {i : Nat} {evm : EVM.State}
    {result : Option (EVM.State × ByteArray)} (h : AssetSearch v asset i evm result)
    (frame : Frame) (hf : frame.contract = contract) (him : frame.immutables = immStore v)
    (hi : frame.locals.get? "i" = some (.int i))
    (ha : frame.locals.get? "asset" = some (.address asset)) :
    match result with
    | none => ExecBlock config frame evm assetSearchTail .reverted
    | some (evm', out) => ∃ frame', ExecBlock config frame evm assetSearchTail
        (.returned frame' evm' (some [assetValue out])) := by
  induction h generalizing frame with
  | exhausted h =>
      apply ExecBlock.consNormal (ExecStmt.whileFalse ?_)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))
      rw [assetSearchCond_eval him hi, decide_eq_false (by omega)]
  | @failed i evm evm' z out hib hc hsize hv =>
      apply ExecBlock.consRevert (ExecStmt.whileRevert ?_ ?_)
      · rw [assetSearchCond_eval him hi, decide_eq_true hib]
      · apply ExecBlock.consRevert (asset_call_revert frame evm evm' (UInt256.ofNat i)
          v.assetList (.var "i") "assetInfo" out z hf (him ▸ immStore_get_assetList v)
          ?_ hc hsize hv)
        rw [UInt256.toNat_ofNat_of_lt (by have := v.numAssets_lt; change i < 2^256; omega)]
        simp only [evalExpr?, hi, EvalResult.ofOption, Int.ofNat_eq_natCast]
  | @found i evm evm' out hib hc hsize hv heq =>
      let f := { frame with locals := frame.locals.insert "assetInfo" (assetValue out) }
      refine ⟨f, ExecBlock.consReturn (ExecStmt.whileReturn ?_ ?_)⟩
      · rw [assetSearchCond_eval him hi, decide_eq_true hib]
      · apply ExecBlock.consNormal (asset_call_ok frame evm evm' (UInt256.ofNat i)
          v.assetList (.var "i") "assetInfo" out hf (him ▸ immStore_get_assetList v)
          ?_ hc hsize hv)
        · apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
          · rw [assetSearchMatch_eval (frame := f) (out := out) (asset := asset)
              (by simp [f, Std.HashMap.getElem?_insert])
              (by simpa [f, Std.HashMap.getElem?_insert] using ha),
              decide_eq_true heq]
          · exact ABlock.start.returns (by
              simp only [evalExpr?, evalExprs?, f, Std.HashMap.get?_eq_getElem?,
                Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]
              rfl)
        · rw [UInt256.toNat_ofNat_of_lt (by have := v.numAssets_lt; change i < 2^256; omega)]
          simp only [evalExpr?, hi, EvalResult.ofOption, Int.ofNat_eq_natCast]
  | @next i evm evm' out result hib hc hsize hv hne tail ih =>
      let f := { frame with locals := frame.locals.insert "assetInfo" (assetValue out) }
      let f' := { f with locals := f.locals.insert "i" (.int (i + 1)) }
      have hib' : f.locals.get? "i" = some (.int i) := by
        simpa [f, Std.HashMap.getElem?_insert] using hi
      have hab' : f'.locals.get? "asset" = some (.address asset) := by
        simpa [f', f, Std.HashMap.getElem?_insert] using ha
      have hb : ExecBlock config frame evm assetSearchBody (.ok f' evm') := by
        apply ExecBlock.consNormal (asset_call_ok frame evm evm' (UInt256.ofNat i)
          v.assetList (.var "i") "assetInfo" out hf (him ▸ immStore_get_assetList v)
          ?_ hc hsize hv)
        · apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil)
          · exact ExecBlock.consNormal
              (assetSearchIncrement_exec hib' (by have := v.numAssets_lt; omega)) ExecBlock.nil
          · rw [assetSearchMatch_eval (frame := f) (out := out) (asset := asset)
              (by simp [f, Std.HashMap.getElem?_insert])
              (by simpa [f, Std.HashMap.getElem?_insert] using ha),
              decide_eq_false hne]
        · rw [UInt256.toNat_ofNat_of_lt (by have := v.numAssets_lt; change i < 2^256; omega)]
          simp only [evalExpr?, hi, EvalResult.ofOption, Int.ofNat_eq_natCast]
      have hcond := assetSearchCond_eval (evm := evm) him hi
      rw [decide_eq_true hib] at hcond
      have ht := ih f' hf him (by simp [f', Std.HashMap.getElem?_insert, Int.ofNat_eq_natCast]) hab'
      cases result with
      | none => exact execBlock_while_step hcond hb ht
      | some result =>
          obtain ⟨f'', ht⟩ := ht
          exact ⟨f'', execBlock_while_step hcond hb ht⟩

theorem assetSearch_call {v : CometWithExtendedAssetListImmutables}
    {asset : AccountAddress} {evm : EVM.State} {result : Option (EVM.State × ByteArray)}
    (h : AssetSearch v asset 0 evm result) (frame : Frame) (expr : Expr) (ret : Ident)
    (hf : frame.contract = contract) (him : frame.immutables = immStore v)
    (he : evalExpr? config frame evm expr = .ok (.address asset)) :
    match result with
    | none => ExecStmt config frame evm (.internalCall "getAssetInfoByAddress_body" [expr] ret)
        .reverted
    | some (evm', out) =>
        ExecStmt config frame evm (.internalCall "getAssetInfoByAddress_body" [expr] ret)
          (.ok { frame with locals := frame.locals.insert ret (assetValue out) } evm') := by
  let locals := (∅ : Store).insert "asset" (.address asset)
  let entry : Frame := { contract := contract, locals := locals, immutables := immStore v }
  let f : Frame := { entry with locals := locals.insert "i" (.int 0) }
  have ht := assetSearch_exec h f rfl rfl
    (by simp only [f, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
    (by simp only [f, locals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)
  have hi : ExecStmt config entry evm
      (.letDecl "i" (some (.elem (.int (.uint ⟨8, by decide⟩)))) (.intLit 0))
      (.ok f evm) := ExecStmt.letDecl (by simp only [evalExpr?, pure])
  cases result with
  | none =>
      apply ExecStmt.internalCallRevert (callee := assetSearchCallable) (locals := locals)
        (argVals := [.address asset])
        (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
        (by rw [hf]; exact assetSearchCallable_lookup) rfl
      have hb : ExecFuncBody config entry evm assetSearchCallable.body .reverted :=
        .execBlockRevert (.consNormal hi ht)
      simpa only [entry, hf, him] using hb
  | some result =>
      obtain ⟨evm', out⟩ := result
      obtain ⟨f', ht⟩ := ht
      have hb : ExecFuncBody config entry evm assetSearchCallable.body
          (.returned f' evm' (some [assetValue out])) := .execBlockRet (.consNormal hi ht)
      exact ExecStmt.internalCallReturn (callee := assetSearchCallable) (locals := locals)
        (cfg := config) (solm := frame) (evm := evm) (args := [expr])
        (argVals := [.address asset])
        (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
        (by rw [hf]; exact assetSearchCallable_lookup) rfl
        (by simpa only [entry, hf, him] using hb)

end Benchmarks.CompoundIII.Comet
