import Benchmarks.WETH9.TransferFrom

/-!
# WETH9 `transfer(address,uint256)` refinement

`transfer(dst, wad)` desugars (Solm `transferTransition.body`) to
`transferFrom(msg.sender, dst, wad)` followed by returning the bool.  On the solc 0.5.16 runtime the
`transfer` dispatch (pc 644) pushes `msg.sender` for `src` and converges on the *same* internal body
at pc 1087 as public `transferFrom` — so the body always takes the `src == caller` (SkipSender)
branch: no allowance logic, only the two balance stores.  The EVM body lemmas (`weth9TF*` in
`TransferFromBody.lean`) and the post-state `accountMapEquiv` bridge (`wtfPostMap_accountMapEquiv`)
are reused directly; only the internal-call wrapper (`1661 → 1087`), the internal-return tail
(`1674 → 361`), and the Solm-side `transferFrom` body on the `src = .address msg.sender` bind-store
are proved here.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## Decoded arguments for `transfer(dst, wad)`

`dst` is the first argument (`calldata[4]`), `wad` the second (`calldata[36]`).  Note these overlap
the `transferFrom` `src`/`dst` calldata offsets, so `tfSrcWord`/`tfSrcMasked` (both `calldata[4]`)
and `tfDstWord` (`calldata[36]`) reconcile the storage slots via `tfBalSrcSlot_eq`. -/

abbrev xferDstWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4
abbrev xferWadWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36
abbrev xferDstMasked (I : ExecutionEnv) : UInt256 := UInt256.land solcAddrMask (xferDstWord I)

abbrev xferDstVal (I : ExecutionEnv) : Value := .address (AccountAddress.ofNat (xferDstWord I).toNat)
abbrev xferWadVal (I : ExecutionEnv) : Value := .int (Int.ofNat (xferWadWord I).toNat)

/-- The `transfer` public store (decoded `dst`, `wad`). -/
abbrev transferStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "dst" (xferDstVal I)).insert "wad" (xferWadVal I)

/-- The internal `transferFrom(msg.sender, dst, wad)` callee store (`src` bound to `msg.sender`). -/
abbrev transferCallStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "wad" (xferWadVal I)).insert "dst" (xferDstVal I)).insert "src"
    (.address I.source)

theorem transferCallStore_bind (I : ExecutionEnv) :
    bindParams? transferFromTransition.params
        [.address I.source, xferDstVal I, xferWadVal I] = some (transferCallStore I) := by
  rfl

theorem xferDecode_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = some (transferStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["dst", "wad"] [addr, uint256]
    I.calldata = _
  simpa [transferStore, xferDstVal, xferWadVal, xferDstWord, xferWadWord, calldataWord]
    using decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "dst") (y := "wad") hsz68

theorem xferDecode_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["dst", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "dst") (y := "wad") hsz4 hshort

theorem weth9SelectorDispatchTransfer {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 8)) :
    selectorDispatchMsg contract I.calldata = some transferTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes, weth9WithdrawSelectorBytes, weth9DecimalsSelectorBytes,
    weth9BalanceOfSelectorBytes, weth9SymbolSelectorBytes, weth9TransferSelectorBytes]
  decide +native

/-! ## Storage slots and reconciliations

`balanceOf[src]` (with `src = msg.sender`) lives at `callerBalSlot I = wtfBalSlot (solcSourceWord I)`;
`balanceOf[dst]` (with `dst = calldata[4]`) at `xferDstSlot I = wtfBalSlot (xferDstMasked I)`. -/

abbrev xferDstBalRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address (AccountAddress.ofNat (xferDstWord I).toNat))] }
def xferDstSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (xferDstWord I).toNat))

theorem xfer_callerBalSlot_eq (I : ExecutionEnv) :
    callerBalSlot I = solcMappingSlot ⟨3⟩ (solcSourceWord I) := by
  unfold callerBalSlot balanceOfSlot solcMappingSlot mapSlot solcSourceWord
  rw [keyValueToWord_address]
theorem xfer_dstSlot_eq (I : ExecutionEnv) : xferDstSlot I = wtfBalSlot (xferDstMasked I) := by
  unfold xferDstSlot xferDstMasked xferDstWord
  exact tfBalSrcSlot_eq I

/-! ## Solm-side store lookups -/

theorem transferCallStore_get_src (I : ExecutionEnv) :
    (transferCallStore I).get? "src" = some (.address I.source) := by
  unfold transferCallStore; simp
theorem transferCallStore_get_dst (I : ExecutionEnv) :
    (transferCallStore I).get? "dst" = some (xferDstVal I) := by
  unfold transferCallStore
  rw [store_get_ne (L := ((∅ : Store).insert "wad" (xferWadVal I)).insert "dst" (xferDstVal I))
    (k := "src") (a := "dst") (.address I.source) (by decide +native)]; simp
theorem transferCallStore_get_wad (I : ExecutionEnv) :
    (transferCallStore I).get? "wad" = some (xferWadVal I) := by
  unfold transferCallStore
  rw [store_get_ne (L := ((∅ : Store).insert "wad" (xferWadVal I)).insert "dst" (xferDstVal I))
    (k := "src") (a := "wad") (.address I.source) (by decide +native)]
  rw [store_get_ne (L := (∅ : Store).insert "wad" (xferWadVal I))
    (k := "dst") (a := "wad") (xferDstVal I) (by decide +native)]; simp
theorem transferStore_index_dst (I : ExecutionEnv) : (transferStore I)["dst"] = xferDstVal I := by
  unfold transferStore; rw [Std.HashMap.getElem_insert]; simp
theorem transferStore_index_wad (I : ExecutionEnv) : (transferStore I)["wad"] = xferWadVal I := by
  unfold transferStore; simp

/-! ## Solm-side storage-ref evaluations (`balanceOf[.var "src"/"dst"]`) -/

theorem xferCall_srcRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferCallStore I } evm
      (balanceOfRef (.var "src")) = .ok (callerBalRef I) := by
  simp only [balanceOfRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    evalExpr?, EvalResult.ofOption, transferCallStore_get_src, valueToKey?, EvalResult.bind,
    bind, pure, callerBalRef]
theorem xferCall_dstRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferCallStore I } evm
      (balanceOfRef (.var "dst")) = .ok (xferDstBalRef I) := by
  simp only [balanceOfRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    evalExpr?, EvalResult.ofOption, transferCallStore_get_dst, valueToKey?, EvalResult.bind,
    bind, pure, xferDstBalRef, xferDstVal]

theorem xferCall_balSrc (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferCallStore I } evm
      (.storage (balanceOfRef (.var "src"))) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (callerBalSlot I)).toNat)) :=
  evalExpr_storage_scalar_value (er := callerBalRef I) (t := .int uint256Int)
    (loc := wordLoc (callerBalSlot I)) (hbase := by simp [balanceOfRef, transferCallStore])
    (xferCall_srcRef evm I)
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]) (by rfl)
    (by simpa [wordLoc, uint256Loc, uint256Int, callerBalSlot] using
      storageLocLoad_uint256 evm (callerBalSlot I))
theorem xferCall_balDst (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferCallStore I } evm
      (.storage (balanceOfRef (.var "dst"))) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (xferDstSlot I)).toNat)) :=
  evalExpr_storage_scalar_value (er := xferDstBalRef I) (t := .int uint256Int)
    (loc := wordLoc (xferDstSlot I)) (hbase := by simp [balanceOfRef, transferCallStore])
    (xferCall_dstRef evm I)
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]) (by rfl)
    (by simpa [wordLoc, uint256Loc, uint256Int, xferDstSlot] using
      storageLocLoad_uint256 evm (xferDstSlot I))

/-! ## Solm-side require / condition / arithmetic evaluations -/

theorem xferCall_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (hle : (xferWadWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat) :
    evalExpr? config { contract := contract, locals := transferCallStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [xferCall_balSrc evm I]
  simp only [evalExpr?, EvalResult.ofOption, transferCallStore_get_wad, EvalResult.bind, bind,
    evalBinaryOp?, xferWadVal, EvalResult.ok.injEq, Value.bool.injEq, decide_eq_true_eq]
  exact Int.ofNat_le.mpr hle
theorem xferCall_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)).toNat <
      (xferWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferCallStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) = .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [xferCall_balSrc evm I]
  simp only [evalExpr?, EvalResult.ofOption, transferCallStore_get_wad, EvalResult.bind, bind,
    evalBinaryOp?, xferWadVal, EvalResult.ok.injEq, Value.bool.injEq, decide_eq_false_iff_not]
  exact fun h => absurd (Int.ofNat_le.mp h) (by omega)

/-- `src != msg.sender` is `false` (`transfer` binds `src = msg.sender`). -/
theorem xferCall_srcNeCaller_false (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I) :
    evalExpr? config { contract := contract, locals := transferCallStore I } evm
      (.binary .ne (.var "src") sender) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, transferCallStore_get_src, sender, envValue, hsrc,
    EvalResult.bind, bind, pure, evalBinaryOp?, beq_self_eq_true, Bool.not_true]
/-- The whole ite guard `(src != caller) && (allowance != max)` short-circuits to `false`. -/
theorem xferCall_cond_false (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I) :
    evalExpr? config { contract := contract, locals := transferCallStore I } evm
      (.binary .and (.binary .ne (.var "src") sender)
        (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)))
      = .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [xferCall_srcNeCaller_false evm I hsrc]
  simp only [EvalResult.bind, bind, pure]

theorem xferCall_sub (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferCallStore I } evm
      (.binary .sub (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (callerBalSlot I)).toNat - Int.ofNat (xferWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [xferCall_balSrc evm I]
  simp only [evalExpr?, EvalResult.ofOption, transferCallStore_get_wad, EvalResult.bind, bind,
    evalBinaryOp?, xferWadVal]
theorem xferCall_add (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferCallStore I } evm
      (.binary .add (.storage (balanceOfRef (.var "dst"))) (.var "wad")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (xferDstSlot I)).toNat + Int.ofNat (xferWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [xferCall_balDst evm I]
  simp only [evalExpr?, EvalResult.ofOption, transferCallStore_get_wad, EvalResult.bind, bind,
    evalBinaryOp?, xferWadVal]

/-! ## Solm-side post-states and their `accountMap` reconciliation to `wtfPostMap` -/

def xferSrcSt (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (callerBalSlot I)
    (UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I))
      (xferWadWord I))
def xferDstSt (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (xferDstSlot I)
    (UInt256.add (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (xferDstSlot I))
      (xferWadWord I))

theorem xferCall_assignSrc (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferCallStore I } evm
      .storage (balanceOfRef (.var "src"))
      (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (callerBalSlot I)).toNat - Int.ofNat (xferWadWord I).toNat)) =
      .ok ({ contract := contract, locals := transferCallStore I }, xferSrcSt evm I) := by
  refine assignStorageRef_storage_scalar_value (er := callerBalRef I) (ty := uint256St)
    (loc := wordLoc (callerBalSlot I)) (hbase := by simp [balanceOfRef, transferCallStore])
    (xferCall_srcRef evm I)
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]) (by rfl)
    (by trivial) ?_
  unfold xferSrcSt
  rw [show wordLoc (callerBalSlot I) = uint256Loc (callerBalSlot I) from rfl,
    storageLocStore_uint256_int, tf_wordOfInt_sub]
theorem xferCall_assignDst (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferCallStore I }
      (xferSrcSt evm I) .storage (balanceOfRef (.var "dst"))
      (.int (Int.ofNat (Solm.EVM.storageLoad (xferSrcSt evm I)
        (xferSrcSt evm I).executionEnv.codeOwner (xferDstSlot I)).toNat
        + Int.ofNat (xferWadWord I).toNat)) =
      .ok ({ contract := contract, locals := transferCallStore I }, xferDstSt (xferSrcSt evm I) I) := by
  refine assignStorageRef_storage_scalar_value (er := xferDstBalRef I) (ty := uint256St)
    (loc := wordLoc (xferDstSlot I)) (hbase := by simp [balanceOfRef, transferCallStore])
    (xferCall_dstRef (xferSrcSt evm I) I)
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]) (by rfl)
    (by trivial) ?_
  unfold xferDstSt
  rw [show wordLoc (xferDstSlot I) = uint256Loc (xferDstSlot I) from rfl,
    storageLocStore_uint256_int, wordOfInt_add_words]

theorem xferSrcSt_co (evm : EVM.State) (I : ExecutionEnv) :
    (xferSrcSt evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  unfold xferSrcSt; rw [tf_execEnv]
theorem xferSrcSt_accountMap (evm : EVM.State) (I : ExecutionEnv)
    (hco : evm.executionEnv.codeOwner = I.codeOwner) :
    (xferSrcSt evm I).accountMap =
      wtfSrcDebitedMap I evm.accountMap (solcSourceWord I) (xferWadWord I) := by
  unfold xferSrcSt wtfSrcDebitedMap
  rw [storageStore_accountMap, tf_load_slot evm I _ hco, hco, xfer_callerBalSlot_eq]
theorem xferDstSt_accountMap (evm : EVM.State) (I : ExecutionEnv)
    (hco : evm.executionEnv.codeOwner = I.codeOwner) :
    (xferDstSt evm I).accountMap = sstoreAccountMap I.codeOwner evm.accountMap
      (wtfBalSlot (xferDstMasked I))
      (UInt256.add (xferWadWord I)
        (solcSlotWord evm.accountMap I (wtfBalSlot (xferDstMasked I)))) := by
  unfold xferDstSt
  rw [storageStore_accountMap, tf_load_slot evm I _ hco, hco, xfer_dstSlot_eq]
  exact congrArg (sstoreAccountMap I.codeOwner evm.accountMap (wtfBalSlot (xferDstMasked I)))
    (u256_add_comm _ _)

theorem xferSkip_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    (xferDstSt (xferSrcSt (initState cA gh bl σ σ₀ g A I) I) I).accountMap =
      wtfPostMap I σ (solcSourceWord I) (xferDstMasked I) (xferWadWord I) := by
  have hco0 : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hcoS : (xferSrcSt (initState cA gh bl σ σ₀ g A I) I).executionEnv.codeOwner = I.codeOwner := by
    rw [xferSrcSt_co, hco0]
  rw [xferDstSt_accountMap _ I hcoS, xferSrcSt_accountMap _ I hco0]
  rfl
theorem xferSkip_created {cA gh bl σ σ₀ A I} {g : Sat256} :
    (xferDstSt (xferSrcSt (initState cA gh bl σ σ₀ g A I) I) I).createdAccounts =
      (initState cA gh bl σ σ₀ g A I).createdAccounts := by
  unfold xferDstSt xferSrcSt; rw [storageStore_createdAccounts, storageStore_createdAccounts]

/-! ## Solm-side `transferFrom` callee body (always SkipSender / balance-revert) -/

/-- `transferFrom(msg.sender, dst, wad)` body, success: `src == caller` short-circuits the allowance
    guard, so it just does the two balance stores and returns `true`. -/
theorem weth9XferCallReturns_skipSender {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (xferWadWord I).toNat ≤ (solcSlotWord σ I (callerBalSlot I)).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (transferCallStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := transferCallStore I }
        (xferDstSt (xferSrcSt (initState cA gh bl σ σ₀ g A I) I) I) (some [.bool true])) := by
  set evm := initState cA gh bl σ σ₀ g A I with hevm
  have hsrc : evm.executionEnv = I := rfl
  have hcv : evm.executionEnv.weiValue = ⟨0⟩ := by rw [hsrc]; exact hwv
  have hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)
      = solcSlotWord σ I (callerBalSlot I) := by rw [tf_load_slot evm I _ rfl]; rfl
  refine ExecFuncBody.execBlockRet ?_
  simp only [transferFromTransition, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hcv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (xferCall_ge_true evm I (by rw [hload]; exact hle))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse (result := .ok { contract := contract, locals := transferCallStore I } evm)
      (xferCall_cond_false evm I hsrc) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (xferCall_sub evm I) (xferCall_assignSrc evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (xferCall_add (xferSrcSt evm I) I) (xferCall_assignDst evm I)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

/-- `transferFrom(msg.sender, dst, wad)` body, revert: `balanceOf[msg.sender] < wad`. -/
theorem weth9XferCallReverts_bal {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlt : (solcSlotWord σ I (callerBalSlot I)).toNat < (xferWadWord I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (transferCallStore I)
      transferFromTransition.body .reverted := by
  set evm := initState cA gh bl σ σ₀ g A I with hevm
  have hsrc : evm.executionEnv = I := rfl
  have hcv : evm.executionEnv.weiValue = ⟨0⟩ := by rw [hsrc]; exact hwv
  have hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (callerBalSlot I)
      = solcSlotWord σ I (callerBalSlot I) := by rw [tf_load_slot evm I _ rfl]; rfl
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hcv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (xferCall_ge_false evm I (by rw [hload]; exact hlt)))

/-! ## Solm-side `transfer` body (the internal `transferFrom` call + return) -/

theorem xferEvalArgs (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExprs? config { contract := contract, locals := transferStore I } evm
      [sender, .var "dst", .var "wad"] =
        .ok [.address I.source, xferDstVal I, xferWadVal I] := by
  have hsrcVal : Value.address evm.executionEnv.source = (.address I.source : Value) := by rw [hsrc]
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure, sender,
    envValue, transferStore_index_dst, hsrcVal]

theorem weth9TransferBodyReturns (evm evmPost : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hsrc : evm.executionEnv.source = I.source)
    (hcallee : ExecTransitionBody config contract evm (transferCallStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := transferCallStore I } evmPost
        (some [.bool true]))) :
    ∃ cs, ExecTransitionBody config contract evm (transferStore I) transferTransition.body
      (.returned cs evmPost (some [.bool true])) := by
  let caller : Frame := { contract := contract, locals := transferStore I }
  let callerAfter : Frame :=
    { contract := contract, locals := (transferStore I).insert "_ok" (.bool true) }
  have hcall : ExecStmt config caller evm
      (.internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok")
      (.ok callerAfter evmPost) := by
    simpa [caller, callerAfter] using
      internalCallTransitionReturn (cfg := config) (caller := caller) (evm := evm)
        (calleeEvm := evmPost) (name := "transferFrom")
        (args := [sender, .var "dst", .var "wad"]) (retVar := "_ok")
        (argVals := [.address I.source, xferDstVal I, xferWadVal I])
        (callee := transferFromTransition) (locals := transferCallStore I)
        (calleeSolm := { contract := contract, locals := transferCallStore I })
        (value := .bool true) (xferEvalArgs evm I hsrc) rfl (transferCallStore_bind I) hcallee
  have hret : evalExprs? config callerAfter evmPost [.var "_ok"] = .ok [.bool true] := by
    simp [callerAfter, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  refine ⟨callerAfter, ExecFuncBody.execBlockRet ?_⟩
  rw [transferTransition]
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal hcall <|
      ExecBlock.consReturn (ExecStmt.return hret)

theorem weth9TransferBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hsrc : evm.executionEnv.source = I.source)
    (hcallee : ExecTransitionBody config contract evm (transferCallStore I)
      transferFromTransition.body .reverted) :
    ExecTransitionBody config contract evm (transferStore I) transferTransition.body .reverted := by
  let caller : Frame := { contract := contract, locals := transferStore I }
  have hcall : ExecStmt config caller evm
      (.internalCall "transferFrom" [sender, .var "dst", .var "wad"] "_ok") .reverted := by
    exact internalCallTransitionRevert (cfg := config) (caller := caller) (evm := evm)
      (name := "transferFrom") (args := [sender, .var "dst", .var "wad"]) (retVar := "_ok")
      (argVals := [.address I.source, xferDstVal I, xferWadVal I])
      (callee := transferFromTransition) (locals := transferCallStore I)
      (xferEvalArgs evm I hsrc) rfl (transferCallStore_bind I) hcallee
  rw [transferTransition]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert hcall

/-! ## EVM trace: reach the shared body (pc 1087), internal-return tail, and revert reaches -/

/-- Peel the callvalue guard (pc 644), pass the 2-word length check, decode `(dst, wad)`, and run the
    `1661` wrapper (which pushes `msg.sender` for `src` and `1674` for the internal return) to reach
    the shared body at pc 1087. -/
theorem weth9TransferReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 8)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1087⟩
      (xferWadWord I :: xferDstMasked I :: solcSourceWord I :: ⟨1674⟩ ::
        ⟨0⟩ :: xferWadWord I :: xferDstMasked I :: ⟨361⟩ :: [weth9SelWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h644⟩ := weth9ReachTransfer (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h658⟩ := weth9GuardPeelOk (gt := ⟨656⟩) h644 hwv
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize
  have h679 := h658.push2 ⟨361⟩ (by decide +native) (by simp)
    |>.push1 ⟨4⟩ (by decide +native) (by simp)
    |>.dup1 (by decide +native) (by simp)
    |>.calldatasize (by decide +native) (by simp)
    |>.sub (by decide +native) (by simp)
    |>.push1 ⟨64⟩ (by decide +native) (by simp)
    |>.dup2 (by decide +native) (by simp)
    |>.lt (by decide +native) (by simp)
    |>.iszero (by decide +native) (by simp)
    |>.push2 ⟨679⟩ (by decide +native) (by simp)
    |>.jumpiT (by decide +native) (by rw [hlt]; decide) (by jump_dest) (by simp)
  obtain ⟨_, _, h1661⟩ := RD.solcAddressUint256ExternalMaskAndJumpMasked (routine := ⟨1661⟩) h679
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by simp only [List.length_singleton]; omega)
  have h1087 := h1661.jumpdest (by decide +native) (by simp)
    |>.push1 ⟨0⟩ (by decide +native) (by simp)
    |>.push2 ⟨1674⟩ (by decide +native) (by simp)
    |>.caller (by decide +native) (by simp)
    |>.dup5 (by decide +native) (by simp)
    |>.dup5 (by decide +native) (by simp)
    |>.push2 ⟨1087⟩ (by decide +native) (by simp)
    |>.jump (by decide +native) (by jump_dest) (by simp)
  exact ⟨_, _, h1087⟩

/-- `wordAt0Mem` leaves the free-pointer slot (bytes 64–95) untouched (local copy of the private
    `TransferFrom.wtf_wordAt0Mem_read64`). -/
private theorem xfer_wordAt0Mem_read64 (word : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (wordAt0Mem word mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega) (by omega)
    (by rw [hmem])]

/-- From the shared tail at pc 1282 (with the internal-return address `1674` as `ret`), run the two
    balance stores, jump back through the internal-return tail (`1674 → 361`), and encode the boolean
    return `1`. -/
theorem weth9TransferReturnTrue {ee g s0 rdata cA σ k C} {src dst wad sel : UInt256}
    {mem : ByteArray}
    (h : RD weth9Bytecode ee g s0 ⟨1282⟩
      (⟨0⟩ :: wad :: dst :: src :: ⟨1674⟩ :: ⟨0⟩ :: wad :: dst :: ⟨361⟩ :: [sel])
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true) (hsrc : src.toNat < EVM.addressModulus)
    (hdst : dst.toNat < EVM.addressModulus)
    (hmemsize : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDret weth9Bytecode g s0 (cA, wtfPostMap ee σ src dst wad)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, h1674⟩ := weth9TFTail (S := ⟨0⟩ :: wad :: dst :: ⟨361⟩ :: [sel]) h hperm hsrc hdst
    hmemsize hread64 (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  have h361 := h1674.jumpdest (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
    |>.swap4 (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
    |>.swap3 (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
    |>.pop (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
    |>.pop (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
    |>.pop (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
    |>.jump (by decide +native) (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hM1size : (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)).size = 96 :=
    wordAt0Mem_size_96 dst (twoWordHashMem_size_96 src ⟨3⟩ hmemsize)
  have hM1read64 : (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ := by
    rw [xfer_wordAt0Mem_read64 dst (twoWordHashMem_size_96 src ⟨3⟩ hmemsize)]
    exact twoWordHashMem_read64 src ⟨3⟩ hmemsize hread64
  have hretWf : solcReturnBoolFromMemWf weth9Bytecode ⟨361⟩ := by
    unfold solcReturnBoolFromMemWf
    repeat' first | apply And.intro | decide +native
  have hbool : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by decide +native
  have hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (wtfBoolReturnMem src dst wad mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((wtfBoolReturnMem src dst wad mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    refine mloadFreePtrValue (by
        unfold wtfBoolReturnMem
        rw [toByteArray_write32_size_of_le
          (solcScratchReturnMem (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)) wad)
          (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128 160 160
          (solcScratchReturnMem_size wad hM1size)
          (by rw [solcScratchReturnMem_size wad hM1size]; decide) (by decide)]
        decide)
      (by decide) ?_
    unfold wtfBoolReturnMem
    rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [solcScratchReturnMem_size wad hM1size]; omega) (by omega)]
    exact solcScratchReturnMem_read64 wad hM1size hM1read64
  have hread128 : (wtfBoolReturnMem src dst wad mem).readWithPadding 128 32
      = UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
    unfold wtfBoolReturnMem
    exact toByteArray_write32_read_back
      (solcScratchReturnMem (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)) wad)
      (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128
      (by rw [solcScratchReturnMem_size wad hM1size]; decide)
  have hret := RD.solcReturnBoolFromMem h361 hretWf
    (solcScratchReturnMem_mload64 wad hM1size hM1read64) (by rfl) hmemoutLoad64 hread128
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [hbool] using hret

/-- `callvalue ≠ 0`: the payable guard at pc 644 reverts. -/
theorem weth9TransferGuardRev {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 8)) :
    RDrev weth9Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h644⟩ := weth9ReachTransfer (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  exact weth9GuardPeelRev (gt := ⟨656⟩) h644 hwv
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) (by decide +native)

/-- Short calldata (`< 68`, but `callvalue = 0`): the 2-word length check reverts. -/
theorem weth9TransferDecodeFailRev {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 8)) :
    RDrev weth9Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h644⟩ := weth9ReachTransfer (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h658⟩ := weth9GuardPeelOk (gt := ⟨656⟩) h644 hwv
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
  have hltShort : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (show (⟨4⟩ : UInt256).toNat ≤ I.calldata.size by simpa using hsz4)
      hsize]
    simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl, show (⟨4⟩ : UInt256).toNat = 4 from rfl]
    omega
  exact h658.push2 ⟨361⟩ (by decide +native) (by simp)
    |>.push1 ⟨4⟩ (by decide +native) (by simp)
    |>.dup1 (by decide +native) (by simp)
    |>.calldatasize (by decide +native) (by simp)
    |>.sub (by decide +native) (by simp)
    |>.push1 ⟨64⟩ (by decide +native) (by simp)
    |>.dup2 (by decide +native) (by simp)
    |>.lt (by decide +native) (by simp)
    |>.iszero (by decide +native) (by simp)
    |>.push2 ⟨679⟩ (by decide +native) (by simp)
    |>.jumpiNT (by decide +native) (by rw [hltShort]; decide) (by simp)
    |>.solcPush1Dup1Revert0 (by decide +native) (by decide +native) (by decide +native) (by simp)

/-- `transfer(address,uint256)` body refines its Solm transition. -/
theorem weth9TransferBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 8))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 8) (by decide +native) hsel
  have hdisp := weth9SelectorDispatchTransfer hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz68 : 68 ≤ I.calldata.size
    · -- decode succeeds; reach the shared body at pc 1087 (`src = msg.sender`)
      obtain ⟨_, _, h1087⟩ := weth9TransferReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz68 hsize hsel
      have hbaleq : solcSlotWord σ_evm I (callerBalSlot I) = solcSlotWord σ_solm I (callerBalSlot I) :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner (callerBalSlot I) ⟨0⟩
      by_cases hbal : (xferWadWord I).toNat ≤ (solcSlotWord σ_evm I (callerBalSlot I)).toNat
      · -- success (SkipSender): the two balance stores, return `true`
        obtain ⟨_, _, h1124⟩ := weth9TFReqBalanceOk h1087 (solcSourceWord_canonical I)
          (by rw [show wtfBalSlot (solcSourceWord I) = callerBalSlot I from
              (xfer_callerBalSlot_eq I).symm]; exact hbal)
          (by simp only [List.length_cons, List.length_nil]; omega)
        obtain ⟨_, _, h1282⟩ := weth9TFBranchSkipSender h1124 (solcSourceWord_canonical I) rfl
          (by simp only [List.length_cons, List.length_nil]; omega)
        have hX := weth9TransferReturnTrue h1282 hperm (solcSourceWord_canonical I)
          (tfSrcMasked_canonical I)
          (twoWordHashMem_size_96 (solcSourceWord I) ⟨3⟩ solcFreePtrMem_size)
          (wtfBalHashMem_read64 (solcSourceWord I))
        obtain ⟨cs, hbody⟩ := weth9TransferBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (xferDstSt (xferSrcSt (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I) I) I
          (by simp only [initState]; exact hwv) (by simp [initState])
          (weth9XferCallReturns_skipSender (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv (by rw [← hbaleq]; exact hbal))
        exact weth9ReEquivExecGen (t := transferTransition) hcode hX hdisp (xferDecode_ok hsz68)
          hbody (by rw [xferSkip_created]; simp [initState])
          (by rw [xferSkip_accountMap]; exact wtfPostMap_accountMapEquiv I _ _ _ hAccounts)
          (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
      · -- balance revert: `balanceOf[msg.sender] < wad`
        have hrev := weth9TFReqBalanceRev h1087 (solcSourceWord_canonical I)
          (by rw [show wtfBalSlot (solcSourceWord I) = callerBalSlot I from
              (xfer_callerBalSlot_eq I).symm]; omega)
          (by simp only [List.length_cons, List.length_nil]; omega)
        exact weth9ReEquivExecRev hcode hrev hdisp (xferDecode_ok hsz68)
          (weth9TransferBodyReverts (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) (by simp [initState])
            (weth9XferCallReverts_bal (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv (by rw [← hbaleq]; omega)))
    · -- calldata < 68: decode failure
      exact weth9ReEquivDecodeFailed hcode
        (weth9TransferDecodeFailRev (g := Sat256.ofUInt256 g) hcode hwv hsz4 (by omega) hsize hsel)
        hdisp (xferDecode_none_short hsz4 (by omega))
  · -- callvalue ≠ 0: the payable guard reverts
    exact weth9NonpayableRevert hcode
      (weth9TransferGuardRev (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel) hdisp
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
