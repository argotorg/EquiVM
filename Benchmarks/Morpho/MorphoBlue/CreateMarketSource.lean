import Benchmarks.Morpho.MorphoBlue.MarketParamsStorage
import Benchmarks.Morpho.MorphoBlue.MarketStorageCommon
import Benchmarks.Morpho.MorphoBlue.BorrowRateABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def createMarketArgs (p : MarketParamsWords) : Store :=
  (∅ : Store).insert "marketParams" p.value

def createMarketFrame (p : MarketParamsWords) (cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((createMarketArgs p).insert "__calldata" (.bytes cd)).insert "id"
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) }

theorem createMarketParams_eval (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm : EVM.State) :
    evalExpr? config (createMarketFrame p cd imms) evm (.var "marketParams") = .ok p.value := by
  simp only [evalExpr?, createMarketFrame, createMarketArgs,
    store_get_ne (k := "id") (a := "marketParams") _ _ (by decide),
    store_get_ne (k := "__calldata") (a := "marketParams") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem createMarketId_eval (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm : EVM.State) :
    evalExpr? config (createMarketFrame p cd imms) evm (.var "id") =
      .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id)) := by
  simp only [evalExpr?, createMarketFrame, store_get_self, EvalResult.ofOption]

theorem createMarketIrm_eval (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm : EVM.State) :
    evalExpr? config (createMarketFrame p cd imms) evm (.tupleGet (.var "marketParams") 3) =
      .ok (.address (AccountAddress.ofNat p.irm.toNat)) := by
  simp only [evalExpr?, createMarketParams_eval, MarketParamsWords.value,
    tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
  rfl

theorem createMarketLltv_eval (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm : EVM.State) :
    evalExpr? config (createMarketFrame p cd imms) evm (.tupleGet (.var "marketParams") 4) =
      .ok (.int (Int.ofNat p.lltv.toNat)) := by
  simp only [evalExpr?, createMarketParams_eval, MarketParamsWords.value,
    tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind]
  rfl

theorem morphoCreateMarketPrelude (p : MarketParamsWords) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := createMarketArgs p, immutables := imms }
      createMarketTransition.body (createMarketFrame p evm.executionEnv.calldata imms)
      (createMarketTransition.body.drop 4) := by
  refine ⟨fun h => (calldataPrelude_ok hcv hsize).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp only [evalExpr?, createMarketArgs,
      store_get_ne (k := "__calldata") (a := "marketParams") _ _ (by decide),
      store_get_self, EvalResult.ofOption])

def createMarketIrmByte (σ : AccountMap) (I : ExecutionEnv) (p : MarketParamsWords) : UInt256 :=
  UInt256.land (solcSlotWordAt (solcMappingSlot ⟨4⟩ p.irm) σ I) ⟨255⟩

def createMarketLltvByte (σ : AccountMap) (I : ExecutionEnv) (p : MarketParamsWords) : UInt256 :=
  UInt256.land (solcSlotWordAt (solcMappingSlot ⟨5⟩ p.lltv) σ I) ⟨255⟩

theorem createMarketIrmEnabled_eval (p : MarketParamsWords) (hc : p.Canonical)
    (cd : ByteArray) (imms : Store) (evm : EVM.State) :
    evalExpr? config (createMarketFrame p cd imms) evm
      (.storage ⟨"isIrmEnabled", [.mindex (.tupleGet (.var "marketParams") 3)]⟩) =
      .ok (.bool (decide (createMarketIrmByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩))) := by
  have he := evalMorphoIrmEnabled evm (createMarketFrame p cd imms).locals imms _ p.irm
    (by simp [createMarketFrame, createMarketArgs]) (createMarketIrm_eval p cd imms evm) hc.2.2.2
  simpa only [wordToElemBool, ← decide_not] using he

theorem createMarketLltvEnabled_eval (p : MarketParamsWords)
    (cd : ByteArray) (imms : Store) (evm : EVM.State) :
    evalExpr? config (createMarketFrame p cd imms) evm
      (.storage ⟨"isLltvEnabled", [.mindex (.tupleGet (.var "marketParams") 4)]⟩) =
      .ok (.bool (decide (createMarketLltvByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩))) := by
  have he := evalMorphoLltvEnabled evm (createMarketFrame p cd imms).locals imms _ p.lltv
    (by simp [createMarketFrame, createMarketArgs]) (createMarketLltv_eval p cd imms evm)
  simpa only [wordToElemBool, ← decide_not] using he

theorem createMarketUnused_eval (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm : EVM.State) :
    evalExpr? config (createMarketFrame p cd imms) evm
      (.binary .eq (.storage ⟨"market", [.mindex (.var "id"), .field "lastUpdate"]⟩) (.intLit 0)) =
      .ok (.bool (decide (marketFieldWord evm.accountMap evm.executionEnv p.id 4 = ⟨0⟩))) := by
  have he := evalMorphoMarketField evm (createMarketFrame p cd imms).locals imms _ p.id ⟨4, by decide⟩
    (by simp [createMarketFrame, createMarketArgs]) (createMarketId_eval p cd imms evm)
  change evalExpr? config (createMarketFrame p cd imms) evm
    (.storage ⟨"market", [.mindex (.var "id"), .field "lastUpdate"]⟩) = _ at he
  rw [evalExpr_binary_nonshort (by decide) (by decide), he]
  simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  constructor
  · intro h
    exact uint256_toNat_eq_zero (Int.ofNat.inj h)
  · intro h
    rw [h]
    rfl

theorem morphoCreateMarketGuards (p : MarketParamsWords) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hirm : createMarketIrmByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩)
    (hlltv : createMarketLltvByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩)
    (hnew : marketFieldWord evm.accountMap evm.executionEnv p.id 4 = ⟨0⟩) :
    ABlock config evm { contract := contract, locals := createMarketArgs p, immutables := imms }
      createMarketTransition.body (createMarketFrame p evm.executionEnv.calldata imms)
      (createMarketTransition.body.drop 7) := by
  exact (((morphoCreateMarketPrelude p hc evm imms hcv hsize).requireStep
    (by simpa only [decide_eq_true hirm] using
      createMarketIrmEnabled_eval p hc evm.executionEnv.calldata imms evm)).requireStep
    (by simpa only [decide_eq_true hlltv] using
      createMarketLltvEnabled_eval p evm.executionEnv.calldata imms evm)).requireStep
    (by simpa only [hnew, decide_true] using createMarketUnused_eval p evm.executionEnv.calldata imms evm)

def createMarketStored (evm : EVM.State) (p : MarketParamsWords) : EVM.State :=
  storeMarketParams (storeMarketLastUpdate evm p.id
    (halfWord false (UInt256.ofNat evm.executionEnv.header.timestamp))) p.id p

theorem createMarketTimestampAssign (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm : EVM.State) :
    ExecStmt config (createMarketFrame p cd imms) evm createMarketTransition.body[7]!
      (.ok (createMarketFrame p cd imms) (storeMarketLastUpdate evm p.id
        (halfWord false (UInt256.ofNat evm.executionEnv.header.timestamp)))) := by
  exact ExecStmt.assign (evalCastUint128 (by simp only [evalExpr?, envValue, pure]))
    (assignMarketLastUpdate evm _ imms _ p.id _ (halfWord_bound false _)
      (by simp [createMarketFrame, createMarketArgs]) (createMarketId_eval p cd imms evm))

theorem createMarketStorePrefix (p : MarketParamsWords) (hc : p.Canonical)
    (cd : ByteArray) (imms : Store) (evm : EVM.State) {result : ExecResult}
    (hrest : ExecBlock config (createMarketFrame p cd imms) (createMarketStored evm p)
      (createMarketTransition.body.drop 10) result) :
    ExecBlock config (createMarketFrame p cd imms) evm (createMarketTransition.body.drop 7) result := by
  apply ExecBlock.consNormal (createMarketTimestampAssign p cd imms evm)
  apply ExecBlock.consNormal (ExecStmt.assign
    (evalMarketParamsStruct p (createMarketParams_eval p cd imms _))
    (assignMarketParams _ _ imms _ p.id p hc
      (by simp [createMarketFrame, createMarketArgs]) (createMarketId_eval p cd imms _)))
  apply ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id), p.value]) ?_)
  · exact hrest
  · change evalExprs? config (createMarketFrame p cd imms) (createMarketStored evm p)
      [.var "id", .var "marketParams"] = _
    simp only [evalExprs?, createMarketId_eval, createMarketParams_eval, pure, bind, EvalResult.bind]

theorem morphoCreateMarketSourceRejects (p : MarketParamsWords) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbad : createMarketIrmByte evm.accountMap evm.executionEnv p = ⟨0⟩ ∨
      createMarketLltvByte evm.accountMap evm.executionEnv p = ⟨0⟩ ∨
      marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (createMarketArgs p) createMarketTransition.body
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  have pref := morphoCreateMarketPrelude p hc evm imms hcv hsize
  have hi := createMarketIrmEnabled_eval p hc evm.executionEnv.calldata imms evm
  have hl := createMarketLltvEnabled_eval p evm.executionEnv.calldata imms evm
  have hn := createMarketUnused_eval p evm.executionEnv.calldata imms evm
  by_cases hi0 : createMarketIrmByte evm.accountMap evm.executionEnv p = ⟨0⟩
  · exact pref.requireRevert (by simpa only [hi0, ne_eq, not_true_eq_false, decide_false] using hi)
  · have pref1 := pref.requireStep (by simpa only [decide_eq_true hi0] using hi)
    by_cases hl0 : createMarketLltvByte evm.accountMap evm.executionEnv p = ⟨0⟩
    · exact pref1.requireRevert (by simpa only [hl0, ne_eq, not_true_eq_false, decide_false] using hl)
    · have hn0 := (hbad.resolve_left hi0).resolve_left hl0
      exact (pref1.requireStep (by simpa only [decide_eq_true hl0] using hl)).requireRevert
        (by simpa only [decide_eq_false hn0] using hn)

theorem morphoCreateMarketSourceStatic (p : MarketParamsWords) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hirm : createMarketIrmByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩)
    (hlltv : createMarketLltvByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩)
    (hnew : marketFieldWord evm.accountMap evm.executionEnv p.id 4 = ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (createMarketArgs p) createMarketTransition.body
      .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (morphoCreateMarketGuards p hc evm imms hcv hsize hirm hlltv hnew).run
  exact ExecBlock.consStatic (execStmt_assign_static
    (createMarketTimestampAssign p evm.executionEnv.calldata imms evm) hperm)

theorem createMarketIrmNonzero_eval (p : MarketParamsWords) (hc : p.Canonical)
    (cd : ByteArray) (imms : Store) (evm : EVM.State) :
    evalExpr? config (createMarketFrame p cd imms) evm
      (.binary .ne (.tupleGet (.var "marketParams") 3) (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (p.irm ≠ ⟨0⟩))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), createMarketIrm_eval]
  simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?, EvalResult.ofOption,
    show ¬ (0 : Int) < 0 from by decide, ↓reduceIte, evalBinaryOp?]
  change EvalResult.ok (Value.bool (!(Value.address (AccountAddress.ofNat p.irm.toNat) ==
    Value.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)))) = _
  rw [canonicalAddress_beq _ _ hc.2.2.2 (by decide)]
  simp only [decide_not]

theorem morphoCreateMarketSourceNoIrm (p : MarketParamsWords) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hirm : createMarketIrmByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩)
    (hlltv : createMarketLltvByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩)
    (hnew : marketFieldWord evm.accountMap evm.executionEnv p.id 4 = ⟨0⟩)
    (hi0 : p.irm = ⟨0⟩) :
    ExecTransitionBody config contract evm (createMarketArgs p) createMarketTransition.body
      (.returned (createMarketFrame p evm.executionEnv.calldata imms) (createMarketStored evm p) none)
      imms := by
  apply ExecFuncBody.execBlockOK
  apply (morphoCreateMarketGuards p hc evm imms hcv hsize hirm hlltv hnew).run
  apply createMarketStorePrefix p hc
  apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
  simpa only [hi0, ne_eq, not_true_eq_false, decide_false] using
    createMarketIrmNonzero_eval p hc evm.executionEnv.calldata imms (createMarketStored evm p)

def createMarketBorrowBody : List Stmt :=
  [.letDecl "irm" (some (.elem .address)) (.tupleGet (.var "marketParams") 3),
   .letDecl "marketState" none (marketStateExpr (.var "id")),
   .externalCall (.var "irm") "borrowRate" (.intLit 0)
     [.var "marketParams", .var "marketState"] "__c1"]

def createMarketCallFrame (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm : EVM.State) : Frame :=
  { createMarketFrame p cd imms with locals :=
      (((createMarketFrame p cd imms).locals.insert "irm"
        (.address (AccountAddress.ofNat p.irm.toNat))).insert
          "marketState" (marketStateValue evm.accountMap evm.executionEnv p.id)) }

theorem createMarketBorrowPrelude (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm : EVM.State) :
    ABlock config evm (createMarketFrame p cd imms) createMarketBorrowBody
      (createMarketCallFrame p cd imms evm) (createMarketBorrowBody.drop 2) := by
  apply (ABlock.start.letStep (createMarketIrm_eval p cd imms evm)).letStep
  apply evalMarketState evm _ imms (.var "id") p.id
  · simp [createMarketFrame, createMarketArgs]
  · simp only [evalExpr?, createMarketFrame,
      store_get_ne (k := "irm") (a := "id") _ _ (by decide), store_get_self, EvalResult.ofOption]

theorem createMarketBorrowRun (p : MarketParamsWords) (cd : ByteArray) (imms : Store)
    (evm evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hcall : typedCallViaEVM config evm (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
      [p.value, marketStateValue evm.accountMap evm.executionEnv p.id] (z, evm', out))
    (hout : out.size < 2 ^ 138) :
    if z = true ∧ 32 ≤ out.size then
      ∃ frame, ExecBlock config (createMarketFrame p cd imms) evm createMarketBorrowBody (.ok frame evm')
    else ExecBlock config (createMarketFrame p cd imms) evm createMarketBorrowBody .reverted := by
  have hrecv : evalExpr? config (createMarketCallFrame p cd imms evm) evm (.var "irm") =
      .ok (.address (AccountAddress.ofNat p.irm.toNat)) := by
    simp only [evalExpr?, createMarketCallFrame,
      store_get_ne (k := "marketState") (a := "irm") _ _ (by decide), store_get_self, EvalResult.ofOption]
  have hzero : evalExpr? config (createMarketCallFrame p cd imms evm) evm (.intLit 0) = .ok (.int 0) := by
    simp only [evalExpr?, pure]
  have hargs : evalExprs? config (createMarketCallFrame p cd imms evm) evm
      [.var "marketParams", .var "marketState"] =
      .ok [p.value, marketStateValue evm.accountMap evm.executionEnv p.id] := by
    simp only [evalExprs?, evalExpr?, createMarketCallFrame, createMarketFrame, createMarketArgs,
      store_get_ne (k := "marketState") (a := "marketParams") _ _ (by decide),
      store_get_ne (k := "irm") (a := "marketParams") _ _ (by decide),
      store_get_ne (k := "id") (a := "marketParams") _ _ (by decide),
      store_get_ne (k := "__calldata") (a := "marketParams") _ _ (by decide),
      store_get_self, EvalResult.ofOption, pure, bind, EvalResult.bind]
  have pref := createMarketBorrowPrelude p cd imms evm
  have htarget : EVM.address (AccountAddress.ofNat p.irm.toNat).val =
      AccountAddress.ofNat p.irm.toNat := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (AccountAddress.ofNat p.irm.toNat).isLt
  rw [← htarget] at hcall
  cases z
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    exact pref.run (ExecBlock.consRevert (ExecStmt.externalCallFailure hrecv hzero hargs hcall))
  · simp only [true_and]
    by_cases hlen : 32 ≤ out.size
    · rw [if_pos hlen]
      exact ⟨_, pref.run (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hrecv hzero hargs hcall
          (decodeBorrowRate_ok hlen (by omega))) ExecBlock.nil)⟩
    · rw [if_neg hlen]
      exact pref.run (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
        hrecv hzero hargs hcall (decodeBorrowRate_short (by omega))))

theorem morphoCreateMarketSourceCall (p : MarketParamsWords) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hirm : createMarketIrmByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩)
    (hlltv : createMarketLltvByte evm.accountMap evm.executionEnv p ≠ ⟨0⟩)
    (hnew : marketFieldWord evm.accountMap evm.executionEnv p.id 4 = ⟨0⟩)
    (hi0 : p.irm ≠ ⟨0⟩) (evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hcall : typedCallViaEVM config (createMarketStored evm p)
      (AccountAddress.ofNat p.irm.toNat) "borrowRate" 0
      [p.value, marketStateValue (createMarketStored evm p).accountMap
        (createMarketStored evm p).executionEnv p.id] (z, evm', out))
    (hout : out.size < 2 ^ 138) :
    if z = true ∧ 32 ≤ out.size then
      ∃ frame, ExecTransitionBody config contract evm (createMarketArgs p) createMarketTransition.body
        (.returned frame evm' none) imms
    else ExecTransitionBody config contract evm (createMarketArgs p) createMarketTransition.body
      .reverted imms := by
  have pref := morphoCreateMarketGuards p hc evm imms hcv hsize hirm hlltv hnew
  have hb := createMarketBorrowRun p evm.executionEnv.calldata imms (createMarketStored evm p)
    evm' z out hcall hout
  have hi := createMarketIrmNonzero_eval p hc evm.executionEnv.calldata imms (createMarketStored evm p)
  rw [decide_eq_true hi0] at hi
  split_ifs at hb ⊢ with hgood
  · obtain ⟨frame, hb⟩ := hb
    exact ⟨frame, ExecFuncBody.execBlockOK (pref.run (createMarketStorePrefix p hc _ _ _
      (ExecBlock.consNormal (ExecStmt.iteTrue hi hb) ExecBlock.nil)))⟩
  · exact ExecFuncBody.execBlockRevert (pref.run (createMarketStorePrefix p hc _ _ _
      (ExecBlock.consRevert (ExecStmt.iteTrue hi hb))))

end Benchmarks.Morpho.MorphoBlue
