import Benchmarks.Morpho.MorphoBlue.WordComparisons
import Benchmarks.Morpho.MorphoBlue.AccruePublicSource
import Benchmarks.Morpho.MorphoBlue.MarketParamsWordABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def maxMarketFee : Nat := 250000000000000000

def setFeeArgs (p : MarketParamsWords) (fee : UInt256) : Store :=
  ((∅ : Store).insert "marketParams" p.value).insert "newFee" (.int (Int.ofNat fee.toNat))

def setFeeBeforeId (p : MarketParamsWords) (fee : UInt256) (cd : ByteArray) (imms : Store) : Frame :=
  { contract := contract, locals := (setFeeArgs p fee).insert "__calldata" (.bytes cd), immutables := imms }

def setFeeFrame (p : MarketParamsWords) (fee : UInt256) (cd : ByteArray) (imms : Store) : Frame :=
  { setFeeBeforeId p fee cd imms with locals := ((setFeeBeforeId p fee cd imms).locals.insert "id"
    (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id))) }

theorem setFeeFrame_market (p : MarketParamsWords) (fee : UInt256) (cd : ByteArray) (imms : Store) :
    MarketLocals p (setFeeFrame p fee cd imms).locals := by
  constructor
  · simp only [setFeeFrame, setFeeBeforeId, setFeeArgs,
      store_get_ne (k := "id") (a := "marketParams") _ _ (by decide),
      store_get_ne (k := "__calldata") (a := "marketParams") _ _ (by decide),
      store_get_ne (k := "newFee") (a := "marketParams") _ _ (by decide), store_get_self]
  · exact store_get_self _ _ _
  · simp [setFeeFrame, setFeeBeforeId, setFeeArgs]
  · simp [setFeeFrame, setFeeBeforeId, setFeeArgs]
  · simp [setFeeFrame, setFeeBeforeId, setFeeArgs]

theorem setFeeFrame_get_fee (p : MarketParamsWords) (fee : UInt256) (cd : ByteArray) (imms : Store) :
    (setFeeFrame p fee cd imms).locals.get? "newFee" = some (.int (Int.ofNat fee.toNat)) := by
  simp only [setFeeFrame, setFeeBeforeId, setFeeArgs,
    store_get_ne (k := "id") (a := "newFee") _ _ (by decide),
    store_get_ne (k := "__calldata") (a := "newFee") _ _ (by decide), store_get_self]

theorem setFeeFrame_eval_fee (p : MarketParamsWords) (fee : UInt256) (cd : ByteArray) (imms : Store) (evm : EVM.State) :
    evalExpr? config (setFeeFrame p fee cd imms) evm (.var "newFee") = .ok (.int (Int.ofNat fee.toNat)) := by
  simp only [evalExpr?, setFeeFrame_get_fee, EvalResult.ofOption]

theorem setFeeLimit_eval (p : MarketParamsWords) (fee : UInt256) (cd : ByteArray) (imms : Store) (evm : EVM.State) :
    evalExpr? config (setFeeFrame p fee cd imms) evm (.binary .le (.var "newFee") (.intLit maxMarketFee)) =
      .ok (.bool (decide (fee.toNat ≤ maxMarketFee))) := by
  simp only [evalExpr?, setFeeFrame_eval_fee, pure, bind, EvalResult.bind, evalBinaryOp?]
  simp only [Int.ofNat_eq_natCast, Int.ofNat_le]

theorem morphoSetFeePrelude (p : MarketParamsWords) (fee : UInt256) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store) (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv) :
    ABlock config evm { contract := contract, locals := setFeeArgs p fee, immutables := imms }
      setFeeTransition.body (setFeeFrame p fee evm.executionEnv.calldata imms) (setFeeTransition.body.drop 5) := by
  have heo := evalMorphoOwnerCheck evm (setFeeBeforeId p fee evm.executionEnv.calldata imms).locals imms
    (by simp [setFeeBeforeId, setFeeArgs])
  refine ⟨fun h => ((calldataPrelude_ok hcv hsize).requireStep
    (by simpa only [ho, decide_true] using heo)).run (ExecBlock.consNormal ?_ h)⟩
  exact morphoMarketParamsIdCall p hc evm _ imms (.var "marketParams") "id"
    (by simp only [evalExpr?, setFeeBeforeId, setFeeArgs,
      store_get_ne (k := "__calldata") (a := "marketParams") _ _ (by decide),
      store_get_ne (k := "newFee") (a := "marketParams") _ _ (by decide), store_get_self, EvalResult.ofOption])

def SetFeeGuards (σ : AccountMap) (I : ExecutionEnv) (p : MarketParamsWords) (fee : UInt256) : Prop :=
  solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I ∧ marketFieldWord σ I p.id 4 ≠ ⟨0⟩ ∧
  fee ≠ marketFieldWord σ I p.id 5 ∧ fee.toNat ≤ maxMarketFee

theorem morphoSetFeeSourceGuards (p : MarketParamsWords) (fee : UInt256) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store) (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hg : SetFeeGuards evm.accountMap evm.executionEnv p fee) :
    ABlock config evm { contract := contract, locals := setFeeArgs p fee, immutables := imms }
      setFeeTransition.body (setFeeFrame p fee evm.executionEnv.calldata imms) (setFeeTransition.body.drop 8) := by
  have hl := setFeeFrame_market p fee evm.executionEnv.calldata imms
  exact (((morphoSetFeePrelude p fee hc evm imms hcv hsize hg.1).requireStep
    (by simpa only [decide_eq_true hg.2.1] using evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩))).requireStep
    (by simpa only [decide_eq_true hg.2.2.1] using
      (evalWordNeWord (setFeeFrame_eval_fee p fee evm.executionEnv.calldata imms evm)
        (hl.evalField imms evm ⟨5, by decide⟩)))).requireStep
    (by simpa only [decide_eq_true hg.2.2.2] using setFeeLimit_eval p fee evm.executionEnv.calldata imms evm)

theorem morphoSetFeeSourceRejects (p : MarketParamsWords) (fee : UInt256) (hc : p.Canonical)
    (evm : EVM.State) (imms : Store) (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbad : ¬ SetFeeGuards evm.accountMap evm.executionEnv p fee) :
    ExecTransitionBody config contract evm (setFeeArgs p fee) setFeeTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  by_cases ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv
  · have pref := morphoSetFeePrelude p fee hc evm imms hcv hsize ho
    have hl := setFeeFrame_market p fee evm.executionEnv.calldata imms
    have hec := evalWordNeZero (hl.evalField imms evm ⟨4, by decide⟩)
    by_cases hcreated : marketFieldWord evm.accountMap evm.executionEnv p.id 4 ≠ ⟨0⟩
    · have pref1 := pref.requireStep (by simpa only [decide_eq_true hcreated] using hec)
      have hen := evalWordNeWord (setFeeFrame_eval_fee p fee evm.executionEnv.calldata imms evm)
        (hl.evalField imms evm ⟨5, by decide⟩)
      by_cases hne : fee ≠ marketFieldWord evm.accountMap evm.executionEnv p.id 5
      · exact (pref1.requireStep (by simpa only [decide_eq_true hne] using hen)).requireRevert
          (by simpa only [decide_eq_false (fun hf => hbad ⟨ho, hcreated, hne, hf⟩)] using
            setFeeLimit_eval p fee evm.executionEnv.calldata imms evm)
      · exact pref1.requireRevert (by simpa only [decide_eq_false hne] using hen)
    · exact pref.requireRevert (by simpa only [decide_eq_false hcreated] using hec)
  · have heo := evalMorphoOwnerCheck evm (setFeeBeforeId p fee evm.executionEnv.calldata imms).locals imms
      (by simp [setFeeBeforeId, setFeeArgs])
    exact (calldataPrelude_ok hcv hsize).requireRevert (by simpa only [decide_eq_false ho] using heo)

theorem morphoSetFeeAssign (p : MarketParamsWords) (fee : UInt256) (locals imms : Store) (evm : EVM.State)
    (hl : MarketLocals p locals) (hg : locals.get? "newFee" = some (.int (Int.ofNat fee.toNat)))
    (hfit : fee.toNat ≤ maxMarketFee) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm setFeeTransition.body[9]!
      (.ok { contract := contract, locals := locals, immutables := imms } (storeMarketField evm p.id ⟨5, by decide⟩ fee)) := by
  have hc : fee.toNat < 2 ^ 128 := by unfold maxMarketFee at hfit; omega
  have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm (.var "newFee") =
      .ok (.int (Int.ofNat fee.toNat)) := by simp only [evalExpr?, hg, EvalResult.ofOption]
  apply ExecStmt.assign
  · simpa only [halfWord_low_clean fee hc] using evalCastUint128 he
  · exact assignMarketField evm locals imms (.var "id") p.id ⟨5, by decide⟩ fee hc hl.market (hl.evalId imms evm)

theorem morphoSetFeeFinishSource (p : MarketParamsWords) (fee : UInt256) (locals imms : Store) (evm : EVM.State)
    (hl : MarketLocals p locals) (hg : locals.get? "newFee" = some (.int (Int.ofNat fee.toNat)))
    (hfit : fee.toNat ≤ maxMarketFee) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms } evm (setFeeTransition.body.drop 9)
      (.ok { contract := contract, locals := locals, immutables := imms } (storeMarketField evm p.id ⟨5, by decide⟩ fee)) := by
  apply ExecBlock.consNormal (morphoSetFeeAssign p fee locals imms evm hl hg hfit)
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE p.id),
    .int (Int.ofNat fee.toNat)]) ?_)
  · exact ExecBlock.nil
  · simp only [evalExprs?, hl.evalId, evalExpr?, hg, EvalResult.ofOption, pure, bind, EvalResult.bind]

end Benchmarks.Morpho.MorphoBlue
