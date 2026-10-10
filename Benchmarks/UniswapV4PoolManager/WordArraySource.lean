import Benchmarks.UniswapV4PoolManager.WordArrayLoop
import Benchmarks.UniswapV4PoolManager.CalldataWordSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

-- LIBRARY CANDIDATE: allocate a local array from any natural-valued length expression.
theorem evalNewArrayNat {cfg : Config} {f : Frame} {evm : EVM.State}
    {e : Expr} {ty : StorageType} {value : Value} {n : Nat}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat n)))
    (hd : defaultValue? ty = .ok value) :
    evalExpr? cfg f evm (.newArray ty e) = .ok (.array (List.replicate n value)) := by
  simp only [evalExpr?, he, bind, EvalResult.bind, Int.ofNat_eq_natCast,
    show ¬ (n : Int) < 0 by omega, if_false, hd, pure, Int.toNat_natCast]

-- LIBRARY CANDIDATE: zero comparison of a natural-valued source expression.
theorem evalNatEqZero {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {n : Nat}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg f evm (.binary .eq e (.intLit 0)) = .ok (.bool (decide (n = 0))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), he]
  simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?, BEq.beq, Value.int.injEq,
    Int.ofNat_eq_natCast, Nat.cast_eq_zero]

def arrayHeadOffsetExpr : Expr := .cast (.abiDecode abiUInt256
  (.bytesSlice (.var "data") (.intLit 4) (.intLit 36))) (.elem (.int (.uint ⟨256, by decide⟩)))

theorem arrayHeadOffset_eval {f : Frame} {evm : EVM.State} {data : ByteArray}
    (hd : f.locals.get? "data" = some (.bytes data)) (hlen : 36 ≤ data.size) :
    evalExpr? config f evm arrayHeadOffsetExpr =
      .ok (.int (Int.ofNat (calldataWord data 4).toNat)) := by
  apply evalCastValue ?_ (by rw [castValue_int, normalizeInt_uint256_word])
  have hs : evalExpr? config f evm (.bytesSlice (.var "data") (.intLit 4) (.intLit 36)) =
      .ok (.bytes (data.extract 4 36)) := by
    simp only [evalExpr?, hd, EvalResult.ofOption, bind, EvalResult.bind, pure]
    exact sliceBytes_nat (by decide) hlen
  have hdec : decodeReturnValueWithMode? config.abiDecodeMode abiUInt256 (data.extract 4 36) =
      some (.int (Int.ofNat (calldataWord data 4).toNat)) :=
    decodeReturnUint_extract (by decide) hlen (by decide)
  rw [evalExpr?, hs]
  simp only [bind, EvalResult.bind, hdec, pure]

def arrayEmptyReadBody (transient : Bool) : List Stmt := [
  .letDecl "data" (some .bytes) (.env .msgData),
  .letDecl "offset" (some abiUInt256) (.binary .add arrayHeadOffsetExpr (.intLit 36)),
  .internalCall "calldataWordAt" [.var "offset"] "slot",
  .letDecl "ignored" (some abiUInt256) (wordArrayRead transient (.var "slot")),
  .return [.var "result"]]

theorem wordArrayEmptyReturns (transient : Bool) {f : Frame} {evm : EVM.State}
    (hf : f.contract = contract) (hlen : 36 ≤ evm.executionEnv.calldata.size)
    (hr : f.locals.get? "result" = some (.array [])) (hraw : f.locals.get? "rawSlots" = none) :
    ∃ f', ExecBlock config f evm (arrayEmptyReadBody transient) (.returned f' evm (some [.array []])) := by
  let f1 := {f with locals := f.locals.insert "data" (.bytes evm.executionEnv.calldata)}
  let f2 := {f1 with locals := f1.locals.insert "offset" (.int (Int.ofNat ((calldataWord evm.executionEnv.calldata 4).toNat + 36)))}
  have hoff : evalExpr? config f1 evm (.binary .add arrayHeadOffsetExpr (.intLit 36)) =
      .ok (.int (Int.ofNat ((calldataWord evm.executionEnv.calldata 4).toNat + 36))) :=
    naturalAddSource (arrayHeadOffset_eval (store_get_self _ _ _) hlen)
      (by simp only [evalExpr?, pure]; rfl)
  obtain ⟨word, hcall⟩ := calldataWordCall (f := f2) (evm := evm) hf
    (evalLocalValue (store_get_self _ _ _)) "slot"
  let f3 := {f2 with locals := f2.locals.insert "slot" (.int (Int.ofNat word.toNat))}
  let f4 := {f3 with locals := f3.locals.insert "ignored" (.int (Int.ofNat
    (wordArrayLoad transient evm word).toNat))}
  have hraw3 : f3.locals.get? "rawSlots" = none := by
    simpa only [f3, f2, f1,
      store_get_ne (k := "slot") (a := "rawSlots") _ _ (by decide),
      store_get_ne (k := "offset") (a := "rawSlots") _ _ (by decide),
      store_get_ne (k := "data") (a := "rawSlots") _ _ (by decide)] using hraw
  have hresult : f4.locals.get? "result" = some (.array []) := by
    simpa only [f4, f3, f2, f1,
      store_get_ne (k := "ignored") (a := "result") _ _ (by decide),
      store_get_ne (k := "slot") (a := "result") _ _ (by decide),
      store_get_ne (k := "offset") (a := "result") _ _ (by decide),
      store_get_ne (k := "data") (a := "result") _ _ (by decide)] using hr
  refine ⟨f4, ?_⟩
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, envValue, pure]))
    (ExecBlock.consNormal (ExecStmt.letDecl hoff)
      (ExecBlock.consNormal hcall (ExecBlock.consNormal (ExecStmt.letDecl
        (wordArrayRead_eval transient hf hraw3 (evalLocalValue (store_get_self _ _ _))))
        (ABlock.start.returns (evalLocalValue hresult)))))

def wordArrayArgs (slots : List Value) : Store := (∅ : Store).insert "slots" (.array slots)
def wordArrayResultFrame (evm : EVM.State) (slots : List Value) (imms : Store) : Frame :=
  {contract := contract, locals := ((wordArrayArgs slots).insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
    "result" (.array (List.replicate slots.length (wordBytes32Value ⟨0⟩))), immutables := imms}

def wordArrayBody (transient : Bool) : List Stmt := nonpayableCalldataPrefix ++ [
  .letDecl "result" (some (.dynamicArray abiBytes32))
    (.newArray (.elem (.bytes abiBytes32Width)) (.arrayLength .localVar {base := "slots"})),
  .ite (.binary .eq (.arrayLength .localVar {base := "slots"}) (.intLit 0)) (arrayEmptyReadBody transient) [],
  .letDecl "i" (some abiUInt256) (.intLit 0),
  .while wordArrayCond (wordArrayLoopBody transient),
  .return [.var "result"]]

theorem wordArrayPrelude (transient : Bool) (evm : EVM.State) (slots : List Value) (imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ABlock config evm {contract := contract, locals := wordArrayArgs slots, immutables := imms}
      (wordArrayBody transient) (wordArrayResultFrame evm slots imms)
      ((wordArrayBody transient).drop 4) := by
  refine ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (by simp only [evalExpr?, envValue, pure])
    |>.requireStep ?_ |>.letStep ?_
  · simpa only [hhi, decide_true] using calldataSizeGuard_eval config contract (wordArrayArgs slots) imms evm
  · exact evalNewArrayNat (evalLocalArrayLength
      ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)))
      (show defaultValue? (.elem (.bytes abiBytes32Width)) = .ok (wordBytes32Value ⟨0⟩) by native_decide)

theorem wordArraySource (transient : Bool) (evm : EVM.State) (slots : List Value) (imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hd : WordArrayDecoded evm.executionEnv.calldata slots) :
    ∃ f, ExecTransitionBody config contract evm (wordArrayArgs slots)
      (wordArrayBody transient)
      (.returned f evm (some [.array (wordArrayValues (wordArrayValue transient evm) 0 slots.length)])) imms := by
  let f := wordArrayResultFrame evm slots imms
  have hslots : f.locals.get? "slots" = some (.array slots) := by
    simp only [f, wordArrayResultFrame, wordArrayArgs,
      store_get_ne (k := "result") (a := "slots") _ _ (by decide),
      store_get_ne (k := "__calldata") (a := "slots") _ _ (by decide), store_get_self]
  have hraw : f.locals.get? "rawSlots" = none := by
    simp only [f, wordArrayResultFrame, wordArrayArgs,
      store_get_ne (k := "result") (a := "rawSlots") _ _ (by decide),
      store_get_ne (k := "__calldata") (a := "rawSlots") _ _ (by decide),
      store_get_ne (k := "slots") (a := "rawSlots") _ _ (by decide), store_get_empty]
  have heq := evalNatEqZero (cfg := config) (f := f) (evm := evm) (evalLocalArrayLength hslots)
  have hp := wordArrayPrelude transient evm slots imms hwv (by have := hd.bounds.2.1; unfold calldataLimit; omega)
  by_cases hz : slots.length = 0
  · have hr : f.locals.get? "result" = some (.array []) := by
      simp only [f, wordArrayResultFrame, hz, List.replicate_zero, store_get_self]
    obtain ⟨last, hb⟩ := wordArrayEmptyReturns transient rfl hd.bounds.1 hr hraw
    refine ⟨last, ExecFuncBody.execBlockRet (hp.run ?_)⟩
    simp only [hz, wordArrayValues, wordArrayWords, List.map_nil]
    change ExecBlock config f evm _ (.returned last evm (some [.array []]))
    exact ExecBlock.consReturn (ExecStmt.iteTrue (by simpa only [hz, decide_true] using heq) hb)
  · let res := List.replicate slots.length (wordBytes32Value ⟨0⟩)
    let locals := f.locals.insert "i" (.int 0)
    have hl : WordArrayLocals slots res 0 locals := by
      constructor
      · exact (store_get_ne _ _ (by decide)).trans hslots
      · exact store_get_self _ _ _
      · exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
      · exact (store_get_ne _ _ (by decide)).trans hraw
    obtain ⟨last, hloop, hlast⟩ := wordArraySourceLoop transient evm imms slots hd slots.length
      locals res 0 hl (by omega) (List.length_replicate ..) (by omega)
    refine ⟨{contract := contract, locals := last, immutables := imms},
      ExecFuncBody.execBlockRet (hp.run ?_)⟩
    exact ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hz, decide_false] using heq) ExecBlock.nil)
      ((ABlock.start.letStep (by simp only [evalExpr?, pure]) |>.whileStep hloop).returns (evalLocalValue hlast))

end Benchmarks.UniswapV4PoolManager
