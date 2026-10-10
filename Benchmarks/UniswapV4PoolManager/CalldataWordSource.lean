import Benchmarks.UniswapV4PoolManager.LocalArray

/-! Source semantics of the bounded, bytewise calldata read used for empty arrays. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: a byte index converted through uint8 has its unsigned byte value.
theorem evalByteIndexUint256 {cfg : Config} {f : Frame} {evm : EVM.State}
    {dataE indexE : Expr} {data : ByteArray} {i : Nat}
    (hd : evalExpr? cfg f evm dataE = .ok (.bytes data))
    (hi : evalExpr? cfg f evm indexE = .ok (.int (Int.ofNat i)))
    (hb : i < data.toList.length) :
    evalExpr? cfg f evm (.cast (.cast (.index dataE indexE)
      (.elem (.int (.uint ⟨8, by decide⟩)))) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat data.toList[i].toNat)) := by
  apply evalCastValue (v := .int (Int.ofNat data.toList[i].toNat))
    (evalCastValue (v := .fixedBytes ⟨0, by decide⟩ [data.toList[i]]) ?_ ?_) ?_
  · simp only [evalExpr?, hd, hi, bind, EvalResult.bind, evalIndex?, evalByteIndex?,
      Int.ofNat_eq_natCast, Int.toNat_natCast, show ¬ (i : Int) < 0 by omega,
      if_false, hb, if_true, lookupNth_eq_getElem, List.getElem?_eq_getElem hb,
      Option.map_some, EvalResult.ofOption]
  · simp only [castValue?, fixedBytesToNat?, fixedBytesValid, fixedBytesSize,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      show (8 : Nat) = 8 from rfl, if_true, fromBytesBigEndian, Function.comp_apply,
      List.reverse_cons, List.reverse_nil, List.nil_append, fromBytes', Nat.mul_zero, Nat.add_zero]
    rfl
  · rw [castValue_int]
    apply congrArg (fun i => some (Value.int i))
    apply normalizeInt_uint_eq_self ⟨256, by decide⟩
    · exact Int.natCast_nonneg _
    · apply Int.ofNat_lt.mpr
      have hbyte : data.toList[i].toNat < 256 := UInt8.toNat_lt _
      change data.toList[i].toNat < 2^256
      omega

abbrev calldataWordFunction : FunctionDecl := contract.functions[2]!
theorem calldataWordFunction_lookup :
    lookupCallable? contract "calldataWordAt" = some calldataWordFunction.toCallable := rfl

def calldataReadCond : Expr := .binary .lt (.var "j") (.intLit 32)
def calldataReadIndex : Expr := .binary .add (.var "offset") (.var "j")
def calldataReadByteCond : Expr := .binary .lt calldataReadIndex
  (.arrayLength .localVar {base := "data"})
def calldataReadByte : Expr := .cast (.cast (.index (.var "data") calldataReadIndex)
  (.elem (.int (.uint ⟨8, by decide⟩)))) (.elem (.int (.uint ⟨256, by decide⟩)))
def calldataReadByteStmt : Stmt := .ite calldataReadByteCond
  [.assign .localVar {base := "word"} (.binary .add (.var "word") calldataReadByte)] []
def calldataReadBody : List Stmt :=
  [.assign .localVar {base := "word"} (.binary .mul (.var "word") (.intLit 256)),
   calldataReadByteStmt,
   .assign .localVar {base := "j"} (.binary .add (.var "j") (.intLit 1))]

structure CalldataReadLocals (data : ByteArray) (off j word : Nat) (f : Frame) : Prop where
  data_eq : f.locals.get? "data" = some (.bytes data)
  off_eq : f.locals.get? "offset" = some (.int (Int.ofNat off))
  index_eq : f.locals.get? "j" = some (.int (Int.ofNat j))
  word_eq : f.locals.get? "word" = some (.int (Int.ofNat word))

theorem CalldataReadLocals.setWord {data off j word f} (h : CalldataReadLocals data off j word f)
    (next : Nat) : CalldataReadLocals data off j next
      {f with locals := f.locals.insert "word" (.int (Int.ofNat next))} := by
  constructor
  · exact (store_get_ne _ _ (by decide)).trans h.data_eq
  · exact (store_get_ne _ _ (by decide)).trans h.off_eq
  · exact (store_get_ne _ _ (by decide)).trans h.index_eq
  · exact store_get_self _ _ _

theorem CalldataReadLocals.setIndex {data off j word f} (h : CalldataReadLocals data off j word f)
    (next : Nat) : CalldataReadLocals data off next word
      {f with locals := f.locals.insert "j" (.int (Int.ofNat next))} := by
  constructor
  · exact (store_get_ne _ _ (by decide)).trans h.data_eq
  · exact (store_get_ne _ _ (by decide)).trans h.off_eq
  · exact store_get_self _ _ _
  · exact (store_get_ne _ _ (by decide)).trans h.word_eq

theorem calldataReadOptionalByte {data : ByteArray} {off j word : Nat} {f : Frame}
    (evm : EVM.State) (h : CalldataReadLocals data off j word f) :
    ∃ f' byte, byte < 256 ∧
      ExecStmt config f evm calldataReadByteStmt (.ok f' evm) ∧
      CalldataReadLocals data off j (word + byte) f' := by
  have heindex : evalExpr? config f evm calldataReadIndex = .ok (.int (Int.ofNat (off + j))) :=
    naturalAddSource (evalLocalValue h.off_eq) (evalLocalValue h.index_eq)
  have hecond : evalExpr? config f evm calldataReadByteCond =
      .ok (.bool (decide (off + j < data.size))) := by
    simp only [calldataReadByteCond, evalExpr?, heindex, h.data_eq, readLocalPath?,
      bind, EvalResult.bind, pure, evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_lt]
  by_cases hb : off + j < data.size
  · have hbl : off + j < data.toList.length := by
      rw [byteArray_toList_eq, Array.length_toList]; exact hb
    let byte := data.toList[off + j].toNat
    have hbfit : byte < 256 := UInt8.toNat_lt _
    refine ⟨{f with locals := f.locals.insert "word" (.int (Int.ofNat (word + byte)))},
      byte, hbfit, ExecStmt.iteTrue ?_ ?_, h.setWord (word + byte)⟩
    · simpa only [hb, decide_true] using hecond
    · exact ExecBlock.consNormal (ExecStmt.assign
        (naturalAddSource (evalLocalValue h.word_eq)
          (evalByteIndexUint256 (evalLocalValue h.data_eq) heindex hbl))
        (assignLocalValue h.word_eq)) ExecBlock.nil
  · refine ⟨f, 0, by decide, ExecStmt.iteFalse ?_ ExecBlock.nil, ?_⟩
    · simpa only [hb, decide_false] using hecond
    · simpa only [Nat.add_zero] using h

theorem calldataReadStep {data : ByteArray} {off j word : Nat} {f : Frame}
    (evm : EVM.State) (h : CalldataReadLocals data off j word f) :
    ∃ f' next, next < (word + 1) * 256 ∧
      ExecBlock config f evm calldataReadBody (.ok f' evm) ∧
      CalldataReadLocals data off (j + 1) next f' := by
  let f1 := {f with locals := f.locals.insert "word" (.int (Int.ofNat (word * 256)))}
  have h1 : CalldataReadLocals data off j (word * 256) f1 := h.setWord _
  obtain ⟨f2, byte, hb, hs, h2⟩ := calldataReadOptionalByte evm h1
  refine ⟨{f2 with locals := f2.locals.insert "j" (.int (Int.ofNat (j + 1)))},
    word * 256 + byte, by omega, ?_, h2.setIndex _⟩
  refine ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalValue h.word_eq))
    (ExecBlock.consNormal hs (ExecBlock.consNormal (ExecStmt.assign
      (naturalAddSource (evalLocalValue h2.index_eq) (by simp only [evalExpr?, pure]; rfl))
      (assignLocalValue h2.index_eq)) ExecBlock.nil))
  simp only [evalExpr?, h.word_eq, EvalResult.ofOption, bind, EvalResult.bind, pure, evalBinaryOp?]
  rfl

theorem calldataReadLoop (evm : EVM.State) (data : ByteArray) (off remaining : Nat) :
    ∀ f j word, CalldataReadLocals data off j word f → j + remaining = 32 → word < 256^j →
    ∃ f' out, out < UInt256.size ∧
      ExecStmt config f evm (.while calldataReadCond calldataReadBody) (.ok f' evm) ∧
      f'.locals.get? "word" = some (.int (Int.ofNat out)) := by
  induction remaining with
  | zero =>
      intro f j word hl hj hw
      have hj : j = 32 := by omega
      refine ⟨f, word, ?_, ExecStmt.whileFalse ?_, hl.word_eq⟩
      · simpa only [hj, show (256 : Nat)^32 = UInt256.size by decide] using hw
      · simp only [calldataReadCond, evalExpr?, hl.index_eq, EvalResult.ofOption,
          bind, EvalResult.bind, pure, evalBinaryOp?, hj]
        rfl
  | succ remaining ih =>
      intro f j word hl hj hw
      obtain ⟨f1, next, hn, hs, hl1⟩ := calldataReadStep evm hl
      have hn' : next < 256^(j+1) := by rw [Nat.pow_succ]; omega
      obtain ⟨f2, out, ho, hs2, hl2⟩ := ih f1 (j+1) next hl1 (by omega) hn'
      refine ⟨f2, out, ho, ExecStmt.whileTrue ?_ hs hs2, hl2⟩
      simp only [calldataReadCond, evalExpr?, hl.index_eq, EvalResult.ofOption,
        bind, EvalResult.bind, pure, evalBinaryOp?]
      have hj' : Int.ofNat j < 32 := by simp only [Int.ofNat_eq_natCast]; omega
      rw [decide_eq_true hj']

/-- The bounded read always returns a word, including reads partly outside calldata. -/
theorem calldataWordBodyExec {f : Frame} {evm : EVM.State} {off : Nat}
    (hoff : f.locals.get? "offset" = some (.int (Int.ofNat off))) :
    ∃ f' : Frame, ∃ word : UInt256, ExecFuncBody config f evm calldataWordFunction.body
      (.returned f' evm (some [.int (Int.ofNat word.toNat)])) := by
  let f1 := {f with locals := ((f.locals.insert "data" (.bytes evm.executionEnv.calldata)).insert
    "word" (.int 0)).insert "j" (.int 0)}
  have hl : CalldataReadLocals evm.executionEnv.calldata off 0 0 f1 := by
    constructor
    · simp only [f1, store_get_ne (k := "j") (a := "data") _ _ (by decide),
        store_get_ne (k := "word") (a := "data") _ _ (by decide), store_get_self]
    · simpa only [f1, store_get_ne (k := "j") (a := "offset") _ _ (by decide),
        store_get_ne (k := "word") (a := "offset") _ _ (by decide),
        store_get_ne (k := "data") (a := "offset") _ _ (by decide)] using hoff
    · exact store_get_self _ _ _
    · exact (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _)
  obtain ⟨last, out, hfit, hloop, hout⟩ := calldataReadLoop evm evm.executionEnv.calldata off 32
    f1 0 0 hl rfl (by decide)
  refine ⟨last, UInt256.ofNat out, ExecFuncBody.execBlockRet ?_⟩
  rw [UInt256.toNat_ofNat_of_lt hfit]
  exact (ABlock.start.letStep (by simp only [evalExpr?, envValue, pure])
    |>.letStep (by simp only [evalExpr?, pure])
    |>.letStep (by simp only [evalExpr?, pure])
    |>.whileStep hloop).returns (evalLocalValue hout)

theorem calldataWordCall {f : Frame} {evm : EVM.State} {e : Expr} {off : Nat}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat off)))
    (retVar : Ident) :
    ∃ word : UInt256, ExecStmt config f evm (.internalCall "calldataWordAt" [e] retVar)
      (.ok {f with locals := f.locals.insert retVar (.int (Int.ofNat word.toNat))} evm) := by
  obtain ⟨last, word, hbody⟩ := calldataWordBodyExec
    (f := {f with locals := (∅ : Store).insert "offset" (.int (Int.ofNat off))})
    (evm := evm) (store_get_self _ _ _)
  refine ⟨word, ?_⟩
  exact internalCallFunctionReturn (evalExprs?_singleton he)
    (by rw [hf]; exact calldataWordFunction_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager
