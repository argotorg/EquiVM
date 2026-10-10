import Benchmarks.UniswapV4PoolManager.WordOperationsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev tickLogFunction : FunctionDecl := contract.functions[1]!
theorem tickLog_lookup : lookupCallable? contract "TickMath_logStep" = some tickLogFunction.toCallable := rfl

def tickLogSquare (r : UInt256) : UInt256 := UInt256.shiftRight (UInt256.mul r r) (UInt256.ofNat 127)
def tickLogFlag (r : UInt256) : UInt256 := UInt256.shiftRight (tickLogSquare r) (UInt256.ofNat 128)
def tickLogWord (r log2 : UInt256) (bit : Nat) : UInt256 :=
  UInt256.lor log2 (UInt256.shiftLeft (tickLogFlag r) (UInt256.ofNat bit))
def tickLogNext (r : UInt256) (normalize : Bool) : UInt256 :=
  if normalize then UInt256.shiftRight (tickLogSquare r) (tickLogFlag r) else tickLogSquare r

theorem tickLogFlag_lt_two (r : UInt256) : (tickLogFlag r).toNat < 2 := by
  have hs := (UInt256.mul r r).val.isLt
  change (UInt256.mul r r).toNat < 2^256 at hs
  rw [tickLogFlag, wordShiftRightNat _ (by decide), tickLogSquare, wordShiftRightNat _ (by decide)]
  omega

theorem tickLogBody {f : Frame} {evm : EVM.State} {r log2 : UInt256} {bit : Nat} {normalize : Bool}
    (hbit : bit < 256)
    (hr : f.locals.get? "r" = some (.int (Int.ofNat r.toNat)))
    (hl : f.locals.get? "log2" = some (.int (EVM.signed log2)))
    (hb : f.locals.get? "bit" = some (.int (Int.ofNat bit)))
    (hn : f.locals.get? "normalize" = some (.bool normalize)) :
    ∃ f', ExecFuncBody config f evm tickLogFunction.body
      (.returned f' evm (some [.int (Int.ofNat (tickLogNext r normalize).toNat),
        .int (EVM.signed (tickLogWord r log2 bit))])) := by
  let f1 : Frame := {f with locals := f.locals.insert "r" (.int (Int.ofNat (tickLogSquare r).toNat))}
  let f2 : Frame := {f1 with locals := f1.locals.insert "f" (.int (Int.ofNat (tickLogFlag r).toNat))}
  let f3 : Frame := {f2 with locals := f2.locals.insert "log2" (.int (EVM.signed (tickLogWord r log2 bit)))}
  have hsquare := evalWordShr (b := .intLit 127) (n := 127) (by decide)
    (evalWordMul (evalLocalValue (cfg := config) (evm := evm) hr) (evalLocalValue hr))
    (by simp only [evalExpr?, pure]; rfl)
  have hs : ExecStmt config f evm tickLogFunction.body[0]! (.ok f1 evm) :=
    ExecStmt.assign hsquare (assignLocalValue hr)
  have hr1 : f1.locals.get? "r" = some (.int (Int.ofNat (tickLogSquare r).toNat)) := store_get_self _ _ _
  have hflag := evalWordShr (cfg := config) (evm := evm) (b := .intLit 128) (n := 128) (by decide)
    (evalLocalValue hr1) (by simp only [evalExpr?, pure]; rfl)
  have hf : ExecStmt config f1 evm tickLogFunction.body[1]! (.ok f2 evm) := ExecStmt.letDecl hflag
  have hl2 : f2.locals.get? "log2" = some (.int (EVM.signed log2)) :=
    (store_get_ne2 _ _ _ (by decide : ("r" == "log2") = false)
      (by decide : ("f" == "log2") = false)).trans hl
  have hb2 : f2.locals.get? "bit" = some (.int (Int.ofNat bit)) :=
    (store_get_ne2 _ _ _ (by decide : ("r" == "bit") = false)
      (by decide : ("f" == "bit") = false)).trans hb
  have hflag2 : f2.locals.get? "f" = some (.int (Int.ofNat (tickLogFlag r).toNat)) := store_get_self _ _ _
  have hcast := evalExpr_cast_int (cfg := config) (evm := evm) (intType := .sint ⟨256, by decide⟩)
    (evalLocalValue hflag2)
  rw [normalizeInt_sint256_word_of_lt _ (by have hh := tickLogFlag_lt_two r; change _ < 2^255; omega)] at hcast
  have hlog := evalSignedWordOr (evalLocalValue hl2) (evalSignedShlOfNat hbit hcast (evalLocalValue hb2))
  have hlogstmt : ExecStmt config f2 evm tickLogFunction.body[2]! (.ok f3 evm) :=
    ExecStmt.assign hlog (assignLocalValue hl2)
  have hr3 : f3.locals.get? "r" = some (.int (Int.ofNat (tickLogSquare r).toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("f" == "r") = false)
      (by decide : ("log2" == "r") = false)).trans hr1
  have hl3 : f3.locals.get? "log2" = some (.int (EVM.signed (tickLogWord r log2 bit))) := store_get_self _ _ _
  have hf3 : f3.locals.get? "f" = some (.int (Int.ofNat (tickLogFlag r).toNat)) :=
    (store_get_ne _ _ (by decide : ("log2" == "f") = false)).trans hflag2
  have hn3 : f3.locals.get? "normalize" = some (.bool normalize) :=
    (store_get_ne3 _ _ _ _ (by decide : ("r" == "normalize") = false)
      (by decide : ("f" == "normalize") = false)
      (by decide : ("log2" == "normalize") = false)).trans hn
  have hnorm := evalWordShr (cfg := config) (evm := evm)
    (by have hh := tickLogFlag_lt_two r; omega : (tickLogFlag r).toNat < 256)
    (evalLocalValue hr3) (evalLocalValue hf3)
  rw [u256_ofNat_toNat] at hnorm
  cases normalize with
  | false =>
    refine ⟨f3, .execBlockRet (ExecBlock.consNormal hs (ExecBlock.consNormal hf
      (ExecBlock.consNormal hlogstmt (ExecBlock.consNormal
        (ExecStmt.iteFalse (evalLocalValue hn3) ExecBlock.nil)
        (ExecBlock.consReturn (ExecStmt.return ?_))))))⟩
    simp only [tickLogNext, Bool.false_eq_true, if_false, evalExprs?,
      evalLocalValue hr3, evalLocalValue hl3, bind, EvalResult.bind, pure]
  | true =>
    let f4 : Frame := {f3 with locals := f3.locals.insert "r" (.int
        (Int.ofNat (UInt256.shiftRight (tickLogSquare r) (tickLogFlag r)).toNat))}
    have hr4 : f4.locals.get? "r" = some (.int (Int.ofNat (tickLogNext r true).toNat)) := store_get_self _ _ _
    have hl4 : f4.locals.get? "log2" = some (.int (EVM.signed (tickLogWord r log2 bit))) :=
      (store_get_ne _ _ (by decide : ("r" == "log2") = false)).trans hl3
    refine ⟨f4, .execBlockRet (ExecBlock.consNormal hs (ExecBlock.consNormal hf
      (ExecBlock.consNormal hlogstmt (ExecBlock.consNormal
        (ExecStmt.iteTrue (evalLocalValue hn3)
          (execBlock_singleton (ExecStmt.assign hnorm (assignLocalValue hr3))))
        (ExecBlock.consReturn (ExecStmt.return ?_))))))⟩
    change evalExprs? config f4 evm [.var "r", .var "log2"] = _
    simp only [evalExprs?, evalLocalValue hr4, evalLocalValue hl4, bind, EvalResult.bind, pure]

theorem tickLogCall {f : Frame} {evm : EVM.State} {er el eb en : Expr}
    {r log2 : UInt256} {bit : Nat} {normalize : Bool}
    (hf : f.contract = contract) (hbit : bit < 256)
    (hr : evalExpr? config f evm er = .ok (.int (Int.ofNat r.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (EVM.signed log2)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat bit)))
    (hn : evalExpr? config f evm en = .ok (.bool normalize)) (retVar : Ident) :
    ExecStmt config f evm (.internalCall "TickMath_logStep" [er, el, eb, en] retVar)
      (.ok {f with locals := f.locals.insert retVar (.tuple
        [.int (Int.ofNat (tickLogNext r normalize).toNat), .int (EVM.signed (tickLogWord r log2 bit))])} evm) := by
  let locals := ((((∅ : Store).insert "normalize" (.bool normalize)).insert "bit" (.int (Int.ofNat bit))).insert
    "log2" (.int (EVM.signed log2))).insert "r" (.int (Int.ofNat r.toNat))
  obtain ⟨f', hbody⟩ := tickLogBody (f := {f with locals := locals}) (evm := evm)
    (r := r) (log2 := log2) (bit := bit) (normalize := normalize) hbit
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("r" == "log2") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("log2" == "bit") = false)
      (by decide : ("r" == "bit") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("bit" == "normalize") = false)
      (by decide : ("log2" == "normalize") = false)
      (by decide : ("r" == "normalize") = false)).trans (store_get_self _ _ _))
  exact internalCallFunctionReturn
    (argVals := [.int (Int.ofNat r.toNat), .int (EVM.signed log2), .int (Int.ofNat bit), .bool normalize])
    (value := some [.int (Int.ofNat (tickLogNext r normalize).toNat), .int (EVM.signed (tickLogWord r log2 bit))])
    (by simp only [evalExprs?, hr, hl, hb, hn, bind, EvalResult.bind, pure])
    (by rw [hf]; exact tickLog_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager
