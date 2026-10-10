import Benchmarks.UniswapV4PoolManager.MostSignificantBit
import Benchmarks.UniswapV4PoolManager.WordByteSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev mostSignificantBitFunction : FunctionDecl := contract.functions[88]!
theorem mostSignificantBit_lookup :
    lookupCallable? contract "BitMath_mostSignificantBit" = some mostSignificantBitFunction.toCallable := rfl

def msbStageStmt (limit : UInt256) (bit : Nat) : Stmt :=
  .assign .localVar {base := "r"} (.binary (.bitOr (.uint ⟨256, by decide⟩)) (.var "r")
    (.ite (.binary .gt (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "x") (.var "r"))
      (.intLit (Int.ofNat limit.toNat))) (.intLit (Int.ofNat (2^bit))) (.intLit 0)))

theorem msbStageStmtExec {f : Frame} {evm : EVM.State} {x r : UInt256}
    (limit : UInt256) (bit : Nat) (hb : bit < 256)
    (hx : f.locals.get? "x" = some (.int (Int.ofNat x.toNat)))
    (hr : f.locals.get? "r" = some (.int (Int.ofNat r.toNat))) :
    ExecStmt config f evm (msbStageStmt limit bit)
      (.ok {f with locals := f.locals.insert "r" (.int (Int.ofNat (msbStage x r limit bit).toNat))} evm) := by
  have hs := evalWordShrWord (evalLocalValue (cfg := config) (evm := evm) hx) (evalLocalValue hr)
  have hp := evalComparisonPower (limit := limit) (b := .intLit (Int.ofNat limit.toNat)) hb hs
    (by simp only [evalExpr?, pure])
  have ho := evalWordOr (evalLocalValue hr) hp
  rw [u256_lor_comm r] at ho
  exact ExecStmt.assign ho (assignLocalValue hr)

theorem mostSignificantBit_guard {f : Frame} {evm : EVM.State} {x : UInt256}
    (hx : f.locals.get? "x" = some (.int (Int.ofNat x.toNat))) :
    evalExpr? config f evm (.binary .gt (.var "x") (.intLit 0)) =
      .ok (.bool (decide (x ≠ ⟨0⟩))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hx]
  simp only [evalExpr?, pure, bind, EvalResult.bind, evalBinaryOp?]
  have he : (0 : Int) < Int.ofNat x.toNat ↔ x ≠ ⟨0⟩ := by
    constructor
    · intro h hz; rw [hz] at h; contradiction
    · intro h; have hn : x.toNat ≠ 0 := fun he => h (uint256_toNat_eq_zero he)
      simp only [Int.ofNat_eq_natCast]
      omega
  change EvalResult.ok (Value.bool (decide ((0 : Int) < Int.ofNat x.toNat))) = _
  simp only [he]

theorem mostSignificantBit_zero {f : Frame} {evm : EVM.State}
    (hx : f.locals.get? "x" = some (.int 0)) :
    ExecFuncBody config f evm mostSignificantBitFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  have he := mostSignificantBit_guard (x := ⟨0⟩) (evm := evm) hx
  simpa only [ne_eq, not_true_eq_false, decide_false] using he

theorem mostSignificantBit_body {f : Frame} {evm : EVM.State} {x : UInt256}
    (hf : f.contract = contract) (hx : f.locals.get? "x" = some (.int (Int.ofNat x.toNat)))
    (hn : x ≠ ⟨0⟩) :
    ∃ f', ExecFuncBody config f evm mostSignificantBitFunction.body
      (.returned f' evm (some [.int (Int.ofNat (mostSignificantBit x).toNat)])) := by
  let f1 : Frame := {f with locals := f.locals.insert "r" (.int (Int.ofNat (msbInitial x).toNat))}
  let f2 : Frame := {f1 with locals := f1.locals.insert "r" (.int (Int.ofNat (msb64 x).toNat))}
  let f3 : Frame := {f2 with locals := f2.locals.insert "r" (.int (Int.ofNat (msb32 x).toNat))}
  let f4 : Frame := {f3 with locals := f3.locals.insert "r" (.int (Int.ofNat (msb16 x).toNat))}
  let f5 : Frame := {f4 with locals := f4.locals.insert "r" (.int (Int.ofNat (msbHigh x).toNat))}
  let f6 : Frame := {f5 with locals := f5.locals.insert "index" (.int (Int.ofNat (msbIndex x).toNat))}
  let f7 : Frame := {f6 with locals := f6.locals.insert "low" (.int (Int.ofNat (UInt256.byteAt (msbIndex x) msbTable).toNat))}
  have hguard : ExecStmt config f evm mostSignificantBitFunction.body[0]! (.ok f evm) :=
    ExecStmt.requireTrue (by rw [mostSignificantBit_guard (x := x) hx, decide_eq_true hn])
  have hi := evalComparisonPower (limit := UInt256.ofNat (2^128-1)) (bit := 7)
    (b := .intLit 340282366920938463463374607431768211455) (by decide)
    (evalLocalValue (cfg := config) (evm := evm) hx) (by simp only [evalExpr?, pure]; rfl)
  have hinit : ExecStmt config f evm mostSignificantBitFunction.body[1]! (.ok f1 evm) := ExecStmt.letDecl hi
  have hx1 : f1.locals.get? "x" = some (.int (Int.ofNat x.toNat)) :=
    (store_get_ne _ _ (by decide : ("r" == "x") = false)).trans hx
  have hx2 : f2.locals.get? "x" = some (.int (Int.ofNat x.toNat)) :=
    (store_get_ne _ _ (by decide : ("r" == "x") = false)).trans hx1
  have hx3 : f3.locals.get? "x" = some (.int (Int.ofNat x.toNat)) :=
    (store_get_ne _ _ (by decide : ("r" == "x") = false)).trans hx2
  have hx4 : f4.locals.get? "x" = some (.int (Int.ofNat x.toNat)) :=
    (store_get_ne _ _ (by decide : ("r" == "x") = false)).trans hx3
  have hx5 : f5.locals.get? "x" = some (.int (Int.ofNat x.toNat)) :=
    (store_get_ne _ _ (by decide : ("r" == "x") = false)).trans hx4
  have hr5 : f5.locals.get? "r" = some (.int (Int.ofNat (msbHigh x).toNat)) := store_get_self _ _ _
  have hindex := evalWordAnd (evalWordShrWord
    (show evalExpr? config f5 evm (.intLit 175629608733387594055579892975202555070) =
      .ok (.int (Int.ofNat (UInt256.ofNat 175629608733387594055579892975202555070).toNat)) by
        simp only [evalExpr?, pure]; rfl)
    (evalWordShrWord (evalLocalValue hx5) (evalLocalValue hr5)))
    (show evalExpr? config f5 evm (.intLit 31) = .ok (.int (Int.ofNat (UInt256.ofNat 31).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  rw [u256_land_comm] at hindex
  have hindexstmt : ExecStmt config f5 evm mostSignificantBitFunction.body[6]! (.ok f6 evm) := ExecStmt.letDecl hindex
  have hbyte := wordByteCall (f := f6) (evm := evm) (word := msbTable) hf
    (show evalExpr? config f6 evm (.intLit 3176832568382053640854229765616608417700587278678501850580078522814972297216) =
      .ok (.int (Int.ofNat msbTable.toNat)) by simp only [evalExpr?, pure]; rfl)
    (evalLocalValue (store_get_self _ _ _)) "low"
  have hr7 : f7.locals.get? "r" = some (.int (Int.ofNat (msbHigh x).toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("index" == "r") = false)
      (by decide : ("low" == "r") = false)).trans hr5
  have hl7 : f7.locals.get? "low" = some (.int (Int.ofNat (UInt256.byteAt (msbIndex x) msbTable).toNat)) := store_get_self _ _ _
  have hret := evalExpr_cast_int (intType := .uint ⟨8, by decide⟩)
    (evalWordOr (evalLocalValue (cfg := config) (evm := evm) hr7) (evalLocalValue hl7))
  rw [u256_lor_comm (msbHigh x)] at hret
  change evalExpr? config f7 evm _ = .ok (.int
    (normalizeInt (.uint ⟨8, by decide⟩) (Int.ofNat (mostSignificantBit x).toNat))) at hret
  simp only [Int.ofNat_eq_natCast] at hret
  rw [normalizeInt_uint_eq_self ⟨8, by decide⟩ _ (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr (mostSignificantBit_lt_256 x))] at hret
  refine ⟨f7, .execBlockRet (ExecBlock.consNormal hguard (ExecBlock.consNormal hinit
    (ExecBlock.consNormal (msbStageStmtExec (UInt256.ofNat (2^64-1)) 6 (by decide) hx1 (store_get_self _ _ _))
      (ExecBlock.consNormal (msbStageStmtExec (UInt256.ofNat (2^32-1)) 5 (by decide) hx2 (store_get_self _ _ _))
        (ExecBlock.consNormal (msbStageStmtExec (UInt256.ofNat (2^16-1)) 4 (by decide) hx3 (store_get_self _ _ _))
          (ExecBlock.consNormal (msbStageStmtExec (UInt256.ofNat 255) 3 (by decide) hx4 (store_get_self _ _ _))
            (ExecBlock.consNormal hindexstmt (ExecBlock.consNormal hbyte
              (ABlock.start.returns hret)))))))))⟩

theorem mostSignificantBitCall {f : Frame} {evm : EVM.State} {e : Expr} {x : UInt256}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat x.toNat)))
    (retVar : Ident) :
    ExecStmt config f evm (.internalCall "BitMath_mostSignificantBit" [e] retVar)
      (if x = ⟨0⟩ then .reverted else
        .ok {f with locals := f.locals.insert retVar (.int (Int.ofNat (mostSignificantBit x).toNat))} evm) := by
  have hl : lookupCallable? f.contract "BitMath_mostSignificantBit" =
      some mostSignificantBitFunction.toCallable := by rw [hf]; exact mostSignificantBit_lookup
  by_cases hz : x = ⟨0⟩
  · rw [if_pos hz]
    apply internalCallFunctionRevert (evalExprs?_singleton he) hl rfl
    apply mostSignificantBit_zero
    simpa only [hz] using store_get_self (∅ : Store) "x" (.int (Int.ofNat x.toNat))
  · rw [if_neg hz]
    obtain ⟨f', hb⟩ := mostSignificantBit_body
      (f := {f with locals := (∅ : Store).insert "x" (.int (Int.ofNat x.toNat))})
      (evm := evm) (x := x) hf (store_get_self _ _ _) hz
    exact internalCallFunctionReturn (value := some [.int (Int.ofNat (mostSignificantBit x).toNat)])
      (evalExprs?_singleton he) hl rfl hb

end Benchmarks.UniswapV4PoolManager
