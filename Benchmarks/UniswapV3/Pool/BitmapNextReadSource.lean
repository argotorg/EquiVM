import Benchmarks.UniswapV3.Pool.BitmapNextMaskSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitmapNextReadFrame (imms : Store) (evm : EVM.State)
    (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextMaskFrame imms tick spacing lte with
    locals := (bitmapNextMaskFrame imms tick spacing lte).locals.insert "masked"
      (.int (Int.ofNat (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte).toNat))}

def bitmapNextInitFrame (imms : Store) (evm : EVM.State)
    (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextReadFrame imms evm tick spacing lte with
    locals := (bitmapNextReadFrame imms evm tick spacing lte).locals.insert "initialized"
      (.bool (decide (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte ≠ ⟨0⟩)))}

def bitmapNextCondName (lte : Bool) : String := if lte then "__cond2" else "__cond5"

def bitmapNextCondFrame (imms : Store) (evm : EVM.State)
    (tick spacing : Int) (lte : Bool) : Frame :=
  {bitmapNextInitFrame imms evm tick spacing lte with
    locals := (bitmapNextInitFrame imms evm tick spacing lte).locals.insert
      (bitmapNextCondName lte) (.int 0)}

theorem bitmapNextMaskGet (imms : Store) (tick spacing : Int) (lte : Bool) :
    (bitmapNextMaskFrame imms tick spacing lte).locals.get? "wordPos" =
        some (.int (bitmapWordPos (bitmapNextPosition (bitmapNextCompressed tick spacing) lte))) ∧
      (bitmapNextMaskFrame imms tick spacing lte).locals.get? "mask" =
        some (.int (Int.ofNat (bitmapNextMask (bitmapNextCompressed tick spacing) lte).toNat)) ∧
      (bitmapNextMaskFrame imms tick spacing lte).locals.get? "tickBitmap" = none := by
  have hb := (bitmapNextPrefixGet imms tick spacing lte).2.2.2.2.2
  cases lte <;>
    simp only [bitmapNextMaskFrame, bitmapNextBitFrame, bitmapNextWordFrame, bitmapNextCallFrame,
      bitmapNextCallName, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;>
    exact ⟨rfl, rfl, hb⟩

theorem evalBitmapNextMasked (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool) :
    evalExpr? config (bitmapNextMaskFrame imms tick spacing lte) evm
      (.binary (.bitAnd (.uint ⟨256, by decide⟩))
        (.storage ⟨"tickBitmap", [.mindex (.var "wordPos")]⟩) (.var "mask")) =
      .ok (.int
        (Int.ofNat (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte).toNat)) := by
  obtain ⟨hw, hm, hb⟩ := bitmapNextMaskGet imms tick spacing lte
  exact evalExpr_word_land (evalBitmapStorage _ imms evm _ _ hb (evalExpr_var_get hw))
    (evalExpr_var_get hm)

theorem bitmapNextReadInitialized (imms : Store) (evm : EVM.State)
    (tick spacing : Int) (lte : Bool) :
    ExecStmt config (bitmapNextReadFrame imms evm tick spacing lte) evm
      (.assign .localVar ⟨"initialized", []⟩ (.binary .ne (.var "masked") (.intLit 0)))
      (.ok (bitmapNextInitFrame imms evm tick spacing lte) evm) := by
  have he : evalExpr? config (bitmapNextReadFrame imms evm tick spacing lte) evm (.var "masked") =
      .ok (.int (Int.ofNat (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  have hz : evalExpr? config (bitmapNextReadFrame imms evm tick spacing lte) evm (.intLit 0) =
      .ok (.int 0) := by simp only [evalExpr?, pure]
  have hg : (bitmapNextReadFrame imms evm tick spacing lte).locals.get? "initialized" =
      some (.bool false) := by
    have hp := (bitmapNextPrefixGet imms tick spacing lte).2.2.2.2.1
    cases lte <;>
      simp only [bitmapNextReadFrame, bitmapNextMaskFrame, bitmapNextBitFrame,
        bitmapNextWordFrame, bitmapNextCallFrame, bitmapNextCallName,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> exact hp
  apply ExecStmt.assign _ (assignLocalVarBase_frame hg)
  refine (evalExpr_int_ne he hz).trans ?_
  apply congrArg (fun b : Bool ↦ (EvalResult.ok (Value.bool b) : EvalResult Value))
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, ne_eq, Int.ofNat_eq_natCast, Int.natCast_eq_zero]
  exact not_congr ⟨uint256_toNat_eq_zero, fun h ↦ congrArg UInt256.toNat h⟩

theorem bitmapNextReadSource (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool) :
    ExecBlock config (bitmapNextBitFrame imms tick spacing lte) evm
      (((bitmapNextBranch lte).drop 3).take 4)
      (.ok (bitmapNextCondFrame imms evm tick spacing lte) evm) := by
  have hr := evalBitmapNextMasked imms evm tick spacing lte
  have hi := bitmapNextReadInitialized imms evm tick spacing lte
  cases lte <;>
    exact ExecBlock.consNormal (bitmapNextMaskSource imms evm tick spacing _)
      (ExecBlock.consNormal (ExecStmt.letDecl hr)
        (ExecBlock.consNormal hi (ExecBlock.consNormal
          (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)))

end Benchmarks.UniswapV3.Pool
