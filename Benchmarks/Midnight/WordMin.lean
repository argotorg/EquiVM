import Benchmarks.Midnight.InternalCall
import Reasoning.VyperDispatch

/-! The shared minimum helper and its branchless word implementation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def wordMin (x y : UInt256) : UInt256 := if y.toNat < x.toNat then y else x

theorem wordMin_branchless (x y : UInt256) :
    UInt256.xor x (UInt256.mul (UInt256.xor x y) (UInt256.lt y x)) = wordMin x y := by
  have hxor (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
    apply u256_inj
    change (a.toNat ^^^ b.toNat) % UInt256.size = (b.toNat ^^^ a.toNat) % UInt256.size
    rw [Nat.xor_comm]
  rw [hxor x, u256_mul_comm]
  exact Reasoning.VyperDispatch.branchlessMin x y

def minFunction : FunctionDecl := contract.functions[11]!

theorem minBodyReturns {cfg : Config} {frame : Frame} {evm : EVM.State} {x y : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat)) :
    ExecFuncBody cfg frame evm minFunction.body
      (.returned frame evm (some [.int (wordMin x y).toNat])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  change evalExpr? cfg frame evm
    (.ite (.binary .lt (.var "y") (.var "x")) (.var "y") (.var "x")) = _
  simp only [evalExpr?, hx, hy, EvalResult.ofOption, bind, pure, EvalResult.bind,
    evalBinaryOp?, Int.ofNat_lt]
  by_cases h : y.toNat < x.toNat <;> simp [wordMin, h]

def minArguments (x y : UInt256) : Store :=
  ((∅ : Store).insert "y" (.int y.toNat)).insert "x" (.int x.toNat)

theorem callMin {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (he : evalExprs? cfg frame evm args = .ok [.int x.toNat, .int y.toNat]) :
    ExecStmt cfg frame evm (.internalCall "UtilsLib_min" args name)
      (.ok (resumeAfterInternalCall frame name (some [.int (wordMin x y).toNat])) evm) := by
  apply internalCallFunctionReturn (callee := minFunction) (locals := minArguments x y) he
  · rw [hc]; rfl
  · rfl
  · apply minBodyReturns (x := x) (y := y) <;>
      simp [minArguments, Std.HashMap.getElem_insert]

end Benchmarks.Midnight
