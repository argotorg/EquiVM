import Benchmarks.Midnight.InternalCall

/-! The values and arithmetic preconditions of Midnight's multiplication and division helpers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def mulDivDown (x y d : UInt256) : UInt256 := UInt256.div (UInt256.mul x y) d

def mulDivUp (x y d : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul x y + UInt256.sub d ⟨1⟩) d

def MulDivUpSafe (x y d : UInt256) : Prop :=
  x.toNat * y.toNat < UInt256.size ∧ 0 < d.toNat ∧
    (UInt256.mul x y).toNat + (UInt256.sub d ⟨1⟩).toNat < UInt256.size

instance (x y d : UInt256) : Decidable (MulDivUpSafe x y d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def mulDivDownFunction : FunctionDecl := contract.functions[7]!
def mulDivUpFunction : FunctionDecl := contract.functions[8]!

def mulDivProductExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "x") (.var "y"))

def mulDivPredExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .sub (.var "d") (.intLit 1))

def mulDivSumExpr : Expr :=
  .inRange (.uint ⟨256, by decide⟩) (.binary .add mulDivProductExpr mulDivPredExpr)

def mulDivDownExpr : Expr := .binary .div mulDivProductExpr (.var "d")
def mulDivUpExpr : Expr := .binary .div mulDivSumExpr (.var "d")

theorem mulDivDown_body : mulDivDownFunction.body = [.return [mulDivDownExpr]] := rfl
theorem mulDivUp_body : mulDivUpFunction.body = [.return [mulDivUpExpr]] := rfl

theorem evalMulDivProduct {cfg : Config} {frame : Frame} {evm : EVM.State} {x y : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hfit : x.toNat * y.toNat < UInt256.size) :
    evalExpr? cfg frame evm mulDivProductExpr = .ok (.int (UInt256.mul x y).toNat) :=
  checkedMulSourceOk (by simp only [evalExpr?, hx, EvalResult.ofOption, Int.ofNat_eq_natCast])
    (by simp only [evalExpr?, hy, EvalResult.ofOption, Int.ofNat_eq_natCast]) hfit

theorem evalMulDivProduct_overflow {cfg : Config} {frame : Frame} {evm : EVM.State} {x y : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    evalExpr? cfg frame evm mulDivProductExpr = .revert :=
  checkedMulSourceOverflow (by simp only [evalExpr?, hx, EvalResult.ofOption, Int.ofNat_eq_natCast])
    (by simp only [evalExpr?, hy, EvalResult.ofOption, Int.ofNat_eq_natCast]) hover

theorem evalMulDivPred {cfg : Config} {frame : Frame} {evm : EVM.State} {d : UInt256}
    (hd : frame.locals.get? "d" = some (.int d.toNat)) (hpos : 0 < d.toNat) :
    evalExpr? cfg frame evm mulDivPredExpr = .ok (.int (UInt256.sub d ⟨1⟩).toNat) :=
  evalExpr_uint256_sub
    (by simp only [evalExpr?, hd, EvalResult.ofOption, uint256Value, Int.ofNat_eq_natCast])
    (by norm_num [evalExpr?, uint256Value, pure, UInt256.toNat, UInt256.size]) hpos

theorem evalMulDivUp {cfg : Config} {frame : Frame} {evm : EVM.State} {x y d : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hd : frame.locals.get? "d" = some (.int d.toNat)) (hsafe : MulDivUpSafe x y d) :
    evalExpr? cfg frame evm mulDivUpExpr = .ok (.int (mulDivUp x y d).toNat) := by
  apply divSourceOk (checkedAddSourceOk (evalMulDivProduct hx hy hsafe.1)
    (evalMulDivPred hd hsafe.2.1) hsafe.2.2)
    (by simp only [evalExpr?, hd, EvalResult.ofOption, Int.ofNat_eq_natCast])
  intro hz
  have hp := hsafe.2.1
  rw [hz] at hp
  contradiction

theorem evalMulDivDown {cfg : Config} {frame : Frame} {evm : EVM.State} {x y d : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat))
    (hd : frame.locals.get? "d" = some (.int d.toNat))
    (hfit : x.toNat * y.toNat < UInt256.size) (hnz : d ≠ ⟨0⟩) :
    evalExpr? cfg frame evm mulDivDownExpr = .ok (.int (mulDivDown x y d).toNat) :=
  divSourceOk (evalMulDivProduct hx hy hfit)
    (by simp only [evalExpr?, hd, EvalResult.ofOption, Int.ofNat_eq_natCast]) hnz

end Benchmarks.Midnight
