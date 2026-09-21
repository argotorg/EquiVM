import Solm.Notation
import Solm.Semantics

open ABI

namespace Solm.IntegerTests

/-! Signed quotient/remainder are explicit, width-free operations. Mathematical
division/modulo and overflow handling retain their separate meanings. -/

private def signedCases : List (Int × Int × Int × Int) :=
  [(-5, 3, -1, -2), (5, -3, -1, 2), (-5, -3, 1, -2), (5, 3, 1, 2),
   (-2, 3, 0, -2), (2, -3, 0, 2), (-6, 3, -2, 0), (0, -3, 0, 0),
   (2 ^ 300 + 1, 2, 2 ^ 299, 1)]

#guard signedCases.all fun (x, y, quotient, remainder) =>
  decide (evalBinaryOp? .sdiv (.int x) (.int y) = .ok (.int quotient) ∧
    evalBinaryOp? .srem (.int x) (.int y) = .ok (.int remainder) ∧
    x = quotient * y + remainder)

#guard evalBinaryOp? .div (.int (-5)) (.int 3) = .ok (.int (-2))
#guard evalBinaryOp? .mod (.int (-5)) (.int 3) = .ok (.int 1)
#guard evalBinaryOp? .mod (.int (-1)) (.int 256) = .ok (.int 255)

#guard [BinaryOp.div, .mod, .sdiv, .srem].all fun op =>
  decide (evalBinaryOp? op (.int 1) (.int 0) = .revert ∧
    evalBinaryOp? op (.bool true) (.int 1) = .error .typeError)

-- The signed minimum divided by -1 is the positive mathematical result.
-- Neither truncating division nor remainder performs an implicit overflow check.
#guard (List.range 32).all fun index =>
  let half : Int := 2 ^ (8 * (index + 1) - 1)
  decide (evalBinaryOp? .sdiv (.int (-half)) (.int (-1)) = .ok (.int half) ∧
    evalBinaryOp? .srem (.int (-half)) (.int (-1)) = .ok (.int 0))

def signedOverflow : Expr := .binary .sdiv (.intLit (-128)) (.intLit (-1))

example (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg frame evm signedOverflow = .ok (.int 128) := by
  simp [signedOverflow, evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure]

example (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg frame evm (.inRange (.sint ⟨8, by decide⟩) signedOverflow) = .revert := by
  simp [signedOverflow, evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure]

example (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg frame evm
      (.cast signedOverflow (.elem (.int (.sint ⟨8, by decide⟩)))) = .ok (.int (-128)) := by
  simp [signedOverflow, evalExpr?, evalBinaryOp?, castValue?, normalizeInt, EVM.twoPow,
    EvalResult.bind, bind, pure, EvalResult.ofOption]

def signedContract : ContractDecl := solidity% contract SignedOperations {
  function quotients(int256 x, int256 y) external returns (int256, int256, int256, int256) {
    return x / y, x % y, sdiv(x, y), srem(x, y);
  }
}

example : signedContract.transitions[0]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.binary .div (.var "x") (.var "y"),
        .binary .mod (.var "x") (.var "y"),
        .binary .sdiv (.var "x") (.var "y"),
        .binary .srem (.var "x") (.var "y")] ] := by rfl

end Solm.IntegerTests
