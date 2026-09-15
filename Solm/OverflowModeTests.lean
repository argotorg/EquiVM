import Solm.Notation
import Solm.Semantics

/-! Regression tests for lexical overflow mode. Test the generated expressions, not just the
arithmetic evaluator in isolation. `unchecked(e)` is a specification-only expression form. -/

open ABI

namespace Solm.OverflowModeTests

private def surface : ContractDecl := solidity% contract OverflowModeTest {
  function named(uint256 x, uint256 y, uint256 wordModulus) external returns (uint256) {
    return x * y % wordModulus;
  }
  function renamed(uint256 x, uint256 y, uint256 denominator) external returns (uint256) {
    return x * y % denominator;
  }
  function literalDivisor(uint8 x, uint8 y) external returns (uint8) {
    return (x + y) % #(2 ^ 8);
  }
  function expression(uint8 x, uint8 y) external returns (uint8) {
    return unchecked(x + y);
  }
  function nested(uint8 x, uint8 y) external returns (uint8) {
    return unchecked((x + y) * y);
  }
  function narrowScope(uint8 x, uint8 y) external returns (uint8) {
    return unchecked(x + y) + y;
  }
  function blockScope(uint8 x, uint8 y) external returns (uint8) {
    unchecked {
      x += y;
      if (x > 0) { x *= y; }
    }
    return x + y;
  }
  function checkedCallee(uint8 x, uint8 y) internal returns (uint8) {
    return x + y;
  }
  function callScope(uint8 x, uint8 y) external returns (uint8) {
    unchecked {
      var result = checkedCallee(x, y);
      return result;
    }
  }
  function division(uint8 x, uint8 y) external returns (uint8) {
    return unchecked(x / y);
  }
  function remainder(uint8 x, uint8 y) external returns (uint8) {
    return unchecked(x % y);
  }
  function checkedAssertion(uint8 x, uint8 y) external returns (bool) {
    return unchecked((x + y) as uint8);
  }
  function typedExpression(uint8 x, uint8 y) external returns (uint8) {
    uint8 z = unchecked(x + y);
    return z;
  }
}

private def cfg : Config := {
  storage := { layout := fun _ _ => none }
  externalABI := { encode? := fun _ _ => none, decode? := fun _ _ => none }
  selfDeployment := fun _ _ => none
}

private def evaluateReturn (index : Nat) (x y : Int) : EvalResult Value := do
  let .return [expr] := surface.transitions[index]!.body[1]!
    | .error .typeError
  let locals := (∅ : Store).insert "x" (.int x) |>.insert "y" (.int y)
    |>.insert "wordModulus" (.int 3) |>.insert "denominator" (.int 3)
  evalExpr? cfg { contract := surface, locals } default expr

-- Identifier spelling and literal divisor spelling never disable overflow checks.
#guard evaluateReturn 0 (2 ^ 256 - 1) 2 = .revert
#guard evaluateReturn 1 (2 ^ 256 - 1) 2 = .revert
#guard evaluateReturn 0 7 2 = .ok (.int 2)
#guard evaluateReturn 1 7 2 = .ok (.int 2)
#guard evaluateReturn 2 255 1 = .revert
#guard evaluateReturn 3 255 1 = .ok (.int 0)
#guard evaluateReturn 4 255 2 = .ok (.int 2)
#guard evaluateReturn 5 254 1 = .revert

-- The block covers compound assignments and branches, but not following statements.
example : surface.transitions[6]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .assign .localVar { base := "x" }
        (.binary (.add (.uint ⟨8, by decide⟩) .wrapping) (.var "x") (.var "y")),
      .ite (.binary .gt (.var "x") (.intLit 0))
        [.assign .localVar { base := "x" }
          (.binary (.mul (.uint ⟨8, by decide⟩) .wrapping) (.var "x") (.var "y"))] [],
      .return [.binary (.add (.uint ⟨8, by decide⟩) .checked) (.var "x") (.var "y")] ] := rfl

-- The callee has its own lexical context, regardless of the call site's mode.
example : surface.functions[0]!.body =
    [.return [.binary (.add (.uint ⟨8, by decide⟩) .checked) (.var "x") (.var "y")]] := rfl
example : surface.transitions[7]!.body[1]! =
    .internalCall "checkedCallee" [.var "x", .var "y"] "result" := rfl

#guard evaluateReturn 8 7 0 = .revert
#guard evaluateReturn 9 7 0 = .revert
#guard evaluateReturn 8 7 2 = .ok (.int 3)
#guard evaluateReturn 9 7 2 = .ok (.int 1)
#guard evaluateReturn 10 255 1 = .revert

example : surface.transitions[11]!.body[1]! =
    .letDecl "z" (some (.elem (.int (.uint ⟨8, by decide⟩))))
      (.binary (.add (.uint ⟨8, by decide⟩) .wrapping) (.var "x") (.var "y")) := rfl

end Solm.OverflowModeTests
