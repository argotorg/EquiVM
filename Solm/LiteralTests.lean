import Solm.Notation
import Solm.Semantics

/-! Regression tests for exact literal arithmetic and Solidity operator-specific typing.
Positive and negative cases are checked against solc 0.8.35 and the Solidity type rules.
The evaluator checks below use the actual surface-generated expressions. -/

open ABI

namespace Solm.LiteralTests

private def surface : ContractDecl := solidity% contract LiteralTest {
  function cancel() external returns (uint8) {
    uint8 z = (255 + 1) - 1;
    return z;
  }
  function huge() external returns (uint8) {
    return (2 ** 800 + 1) - 2 ** 800;
  }
  function rational() external returns (uint8) {
    return (5 / 2) * 2;
  }
  function negativeFraction() external returns (int8) {
    return (((-5) / 2) % 2) * 2;
  }
  function promotion(uint32 x) external returns (uint256) {
    return x + 4294967296;
  }
  function shift(uint8 x, uint256 s) external returns (uint256) {
    return x << s;
  }
  function power(uint8 x, uint256 s) external returns (uint256) {
    return x ** s;
  }
  function signedShift(int8 x, uint256 s) external returns (int256) {
    return x >> s;
  }
  function signedPower(int8 x, uint256 s) external returns (int256) {
    return x ** s;
  }
  function literalBase(uint8 s) external returns (uint256) {
    return 1 << s;
  }
  function signedLiteralBase(uint8 s) external returns (int256) {
    return (-1) << s;
  }
  function negativePromotion(int8 x) external returns (int16) {
    return x + (-129);
  }
  function narrower(uint8 x) external returns (uint256) {
    return (x + 1) + uint256(1);
  }
  function ternary() external returns (uint8) {
    return 255 + (true ? 1 : 0);
  }
  function maxTyped(uint8 x) external returns (uint256) {
    return x + type(uint16).max;
  }
  function exponentContext(uint8 x, uint8 s) external returns (uint256) {
    uint256 z = x ** (s + 1);
    return z;
  }
  function rationalComparison() external returns (bool) {
    return 5 / 2 < 3;
  }
  function signedBitwise() external returns (int256) {
    return (~0 & (-16)) | ((-3) ^ 7);
  }
  function literalShifts() external returns (int256) {
    return ((-3) >> 1) + (1 << 9);
  }
  function counterContext(uint8 x, uint256 s) external returns (uint8) {
    return (x ** (s + 1)) as uint8;
  }
  function wrappingPower(uint8 x, uint256 s) external returns (uint8) {
    return unchecked(x ** s);
  }
  function literalPower(uint8 s) external returns (uint256) {
    return 2 ** s;
  }
  function rationalPower() external returns (uint8) {
    return 2 ** (-1) * 2;
  }
}


example : surface.transitions[0]!.body[1]! =
    .letDecl "z" (some (.elem (.int (.uint ⟨8, by decide⟩)))) (.intLit 255) := rfl
example : surface.transitions[1]!.body[1]! = .return [.intLit 1] := rfl
example : surface.transitions[2]!.body[1]! = .return [.intLit 5] := rfl
example : surface.transitions[3]!.body[1]! = .return [.intLit (-1)] := rfl
example : surface.transitions[4]!.body[1]! =
    .return [.binary (.add (.uint ⟨40, by decide⟩) .checked) (.var "x") (.intLit 4294967296)] := rfl
example : surface.transitions[5]!.body[1]! =
    .return [.binary (.shl (.uint ⟨8, by decide⟩)) (.var "x") (.var "s")] := rfl
example : surface.transitions[6]!.body[1]! =
    .return [.binary (.exp (.uint ⟨8, by decide⟩) .checked) (.var "x") (.var "s")] := rfl
example : surface.transitions[7]!.body[1]! =
    .return [.binary (.shr (.sint ⟨8, by decide⟩)) (.var "x") (.var "s")] := rfl
example : surface.transitions[8]!.body[1]! =
    .return [.binary (.exp (.sint ⟨8, by decide⟩) .checked) (.var "x") (.var "s")] := rfl
example : surface.transitions[9]!.body[1]! =
    .return [.binary (.shl (.uint ⟨256, by decide⟩)) (.intLit 1) (.var "s")] := rfl
example : surface.transitions[10]!.body[1]! =
    .return [.binary (.shl (.sint ⟨256, by decide⟩)) (.intLit (-1)) (.var "s")] := rfl

private def cfg : Config := {
  storage := { layout := fun _ _ => none }
  externalABI := { encode? := fun _ _ => none, decode? := fun _ _ => none }
  selfDeployment := fun _ _ => none
}

private def evaluate (index : Nat) (x s : Int) : EvalResult Value := do
  let expr ← match surface.transitions[index]!.body[1]! with
    | .return [expr] | .letDecl _ _ expr => pure expr
    | _ => .error .typeError
  let locals := (∅ : Store).insert "x" (.int x) |>.insert "s" (.int s)
  evalExpr? cfg { contract := surface, locals } default expr

#guard evaluate 4 0 0 = .ok (.int (2 ^ 32))
#guard evaluate 5 128 1 = .ok (.int 0)
#guard evaluate 5 128 (2 ^ 256 - 1) = .ok (.int 0)
#guard evaluate 6 16 2 = .revert
#guard evaluate 7 (-3) 1 = .ok (.int (-2))
#guard evaluate 8 (-2) 3 = .ok (.int (-8))
#guard evaluate 9 0 8 = .ok (.int 256)
#guard evaluate 10 0 1 = .ok (.int (-2))
#guard evaluate 11 (-128) 0 = .ok (.int (-257))
#guard evaluate 12 255 0 = .revert
#guard evaluate 13 0 0 = .revert
#guard evaluate 14 255 0 = .revert
#guard evaluate 15 1 255 = .revert
#guard evaluate 16 0 0 = .ok (.bool true)
#guard evaluate 17 0 0 = .ok (.int (-6))
#guard evaluate 18 0 0 = .ok (.int 510)
#guard evaluate 19 1 255 = .ok (.int 1)
#guard evaluate 20 16 2 = .ok (.int 0)
#guard evaluate 21 0 8 = .ok (.int 256)
#guard evaluate 22 0 0 = .ok (.int 1)

/-- error: solm: shift amount or exponent must be an unsigned integer -/
#guard_msgs in
private def signedExponent : ContractDecl := solidity% contract Rejected {
  function f(uint8 x, int8 s) external returns (uint8) { return x ** s; }
}

/-- error: solm: shift amount or exponent must be an unsigned integer -/
#guard_msgs in
private def signedAmount : ContractDecl := solidity% contract Rejected {
  function f(int8 x, int8 s) external returns (int8) { return x >> s; }
}

/-- error: solm: non-integral literal '5/2' cannot be used as an integer -/
#guard_msgs in
private def mixedFraction : ContractDecl := solidity% contract Rejected {
  function f(uint8 x) external returns (uint8) { return x + 5 / 2; }
}

/-- error: solm: binary operands mix signed and unsigned types 'uint8' and 'int8' -/
#guard_msgs in
private def badPromotion : ContractDecl := solidity% contract Rejected {
  function f(int8 x) external returns (int16) { return x + 128; }
}

/-- error: solm: shift amount or exponent must be an unsigned integer -/
#guard_msgs in
private def negativeAmount : ContractDecl := solidity% contract Rejected {
  function f(uint8 x) external returns (uint8) { return x << (-1); }
}

/-- error: solm: non-integral literal '1/2' cannot be used as an integer -/
#guard_msgs in
private def fractionalExponent : ContractDecl := solidity% contract Rejected {
  function f(uint8 x) external returns (uint8) { return x ** (1 / 2); }
}

end Solm.LiteralTests
