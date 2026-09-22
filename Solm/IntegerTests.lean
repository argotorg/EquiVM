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

private def integerWidths : List BitWidth :=
  List.ofFn fun index : Fin 32 => ⟨8 * (index.val + 1), by omega⟩

private def bitCases (bits : BitWidth) : List (BinaryOp × Int × Int × Int) :=
  let modulus : Int := 2 ^ bits.val
  let half : Int := 2 ^ (bits.val - 1)
  let u := IntType.uint bits
  let s := IntType.sint bits
  [(.bitAnd u, -1, modulus + 5, 5),
   (.bitAnd s, -1, half, -half),
   (.bitOr u, half, half - 1, modulus - 1),
   (.bitOr s, half, half - 1, -1),
   (.bitXor u, -1, half - 1, half),
   (.bitXor s, -1, half - 1, -half),
   (.shl u, half, 1, 0), (.shl s, half - 1, 1, -2),
   (.shl u, modulus + 1, 0, 1), (.shl s, half, 0, -half),
   (.shr u, -1, 1, half - 1), (.shr s, -3, 1, -2),
   (.shr s, half, 1, -(half / 2)),
   (.shl u, 1, bits.val - 1, half), (.shl s, 1, bits.val - 1, -half),
   (.shr u, modulus - 1, bits.val - 1, 1),
   (.shr s, -half, bits.val - 1, -1)]

#guard integerWidths.all fun bits => (bitCases bits).all fun (op, x, y, result) =>
  decide (evalBinaryOp? op (.int x) (.int y) = .ok (.int result))

#guard integerWidths.all fun bits =>
  let modulus : Int := 2 ^ bits.val
  let half : Int := 2 ^ (bits.val - 1)
  decide (evalUnaryOp? (.bitNot (.uint bits)) (.int 0) = some (.int (modulus - 1)) ∧
    evalUnaryOp? (.bitNot (.uint bits)) (.int (-1)) = some (.int 0) ∧
    evalUnaryOp? (.bitNot (.sint bits)) (.int 0) = some (.int (-1)) ∧
    evalUnaryOp? (.bitNot (.sint bits)) (.int (half - 1)) = some (.int (-half)))

#guard integerWidths.all fun bits =>
  [Int.ofNat bits.val, Int.ofNat bits.val + 1, 2 ^ 300].all fun count =>
    decide (evalBinaryOp? (.shl (.uint bits)) (.int 1) (.int count) = .ok (.int 0) ∧
      evalBinaryOp? (.shl (.sint bits)) (.int (-1)) (.int count) = .ok (.int 0) ∧
      evalBinaryOp? (.shr (.uint bits)) (.int (-1)) (.int count) = .ok (.int 0) ∧
      evalBinaryOp? (.shr (.sint bits)) (.int (-1)) (.int count) = .ok (.int (-1)) ∧
      evalBinaryOp? (.shr (.sint bits)) (.int 1) (.int count) = .ok (.int 0))

#guard integerWidths.all fun bits => [IntType.uint bits, .sint bits].all fun ty =>
  decide (evalBinaryOp? (.shl ty) (.int 1) (.int (-1)) = .error .typeError ∧
    evalBinaryOp? (.shr ty) (.int 1) (.int (-1)) = .error .typeError ∧
    evalBinaryOp? (.bitAnd ty) (.bool true) (.int 1) = .error .typeError ∧
    evalUnaryOp? (.bitNot ty) (.bool true) = none)

-- Fixed bytes retain their own width and bytewise behavior.
private def byte (n : UInt8) : Value := .fixedBytes ⟨0, by decide⟩ [n]

#guard evalUnaryOp? .fixedBitNot (byte 0xF0) = some (byte 0x0F)
#guard evalBinaryOp? .fixedBitAnd (byte 0xF0) (byte 0x3C) = .ok (byte 0x30)
#guard evalBinaryOp? .fixedBitOr (byte 0xF0) (byte 0x3C) = .ok (byte 0xFC)
#guard evalBinaryOp? .fixedBitXor (byte 0xF0) (byte 0x3C) = .ok (byte 0xCC)
#guard evalBinaryOp? .fixedShl (byte 0x80) (.int 1) = .ok (byte 0)
#guard evalBinaryOp? .fixedShr (byte 0x80) (.int 7) = .ok (byte 1)
#guard evalBinaryOp? .fixedBitAnd (byte 0) (.fixedBytes ⟨1, by decide⟩ [0, 0]) =
  .error .typeError
#guard evalBinaryOp? .fixedBitAnd (.int 1) (.int 1) = .error .typeError

-- Explicit bit widths do not bound surrounding arithmetic or change modulo.
#guard evalBinaryOp? .exp (.int 2) (.int 300) = .ok (.int (2 ^ 300))
#guard evalUnaryOp? .neg (.int (-128)) = some (.int 128)

def bitContract : ContractDecl := solidity% contract BitOperations {
  function bits(uint8 x, uint8 y, uint256 n) external
      returns (uint8, uint8, uint8, uint8, uint8, int8) {
    return x &[uint8] y, x |[uint8] y, x ^[uint8] y, ~[uint8] x,
      x <<[uint8] n, x >>[int8] n;
  }
  function fixedBits(bytes1 x, bytes1 y) external returns (bytes1, bytes1, bytes1) {
    return x & y, ~x, x >> 1;
  }
}

example : bitContract.transitions[0]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.binary (.bitAnd (.uint ⟨8, by decide⟩)) (.var "x") (.var "y"),
        .binary (.bitOr (.uint ⟨8, by decide⟩)) (.var "x") (.var "y"),
        .binary (.bitXor (.uint ⟨8, by decide⟩)) (.var "x") (.var "y"),
        .unary (.bitNot (.uint ⟨8, by decide⟩)) (.var "x"),
        .binary (.shl (.uint ⟨8, by decide⟩)) (.var "x") (.var "n"),
        .binary (.shr (.sint ⟨8, by decide⟩)) (.var "x") (.var "n")] ] := by rfl

example : bitContract.transitions[1]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.binary .fixedBitAnd (.var "x") (.var "y"),
        .unary .fixedBitNot (.var "x"),
        .binary .fixedShr (.var "x") (.intLit 1)] ] := by rfl

example (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg frame evm
      (.binary .add
        (.binary (.shl (.uint ⟨8, by decide⟩)) (.intLit 127) (.intLit 1))
        (.intLit 2)) = .ok (.int 256) := by
  simp [evalExpr?, evalBinaryOp?, IntType.bitWidth, normalizeInt, EVM.twoPow,
    EvalResult.bind, bind, pure]

end Solm.IntegerTests
