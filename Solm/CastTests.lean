import ABI.Decode
import ABI.Encode
import Solm.Notation
import Solm.Semantics

open ABI

namespace Solm.CastTests

def uint8Storage : StorageType := .elem (.int (.uint ⟨8, by decide⟩))
def int8Storage : StorageType := .elem (.int (.sint ⟨8, by decide⟩))
def uint256Storage : StorageType := .elem (.int (.uint ⟨256, by decide⟩))
def int256Storage : StorageType := .elem (.int (.sint ⟨256, by decide⟩))

/-! Explicit casts truncate; ABI encoding and modern decoding validate instead.
Exercise all Solidity integer widths with independently stated boundary results. -/

private def integerWidths : List BitWidth :=
  List.ofFn fun index : Fin 32 => ⟨8 * (index.val + 1), by omega⟩

private def castBoundaryCases (bits : BitWidth) : List (Int × Int × Int) :=
  let modulus : Int := EVM.twoPow bits.val
  let half : Int := EVM.twoPow (bits.val - 1)
  [(-modulus - 1, modulus - 1, -1), (-modulus, 0, 0),
   (-half - 1, half - 1, half - 1), (-half, half, -half),
   (-1, modulus - 1, -1), (0, 0, 0), (1, 1, 1),
   (half - 1, half - 1, half - 1), (half, half, -half),
   (modulus - 1, modulus - 1, -1), (modulus, 0, 0), (modulus + 1, 1, 1)]

#guard integerWidths.all fun bits => (castBoundaryCases bits).all fun (input, unsigned, signed) =>
  decide (castValue? (.int input) (.elem (.int (.uint bits))) = some (.int unsigned) ∧
    castValue? (.int input) (.elem (.int (.sint bits))) = some (.int signed) ∧
    wordToElem (.int (.uint bits)) (EVM.wordOfInt input) = .int unsigned ∧
    wordToElem (.int (.sint bits)) (EVM.wordOfInt input) = .int signed)

#guard integerWidths.all fun bits => (castBoundaryCases bits).all fun (input, unsigned, signed) =>
  decide (decodeABIWord? (.elem (.int (.uint bits))) (EVM.wordOfInt input) .legacySolc05 =
      some (.int unsigned) ∧
    decodeABIWord? (.elem (.int (.sint bits))) (EVM.wordOfInt input) .legacySolc05 =
      some (.int signed))

#guard integerWidths.all fun bits => (castBoundaryCases bits).all fun (_, unsigned, signed) =>
  decide (encodeABIWord? (.elem (.int (.uint bits))) (.int unsigned) =
      some (EVM.wordOfInt unsigned) ∧
    encodeABIWord? (.elem (.int (.sint bits))) (.int signed) =
      some (EVM.wordOfInt signed)) &&
  [DecodeMode.modern, .vyper].all fun mode =>
    decide (decodeABIWord? (.elem (.int (.uint bits))) (EVM.wordOfInt unsigned) mode =
        some (.int unsigned) ∧
      decodeABIWord? (.elem (.int (.sint bits))) (EVM.wordOfInt signed) mode =
        some (.int signed))

#guard integerWidths.all fun bits =>
  let modulus : Int := EVM.twoPow bits.val
  let half : Int := EVM.twoPow (bits.val - 1)
  decide (encodeABIWord? (.elem (.int (.uint bits))) (.int (-1)) = none ∧
    encodeABIWord? (.elem (.int (.uint bits))) (.int modulus) = none ∧
    encodeABIWord? (.elem (.int (.sint bits))) (.int (-half - 1)) = none ∧
    encodeABIWord? (.elem (.int (.sint bits))) (.int half) = none) &&
  (bits.val == 256 || [DecodeMode.modern, .vyper].all fun mode =>
    decide (decodeABIWord? (.elem (.int (.uint bits))) (EVM.wordOfInt modulus) mode = none ∧
      decodeABIWord? (.elem (.int (.sint bits))) (EVM.wordOfInt half) mode = none))

def unsignedNarrowExpr : Expr :=
  .cast (.cast (.intLit 511) uint8Storage) uint256Storage

def signedNarrowExpr : Expr :=
  .cast (.cast (.intLit 255) int8Storage) int256Storage

def signedMinNegExpr : Expr :=
  .unary (.neg (.sint ⟨256, by decide⟩))
    (.cast (.intLit (EVM.twoPow 255)) int256Storage)

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm unsignedNarrowExpr = .ok (.int 255) := by
  simp [unsignedNarrowExpr, evalExpr?, uint8Storage, uint256Storage, castValue?,
    EvalResult.bind, bind, pure, EvalResult.ofOption, normalizeInt]
  native_decide

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm signedNarrowExpr = .ok (.int (-1)) := by
  simp [signedNarrowExpr, evalExpr?, int8Storage, int256Storage, castValue?,
    EvalResult.bind, bind, pure, EvalResult.ofOption, normalizeInt]
  native_decide

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm signedMinNegExpr = .ok (.int (-(EVM.twoPow 255 : Int))) := by
  simp [signedMinNegExpr, evalExpr?, int256Storage, castValue?, evalUnaryOp?,
    EvalResult.bind, bind, pure, EvalResult.ofOption, normalizeInt]
  native_decide

def surfaceContract : ContractDecl := solidity% contract CastTest {
  function narrow(uint256 value) external returns (uint256) {
    return uint256(uint8(value));
  }
}

example : surfaceContract.transitions[0]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.cast (.cast (.var "value") uint8Storage) uint256Storage] ] := by
  rfl

-- Widening a negative signed value before changing signedness differs from
-- changing signedness at the narrow width before widening.
example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm
      (.cast (.cast (.cast (.intLit 255) int8Storage) int256Storage) uint256Storage) =
      .ok (.int (EVM.wordModulus - 1)) := by
  simp [evalExpr?, int8Storage, int256Storage, uint256Storage, castValue?,
    EvalResult.bind, bind, pure, EvalResult.ofOption, normalizeInt]
  native_decide

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm
      (.cast (.cast (.cast (.intLit 255) int8Storage) uint8Storage) uint256Storage) =
      .ok (.int 255) := by
  simp [evalExpr?, int8Storage, uint8Storage, uint256Storage, castValue?,
    EvalResult.bind, bind, pure, EvalResult.ofOption, normalizeInt]
  native_decide

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨8, by decide⟩) (.intLit 256)) = .revert := by
  simp [evalExpr?, pure, bind, EvalResult.bind]

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm (.cast (.boolLit true) uint8Storage) = .error .typeError := by
  simp [evalExpr?, uint8Storage, castValue?, pure, bind, EvalResult.bind, EvalResult.ofOption]

def surfaceNegContract : ContractDecl := solidity% contract NegTest {
  function neg(uint256 value) external returns (int256) {
    return -int256(value);
  }
}

example : surfaceNegContract.transitions[0]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.unary (.neg (.sint ⟨256, by decide⟩)) (.cast (.var "value") int256Storage)] ] := by
  rfl

/-! `UnaryOp.neg` models wrapping (legacy/unchecked) negation, not modern
Solidity's checked-overflow mode. In particular, every signed minimum is
fixed by negation; do not exclude that boundary from the contract proofs. -/

#guard integerWidths.all fun bits =>
  let half : Int := EVM.twoPow (bits.val - 1)
  [(-half, -half), (-half + 1, half - 1), (-1, 1), (0, 0), (1, -1),
   (half - 1, 1 - half)].all fun (input, expected) =>
    decide (evalUnaryOp? (.neg (.sint bits)) (.int input) = some (.int expected))

#guard integerWidths.all fun bits => (castBoundaryCases bits).all fun (_, _, signed) =>
  decide (((evalUnaryOp? (.neg (.sint bits)) (.int signed)).bind
    (evalUnaryOp? (.neg (.sint bits)))) = some (.int signed))

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm
      (.unary (.neg (.sint ⟨8, by decide⟩)) (.cast (.intLit 128) int8Storage)) =
      .ok (.int (-128)) := by
  simp [evalExpr?, int8Storage, castValue?, evalUnaryOp?,
    EvalResult.bind, bind, pure, EvalResult.ofOption, normalizeInt]
  native_decide

-- An operand range assertion must still revert instead of cleaning the input.
example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm
      (.unary (.neg (.sint ⟨8, by decide⟩))
        (.inRange (.sint ⟨8, by decide⟩) (.intLit 128))) = .revert := by
  simp [evalExpr?, EvalResult.bind, bind, pure]

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm
      (.unary (.neg (.sint ⟨8, by decide⟩)) (.boolLit true)) = .error .typeError := by
  simp [evalExpr?, evalUnaryOp?, EvalResult.bind, bind, pure, EvalResult.ofOption]

def surfaceNegVariants : ContractDecl := solidity% contract NegVariants {
  function parenthesized(int256 value) external returns (int8) {
    return -(int8(value));
  }
  function rangeChecked(int256 value) external returns (int8) {
    return -(value as int8);
  }
}

example : surfaceNegVariants.transitions[0]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.unary (.neg (.sint ⟨8, by decide⟩)) (.cast (.var "value") int8Storage)] ] := by
  rfl

example : surfaceNegVariants.transitions[1]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.unary (.neg (.sint ⟨8, by decide⟩))
        (.inRange (.sint ⟨8, by decide⟩) (.var "value"))] ] := by
  rfl

/-- error: solm: unary '-' requires an explicitly typed operand, e.g. '-int256(x)' -/
#guard_msgs in
def surfaceNegUntyped : ContractDecl := solidity% contract UntypedNeg {
  function neg(int8 value) external returns (int8) {
    return -value;
  }
}

end Solm.CastTests
