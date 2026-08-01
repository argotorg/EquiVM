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

/-! Arithmetic stays unbounded, even for explicitly narrowed operands.
Only an explicit cast or range assertion handles overflow. -/

def narrowSum : Expr :=
  .binary .add (.cast (.intLit 250) uint8Storage) (.cast (.intLit 10) uint8Storage)

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm narrowSum = .ok (.int 260) := by
  simp [narrowSum, evalExpr?, uint8Storage, castValue?, normalizeInt, EVM.twoPow,
    evalBinaryOp?, EvalResult.bind, bind, pure, EvalResult.ofOption]

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm (.cast narrowSum uint8Storage) = .ok (.int 4) := by
  simp [narrowSum, evalExpr?, uint8Storage, castValue?, normalizeInt, EVM.twoPow,
    evalBinaryOp?, EvalResult.bind, bind, pure, EvalResult.ofOption]

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨8, by decide⟩) narrowSum) = .revert := by
  simp [narrowSum, evalExpr?, uint8Storage, castValue?, normalizeInt, EVM.twoPow,
    evalBinaryOp?, EvalResult.bind, bind, pure, EvalResult.ofOption]

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    ExecStmt cfg solm evm
      (.letDecl "sum" (some (.elem (.int (.uint ⟨8, by decide⟩)))) narrowSum)
      (.ok { solm with locals := solm.locals.insert "sum" (.int 260) } evm) := by
  apply ExecStmt.letDecl
  simp [narrowSum, evalExpr?, uint8Storage, castValue?, normalizeInt, EVM.twoPow,
    evalBinaryOp?, EvalResult.bind, bind, pure, EvalResult.ofOption]

#guard evalBinaryOp? .sub (.int 0) (.int 1) = .ok (.int (-1))
#guard evalBinaryOp? .mul (.int 128) (.int 2) = .ok (.int 256)
#guard evalBinaryOp? .add (.int (EVM.wordModulus - 1)) (.int 1) =
  .ok (.int EVM.wordModulus)

-- At every signed minimum, mathematical negation leaves the declared range;
-- an explicit cast wraps the result back to the signed minimum.
#guard integerWidths.all fun bits =>
  let half : Int := EVM.twoPow (bits.val - 1)
  decide (evalUnaryOp? .neg (.int (-half)) = some (.int half) ∧
    ((evalUnaryOp? .neg (.int (-half))).bind fun value =>
      castValue? value (.elem (.int (.sint bits)))) = some (.int (-half)))

-- Cat permits the input 2^255: the outer cast is necessary at that equality.
example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm
      (.unary .neg (.cast (.intLit (EVM.twoPow 255)) int256Storage)) =
      .ok (.int (EVM.twoPow 255)) := by
  simp [evalExpr?, int256Storage, castValue?, normalizeInt, evalUnaryOp?,
    EvalResult.bind, bind, pure, EvalResult.ofOption]
  native_decide

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    evalExpr? cfg solm evm
      (.cast (.unary .neg (.cast (.intLit (EVM.twoPow 255)) int256Storage)) int256Storage) =
      .ok (.int (-Int.ofNat (EVM.twoPow 255))) := by
  simp [evalExpr?, int256Storage, castValue?, normalizeInt, evalUnaryOp?,
    EvalResult.bind, bind, pure, EvalResult.ofOption]
  native_decide

def arithmeticContract : ContractDecl := solidity% contract ExplicitOverflow {
  function unbounded(uint8 a, uint8 b) external returns (uint256) {
    uint8 sum = a + b;
    return sum;
  }
  function wrap(uint8 a, uint8 b) external returns (uint8) {
    return uint8(a + b);
  }
  function check(uint8 a, uint8 b) external returns (uint8) {
    return (a + b) as uint8;
  }
  function wrapNegation(uint256 value) external returns (int256) {
    return int256(-int256(value));
  }
}

example : arithmeticContract.transitions[0]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "sum" (some (.elem (.int (.uint ⟨8, by decide⟩))))
        (.binary .add (.var "a") (.var "b")),
      .return [.var "sum"] ] := by rfl

example : arithmeticContract.transitions[1]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.cast (.binary .add (.var "a") (.var "b")) uint8Storage] ] := by rfl

example : arithmeticContract.transitions[2]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.inRange (.uint ⟨8, by decide⟩) (.binary .add (.var "a") (.var "b"))] ] := by rfl

example : arithmeticContract.transitions[3]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return [.cast (.unary .neg (.cast (.var "value") int256Storage)) int256Storage] ] := by rfl

end Solm.CastTests
