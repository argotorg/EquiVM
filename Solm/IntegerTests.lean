import Solm.Notation
import Solm.Semantics
import Solm.OverflowModeTests
import Solm.LiteralTests

open ABI

namespace Solm.IntegerTests

/-! Boundary results across all Solidity integer widths. Expected results are stated directly,
independently of `normalizeInt` and `evalIntArithResult`. -/

private def integerWidths : List BitWidth :=
  List.ofFn fun index : Fin 32 => ⟨8 * (index.val + 1), by omega⟩

private def arithmeticBoundaryCases (bits : BitWidth) : List (BinaryOp × Int × Int × EvalResult Value) :=
  let modulus : Int := EVM.twoPow bits.val
  let half : Int := EVM.twoPow (bits.val - 1)
  let u := IntType.uint bits
  let s := IntType.sint bits
  [(.add u .checked, modulus - 1, 1, .revert),
   (.add u .wrapping, modulus - 1, 1, .ok (.int 0)),
   (.sub u .checked, 0, 1, .revert),
   (.sub u .wrapping, 0, 1, .ok (.int (modulus - 1))),
   (.mul u .checked, modulus - 1, 2, .revert),
   (.mul u .wrapping, modulus - 1, 2, .ok (.int (modulus - 2))),
   (.add s .checked, half - 1, 1, .revert),
   (.add s .wrapping, half - 1, 1, .ok (.int (-half))),
   (.sub s .checked, -half, 1, .revert),
   (.sub s .wrapping, -half, 1, .ok (.int (half - 1))),
   (.mul s .checked, -half, -1, .revert),
   (.mul s .wrapping, -half, -1, .ok (.int (-half))),
   (.div s .checked, -half, -1, .revert),
   (.div s .wrapping, -half, -1, .ok (.int (-half))),
   (.div s .checked, -5, 2, .ok (.int (-2))),
   (.mod s, -5, 2, .ok (.int (-1))),
   (.mod s, -half, -1, .ok (.int 0)),
   (.shl u, 1, bits.val, .ok (.int 0)),
   (.shl s, half - 1, 1, .ok (.int (-2))),
   (.shr s, -3, 1, .ok (.int (-2))),
   (.shr s, -half, bits.val, .ok (.int (-1))),
   (.bitXor s, -1, half - 1, .ok (.int (-half))),
   (.exp u .checked, half, 2, .revert),
   (.exp u .wrapping, half, 2, .ok (.int 0))]

#guard integerWidths.all fun bits => (arithmeticBoundaryCases bits).all fun (op, lhs, rhs, result) =>
  decide (evalBinaryOp? op (.int lhs) (.int rhs) = result)

#guard integerWidths.all fun bits => [IntType.uint bits, .sint bits].all fun ty =>
  [IntArithMode.checked, .wrapping].all fun mode =>
    decide (evalBinaryOp? (.div ty mode) (.int 1) (.int 0) = .revert ∧
      evalBinaryOp? (.mod ty) (.int 1) (.int 0) = .revert)

def uint8Type : ABIType := .elem (.int (.uint ⟨8, by decide⟩))

def surfaceContract : ContractDecl := solidity% contract IntegerTest {
  function checkedAdd(uint8 x, uint8 y) external returns (uint8) {
    uint8 z = x + y;
    return z;
  }

  function wrappedAdd(uint8 x, uint8 y) external returns (uint8) {
    return unchecked(x + y) % #(2 ^ 8);
  }

  function ordinaryModulo(uint256 x, uint256 y, uint256 denominator)
      external returns (uint256) {
    return x * y % denominator;
  }

  function signedOps(int8 x, int8 y) external returns (int8, int8, int8) {
    return x / y, x % y, x >> 1;
  }
}

example : surfaceContract.transitions[0]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "z" (some uint8Type)
        (.binary (.add (.uint ⟨8, by decide⟩) .checked) (.var "x") (.var "y")),
      .return [.var "z"] ] := by
  rfl

example : surfaceContract.transitions[1]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return
        [ .binary (.mod (.uint ⟨8, by decide⟩))
            (.binary (.add (.uint ⟨8, by decide⟩) .wrapping) (.var "x") (.var "y"))
            (.intLit 256) ] ] := by
  rfl

example : surfaceContract.transitions[2]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return
        [ .binary (.mod (.uint ⟨256, by decide⟩))
            (.binary (.mul (.uint ⟨256, by decide⟩) .checked) (.var "x") (.var "y"))
            (.var "denominator") ] ] := by
  rfl

example : surfaceContract.transitions[3]!.body =
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .return
        [ .binary (.div (.sint ⟨8, by decide⟩) .checked) (.var "x") (.var "y"),
          .binary (.mod (.sint ⟨8, by decide⟩)) (.var "x") (.var "y"),
          .binary (.shr (.sint ⟨8, by decide⟩)) (.var "x") (.intLit 1) ] ] := by
  rfl

example (cfg : Config) (solm : Frame) (evm : EVM.State) :
    ExecStmt cfg solm evm (.letDecl "x" (some uint8Type) (.intLit 255))
      (.ok { solm with locals := solm.locals.insert "x" (.int 255) } evm) := by
  exact ExecStmt.letDecl (by simp [evalExpr?, pure]) (by native_decide)

example (cfg : Config) (solm : Frame) (evm : EVM.State) (result : ExecResult) :
    ¬ExecStmt cfg solm evm (.letDecl "x" (some uint8Type) (.intLit 256)) result := by
  intro execution
  cases execution with
  | letDecl heval htype =>
      simp [evalExpr?, pure] at heval
      subst_vars
      norm_num [uint8Type, valueMatchesOptionalABIType, valueMatchesABIType, normalizeInt,
        EVM.twoPow] at htype
  | letDeclRevert heval => simp [evalExpr?] at heval

example :
    bindParams? [{ name := "x", ty := uint8Type }] [.int 255] =
      some ((∅ : Store).insert "x" (.int 255)) := by
  norm_num [bindParams?, uint8Type, valueMatchesABIType, normalizeInt, EVM.twoPow]

example : bindParams? [{ name := "x", ty := uint8Type }] [.int 256] = none := by
  norm_num [bindParams?, uint8Type, valueMatchesABIType, normalizeInt, EVM.twoPow]

end Solm.IntegerTests
