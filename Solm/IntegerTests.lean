import Solm.Notation
import Solm.Semantics
import Solm.OverflowModeTests

open ABI

namespace Solm.IntegerTests

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
