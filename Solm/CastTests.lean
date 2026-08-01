import Solm.Notation
import Solm.Semantics

open ABI

namespace Solm.CastTests

def uint8Storage : StorageType := .elem (.int (.uint ⟨8, by decide⟩))
def int8Storage : StorageType := .elem (.int (.sint ⟨8, by decide⟩))
def uint256Storage : StorageType := .elem (.int (.uint ⟨256, by decide⟩))
def int256Storage : StorageType := .elem (.int (.sint ⟨256, by decide⟩))

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

end Solm.CastTests
