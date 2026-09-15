import Benchmarks.Scaffolds.UniswapV3Pool.SpecSyntax

/-! Concrete regressions for the scaffold's source-level arithmetic. These test the actual helper
expressions; they are not a replacement for the scaffold's unfinished bytecode-equivalence proofs.
The reference is the vendored `contracts/libraries/Oracle.sol` (Solidity 0.7.6 wrapping arithmetic). -/

open ABI Solm

namespace Benchmarks.UniswapV3Pool.ArithmeticTests

private def cfg : Config := {
  storage := storageLayout
  externalABI := poolExternalABI
  selfDeployment := fun _ _ => none
}

private def interpolateSeconds (before after observationDelta targetDelta : Int) : EvalResult Value := do
  let .return [_, seconds] := observeSingleFunction.body[7]!
    | .error .typeError
  let surrounding : Value := .tuple
    [.int 0, .int 0, .int before, .bool true,
      .int observationDelta, .int 0, .int after, .bool true]
  let locals := (∅ : Store).insert "surrounding" surrounding
    |>.insert "observationTimeDelta" (.int observationDelta)
    |>.insert "targetDelta" (.int targetDelta)
  evalExpr? cfg { contract := default, locals } default seconds

-- Values above 32 bits survive; the product is widened before the multiplication.
#guard interpolateSeconds 0 (2 ^ 128) 4 2 = .ok (.int (2 ^ 127))
#guard interpolateSeconds 0 (2 ^ 159) 4 3 = .ok (.int (3 * 2 ^ 157))

-- Subtraction and final addition wrap at 160 bits, before/after the uint256 calculation.
#guard interpolateSeconds (2 ^ 160 - 2) 2 4 1 = .ok (.int (2 ^ 160 - 1))
#guard interpolateSeconds (2 ^ 160 - 2) 2 4 2 = .ok (.int 0)
#guard interpolateSeconds (2 ^ 160 - 2) 2 4 3 = .ok (.int 1)
#guard interpolateSeconds 7 12 3 1 = .ok (.int 8)
#guard interpolateSeconds 7 12 0 1 = .revert

end Benchmarks.UniswapV3Pool.ArithmeticTests
