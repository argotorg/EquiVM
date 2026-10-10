import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.SolmBody.frame_eq_of_contract to arbitrary immutable bindings.
theorem frame_eq_of_parts {frame : Frame} {decl : ContractDecl} {imms : Store}
    (hc : frame.contract = decl) (hi : frame.immutables = imms) :
    frame = {contract := decl, locals := frame.locals, immutables := imms} := by
  cases frame
  dsimp only at hc hi ⊢
  cases hc
  cases hi
  rfl

end Benchmarks.UniswapV3.Pool
