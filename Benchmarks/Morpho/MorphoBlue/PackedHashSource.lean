import Benchmarks.Morpho.MorphoBlue.ReturnCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: hash a proved packed byte encoding in an arbitrary source frame.
theorem evalPackedKeccak {cfg : Config} {frame : Frame} {evm : EVM.State}
    {args : List (ABIType × Expr)} {bytes : ByteArray}
    (he : evalPackedArgs? cfg frame evm args = .ok bytes.toList) :
    evalExpr? cfg frame evm (.keccak256 (.abiEncodePacked args)) =
      .ok (wordBytes32Value (uInt256OfByteArray (KEC bytes))) := by
  have hb : ByteArray.mk bytes.toList.toArray = bytes := by
    apply byteArray_eq_of_toList_eq
    simp only [byteArray_toList_eq, List.toList_toArray]
  simp only [evalExpr?, he, bind, EvalResult.bind, pure, hb, wordBytes32Value,
    toBytesBE_keccak_uInt256OfByteArray]
  rfl

end Benchmarks.Morpho.MorphoBlue
