import Benchmarks.UniswapV4PoolManager.PoolKeySource
import Benchmarks.UniswapV4PoolManager.PoolTicksSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

structure PoolModifyParams where
  owner : AccountAddress
  lower : UInt256
  upper : UInt256
  delta : Int
  spacing : UInt256
  salt : UInt256

def poolModifyParamsValue (p : PoolModifyParams) : Value :=
  .struct "Pool_ModifyLiquidityParams"
    [("owner", .address p.owner), ("tickLower", .int (EVM.signed p.lower)),
     ("tickUpper", .int (EVM.signed p.upper)), ("liquidityDelta", .int p.delta),
     ("tickSpacing", .int (EVM.signed p.spacing)), ("salt", wordBytes32Value p.salt)]

def poolModifyStateValue (flippedLower : Bool) (grossLower : UInt256)
    (flippedUpper : Bool) (grossUpper : UInt256) : Value :=
  .struct "ModifyLiquidityState"
    [("flippedLower", .bool flippedLower), ("liquidityGrossAfterLower", .int (Int.ofNat grossLower.toNat)),
     ("flippedUpper", .bool flippedUpper), ("liquidityGrossAfterUpper", .int (Int.ofNat grossUpper.toNat))]

abbrev poolModifyFunction : FunctionDecl := contract.functions[17]!
theorem poolModify_lookup : lookupCallable? contract "Pool_modifyLiquidity" = some poolModifyFunction.toCallable := rfl

end Benchmarks.UniswapV4PoolManager
