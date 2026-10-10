import Benchmarks.UniswapV3.Pool.PoolEntrySource
import Benchmarks.UniswapV3.Pool.Slot0Struct

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

structure SwapArgs where
  recipient : AccountAddress
  zeroForOne : Bool
  amountSpecified : Int
  priceLimit : UInt256
  data : ByteArray

def SwapArgs.Fits (a : SwapArgs) : Prop :=
  (-(2 ^ 255 : Int) ≤ a.amountSpecified ∧ a.amountSpecified < 2 ^ 255) ∧
    a.priceLimit.toNat < 2 ^ 160

def swapLocals (a : SwapArgs) : Store :=
  let locals := (∅ : Store).insert "recipient" (.address a.recipient)
  let locals := locals.insert "zeroForOne" (.bool a.zeroForOne)
  let locals := locals.insert "amountSpecified" (.int a.amountSpecified)
  let locals := locals.insert "sqrtPriceLimitX96" (.int (Int.ofNat a.priceLimit.toNat))
  locals.insert "data" (.bytes a.data)

def swapFrame (v : UniswapV3PoolImmutables) (a : SwapArgs) : Frame :=
  {contract := contract, locals := swapLocals a, immutables := immStore v}

def swapInitFrame (v : UniswapV3PoolImmutables) (a : SwapArgs) : Frame :=
  poolAmountsFrame (swapLocals a) (immStore v)

def swapDelegateFrame (v : UniswapV3PoolImmutables) (a : SwapArgs) : Frame :=
  resumeAfterInternalCall (swapInitFrame v a) "__c0" none

def swapSlot0Frame (v : UniswapV3PoolImmutables) (a : SwapArgs) (evm : EVM.State) : Frame :=
  {swapDelegateFrame v a with
    locals := (swapDelegateFrame v a).locals.insert "slot0Start"
      (slot0StructValue evm.accountMap evm.executionEnv)}

end Benchmarks.UniswapV3.Pool
