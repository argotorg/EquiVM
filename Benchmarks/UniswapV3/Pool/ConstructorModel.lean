import Benchmarks.UniswapV3.Pool.ConstructorPrefix
import Benchmarks.UniswapV3.Pool.ConstructorParameters

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

def constructorUnsignedSpacing (out : ByteArray) : Int :=
  normalizeInt (.uint ⟨24, by decide⟩) (constructorSpacing out)

theorem constructorUnsignedSpacing_bounds (out : ByteArray) :
    0 ≤ constructorUnsignedSpacing out ∧ constructorUnsignedSpacing out < 2 ^ 24 :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

def constructorParameterImms (original : AccountAddress) (out : ByteArray) : Store :=
  ((((constructorOriginalImms original).insert
    "factory" (.address (AccountAddress.ofNat (calldataWord out 0).toNat))).insert
    "token0" (.address (AccountAddress.ofNat (calldataWord out 32).toNat))).insert
    "token1" (.address (AccountAddress.ofNat (calldataWord out 64).toNat))).insert
    "fee" (.int (constructorFee out))

def constructorSpacingImms (original : AccountAddress) (out : ByteArray) : Store :=
  (constructorParameterImms original out).insert "tickSpacing" (.int (constructorUnsignedSpacing out))

def constructorFinalImms (original : AccountAddress) (out : ByteArray) : Store :=
  (constructorSpacingImms original out).insert "maxLiquidityPerTick"
    (.int (spacingLiquidity (constructorSpacing out)))

def constructorDecodedFrame (original : AccountAddress) (out : ByteArray) : Frame :=
  {constructorCallFrame original true out with
    locals := (constructorCallFrame original true out).locals.insert "__c0"
      (.tuple (constructorParameterValues out))}

def constructorFieldsFrame (original : AccountAddress) (out : ByteArray) : Frame :=
  {constructorDecodedFrame original out with immutables := constructorParameterImms original out}

def constructorSpacingFrame (original : AccountAddress) (out : ByteArray) : Frame :=
  {constructorFieldsFrame original out with
    locals := (constructorFieldsFrame original out).locals.insert "_tickSpacing" (.int (constructorSpacing out))
    immutables := constructorSpacingImms original out}

def constructorLiquidityFrame (original : AccountAddress) (out : ByteArray) : Frame :=
  {constructorSpacingFrame original out with
    locals := (constructorSpacingFrame original out).locals.insert "__c1"
      (.int (spacingLiquidity (constructorSpacing out)))}

def constructorFinalFrame (original : AccountAddress) (out : ByteArray) : Frame :=
  {constructorLiquidityFrame original out with immutables := constructorFinalImms original out}

def constructorValuation (original : AccountAddress) (out : ByteArray) : UniswapV3PoolImmutables :=
  {original := original
   factory := AccountAddress.ofNat (calldataWord out 0).toNat
   token0 := AccountAddress.ofNat (calldataWord out 32).toNat
   token1 := AccountAddress.ofNat (calldataWord out 64).toNat
   fee := EVM.wordOfInt (constructorFee out)
   tickSpacing := EVM.wordOfInt (constructorUnsignedSpacing out)
   maxLiquidityPerTick := EVM.wordOfInt (spacingLiquidity (constructorSpacing out))}

end Benchmarks.UniswapV3.Pool
