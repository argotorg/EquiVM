import Benchmarks.Scaffolds.UniswapV3Pool.Bytecode
import Solm.Semantics

/-!
# UniswapV3Pool trusted selector facts

These are the contract-local selector facts for the public ABI. They are the same trusted-base
kind as the selector facts used by the existing benchmark proofs: each states the first four bytes
of `keccak256(<canonical signature>)`.
-/

open Solm ABI Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool

axiom burnSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr burnTransition))).extract 0 4
      = ⟨#[0xa3, 0x41, 0x23, 0xa7]⟩

axiom collectSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (collectTransition v)))).extract 0 4
      = ⟨#[0x4f, 0x1e, 0xb3, 0xd8]⟩

axiom collectProtocolSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (collectprotocolTransition v)))).extract 0 4
      = ⟨#[0x85, 0xb6, 0x67, 0x29]⟩

axiom factorySelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (factoryTransition v)))).extract 0 4
      = ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩

axiom feeSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (feeTransition v)))).extract 0 4
      = ⟨#[0xdd, 0xca, 0x3f, 0x43]⟩

axiom feeGrowthGlobal0X128SelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr feegrowthglobal0X128Transition))).extract 0 4
      = ⟨#[0xf3, 0x05, 0x83, 0x99]⟩

axiom feeGrowthGlobal1X128SelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr feegrowthglobal1X128Transition))).extract 0 4
      = ⟨#[0x46, 0x14, 0x13, 0x19]⟩

axiom flashSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (flashTransition v)))).extract 0 4
      = ⟨#[0x49, 0x0e, 0x6c, 0xbc]⟩

axiom increaseObservationCardinalityNextSelectorBytes (v : PoolImmutables) :
    (ffi.KEC
      (String.toByteArray
        (transitionSigStr (increaseobservationcardinalitynextTransition v)))).extract 0 4
      = ⟨#[0x32, 0x14, 0x8f, 0x67]⟩

axiom initializeSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr initializeTransition))).extract 0 4
      = ⟨#[0xf6, 0x37, 0x73, 0x1d]⟩

axiom liquiditySelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr liquidityTransition))).extract 0 4
      = ⟨#[0x1a, 0x68, 0x65, 0x02]⟩

axiom maxLiquidityPerTickSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (maxliquiditypertickTransition v)))).extract 0 4
      = ⟨#[0x70, 0xcf, 0x75, 0x4a]⟩

axiom mintSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (mintTransition v)))).extract 0 4
      = ⟨#[0x3c, 0x8a, 0x7d, 0x8d]⟩

axiom observationsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr observationsTransition))).extract 0 4
      = ⟨#[0x25, 0x2c, 0x09, 0xd7]⟩

axiom observeSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (observeTransition v)))).extract 0 4
      = ⟨#[0x88, 0x3b, 0xdb, 0xfd]⟩

axiom positionsSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr positionsTransition))).extract 0 4
      = ⟨#[0x51, 0x4e, 0xa4, 0xbf]⟩

axiom protocolFeesSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr protocolfeesTransition))).extract 0 4
      = ⟨#[0x1a, 0xd8, 0xb0, 0x3b]⟩

axiom setFeeProtocolSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (setfeeprotocolTransition v)))).extract 0 4
      = ⟨#[0x82, 0x06, 0xa4, 0xd1]⟩

axiom slot0SelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr slot0Transition))).extract 0 4
      = ⟨#[0x38, 0x50, 0xc7, 0xbd]⟩

axiom snapshotCumulativesInsideSelectorBytes (v : PoolImmutables) :
    (ffi.KEC
      (String.toByteArray (transitionSigStr (snapshotcumulativesinsideTransition v)))).extract 0 4
      = ⟨#[0xa3, 0x88, 0x07, 0xf2]⟩

axiom swapSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (swapTransition v)))).extract 0 4
      = ⟨#[0x12, 0x8a, 0xcb, 0x08]⟩

axiom tickBitmapSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr tickbitmapTransition))).extract 0 4
      = ⟨#[0x53, 0x39, 0xc2, 0x96]⟩

axiom tickSpacingSelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (tickspacingTransition v)))).extract 0 4
      = ⟨#[0xd0, 0xc9, 0x3a, 0x7c]⟩

axiom ticksSelectorBytes :
    (ffi.KEC (String.toByteArray (transitionSigStr ticksTransition))).extract 0 4
      = ⟨#[0xf3, 0x0d, 0xba, 0x93]⟩

axiom token0SelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (token0Transition v)))).extract 0 4
      = ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩

axiom token1SelectorBytes (v : PoolImmutables) :
    (ffi.KEC (String.toByteArray (transitionSigStr (token1Transition v)))).extract 0 4
      = ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩

end Benchmarks.UniswapV3Pool
