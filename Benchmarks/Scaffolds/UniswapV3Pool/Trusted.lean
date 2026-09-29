import Benchmarks.Scaffolds.UniswapV3Pool.Bytecode
import Solm.Semantics

/-!
# UniswapV3Pool selector proofs

These proofs identify the first four bytes of `keccak256(<canonical signature>)` for each public
ABI entry point.
-/

open Solm ABI Ethereum Benchmarks.UniswapV3Pool.Immutables

namespace Benchmarks.UniswapV3Pool

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem burnSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr burnTransition))).extract 0 4
      = ⟨#[0xa3, 0x41, 0x23, 0xa7]⟩ := by
  have hsig : transitionSigStr burnTransition = "burn(int24,int24,uint128)" := by
    simp [transitionSigStr, ABI.printSignature, transitionSignature, burnTransition,
      int24, uint128, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

theorem collectSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (collectTransition v)))).extract 0 4
      = ⟨#[0x4f, 0x1e, 0xb3, 0xd8]⟩ := by
  have hsig : transitionSigStr (collectTransition v) =
      "collect(address,int24,int24,uint128,uint128)" := by
    simp [transitionSigStr, ABI.printSignature, transitionSignature, collectTransition,
      addr, int24, uint128, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

theorem collectProtocolSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (collectprotocolTransition v)))).extract 0 4
      = ⟨#[0x85, 0xb6, 0x67, 0x29]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, collectprotocolTransition, addr, uint128, uint128Int]; decide +kernel

theorem factorySelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (factoryTransition v)))).extract 0 4
      = ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, factoryTransition]; decide +kernel

theorem feeSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (feeTransition v)))).extract 0 4
      = ⟨#[0xdd, 0xca, 0x3f, 0x43]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, feeTransition]; decide +kernel

theorem feeGrowthGlobal0X128SelectorBytes :
    (KEC (String.toByteArray (transitionSigStr feegrowthglobal0X128Transition))).extract 0 4
      = ⟨#[0xf3, 0x05, 0x83, 0x99]⟩ := by decide +kernel

theorem feeGrowthGlobal1X128SelectorBytes :
    (KEC (String.toByteArray (transitionSigStr feegrowthglobal1X128Transition))).extract 0 4
      = ⟨#[0x46, 0x14, 0x13, 0x19]⟩ := by decide +kernel

theorem flashSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (flashTransition v)))).extract 0 4
      = ⟨#[0x49, 0x0e, 0x6c, 0xbc]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, flashTransition, addr, uint256, uint256Int, bytesTy]; decide +kernel

theorem increaseObservationCardinalityNextSelectorBytes (v : PoolImmutables) :
    (KEC
      (String.toByteArray
        (transitionSigStr (increaseobservationcardinalitynextTransition v)))).extract 0 4
      = ⟨#[0x32, 0x14, 0x8f, 0x67]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, increaseobservationcardinalitynextTransition, uint16, uint16Int]; decide +kernel

theorem initializeSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr initializeTransition))).extract 0 4
      = ⟨#[0xf6, 0x37, 0x73, 0x1d]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, initializeTransition, uint160, uint160Int]; decide +kernel

theorem liquiditySelectorBytes :
    (KEC (String.toByteArray (transitionSigStr liquidityTransition))).extract 0 4
      = ⟨#[0x1a, 0x68, 0x65, 0x02]⟩ := by decide +kernel

theorem maxLiquidityPerTickSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (maxliquiditypertickTransition v)))).extract 0 4
      = ⟨#[0x70, 0xcf, 0x75, 0x4a]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, maxliquiditypertickTransition]; decide +kernel

theorem mintSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (mintTransition v)))).extract 0 4
      = ⟨#[0x3c, 0x8a, 0x7d, 0x8d]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, mintTransition, addr, int24, int24Int, uint128, uint128Int, bytesTy]; decide +kernel

theorem observationsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr observationsTransition))).extract 0 4
      = ⟨#[0x25, 0x2c, 0x09, 0xd7]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, observationsTransition, uint256, uint256Int]; decide +kernel

theorem observeSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (observeTransition v)))).extract 0 4
      = ⟨#[0x88, 0x3b, 0xdb, 0xfd]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, observeTransition, uint32, uint32Int]; decide +kernel

theorem positionsSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr positionsTransition))).extract 0 4
      = ⟨#[0x51, 0x4e, 0xa4, 0xbf]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, positionsTransition, bytes32, bytes32Width]; decide +kernel

theorem protocolFeesSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr protocolfeesTransition))).extract 0 4
      = ⟨#[0x1a, 0xd8, 0xb0, 0x3b]⟩ := by decide +kernel

theorem setFeeProtocolSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (setfeeprotocolTransition v)))).extract 0 4
      = ⟨#[0x82, 0x06, 0xa4, 0xd1]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, setfeeprotocolTransition, uint8, uint8Int]; decide +kernel

theorem slot0SelectorBytes :
    (KEC (String.toByteArray (transitionSigStr slot0Transition))).extract 0 4
      = ⟨#[0x38, 0x50, 0xc7, 0xbd]⟩ := by decide +kernel

theorem snapshotCumulativesInsideSelectorBytes (v : PoolImmutables) :
    (KEC
      (String.toByteArray (transitionSigStr (snapshotcumulativesinsideTransition v)))).extract 0 4
      = ⟨#[0xa3, 0x88, 0x07, 0xf2]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, snapshotcumulativesinsideTransition, int24, int24Int]; decide +kernel

theorem swapSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (swapTransition v)))).extract 0 4
      = ⟨#[0x12, 0x8a, 0xcb, 0x08]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, swapTransition, addr, boolTy, int256, int256Int, uint160, uint160Int, bytesTy]; decide +kernel

theorem tickBitmapSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr tickbitmapTransition))).extract 0 4
      = ⟨#[0x53, 0x39, 0xc2, 0x96]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, tickbitmapTransition, int16, int16Int]; decide +kernel

theorem tickSpacingSelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (tickspacingTransition v)))).extract 0 4
      = ⟨#[0xd0, 0xc9, 0x3a, 0x7c]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, tickspacingTransition]; decide +kernel

theorem ticksSelectorBytes :
    (KEC (String.toByteArray (transitionSigStr ticksTransition))).extract 0 4
      = ⟨#[0xf3, 0x0d, 0xba, 0x93]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, ticksTransition, int24, int24Int]; decide +kernel

theorem token0SelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (token0Transition v)))).extract 0 4
      = ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, token0Transition]; decide +kernel

theorem token1SelectorBytes (v : PoolImmutables) :
    (KEC (String.toByteArray (transitionSigStr (token1Transition v)))).extract 0 4
      = ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩ := by
  simp [transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, token1Transition]; decide +kernel

end Benchmarks.UniswapV3Pool
