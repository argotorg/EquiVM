import Benchmarks.UniswapV3Pool.InitializeSourceGetSqrtRatio

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def getSqrtRatioSourceTickHiInitialRatioPrefixBlock : List Stmt :=
  [ .letDecl "absTick" (some uint256)
      (.ite (ltE (.var "tick") (.intLit 0))
        (subE (.intLit 0) (.var "tick"))
        (.var "tick")),
    .require (leE (.var "absTick") maxTick),
    .letDecl "ratio" (some uint256)
      (.ite (neE (bitAndE (.var "absTick") (.intLit 0x1)) (.intLit 0))
        (.intLit 0xfffcb933bd6fad37aa2d162d1a594001)
        fixedPoint128Q128) ]

def getSqrtRatioSourceTickHiPrefixThroughBit8 : List Stmt :=
  (((getSqrtRatioSourceTickHiInitialRatioPrefixBlock ++
      tickRatioStep 0x2 0xfff97272373d413259a46990580e213a) ++
    tickRatioStep 0x4 0xfff2e50f5f656932ef12357cf3c7fdcc) ++
    tickRatioStep 0x8 0xffe5caca7e10e4e61c3624eaa0941cd0)

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit8Block
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit8
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit8 I }
        evm) := by
  simpa [getSqrtRatioSourceTickHiPrefixThroughBit8,
    getSqrtRatioSourceTickHiInitialRatioPrefixBlock] using
    uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit8 evm I hrange

theorem getSqrtRatioStoreAfterTickHiBit8_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit8 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit8, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit4 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4Int I)
      8
      getSqrtRatioSourceFactor8Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit4_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit8_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit8 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit8Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit8, getSqrtRatioSourceTickHiAfterBit8Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit4 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4Int I)
      8
      getSqrtRatioSourceFactor8Int
      (getSqrtRatioStoreAfterTickHiBit4_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit8Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit8Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit8Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4Int I)
      8
      getSqrtRatioSourceFactor8Int
      (getSqrtRatioSourceTickHiAfterBit4Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit8Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit8Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit8Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4Int I)
      8
      getSqrtRatioSourceFactor8Int
      (getSqrtRatioSourceTickHiAfterBit4Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit4Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor8Int])
      (by norm_num [getSqrtRatioSourceFactor8Int])

def getSqrtRatioSourceFactor16Int : Int :=
  340010263488231146823593991679159461444

def getSqrtRatioSourceTickHiAfterBit16Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit8Int I)
    16
    getSqrtRatioSourceFactor16Int

def getSqrtRatioStoreAfterTickHiBit16 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit8 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit8Int I)
    16
    getSqrtRatioSourceFactor16Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit16
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit8 I } evm
      (tickRatioStep 0x10 0xffcb9843d60f6159c9db58835c926644)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit16 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit8 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit8Int I)
    16
    getSqrtRatioSourceFactor16Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit8_absTick I)
    (getSqrtRatioStoreAfterTickHiBit8_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit8Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit8Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor16Int])
    (by norm_num [getSqrtRatioSourceFactor16Int])

def getSqrtRatioSourceTickHiPrefixThroughBit16 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit8 ++
    tickRatioStep 0x10 0xffcb9843d60f6159c9db58835c926644

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit16
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit16
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit16 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit8Block evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit16 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit16_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit16 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit16, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit8 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8Int I)
      16
      getSqrtRatioSourceFactor16Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit8_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit16_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit16 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit16Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit16, getSqrtRatioSourceTickHiAfterBit16Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit8 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8Int I)
      16
      getSqrtRatioSourceFactor16Int
      (getSqrtRatioStoreAfterTickHiBit8_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit16Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit16Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit16Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8Int I)
      16
      getSqrtRatioSourceFactor16Int
      (getSqrtRatioSourceTickHiAfterBit8Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit16Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit16Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit16Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8Int I)
      16
      getSqrtRatioSourceFactor16Int
      (getSqrtRatioSourceTickHiAfterBit8Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit8Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor16Int])
      (by norm_num [getSqrtRatioSourceFactor16Int])

def getSqrtRatioSourceFactor32Int : Int :=
  339738377640345403697157401104375502016

def getSqrtRatioSourceTickHiAfterBit32Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit16Int I)
    32
    getSqrtRatioSourceFactor32Int

def getSqrtRatioStoreAfterTickHiBit32 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit16 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit16Int I)
    32
    getSqrtRatioSourceFactor32Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit32
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit16 I } evm
      (tickRatioStep 0x20 0xff973b41fa98c081472e6896dfb254c0)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit32 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit16 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit16Int I)
    32
    getSqrtRatioSourceFactor32Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit16_absTick I)
    (getSqrtRatioStoreAfterTickHiBit16_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit16Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit16Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor32Int])
    (by norm_num [getSqrtRatioSourceFactor32Int])

def getSqrtRatioSourceTickHiPrefixThroughBit32 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit16 ++
    tickRatioStep 0x20 0xff973b41fa98c081472e6896dfb254c0

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit32
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit32
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit32 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit16 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit32 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit32_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit32 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit32, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit16 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16Int I)
      32
      getSqrtRatioSourceFactor32Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit16_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit32_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit32 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit32Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit32, getSqrtRatioSourceTickHiAfterBit32Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit16 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16Int I)
      32
      getSqrtRatioSourceFactor32Int
      (getSqrtRatioStoreAfterTickHiBit16_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit32Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit32Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit32Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16Int I)
      32
      getSqrtRatioSourceFactor32Int
      (getSqrtRatioSourceTickHiAfterBit16Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit32Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit32Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit32Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16Int I)
      32
      getSqrtRatioSourceFactor32Int
      (getSqrtRatioSourceTickHiAfterBit16Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit16Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor32Int])
      (by norm_num [getSqrtRatioSourceFactor32Int])

def getSqrtRatioSourceFactor64Int : Int :=
  339195258003219555707034227454543997025

def getSqrtRatioSourceTickHiAfterBit64Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit32Int I)
    64
    getSqrtRatioSourceFactor64Int

def getSqrtRatioStoreAfterTickHiBit64 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit32 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit32Int I)
    64
    getSqrtRatioSourceFactor64Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit64
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit32 I } evm
      (tickRatioStep 0x40 0xff2ea16466c96a3843ec78b326b52861)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit64 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit32 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit32Int I)
    64
    getSqrtRatioSourceFactor64Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit32_absTick I)
    (getSqrtRatioStoreAfterTickHiBit32_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit32Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit32Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor64Int])
    (by norm_num [getSqrtRatioSourceFactor64Int])

def getSqrtRatioSourceTickHiPrefixThroughBit64 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit32 ++
    tickRatioStep 0x40 0xff2ea16466c96a3843ec78b326b52861

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit64
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit64
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit64 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit32 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit64 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit64_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit64 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit64, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit32 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32Int I)
      64
      getSqrtRatioSourceFactor64Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit32_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit64_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit64 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit64Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit64, getSqrtRatioSourceTickHiAfterBit64Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit32 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32Int I)
      64
      getSqrtRatioSourceFactor64Int
      (getSqrtRatioStoreAfterTickHiBit32_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit64Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit64Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit64Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32Int I)
      64
      getSqrtRatioSourceFactor64Int
      (getSqrtRatioSourceTickHiAfterBit32Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit64Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit64Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit64Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32Int I)
      64
      getSqrtRatioSourceFactor64Int
      (getSqrtRatioSourceTickHiAfterBit32Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit32Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor64Int])
      (by norm_num [getSqrtRatioSourceFactor64Int])

def getSqrtRatioSourceFactor128Int : Int :=
  338111622100601834656805679988414885971

def getSqrtRatioSourceTickHiAfterBit128Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit64Int I)
    128
    getSqrtRatioSourceFactor128Int

def getSqrtRatioStoreAfterTickHiBit128 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit64 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit64Int I)
    128
    getSqrtRatioSourceFactor128Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit128
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit64 I } evm
      (tickRatioStep 0x80 0xfe5dee046a99a2a811c461f1969c3053)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit128 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit64 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit64Int I)
    128
    getSqrtRatioSourceFactor128Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit64_absTick I)
    (getSqrtRatioStoreAfterTickHiBit64_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit64Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit64Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor128Int])
    (by norm_num [getSqrtRatioSourceFactor128Int])

def getSqrtRatioSourceTickHiPrefixThroughBit128 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit64 ++
    tickRatioStep 0x80 0xfe5dee046a99a2a811c461f1969c3053

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit128
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit128
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit128 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit64 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit128 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit128_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit128 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit128, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit64 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit64Int I)
      128
      getSqrtRatioSourceFactor128Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit64_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit128_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit128 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit128Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit128, getSqrtRatioSourceTickHiAfterBit128Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit64 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit64Int I)
      128
      getSqrtRatioSourceFactor128Int
      (getSqrtRatioStoreAfterTickHiBit64_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit128Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit128Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit128Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit64Int I)
      128
      getSqrtRatioSourceFactor128Int
      (getSqrtRatioSourceTickHiAfterBit64Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit128Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit128Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit128Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit64Int I)
      128
      getSqrtRatioSourceFactor128Int
      (getSqrtRatioSourceTickHiAfterBit64Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit64Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor128Int])
      (by norm_num [getSqrtRatioSourceFactor128Int])

def getSqrtRatioSourceFactor256Int : Int :=
  335954724994790223023589805789778977700

def getSqrtRatioSourceTickHiAfterBit256Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit128Int I)
    256
    getSqrtRatioSourceFactor256Int

def getSqrtRatioStoreAfterTickHiBit256 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit128 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit128Int I)
    256
    getSqrtRatioSourceFactor256Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit256
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit128 I } evm
      (tickRatioStep 0x100 0xfcbe86c7900a88aedcffc83b479aa3a4)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit256 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit128 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit128Int I)
    256
    getSqrtRatioSourceFactor256Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit128_absTick I)
    (getSqrtRatioStoreAfterTickHiBit128_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit128Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit128Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor256Int])
    (by norm_num [getSqrtRatioSourceFactor256Int])

def getSqrtRatioSourceTickHiPrefixThroughBit256 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit128 ++
    tickRatioStep 0x100 0xfcbe86c7900a88aedcffc83b479aa3a4

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit256
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit256
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit256 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit128 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit256 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit256_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit256 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit256, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit128 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit128Int I)
      256
      getSqrtRatioSourceFactor256Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit128_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit256_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit256 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit256Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit256, getSqrtRatioSourceTickHiAfterBit256Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit128 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit128Int I)
      256
      getSqrtRatioSourceFactor256Int
      (getSqrtRatioStoreAfterTickHiBit128_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit256Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit256Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit256Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit128Int I)
      256
      getSqrtRatioSourceFactor256Int
      (getSqrtRatioSourceTickHiAfterBit128Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit256Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit256Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit256Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit128Int I)
      256
      getSqrtRatioSourceFactor256Int
      (getSqrtRatioSourceTickHiAfterBit128Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit128Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor256Int])
      (by norm_num [getSqrtRatioSourceFactor256Int])

def getSqrtRatioSourceFactor512Int : Int :=
  331682121138379247127172139078559817300

def getSqrtRatioSourceTickHiAfterBit512Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit256Int I)
    512
    getSqrtRatioSourceFactor512Int

def getSqrtRatioStoreAfterTickHiBit512 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit256 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit256Int I)
    512
    getSqrtRatioSourceFactor512Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit512
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit256 I } evm
      (tickRatioStep 0x200 0xf987a7253ac413176f2b074cf7815e54)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit512 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit256 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit256Int I)
    512
    getSqrtRatioSourceFactor512Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit256_absTick I)
    (getSqrtRatioStoreAfterTickHiBit256_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit256Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit256Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor512Int])
    (by norm_num [getSqrtRatioSourceFactor512Int])

def getSqrtRatioSourceTickHiPrefixThroughBit512 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit256 ++
    tickRatioStep 0x200 0xf987a7253ac413176f2b074cf7815e54

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit512
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit512
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit512 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit256 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit512 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit512_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit512 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit512, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit256 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit256Int I)
      512
      getSqrtRatioSourceFactor512Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit256_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit512_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit512 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit512Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit512, getSqrtRatioSourceTickHiAfterBit512Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit256 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit256Int I)
      512
      getSqrtRatioSourceFactor512Int
      (getSqrtRatioStoreAfterTickHiBit256_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit512Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit512Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit512Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit256Int I)
      512
      getSqrtRatioSourceFactor512Int
      (getSqrtRatioSourceTickHiAfterBit256Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit512Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit512Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit512Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit256Int I)
      512
      getSqrtRatioSourceFactor512Int
      (getSqrtRatioSourceTickHiAfterBit256Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit256Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor512Int])
      (by norm_num [getSqrtRatioSourceFactor512Int])

def getSqrtRatioSourceFactor1024Int : Int :=
  323299236684853023288211250268160618739

def getSqrtRatioSourceTickHiAfterBit1024Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit512Int I)
    1024
    getSqrtRatioSourceFactor1024Int

def getSqrtRatioStoreAfterTickHiBit1024 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit512 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit512Int I)
    1024
    getSqrtRatioSourceFactor1024Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit1024
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit512 I } evm
      (tickRatioStep 0x400 0xf3392b0822b70005940c7a398e4b70f3)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit1024 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit512 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit512Int I)
    1024
    getSqrtRatioSourceFactor1024Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit512_absTick I)
    (getSqrtRatioStoreAfterTickHiBit512_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit512Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit512Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor1024Int])
    (by norm_num [getSqrtRatioSourceFactor1024Int])

def getSqrtRatioSourceTickHiPrefixThroughBit1024 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit512 ++
    tickRatioStep 0x400 0xf3392b0822b70005940c7a398e4b70f3

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit1024
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit1024
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit1024 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit512 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit1024 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit8_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit8 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit8] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit4 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4Int I)
      8
      getSqrtRatioSourceFactor8Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit4_tick I)

theorem getSqrtRatioStoreAfterTickHiBit16_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit16 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit16] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit8 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8Int I)
      16
      getSqrtRatioSourceFactor16Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit8_tick I)

theorem getSqrtRatioStoreAfterTickHiBit32_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit32 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit32] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit16 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16Int I)
      32
      getSqrtRatioSourceFactor32Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit16_tick I)

theorem getSqrtRatioStoreAfterTickHiBit64_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit64 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit64] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit32 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32Int I)
      64
      getSqrtRatioSourceFactor64Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit32_tick I)

theorem getSqrtRatioStoreAfterTickHiBit128_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit128 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit128] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit64 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit64Int I)
      128
      getSqrtRatioSourceFactor128Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit64_tick I)

theorem getSqrtRatioStoreAfterTickHiBit256_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit256 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit256] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit128 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit128Int I)
      256
      getSqrtRatioSourceFactor256Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit128_tick I)

theorem getSqrtRatioStoreAfterTickHiBit512_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit512 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit512] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit256 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit256Int I)
      512
      getSqrtRatioSourceFactor512Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit256_tick I)

theorem getSqrtRatioStoreAfterTickHiBit1024_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit1024 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit1024] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit512 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit512Int I)
      1024
      getSqrtRatioSourceFactor1024Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit512_tick I)

end Benchmarks.UniswapV3Pool
