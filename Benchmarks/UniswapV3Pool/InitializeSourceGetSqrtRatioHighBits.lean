import Benchmarks.UniswapV3Pool.InitializeSourceGetSqrtRatioLowBits

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem getSqrtRatioStoreAfterTickHiBit1024_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit1024 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit1024, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit512 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit512Int I)
      1024
      getSqrtRatioSourceFactor1024Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit512_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit1024_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit1024 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit1024Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit1024, getSqrtRatioSourceTickHiAfterBit1024Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit512 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit512Int I)
      1024
      getSqrtRatioSourceFactor1024Int
      (getSqrtRatioStoreAfterTickHiBit512_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit1024Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit1024Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit1024Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit512Int I)
      1024
      getSqrtRatioSourceFactor1024Int
      (getSqrtRatioSourceTickHiAfterBit512Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit1024Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit1024Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit1024Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit512Int I)
      1024
      getSqrtRatioSourceFactor1024Int
      (getSqrtRatioSourceTickHiAfterBit512Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit512Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor1024Int])
      (by norm_num [getSqrtRatioSourceFactor1024Int])

def getSqrtRatioSourceFactor2048Int : Int :=
  307163716377032989948697243942600083929

def getSqrtRatioSourceTickHiAfterBit2048Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit1024Int I)
    2048
    getSqrtRatioSourceFactor2048Int

def getSqrtRatioStoreAfterTickHiBit2048 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit1024 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit1024Int I)
    2048
    getSqrtRatioSourceFactor2048Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit2048
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit1024 I } evm
      (tickRatioStep 0x800 0xe7159475a2c29b7443b29c7fa6e889d9)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit2048 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit1024 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit1024Int I)
    2048
    getSqrtRatioSourceFactor2048Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit1024_absTick I)
    (getSqrtRatioStoreAfterTickHiBit1024_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit1024Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit1024Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor2048Int])
    (by norm_num [getSqrtRatioSourceFactor2048Int])

def getSqrtRatioSourceTickHiPrefixThroughBit2048 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit1024 ++
    tickRatioStep 0x800 0xe7159475a2c29b7443b29c7fa6e889d9

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit2048
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit2048
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit2048 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit1024 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit2048 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit2048_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit2048 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit2048, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit1024 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit1024Int I)
      2048
      getSqrtRatioSourceFactor2048Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit1024_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit2048_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit2048 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit2048Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit2048, getSqrtRatioSourceTickHiAfterBit2048Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit1024 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit1024Int I)
      2048
      getSqrtRatioSourceFactor2048Int
      (getSqrtRatioStoreAfterTickHiBit1024_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit2048Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit2048Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit2048Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit1024Int I)
      2048
      getSqrtRatioSourceFactor2048Int
      (getSqrtRatioSourceTickHiAfterBit1024Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit2048Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit2048Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit2048Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit1024Int I)
      2048
      getSqrtRatioSourceFactor2048Int
      (getSqrtRatioSourceTickHiAfterBit1024Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit1024Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor2048Int])
      (by norm_num [getSqrtRatioSourceFactor2048Int])

def getSqrtRatioSourceFactor4096Int : Int :=
  277268403626896220162999269216087595045

def getSqrtRatioSourceTickHiAfterBit4096Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit2048Int I)
    4096
    getSqrtRatioSourceFactor4096Int

def getSqrtRatioStoreAfterTickHiBit4096 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit2048 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit2048Int I)
    4096
    getSqrtRatioSourceFactor4096Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit4096
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit2048 I } evm
      (tickRatioStep 0x1000 0xd097f3bdfd2022b8845ad8f792aa5825)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit4096 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit2048 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit2048Int I)
    4096
    getSqrtRatioSourceFactor4096Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit2048_absTick I)
    (getSqrtRatioStoreAfterTickHiBit2048_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit2048Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit2048Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor4096Int])
    (by norm_num [getSqrtRatioSourceFactor4096Int])

def getSqrtRatioSourceTickHiPrefixThroughBit4096 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit2048 ++
    tickRatioStep 0x1000 0xd097f3bdfd2022b8845ad8f792aa5825

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit4096
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit4096
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit4096 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit2048 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit4096 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit4096_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit4096 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit4096, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit2048 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2048Int I)
      4096
      getSqrtRatioSourceFactor4096Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit2048_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit4096_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit4096 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit4096Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit4096, getSqrtRatioSourceTickHiAfterBit4096Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit2048 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2048Int I)
      4096
      getSqrtRatioSourceFactor4096Int
      (getSqrtRatioStoreAfterTickHiBit2048_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit4096Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit4096Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit4096Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2048Int I)
      4096
      getSqrtRatioSourceFactor4096Int
      (getSqrtRatioSourceTickHiAfterBit2048Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit4096Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit4096Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit4096Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2048Int I)
      4096
      getSqrtRatioSourceFactor4096Int
      (getSqrtRatioSourceTickHiAfterBit2048Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit2048Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor4096Int])
      (by norm_num [getSqrtRatioSourceFactor4096Int])

def getSqrtRatioSourceFactor8192Int : Int :=
  225923453940442621947126027127485391333

def getSqrtRatioSourceTickHiAfterBit8192Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit4096Int I)
    8192
    getSqrtRatioSourceFactor8192Int

def getSqrtRatioStoreAfterTickHiBit8192 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit4096 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit4096Int I)
    8192
    getSqrtRatioSourceFactor8192Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit8192
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit4096 I } evm
      (tickRatioStep 0x2000 0xa9f746462d870fdf8a65dc1f90e061e5)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit8192 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit4096 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit4096Int I)
    8192
    getSqrtRatioSourceFactor8192Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit4096_absTick I)
    (getSqrtRatioStoreAfterTickHiBit4096_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit4096Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit4096Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor8192Int])
    (by norm_num [getSqrtRatioSourceFactor8192Int])

def getSqrtRatioSourceTickHiPrefixThroughBit8192 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit4096 ++
    tickRatioStep 0x2000 0xa9f746462d870fdf8a65dc1f90e061e5

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit8192
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit8192
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit8192 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit4096 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit8192 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit8192_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit8192 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit8192, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit4096 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4096Int I)
      8192
      getSqrtRatioSourceFactor8192Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit4096_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit8192_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit8192 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit8192Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit8192, getSqrtRatioSourceTickHiAfterBit8192Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit4096 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4096Int I)
      8192
      getSqrtRatioSourceFactor8192Int
      (getSqrtRatioStoreAfterTickHiBit4096_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit8192Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit8192Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit8192Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4096Int I)
      8192
      getSqrtRatioSourceFactor8192Int
      (getSqrtRatioSourceTickHiAfterBit4096Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit8192Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit8192Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit8192Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4096Int I)
      8192
      getSqrtRatioSourceFactor8192Int
      (getSqrtRatioSourceTickHiAfterBit4096Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit4096Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor8192Int])
      (by norm_num [getSqrtRatioSourceFactor8192Int])

def getSqrtRatioSourceFactor16384Int : Int :=
  149997214084966997727330242082538205943

def getSqrtRatioSourceTickHiAfterBit16384Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit8192Int I)
    16384
    getSqrtRatioSourceFactor16384Int

def getSqrtRatioStoreAfterTickHiBit16384 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit8192 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit8192Int I)
    16384
    getSqrtRatioSourceFactor16384Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit16384
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit8192 I } evm
      (tickRatioStep 0x4000 0x70d869a156d2a1b890bb3df62baf32f7)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit16384 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit8192 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit8192Int I)
    16384
    getSqrtRatioSourceFactor16384Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit8192_absTick I)
    (getSqrtRatioStoreAfterTickHiBit8192_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit8192Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit8192Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor16384Int])
    (by norm_num [getSqrtRatioSourceFactor16384Int])

def getSqrtRatioSourceTickHiPrefixThroughBit16384 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit8192 ++
    tickRatioStep 0x4000 0x70d869a156d2a1b890bb3df62baf32f7

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit16384
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit16384
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit16384 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit8192 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit16384 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit16384_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit16384 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit16384, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit8192 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8192Int I)
      16384
      getSqrtRatioSourceFactor16384Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit8192_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit16384_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit16384 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit16384Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit16384, getSqrtRatioSourceTickHiAfterBit16384Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit8192 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8192Int I)
      16384
      getSqrtRatioSourceFactor16384Int
      (getSqrtRatioStoreAfterTickHiBit8192_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit16384Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit16384Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit16384Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8192Int I)
      16384
      getSqrtRatioSourceFactor16384Int
      (getSqrtRatioSourceTickHiAfterBit8192Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit16384Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit16384Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit16384Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8192Int I)
      16384
      getSqrtRatioSourceFactor16384Int
      (getSqrtRatioSourceTickHiAfterBit8192Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit8192Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor16384Int])
      (by norm_num [getSqrtRatioSourceFactor16384Int])

def getSqrtRatioSourceFactor32768Int : Int :=
  66119101136024775622716233608466517926

def getSqrtRatioSourceTickHiAfterBit32768Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit16384Int I)
    32768
    getSqrtRatioSourceFactor32768Int

def getSqrtRatioStoreAfterTickHiBit32768 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit16384 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit16384Int I)
    32768
    getSqrtRatioSourceFactor32768Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit32768
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit16384 I } evm
      (tickRatioStep 0x8000 0x31be135f97d08fd981231505542fcfa6)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit32768 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit16384 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit16384Int I)
    32768
    getSqrtRatioSourceFactor32768Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit16384_absTick I)
    (getSqrtRatioStoreAfterTickHiBit16384_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit16384Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit16384Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor32768Int])
    (by norm_num [getSqrtRatioSourceFactor32768Int])

def getSqrtRatioSourceTickHiPrefixThroughBit32768 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit16384 ++
    tickRatioStep 0x8000 0x31be135f97d08fd981231505542fcfa6

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit32768
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit32768
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit32768 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit16384 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit32768 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit32768_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit32768 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit32768, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit16384 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16384Int I)
      32768
      getSqrtRatioSourceFactor32768Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit16384_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit32768_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit32768 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit32768Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit32768, getSqrtRatioSourceTickHiAfterBit32768Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit16384 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16384Int I)
      32768
      getSqrtRatioSourceFactor32768Int
      (getSqrtRatioStoreAfterTickHiBit16384_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit32768Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit32768Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit32768Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16384Int I)
      32768
      getSqrtRatioSourceFactor32768Int
      (getSqrtRatioSourceTickHiAfterBit16384Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit32768Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit32768Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit32768Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16384Int I)
      32768
      getSqrtRatioSourceFactor32768Int
      (getSqrtRatioSourceTickHiAfterBit16384Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit16384Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor32768Int])
      (by norm_num [getSqrtRatioSourceFactor32768Int])

def getSqrtRatioSourceFactor65536Int : Int :=
  12847376061809297530290974190478138313

def getSqrtRatioSourceTickHiAfterBit65536Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit32768Int I)
    65536
    getSqrtRatioSourceFactor65536Int

def getSqrtRatioStoreAfterTickHiBit65536 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit32768 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit32768Int I)
    65536
    getSqrtRatioSourceFactor65536Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit65536
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit32768 I } evm
      (tickRatioStep 0x10000 0x9aa508b5b7a84e1c677de54f3e99bc9)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit65536 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit32768 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit32768Int I)
    65536
    getSqrtRatioSourceFactor65536Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit32768_absTick I)
    (getSqrtRatioStoreAfterTickHiBit32768_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit32768Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit32768Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor65536Int])
    (by norm_num [getSqrtRatioSourceFactor65536Int])

def getSqrtRatioSourceTickHiPrefixThroughBit65536 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit32768 ++
    tickRatioStep 0x10000 0x9aa508b5b7a84e1c677de54f3e99bc9

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit65536
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit65536
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit65536 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit32768 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit65536 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit65536_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit65536 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit65536, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit32768 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32768Int I)
      65536
      getSqrtRatioSourceFactor65536Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit32768_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit65536_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit65536 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit65536Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit65536, getSqrtRatioSourceTickHiAfterBit65536Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit32768 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32768Int I)
      65536
      getSqrtRatioSourceFactor65536Int
      (getSqrtRatioStoreAfterTickHiBit32768_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit65536Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit65536Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit65536Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32768Int I)
      65536
      getSqrtRatioSourceFactor65536Int
      (getSqrtRatioSourceTickHiAfterBit32768Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit65536Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit65536Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit65536Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32768Int I)
      65536
      getSqrtRatioSourceFactor65536Int
      (getSqrtRatioSourceTickHiAfterBit32768Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit32768Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor65536Int])
      (by norm_num [getSqrtRatioSourceFactor65536Int])

def getSqrtRatioSourceFactor131072Int : Int :=
  485053260817066172746253684029974020

def getSqrtRatioSourceTickHiAfterBit131072Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit65536Int I)
    131072
    getSqrtRatioSourceFactor131072Int

def getSqrtRatioStoreAfterTickHiBit131072 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit65536 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit65536Int I)
    131072
    getSqrtRatioSourceFactor131072Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit131072
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit65536 I } evm
      (tickRatioStep 0x20000 0x5d6af8dedb81196699c329225ee604)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit131072 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit65536 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit65536Int I)
    131072
    getSqrtRatioSourceFactor131072Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit65536_absTick I)
    (getSqrtRatioStoreAfterTickHiBit65536_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit65536Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit65536Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor131072Int])
    (by norm_num [getSqrtRatioSourceFactor131072Int])

def getSqrtRatioSourceTickHiPrefixThroughBit131072 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit65536 ++
    tickRatioStep 0x20000 0x5d6af8dedb81196699c329225ee604

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit131072
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit131072
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit131072 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit65536 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit131072 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit131072_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit131072 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit131072, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit65536 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit65536Int I)
      131072
      getSqrtRatioSourceFactor131072Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit65536_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit131072_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit131072 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit131072Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit131072, getSqrtRatioSourceTickHiAfterBit131072Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit65536 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit65536Int I)
      131072
      getSqrtRatioSourceFactor131072Int
      (getSqrtRatioStoreAfterTickHiBit65536_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit131072Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit131072Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit131072Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit65536Int I)
      131072
      getSqrtRatioSourceFactor131072Int
      (getSqrtRatioSourceTickHiAfterBit65536Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit131072Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit131072Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit131072Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit65536Int I)
      131072
      getSqrtRatioSourceFactor131072Int
      (getSqrtRatioSourceTickHiAfterBit65536Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit65536Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor131072Int])
      (by norm_num [getSqrtRatioSourceFactor131072Int])

def getSqrtRatioSourceFactor262144Int : Int :=
  691415978906521570653435304214168

def getSqrtRatioSourceTickHiAfterBit262144Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit131072Int I)
    262144
    getSqrtRatioSourceFactor262144Int

def getSqrtRatioStoreAfterTickHiBit262144 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit131072 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit131072Int I)
    262144
    getSqrtRatioSourceFactor262144Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit262144
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit131072 I } evm
      (tickRatioStep 0x40000 0x2216e584f5fa1ea926041bedfe98)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit262144 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit131072 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit131072Int I)
    262144
    getSqrtRatioSourceFactor262144Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit131072_absTick I)
    (getSqrtRatioStoreAfterTickHiBit131072_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit131072Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit131072Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor262144Int])
    (by norm_num [getSqrtRatioSourceFactor262144Int])

def getSqrtRatioSourceTickHiPrefixThroughBit262144 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit131072 ++
    tickRatioStep 0x40000 0x2216e584f5fa1ea926041bedfe98

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit262144
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit262144
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit262144 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit131072 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit262144 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit262144_absTick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit262144 I).get? "absTick" =
      some (getSqrtRatioSourceTickHiAbsTickValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit262144, getSqrtRatioSourceTickHiAbsTickValue] using
    getSqrtRatioSourceTickRatioStepStoreAfter_absTick
      (getSqrtRatioStoreAfterTickHiBit131072 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit131072Int I)
      262144
      getSqrtRatioSourceFactor262144Int
      (by
        simpa [getSqrtRatioSourceTickHiAbsTickValue] using
          getSqrtRatioStoreAfterTickHiBit131072_absTick I)

theorem getSqrtRatioStoreAfterTickHiBit262144_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit262144 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit262144Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit262144, getSqrtRatioSourceTickHiAfterBit262144Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit131072 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit131072Int I)
      262144
      getSqrtRatioSourceFactor262144Int
      (getSqrtRatioStoreAfterTickHiBit131072_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit262144Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit262144Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit262144Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit131072Int I)
      262144
      getSqrtRatioSourceFactor262144Int
      (getSqrtRatioSourceTickHiAfterBit131072Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit262144Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit262144Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit262144Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit131072Int I)
      262144
      getSqrtRatioSourceFactor262144Int
      (getSqrtRatioSourceTickHiAfterBit131072Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit131072Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor262144Int])
      (by norm_num [getSqrtRatioSourceFactor262144Int])

def getSqrtRatioSourceFactor524288Int : Int :=
  1404880482679654955896180642

def getSqrtRatioSourceTickHiAfterBit524288Int (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceTickRatioStepRatioInt
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit262144Int I)
    524288
    getSqrtRatioSourceFactor524288Int

def getSqrtRatioStoreAfterTickHiBit524288 (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceTickRatioStepStoreAfter
    (getSqrtRatioStoreAfterTickHiBit262144 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit262144Int I)
    524288
    getSqrtRatioSourceFactor524288Int

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit524288
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit262144 I } evm
      (tickRatioStep 0x80000 0x48a170391f7dc42444e8fa2)
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit524288 I }
        evm) := by
  exact getSqrtRatioSourceTickRatioStepExecOfBounded (v := v) evm
    (getSqrtRatioStoreAfterTickHiBit262144 I)
    (getSqrtRatioSourceTickHiAbsTickInt I)
    (getSqrtRatioSourceTickHiAfterBit262144Int I)
    524288
    getSqrtRatioSourceFactor524288Int
    (by
      simpa [getSqrtRatioSourceTickHiAbsTickValue] using
        getSqrtRatioStoreAfterTickHiBit262144_absTick I)
    (getSqrtRatioStoreAfterTickHiBit262144_ratio I)
    (getSqrtRatioSourceTickHiAbsTickInt_nonneg I)
    (getSqrtRatioSourceTickHiAbsTickInt_lt_wordModulus I hrange)
    (by norm_num)
    (by norm_num [EVM.wordModulus, EVM.twoPow])
    (getSqrtRatioSourceTickHiAfterBit262144Int_nonneg I)
    (getSqrtRatioSourceTickHiAfterBit262144Int_le_q128 I)
    (by norm_num [getSqrtRatioSourceFactor524288Int])
    (by norm_num [getSqrtRatioSourceFactor524288Int])

def getSqrtRatioSourceTickHiPrefixThroughBit524288 : List Stmt :=
  getSqrtRatioSourceTickHiPrefixThroughBit262144 ++
    tickRatioStep 0x80000 0x48a170391f7dc42444e8fa2

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit524288
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272) :
    ExecBlock (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I } evm
      getSqrtRatioSourceTickHiPrefixThroughBit524288
      (.ok { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit524288 I }
        evm) := by
  exact execBlock_append
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit262144 evm I hrange)
    (uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBit524288 evm I hrange)

theorem getSqrtRatioStoreAfterTickHiBit2048_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit2048 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit2048] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit1024 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit1024Int I)
      2048
      getSqrtRatioSourceFactor2048Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit1024_tick I)

theorem getSqrtRatioStoreAfterTickHiBit4096_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit4096 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit4096] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit2048 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit2048Int I)
      4096
      getSqrtRatioSourceFactor4096Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit2048_tick I)

theorem getSqrtRatioStoreAfterTickHiBit8192_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit8192 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit8192] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit4096 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit4096Int I)
      8192
      getSqrtRatioSourceFactor8192Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit4096_tick I)

theorem getSqrtRatioStoreAfterTickHiBit16384_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit16384 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit16384] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit8192 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit8192Int I)
      16384
      getSqrtRatioSourceFactor16384Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit8192_tick I)

theorem getSqrtRatioStoreAfterTickHiBit32768_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit32768 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit32768] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit16384 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit16384Int I)
      32768
      getSqrtRatioSourceFactor32768Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit16384_tick I)

theorem getSqrtRatioStoreAfterTickHiBit65536_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit65536 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit65536] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit32768 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit32768Int I)
      65536
      getSqrtRatioSourceFactor65536Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit32768_tick I)

theorem getSqrtRatioStoreAfterTickHiBit131072_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit131072 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit131072] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit65536 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit65536Int I)
      131072
      getSqrtRatioSourceFactor131072Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit65536_tick I)

theorem getSqrtRatioStoreAfterTickHiBit262144_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit262144 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit262144] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit131072 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit131072Int I)
      262144
      getSqrtRatioSourceFactor262144Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit131072_tick I)

theorem getSqrtRatioStoreAfterTickHiBit524288_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit524288 I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiBit524288] using
    getSqrtRatioSourceTickRatioStepStoreAfter_preserve_of_ne
      (getSqrtRatioStoreAfterTickHiBit262144 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit262144Int I)
      524288
      getSqrtRatioSourceFactor524288Int
      "tick"
      (by decide) |>.trans (getSqrtRatioStoreAfterTickHiBit262144_tick I)

theorem getSqrtRatioStoreAfterTickHiBit524288_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiBit524288 I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiAfterBit524288Int I)) := by
  simpa [getSqrtRatioStoreAfterTickHiBit524288, getSqrtRatioSourceTickHiAfterBit524288Int] using
    getSqrtRatioSourceTickRatioStepStoreAfter_ratio
      (getSqrtRatioStoreAfterTickHiBit262144 I)
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit262144Int I)
      524288
      getSqrtRatioSourceFactor524288Int
      (getSqrtRatioStoreAfterTickHiBit262144_ratio I)

theorem getSqrtRatioSourceTickHiAfterBit524288Int_nonneg (I : ExecutionEnv) :
    0 ≤ getSqrtRatioSourceTickHiAfterBit524288Int I := by
  simpa [getSqrtRatioSourceTickHiAfterBit524288Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_nonneg
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit262144Int I)
      524288
      getSqrtRatioSourceFactor524288Int
      (getSqrtRatioSourceTickHiAfterBit262144Int_nonneg I)

theorem getSqrtRatioSourceTickHiAfterBit524288Int_le_q128 (I : ExecutionEnv) :
    getSqrtRatioSourceTickHiAfterBit524288Int I ≤ 2 ^ (128 : Nat) := by
  simpa [getSqrtRatioSourceTickHiAfterBit524288Int] using
    getSqrtRatioSourceTickRatioStepRatioInt_le_q128
      (getSqrtRatioSourceTickHiAbsTickInt I)
      (getSqrtRatioSourceTickHiAfterBit262144Int I)
      524288
      getSqrtRatioSourceFactor524288Int
      (getSqrtRatioSourceTickHiAfterBit262144Int_nonneg I)
      (getSqrtRatioSourceTickHiAfterBit262144Int_le_q128 I)
      (by norm_num [getSqrtRatioSourceFactor524288Int])
      (by norm_num [getSqrtRatioSourceFactor524288Int])

def getSqrtRatioSourceFinalRatioIntOf (tick ratio : Int) : Int :=
  if 0 < tick then (2 ^ (256 : Nat) - 1) / ratio else ratio

def getSqrtRatioSourceFinalRatioStoreOf (S : Store) (tick ratio : Int) : Store :=
  if 0 < tick then S.insert "ratio" (.int (getSqrtRatioSourceFinalRatioIntOf tick ratio))
  else S

def getSqrtRatioSourceReturnExpr : Expr :=
  addE (shrE (.var "ratio") shift32)
    (.ite (eqE (modE (.var "ratio") uint32Modulus) (.intLit 0))
      (.intLit 0) (.intLit 1))

def getSqrtRatioSourceReturnIntOf (ratio : Int) : Int :=
  ((ratio.toNat / 2 ^ (32 : Nat) : Nat) : Int) +
    if Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0 then 0 else 1

def getSqrtRatioSourceReturnValueOf (ratio : Int) : Value :=
  .int (getSqrtRatioSourceReturnIntOf ratio)

def getSqrtRatioSourceTailBlock : List Stmt :=
  [ Stmt.ite (gtE (.var "tick") (.intLit 0))
      [ .assign .localVar (varRef "ratio") (divE uint256MaxExpr (.var "ratio")) ]
      [],
    .return [getSqrtRatioSourceReturnExpr] ]

def getSqrtRatioSourceTickHiFinalRatioInt (I : ExecutionEnv) : Int :=
  getSqrtRatioSourceFinalRatioIntOf
    (getTickSourceTickHiInt I)
    (getSqrtRatioSourceTickHiAfterBit524288Int I)

def getSqrtRatioStoreAfterTickHiFinalRatio (I : ExecutionEnv) : Store :=
  getSqrtRatioSourceFinalRatioStoreOf
    (getSqrtRatioStoreAfterTickHiBit524288 I)
    (getTickSourceTickHiInt I)
    (getSqrtRatioSourceTickHiAfterBit524288Int I)

theorem getSqrtRatioSourceFinalRatioStoreOf_ratio
    (S : Store) (tick ratio : Int)
    (hratio : S.get? "ratio" = some (.int ratio)) :
    (getSqrtRatioSourceFinalRatioStoreOf S tick ratio).get? "ratio" =
      some (.int (getSqrtRatioSourceFinalRatioIntOf tick ratio)) := by
  unfold getSqrtRatioSourceFinalRatioStoreOf
  by_cases hpos : 0 < tick
  · rw [if_pos hpos, store_get_self]
  · rw [if_neg hpos]
    simpa [getSqrtRatioSourceFinalRatioIntOf, hpos] using hratio

theorem getSqrtRatioSourceFinalRatioStoreOf_tick
    (S : Store) (tick ratio : Int) (value : Value)
    (htick : S.get? "tick" = some value) :
    (getSqrtRatioSourceFinalRatioStoreOf S tick ratio).get? "tick" = some value := by
  unfold getSqrtRatioSourceFinalRatioStoreOf
  by_cases hpos : 0 < tick
  · rw [if_pos hpos]
    rw [store_get_ne S (k := "ratio") (a := "tick")
      (.int (getSqrtRatioSourceFinalRatioIntOf tick ratio)) (by decide)]
    exact htick
  · rw [if_neg hpos]
    exact htick

theorem getSqrtRatioStoreAfterTickHiFinalRatio_ratio (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiFinalRatio I).get? "ratio" =
      some (.int (getSqrtRatioSourceTickHiFinalRatioInt I)) := by
  simpa [getSqrtRatioStoreAfterTickHiFinalRatio, getSqrtRatioSourceTickHiFinalRatioInt] using
    getSqrtRatioSourceFinalRatioStoreOf_ratio
      (getSqrtRatioStoreAfterTickHiBit524288 I)
      (getTickSourceTickHiInt I)
      (getSqrtRatioSourceTickHiAfterBit524288Int I)
      (getSqrtRatioStoreAfterTickHiBit524288_ratio I)

theorem getSqrtRatioStoreAfterTickHiFinalRatio_tick (I : ExecutionEnv) :
    (getSqrtRatioStoreAfterTickHiFinalRatio I).get? "tick" =
      some (getTickSourceTickHiValue I) := by
  simpa [getSqrtRatioStoreAfterTickHiFinalRatio] using
    getSqrtRatioSourceFinalRatioStoreOf_tick
      (getSqrtRatioStoreAfterTickHiBit524288 I)
      (getTickSourceTickHiInt I)
      (getSqrtRatioSourceTickHiAfterBit524288Int I)
      (getTickSourceTickHiValue I)
      (getSqrtRatioStoreAfterTickHiBit524288_tick I)

theorem evalExpr_getSqrtRatio_tickPosCond
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (tick : Int)
    (htick : S.get? "tick" = some (.int tick)) :
    evalExpr? (config v) { contract := contract v, locals := S } evm
      (gtE (.var "tick") (.intLit 0)) = .ok (.bool (0 < tick)) := by
  unfold gtE
  have hvar :=
    evalExpr_getSqrtRatio_var_of_get (v := v) evm S "tick" (.int tick) htick
  simp only [evalExpr?, hvar, EvalResult.bind, bind, pure, evalBinaryOp?]

theorem evalExpr_getSqrtRatio_finalRatioAssign
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (tick ratio : Int)
    (hratio : S.get? "ratio" = some (.int ratio))
    (hden : ratio ≠ 0) (hpos : 0 < tick) :
    evalExpr? (config v) { contract := contract v, locals := S } evm
      (divE uint256MaxExpr (.var "ratio")) =
      .ok (.int (getSqrtRatioSourceFinalRatioIntOf tick ratio)) := by
  unfold divE uint256MaxExpr getSqrtRatioSourceFinalRatioIntOf
  have hvar :=
    evalExpr_getSqrtRatio_var_of_get (v := v) evm S "ratio" (.int ratio) hratio
  simp only [evalExpr?, hvar, EvalResult.bind, bind, pure, evalBinaryOp?]
  simp [hpos, hden]

theorem getSqrtRatioSourceFinalRatioIntOf_nonneg (tick ratio : Int)
    (hratio0 : 0 ≤ ratio) :
    0 ≤ getSqrtRatioSourceFinalRatioIntOf tick ratio := by
  unfold getSqrtRatioSourceFinalRatioIntOf
  by_cases hpos : 0 < tick
  · rw [if_pos hpos]
    exact Int.ediv_nonneg (by norm_num) hratio0
  · rw [if_neg hpos]
    exact hratio0

theorem getSqrtRatioSourceFinalRatioIntOf_lt_wordModulus (tick ratio : Int)
    (hratioLt : ratio < (EVM.wordModulus : Int)) :
    getSqrtRatioSourceFinalRatioIntOf tick ratio < (EVM.wordModulus : Int) := by
  unfold getSqrtRatioSourceFinalRatioIntOf
  by_cases hpos : 0 < tick
  · rw [if_pos hpos]
    exact lt_of_le_of_lt
      (Int.ediv_le_self ratio (by norm_num : 0 ≤ (2 ^ (256 : Nat) - 1 : Int)))
      (by norm_num [EVM.wordModulus, EVM.twoPow])
  · rw [if_neg hpos]
    exact hratioLt

theorem evalExpr_getSqrtRatio_returnExpr
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (ratio : Int)
    (hratio : S.get? "ratio" = some (.int ratio))
    (hratio0 : 0 ≤ ratio) (hratioLt : ratio < (EVM.wordModulus : Int)) :
    evalExpr? (config v) { contract := contract v, locals := S } evm
      getSqrtRatioSourceReturnExpr = .ok (getSqrtRatioSourceReturnValueOf ratio) := by
  unfold getSqrtRatioSourceReturnExpr getSqrtRatioSourceReturnValueOf
    getSqrtRatioSourceReturnIntOf addE shrE eqE modE shift32 uint32Modulus
  have hvar :=
    evalExpr_getSqrtRatio_var_of_get (v := v) evm S "ratio" (.int ratio) hratio
  have hshr :
      evalBinaryOp? .shr (.int ratio) (.int 32) =
        .ok (.int (ratio.toNat / 2 ^ (32 : Nat))) := by
    simpa using evalBinaryOp_int_shr_ok (x := ratio) (s := 32) hratio0 hratioLt
      (by norm_num) (by norm_num)
  by_cases hbeq :
      (Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0) = true
  · norm_num at hbeq
    have hmod : ratio % (4294967296 : Int) = 0 :=
      Int.emod_eq_zero_of_dvd hbeq
    have hbeqValue :
        (Value.int (ratio % (4294967296 : Int)) == Value.int 0) = true := by
      simp [hmod]
    simp only [evalExpr?, hvar, EvalResult.bind, bind, pure]
    rw [hshr]
    simp [evalBinaryOp?, hmod, hratio0]
  · have hbeqFalse :
        (Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0) = false := by
      cases h : (Value.int (ratio % (2 ^ (32 : Nat) : Int)) == Value.int 0) <;>
        simp_all
    norm_num at hbeqFalse
    have hmodNe : ratio % (4294967296 : Int) ≠ 0 := by
      intro hmod
      exact hbeqFalse (Int.dvd_of_emod_eq_zero hmod)
    have hbeqValue :
        (Value.int (ratio % (4294967296 : Int)) == Value.int 0) = false := by
      cases h : (Value.int (ratio % (4294967296 : Int)) == Value.int 0) <;>
        simp_all
    simp only [evalExpr?, hvar, EvalResult.bind, bind, pure]
    rw [hshr]
    simp [evalBinaryOp?, hbeqValue, hratio0]

theorem uniswapV3PoolGetSqrtRatioAtTickSourceFinalRatioOf
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (tick ratio : Int)
    (htick : S.get? "tick" = some (.int tick))
    (hratio : S.get? "ratio" = some (.int ratio))
    (hden : ratio ≠ 0) :
    ExecBlock (config v) { contract := contract v, locals := S } evm
      [ Stmt.ite (gtE (.var "tick") (.intLit 0))
          [ .assign .localVar (varRef "ratio") (divE uint256MaxExpr (.var "ratio")) ]
          [] ]
      (.ok
        { contract := contract v,
          locals := getSqrtRatioSourceFinalRatioStoreOf S tick ratio }
        evm) := by
  by_cases hpos : 0 < tick
  · refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
    · rw [evalExpr_getSqrtRatio_tickPosCond (v := v) evm S tick htick]
      simp [hpos]
    · refine ExecBlock.consNormal
        (ExecStmt.assign
          (evalExpr_getSqrtRatio_finalRatioAssign (v := v) evm S tick ratio hratio hden hpos)
          ?_)
        ExecBlock.nil
      unfold assignStorageRef?
      simp only [varRef]
      rw [hratio]
      simp [updateLocalPath?, getSqrtRatioSourceFinalRatioStoreOf,
        getSqrtRatioSourceFinalRatioIntOf, hpos, EvalResult.bind, bind, pure]
  · refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ?_) ExecBlock.nil
    · rw [evalExpr_getSqrtRatio_tickPosCond (v := v) evm S tick htick]
      simp [hpos]
    · simpa [getSqrtRatioSourceFinalRatioStoreOf, hpos] using
        (ExecBlock.nil :
          ExecBlock (config v) { contract := contract v, locals := S } evm []
            (.ok { contract := contract v, locals := S } evm))

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTailOf
    {v : PoolImmutables} (evm : EVM.State) (S : Store) (tick ratio : Int)
    (htick : S.get? "tick" = some (.int tick))
    (hratio : S.get? "ratio" = some (.int ratio))
    (hratio0 : 0 ≤ ratio) (hratioLt : ratio < (EVM.wordModulus : Int))
    (hden : ratio ≠ 0) :
    ExecBlock (config v) { contract := contract v, locals := S } evm
      getSqrtRatioSourceTailBlock
      (.returned
        { contract := contract v,
          locals := getSqrtRatioSourceFinalRatioStoreOf S tick ratio }
        evm (some [getSqrtRatioSourceReturnValueOf
          (getSqrtRatioSourceFinalRatioIntOf tick ratio)])) := by
  unfold getSqrtRatioSourceTailBlock
  have hfinal :=
    uniswapV3PoolGetSqrtRatioAtTickSourceFinalRatioOf (v := v) evm S tick ratio
      htick hratio hden
  have hratioFinal :=
    getSqrtRatioSourceFinalRatioStoreOf_ratio S tick ratio hratio
  have hfinal0 :
      0 ≤ getSqrtRatioSourceFinalRatioIntOf tick ratio :=
    getSqrtRatioSourceFinalRatioIntOf_nonneg tick ratio hratio0
  have hfinalLt :
      getSqrtRatioSourceFinalRatioIntOf tick ratio < (EVM.wordModulus : Int) :=
    getSqrtRatioSourceFinalRatioIntOf_lt_wordModulus tick ratio hratioLt
  have hret :=
    evalExpr_getSqrtRatio_returnExpr (v := v) evm
      (getSqrtRatioSourceFinalRatioStoreOf S tick ratio)
      (getSqrtRatioSourceFinalRatioIntOf tick ratio)
      hratioFinal hfinal0 hfinalLt
  exact execBlock_append hfinal
    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hret)))

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiTail
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hden : getSqrtRatioSourceTickHiAfterBit524288Int I ≠ 0) :
    ExecBlock (config v)
      { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit524288 I } evm
      getSqrtRatioSourceTailBlock
      (.returned { contract := contract v, locals := getSqrtRatioStoreAfterTickHiFinalRatio I }
        evm (some [getSqrtRatioSourceReturnValueOf
          (getSqrtRatioSourceTickHiFinalRatioInt I)])) := by
  have htick :
      (getSqrtRatioStoreAfterTickHiBit524288 I).get? "tick" =
        some (.int (getTickSourceTickHiInt I)) := by
    simpa [getTickSourceTickHiValue] using getSqrtRatioStoreAfterTickHiBit524288_tick I
  have hratio :=
    getSqrtRatioStoreAfterTickHiBit524288_ratio I
  have hratioLt :
      getSqrtRatioSourceTickHiAfterBit524288Int I < (EVM.wordModulus : Int) := by
    exact lt_of_le_of_lt
      (getSqrtRatioSourceTickHiAfterBit524288Int_le_q128 I)
      (by norm_num [EVM.wordModulus, EVM.twoPow])
  simpa [getSqrtRatioStoreAfterTickHiFinalRatio, getSqrtRatioSourceTickHiFinalRatioInt]
    using
      uniswapV3PoolGetSqrtRatioAtTickSourceTailOf (v := v) evm
        (getSqrtRatioStoreAfterTickHiBit524288 I)
        (getTickSourceTickHiInt I)
        (getSqrtRatioSourceTickHiAfterBit524288Int I)
        htick hratio
        (getSqrtRatioSourceTickHiAfterBit524288Int_nonneg I)
        hratioLt
        hden

theorem getSqrtRatioAtTickFunction_body_eq_tickHiSourceBlocks :
    getSqrtRatioAtTickFunction.body =
      getSqrtRatioSourceTickHiPrefixThroughBit524288 ++ getSqrtRatioSourceTailBlock := by
  rfl

theorem uniswapV3PoolGetSqrtRatioAtTickSourceTickHiBodyOfReturnEq
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hrange : getSqrtRatioSourceTickHiAbsTickInt I ≤ 887272)
    (hden : getSqrtRatioSourceTickHiAfterBit524288Int I ≠ 0)
    (hret :
      getSqrtRatioSourceReturnValueOf (getSqrtRatioSourceTickHiFinalRatioInt I) =
        getTickSourceSqrtRatioAtTickHiValue I) :
    ExecFuncBody (config v)
      { contract := contract v, locals := getTickStoreForSqrtRatioAtTickHiCall I }
      evm getSqrtRatioAtTickFunction.body
      (.returned { contract := contract v, locals := getSqrtRatioStoreAfterTickHiFinalRatio I }
        evm (some [getTickSourceSqrtRatioAtTickHiValue I])) := by
  refine ExecFuncBody.execBlockRet ?_
  rw [getSqrtRatioAtTickFunction_body_eq_tickHiSourceBlocks]
  have hprefix :=
    uniswapV3PoolGetSqrtRatioAtTickSourceTickHiThroughBit524288 (v := v) evm I hrange
  have htail :=
    uniswapV3PoolGetSqrtRatioAtTickSourceTickHiTail (v := v) evm I hden
  simpa [hret] using execBlock_append hprefix htail

set_option maxRecDepth 20000 in
theorem evalExpr_getSqrtRatio_tickVar_afterBit524288 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit524288 I }
        evm (.var "tick") = .ok (getTickSourceTickHiValue I) := by
  exact evalExpr_getSqrtRatio_var_of_get evm
    (getSqrtRatioStoreAfterTickHiBit524288 I)
    "tick"
    (getTickSourceTickHiValue I)
    (getSqrtRatioStoreAfterTickHiBit524288_tick I)

set_option maxRecDepth 20000 in
theorem evalExpr_getSqrtRatio_tickPosCond_afterBit524288 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit524288 I }
        evm (gtE (.var "tick") (.intLit 0)) =
      .ok (.bool (0 < getTickSourceTickHiInt I)) := by
  unfold gtE
  simp only [evalExpr?, evalExpr_getSqrtRatio_tickVar_afterBit524288, EvalResult.bind,
    bind, pure, evalBinaryOp?]
  simp [getTickSourceTickHiValue]

set_option maxRecDepth 20000 in
theorem evalExpr_getSqrtRatio_ratioVar_afterBit524288 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit524288 I }
        evm (.var "ratio") = .ok (.int (getSqrtRatioSourceTickHiAfterBit524288Int I)) := by
  exact evalExpr_getSqrtRatio_var_of_get evm
    (getSqrtRatioStoreAfterTickHiBit524288 I)
    "ratio"
    (.int (getSqrtRatioSourceTickHiAfterBit524288Int I))
    (getSqrtRatioStoreAfterTickHiBit524288_ratio I)

set_option maxRecDepth 20000 in
theorem evalExpr_getSqrtRatio_finalRatioAssign_afterBit524288
    {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv)
    (hden : getSqrtRatioSourceTickHiAfterBit524288Int I ≠ 0)
    (hpos : 0 < getTickSourceTickHiInt I) :
    evalExpr? (config v)
        { contract := contract v, locals := getSqrtRatioStoreAfterTickHiBit524288 I }
        evm (divE uint256MaxExpr (.var "ratio")) =
      .ok (.int (getSqrtRatioSourceTickHiFinalRatioInt I)) := by
  unfold divE uint256MaxExpr getSqrtRatioSourceTickHiFinalRatioInt
    getSqrtRatioSourceFinalRatioIntOf
  simp only [evalExpr?, evalExpr_getSqrtRatio_ratioVar_afterBit524288, EvalResult.bind,
    bind, pure, evalBinaryOp?]
  simp [hpos, hden]

end Benchmarks.UniswapV3Pool
