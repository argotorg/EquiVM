import Benchmarks.UniswapV3Pool.InitializeSourceGetTickLogStep60

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def getTickSourceLog2AfterStep (log2 : Int) (r bit : Nat) : Int :=
  getTickSourceLogStepLog2AfterInt log2 r bit

def getTickSourceLogRAfterStep (r : Nat) : Nat :=
  getTickSourceLogStepRAfterNat r

def getTickStoreAfterLogStep (S : Store) (log2 : Int) (r bit : Nat) : Store :=
  getTickSourceLogStepStoreAfter S log2 r bit

theorem getTickStoreAfterLogStep_r (S : Store) (log2 : Int) (r bit : Nat) :
    (getTickStoreAfterLogStep S log2 r bit).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfterStep r))) := by
  simpa [getTickStoreAfterLogStep, getTickSourceLogRAfterStep,
    getTickSourceLogStepRAfterValue]
    using getTickSourceLogStepStoreAfter_r S log2 r bit

theorem getTickStoreAfterLogStep_log2 (S : Store) (log2 : Int) (r bit : Nat) :
    (getTickStoreAfterLogStep S log2 r bit).get? "log_2" =
      some (Value.int (getTickSourceLog2AfterStep log2 r bit)) := by
  simpa [getTickStoreAfterLogStep, getTickSourceLog2AfterStep,
    getTickSourceLogStepLog2AfterValue]
    using getTickSourceLogStepStoreAfter_log2 S log2 r bit

def getTickSourceLog2After59Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After60Int I) (getTickSourceLogRAfter60Nat I) 59

def getTickSourceLogRAfter59Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter60Nat I)

def getTickStoreAfterLogStep59 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep60 I)
    (getTickSourceLog2After60Int I) (getTickSourceLogRAfter60Nat I) 59

theorem getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter59Nat I * getTickSourceLogRAfter59Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter59Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter60Nat I)
    (getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep60_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep60 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter60Nat I))) := by
  simpa [getTickStoreAfterLogStep60, getTickSourceLogRAfter60Nat,
    getTickSourceLogStepRAfterValue]
    using getTickSourceLogStepStoreAfter_r (getTickStoreAfterLogStep61 I)
      (getTickSourceLog2After61Int I) (getTickSourceLogRAfter61Nat I) 60

theorem getTickStoreAfterLogStep60_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep60 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After60Int I)) := by
  simpa [getTickStoreAfterLogStep60, getTickSourceLog2After60Int,
    getTickSourceLogStepLog2AfterValue]
    using getTickSourceLogStepStoreAfter_log2 (getTickStoreAfterLogStep61 I)
      (getTickSourceLog2After61Int I) (getTickSourceLogRAfter61Nat I) 60

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep59 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I }
      evm (logStep 59 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep59 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep60 I)
    (getTickSourceLog2After60Int I) (getTickSourceLogRAfter60Nat I) 59
    (getTickStoreAfterLogStep60_r I)
    (getTickStoreAfterLogStep60_log2 I)
    (getTickSourceLogRAfter60Nat_mul_self_lt_wordModulus I)

def getTickSourceLog2After58Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After59Int I) (getTickSourceLogRAfter59Nat I) 58

def getTickSourceLogRAfter58Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter59Nat I)

def getTickStoreAfterLogStep58 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep59 I)
    (getTickSourceLog2After59Int I) (getTickSourceLogRAfter59Nat I) 58

theorem getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter58Nat I * getTickSourceLogRAfter58Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter58Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter59Nat I)
    (getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep59_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep59 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter59Nat I))) := by
  simpa [getTickStoreAfterLogStep59, getTickSourceLogRAfter59Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep60 I)
      (getTickSourceLog2After60Int I) (getTickSourceLogRAfter60Nat I) 59

theorem getTickStoreAfterLogStep59_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep59 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After59Int I)) := by
  simpa [getTickStoreAfterLogStep59, getTickSourceLog2After59Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep60 I)
      (getTickSourceLog2After60Int I) (getTickSourceLogRAfter60Nat I) 59

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep58 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep59 I }
      evm (logStep 58 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep58 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep59 I)
    (getTickSourceLog2After59Int I) (getTickSourceLogRAfter59Nat I) 58
    (getTickStoreAfterLogStep59_r I)
    (getTickStoreAfterLogStep59_log2 I)
    (getTickSourceLogRAfter59Nat_mul_self_lt_wordModulus I)

def getTickSourceLog2After57Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After58Int I) (getTickSourceLogRAfter58Nat I) 57

def getTickSourceLogRAfter57Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter58Nat I)

def getTickStoreAfterLogStep57 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep58 I)
    (getTickSourceLog2After58Int I) (getTickSourceLogRAfter58Nat I) 57

theorem getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter57Nat I * getTickSourceLogRAfter57Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter57Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter58Nat I)
    (getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep58_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep58 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter58Nat I))) := by
  simpa [getTickStoreAfterLogStep58, getTickSourceLogRAfter58Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep59 I)
      (getTickSourceLog2After59Int I) (getTickSourceLogRAfter59Nat I) 58

theorem getTickStoreAfterLogStep58_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep58 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After58Int I)) := by
  simpa [getTickStoreAfterLogStep58, getTickSourceLog2After58Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep59 I)
      (getTickSourceLog2After59Int I) (getTickSourceLogRAfter59Nat I) 58

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep57 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep58 I }
      evm (logStep 57 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep57 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep58 I)
    (getTickSourceLog2After58Int I) (getTickSourceLogRAfter58Nat I) 57
    (getTickStoreAfterLogStep58_r I)
    (getTickStoreAfterLogStep58_log2 I)
    (getTickSourceLogRAfter58Nat_mul_self_lt_wordModulus I)

def getTickSourceLog2After56Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After57Int I) (getTickSourceLogRAfter57Nat I) 56

def getTickSourceLogRAfter56Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter57Nat I)

def getTickStoreAfterLogStep56 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep57 I)
    (getTickSourceLog2After57Int I) (getTickSourceLogRAfter57Nat I) 56

theorem getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter56Nat I * getTickSourceLogRAfter56Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter56Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter57Nat I)
    (getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep57_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep57 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter57Nat I))) := by
  simpa [getTickStoreAfterLogStep57, getTickSourceLogRAfter57Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep58 I)
      (getTickSourceLog2After58Int I) (getTickSourceLogRAfter58Nat I) 57

theorem getTickStoreAfterLogStep57_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep57 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After57Int I)) := by
  simpa [getTickStoreAfterLogStep57, getTickSourceLog2After57Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep58 I)
      (getTickSourceLog2After58Int I) (getTickSourceLogRAfter58Nat I) 57

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep56 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep57 I }
      evm (logStep 56 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep56 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep57 I)
    (getTickSourceLog2After57Int I) (getTickSourceLogRAfter57Nat I) 56
    (getTickStoreAfterLogStep57_r I)
    (getTickStoreAfterLogStep57_log2 I)
    (getTickSourceLogRAfter57Nat_mul_self_lt_wordModulus I)

def getTickSourceLog2After55Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After56Int I) (getTickSourceLogRAfter56Nat I) 55

def getTickSourceLogRAfter55Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter56Nat I)

def getTickStoreAfterLogStep55 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep56 I)
    (getTickSourceLog2After56Int I) (getTickSourceLogRAfter56Nat I) 55

theorem getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter55Nat I * getTickSourceLogRAfter55Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter55Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter56Nat I)
    (getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep56_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep56 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter56Nat I))) := by
  simpa [getTickStoreAfterLogStep56, getTickSourceLogRAfter56Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep57 I)
      (getTickSourceLog2After57Int I) (getTickSourceLogRAfter57Nat I) 56

theorem getTickStoreAfterLogStep56_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep56 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After56Int I)) := by
  simpa [getTickStoreAfterLogStep56, getTickSourceLog2After56Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep57 I)
      (getTickSourceLog2After57Int I) (getTickSourceLogRAfter57Nat I) 56

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep55 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep56 I }
      evm (logStep 55 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep55 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep56 I)
    (getTickSourceLog2After56Int I) (getTickSourceLogRAfter56Nat I) 55
    (getTickStoreAfterLogStep56_r I)
    (getTickStoreAfterLogStep56_log2 I)
    (getTickSourceLogRAfter56Nat_mul_self_lt_wordModulus I)

def getTickSourceLog2After54Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After55Int I) (getTickSourceLogRAfter55Nat I) 54

def getTickSourceLogRAfter54Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter55Nat I)

def getTickStoreAfterLogStep54 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep55 I)
    (getTickSourceLog2After55Int I) (getTickSourceLogRAfter55Nat I) 54

theorem getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter54Nat I * getTickSourceLogRAfter54Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter54Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter55Nat I)
    (getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep55_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep55 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter55Nat I))) := by
  simpa [getTickStoreAfterLogStep55, getTickSourceLogRAfter55Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep56 I)
      (getTickSourceLog2After56Int I) (getTickSourceLogRAfter56Nat I) 55

theorem getTickStoreAfterLogStep55_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep55 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After55Int I)) := by
  simpa [getTickStoreAfterLogStep55, getTickSourceLog2After55Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep56 I)
      (getTickSourceLog2After56Int I) (getTickSourceLogRAfter56Nat I) 55

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep54 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep55 I }
      evm (logStep 54 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep54 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep55 I)
    (getTickSourceLog2After55Int I) (getTickSourceLogRAfter55Nat I) 54
    (getTickStoreAfterLogStep55_r I)
    (getTickStoreAfterLogStep55_log2 I)
    (getTickSourceLogRAfter55Nat_mul_self_lt_wordModulus I)

def getTickSourceLog2After53Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After54Int I) (getTickSourceLogRAfter54Nat I) 53

def getTickSourceLogRAfter53Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter54Nat I)

def getTickStoreAfterLogStep53 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep54 I)
    (getTickSourceLog2After54Int I) (getTickSourceLogRAfter54Nat I) 53

theorem getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter53Nat I * getTickSourceLogRAfter53Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter53Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter54Nat I)
    (getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep54_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep54 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter54Nat I))) := by
  simpa [getTickStoreAfterLogStep54, getTickSourceLogRAfter54Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep55 I)
      (getTickSourceLog2After55Int I) (getTickSourceLogRAfter55Nat I) 54

theorem getTickStoreAfterLogStep54_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep54 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After54Int I)) := by
  simpa [getTickStoreAfterLogStep54, getTickSourceLog2After54Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep55 I)
      (getTickSourceLog2After55Int I) (getTickSourceLogRAfter55Nat I) 54

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep53 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep54 I }
      evm (logStep 53 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep53 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep54 I)
    (getTickSourceLog2After54Int I) (getTickSourceLogRAfter54Nat I) 53
    (getTickStoreAfterLogStep54_r I)
    (getTickStoreAfterLogStep54_log2 I)
    (getTickSourceLogRAfter54Nat_mul_self_lt_wordModulus I)

def getTickSourceLog2After52Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After53Int I) (getTickSourceLogRAfter53Nat I) 52

def getTickSourceLogRAfter52Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter53Nat I)

def getTickStoreAfterLogStep52 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep53 I)
    (getTickSourceLog2After53Int I) (getTickSourceLogRAfter53Nat I) 52

theorem getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter52Nat I * getTickSourceLogRAfter52Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter52Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter53Nat I)
    (getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep53_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep53 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter53Nat I))) := by
  simpa [getTickStoreAfterLogStep53, getTickSourceLogRAfter53Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep54 I)
      (getTickSourceLog2After54Int I) (getTickSourceLogRAfter54Nat I) 53

theorem getTickStoreAfterLogStep53_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep53 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After53Int I)) := by
  simpa [getTickStoreAfterLogStep53, getTickSourceLog2After53Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep54 I)
      (getTickSourceLog2After54Int I) (getTickSourceLogRAfter54Nat I) 53

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep52 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep53 I }
      evm (logStep 52 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep52 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep53 I)
    (getTickSourceLog2After53Int I) (getTickSourceLogRAfter53Nat I) 52
    (getTickStoreAfterLogStep53_r I)
    (getTickStoreAfterLogStep53_log2 I)
    (getTickSourceLogRAfter53Nat_mul_self_lt_wordModulus I)

def getTickSourceLog2After51Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After52Int I) (getTickSourceLogRAfter52Nat I) 51

def getTickSourceLogRAfter51Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogRAfterStep (getTickSourceLogRAfter52Nat I)

def getTickStoreAfterLogStep51 (I : ExecutionEnv) : Store :=
  getTickStoreAfterLogStep (getTickStoreAfterLogStep52 I)
    (getTickSourceLog2After52Int I) (getTickSourceLogRAfter52Nat I) 51

theorem getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRAfter51Nat I * getTickSourceLogRAfter51Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRAfter51Nat getTickSourceLogRAfterStep
  exact getTickSourceLogStepRAfterNat_mul_self_lt_wordModulus
    (getTickSourceLogRAfter52Nat I)
    (getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep52_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep52 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter52Nat I))) := by
  simpa [getTickStoreAfterLogStep52, getTickSourceLogRAfter52Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep53 I)
      (getTickSourceLog2After53Int I) (getTickSourceLogRAfter53Nat I) 52

theorem getTickStoreAfterLogStep52_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep52 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After52Int I)) := by
  simpa [getTickStoreAfterLogStep52, getTickSourceLog2After52Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep53 I)
      (getTickSourceLog2After53Int I) (getTickSourceLogRAfter53Nat I) 52

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep51 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep52 I }
      evm (logStep 51 true)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep51 I } evm) := by
  exact getTickSourceLogStepExec evm (getTickStoreAfterLogStep52 I)
    (getTickSourceLog2After52Int I) (getTickSourceLogRAfter52Nat I) 51
    (getTickStoreAfterLogStep52_r I)
    (getTickStoreAfterLogStep52_log2 I)
    (getTickSourceLogRAfter52Nat_mul_self_lt_wordModulus I)

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogSteps59To51 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      (logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true))))))))
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep51 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep59 evm I)
    (execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep58 evm I)
    (execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep57 evm I)
    (execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep56 evm I)
    (execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep55 evm I)
    (execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep54 evm I)
    (execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep53 evm I)
    (execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep52 evm I)
      (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep51 evm I))))))))

def getTickSourceLogRShifted50Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogStepRShiftedNat (getTickSourceLogRAfter51Nat I)

def getTickSourceLogRShifted50Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogRShifted50Nat I)

def getTickStoreAfterLogRShifted50 (I : ExecutionEnv) : Store :=
  getTickSourceLogStepStoreAfterRShifted (getTickStoreAfterLogStep51 I)
    (getTickSourceLogRAfter51Nat I)

def getTickSourceLogF50Nat (I : ExecutionEnv) : Nat :=
  getTickSourceLogStepFNat (getTickSourceLogRAfter51Nat I)

def getTickSourceLogF50Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLogF50Nat I)

def getTickStoreAfterLogF50Let (I : ExecutionEnv) : Store :=
  getTickSourceLogStepStoreAfterFLet (getTickStoreAfterLogStep51 I)
    (getTickSourceLogRAfter51Nat I)

def getTickSourceLog2After50Int (I : ExecutionEnv) : Int :=
  getTickSourceLog2AfterStep (getTickSourceLog2After51Int I) (getTickSourceLogRAfter51Nat I) 50

def getTickSourceLog2After50Value (I : ExecutionEnv) : Value :=
  .int (getTickSourceLog2After50Int I)

def getTickStoreAfterLogStep50 (I : ExecutionEnv) : Store :=
  getTickSourceLogStepStoreAfterLog2 (getTickStoreAfterLogStep51 I)
    (getTickSourceLog2After51Int I) (getTickSourceLogRAfter51Nat I) 50

theorem getTickSourceLogRShifted50Nat_lt_wordModulus (I : ExecutionEnv) :
    getTickSourceLogRShifted50Nat I < EVM.wordModulus := by
  unfold getTickSourceLogRShifted50Nat
  exact getTickSourceLogStepRShiftedNat_lt_wordModulus (getTickSourceLogRAfter51Nat I)
    (getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus I)

theorem getTickStoreAfterLogStep51_r (I : ExecutionEnv) :
    (getTickStoreAfterLogStep51 I).get? "r" =
      some (Value.int (Int.ofNat (getTickSourceLogRAfter51Nat I))) := by
  simpa [getTickStoreAfterLogStep51, getTickSourceLogRAfter51Nat]
    using getTickStoreAfterLogStep_r (getTickStoreAfterLogStep52 I)
      (getTickSourceLog2After52Int I) (getTickSourceLogRAfter52Nat I) 51

theorem getTickStoreAfterLogStep51_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogStep51 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After51Int I)) := by
  simpa [getTickStoreAfterLogStep51, getTickSourceLog2After51Int]
    using getTickStoreAfterLogStep_log2 (getTickStoreAfterLogStep52 I)
      (getTickSourceLog2After52Int I) (getTickSourceLogRAfter52Nat I) 51

theorem getTickStoreAfterLogRShifted50_r (I : ExecutionEnv) :
    (getTickStoreAfterLogRShifted50 I).get? "r" =
      some (getTickSourceLogRShifted50Value I) := by
  rw [getTickStoreAfterLogRShifted50, getTickSourceLogStepStoreAfterRShifted,
    store_get_self]
  rfl

theorem getTickStoreAfterLogRShifted50_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogRShifted50 I).get? "log_2" =
      some (Value.int (getTickSourceLog2After51Int I)) := by
  rw [getTickStoreAfterLogRShifted50, getTickSourceLogStepStoreAfterRShifted]
  rw [store_get_ne (getTickStoreAfterLogStep51 I) (k := "r") (a := "log_2")
    (getTickSourceLogStepRShiftedValue (getTickSourceLogRAfter51Nat I)) (by decide)]
  exact getTickStoreAfterLogStep51_log2 I

theorem getTickStoreAfterLogF50Let_log2 (I : ExecutionEnv) :
    (getTickStoreAfterLogF50Let I).get? "log_2" =
      some (Value.int (getTickSourceLog2After51Int I)) := by
  rw [getTickStoreAfterLogF50Let, getTickSourceLogStepStoreAfterFLet]
  rw [store_get_ne
    (getTickSourceLogStepStoreAfterRShifted (getTickStoreAfterLogStep51 I)
      (getTickSourceLogRAfter51Nat I))
    (k := "f") (a := "log_2")
    (getTickSourceLogStepFValue (getTickSourceLogRAfter51Nat I)) (by decide)]
  simpa [getTickStoreAfterLogRShifted50] using getTickStoreAfterLogRShifted50_log2 I

theorem getTickStoreAfterLogF50Let_f (I : ExecutionEnv) :
    (getTickStoreAfterLogF50Let I).get? "f" = some (getTickSourceLogF50Value I) := by
  rw [getTickStoreAfterLogF50Let, getTickSourceLogStepStoreAfterFLet, store_get_self]
  rfl

theorem evalExpr_getTick_log2Var_afterLogF50 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogF50Let I }
      evm (.var "log_2") = .ok (Value.int (getTickSourceLog2After51Int I)) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogF50Let_log2]

theorem evalExpr_getTick_fVar_afterLogF50 {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := getTickStoreAfterLogF50Let I }
      evm (.var "f") = .ok (getTickSourceLogF50Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [getTickStoreAfterLogF50Let_f]

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogStep50 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep51 I }
      evm (logStep 50 false)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep50 I } evm) := by
  have evalR : evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterLogStep51 I } evm (.var "r") =
      .ok (Value.int (Int.ofNat (getTickSourceLogRAfter51Nat I))) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [getTickStoreAfterLogStep51_r]
  have evalMul : evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterLogStep51 I } evm
      (mulE (.var "r") (.var "r")) =
      .ok (Value.int (Int.ofNat
        (getTickSourceLogRAfter51Nat I * getTickSourceLogRAfter51Nat I))) := by
    unfold mulE
    simp only [evalExpr?, evalR, EvalResult.bind, bind, evalBinaryOp?]
    change EvalResult.ok
        (Value.int ((getTickSourceLogRAfter51Nat I : Int) *
          (getTickSourceLogRAfter51Nat I : Int))) =
      EvalResult.ok
        (Value.int (((getTickSourceLogRAfter51Nat I *
          getTickSourceLogRAfter51Nat I : Nat) : Int)))
    rw [← Int.natCast_mul]
  have evalRShifted : evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterLogStep51 I } evm
      (shrE (mulE (.var "r") (.var "r")) (.intLit 127)) =
      .ok (getTickSourceLogRShifted50Value I) := by
    unfold shrE
    simp only [evalExpr?, evalMul, EvalResult.bind, bind, pure]
    rw [evalBinaryOp_int_shr_ok]
    · rw [getTickSourceLogRShifted50Value, getTickSourceLogRShifted50Nat,
        getTickSourceLogStepRShiftedNat]
      rw [intOfNat_toNat_div_pow_127_cast]
    · exact Int.natCast_nonneg _
    · exact Int.ofNat_lt.mpr (getTickSourceLogRAfter51Nat_mul_self_lt_wordModulus I)
    · norm_num
    · norm_num
  have assignRShifted :
      assignStorageRef? (config v)
        { contract := contract v, locals := getTickStoreAfterLogStep51 I }
        evm .localVar (varRef "r") (getTickSourceLogRShifted50Value I) =
        .ok ({ contract := contract v, locals := getTickStoreAfterLogRShifted50 I }, evm) := by
    rw [assignStorageRef?]
    rw [varRef]
    rw [getTickStoreAfterLogStep51_r]
    simp [getTickStoreAfterLogRShifted50, getTickSourceLogStepStoreAfterRShifted,
      getTickSourceLogRShifted50Value, getTickSourceLogRShifted50Nat,
      getTickSourceLogStepRShiftedValue, updateLocalPath?, pure, bind, EvalResult.bind]
  have evalRShiftedVar : evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterLogRShifted50 I }
      evm (.var "r") = .ok (getTickSourceLogRShifted50Value I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [getTickStoreAfterLogRShifted50_r]
  have evalF : evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterLogRShifted50 I }
      evm (shrE (.var "r") shift128) = .ok (getTickSourceLogF50Value I) := by
    unfold shrE shift128
    simp only [evalExpr?, evalRShiftedVar, EvalResult.bind, bind, pure]
    change evalBinaryOp? .shr (.int (Int.ofNat (getTickSourceLogRShifted50Nat I)))
        (.int (Int.ofNat 128)) = .ok (getTickSourceLogF50Value I)
    rw [evalBinaryOp_int_shr_ok]
    · unfold getTickSourceLogF50Value getTickSourceLogF50Nat
      rw [getTickSourceLogRShifted50Nat]
      rw [getTickSourceLogStepFNat]
      rw [intOfNat_toNat_div_pow_cast]
    · exact Int.natCast_nonneg _
    · exact Int.ofNat_lt.mpr (getTickSourceLogRShifted50Nat_lt_wordModulus I)
    · norm_num
    · norm_num
  have evalLog2Add : evalExpr? (config v)
      { contract := contract v, locals := getTickStoreAfterLogF50Let I }
      evm (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ (50 : Nat))))) =
      .ok (getTickSourceLog2After50Value I) := by
    unfold addE mulE getTickSourceLog2After50Value getTickSourceLog2After50Int
      getTickSourceLog2AfterStep
    simp only [evalExpr?, evalExpr_getTick_log2Var_afterLogF50,
      evalExpr_getTick_fVar_afterLogF50, EvalResult.bind, bind, evalBinaryOp?,
      getTickSourceLogF50Value, getTickSourceLogF50Nat,
      getTickSourceLogStepLog2AfterInt]
  have assignLog2 :
      assignStorageRef? (config v)
        { contract := contract v, locals := getTickStoreAfterLogF50Let I }
        evm .localVar (varRef "log_2") (getTickSourceLog2After50Value I) =
        .ok ({ contract := contract v, locals := getTickStoreAfterLogStep50 I }, evm) := by
    rw [assignStorageRef?]
    rw [varRef]
    rw [getTickStoreAfterLogF50Let_log2]
    simp [getTickStoreAfterLogStep50, getTickSourceLogStepStoreAfterLog2,
      getTickStoreAfterLogF50Let, getTickSourceLogStepStoreAfterFLet,
      getTickSourceLog2After50Value, getTickSourceLog2After50Int,
      getTickSourceLog2AfterStep, getTickSourceLogStepLog2AfterValue,
      updateLocalPath?, pure, bind, EvalResult.bind]
  change ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep51 I } evm
      [ .assign .localVar (varRef "r") (shrE (mulE (.var "r") (.var "r")) (.intLit 127)),
        .letDecl "f" (some uint256) (shrE (.var "r") shift128),
        .assign .localVar (varRef "log_2")
          (addE (.var "log_2") (mulE (.var "f") (.intLit (2 ^ (50 : Nat))))) ]
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep50 I } evm)
  refine ExecBlock.consNormal (ExecStmt.assign evalRShifted assignRShifted) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl evalF) ?_
  exact ExecBlock.consNormal (ExecStmt.assign evalLog2Add assignLog2) ExecBlock.nil

theorem uniswapV3PoolGetTickAtSqrtRatioSourceLogSteps59To50 {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    ExecBlock (config v) { contract := contract v, locals := getTickStoreAfterLogStep60 I } evm
      ((logStep 59 true ++
        (logStep 58 true ++
        (logStep 57 true ++
        (logStep 56 true ++
        (logStep 55 true ++
        (logStep 54 true ++
        (logStep 53 true ++
        (logStep 52 true ++
        logStep 51 true)))))))) ++
        logStep 50 false)
      (.ok { contract := contract v, locals := getTickStoreAfterLogStep50 I } evm) := by
  exact execBlock_append (uniswapV3PoolGetTickAtSqrtRatioSourceLogSteps59To51 evm I)
    (uniswapV3PoolGetTickAtSqrtRatioSourceLogStep50 evm I)

end Benchmarks.UniswapV3Pool
