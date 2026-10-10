import Benchmarks.UniswapV3.Pool.InitializeSource
import Benchmarks.UniswapV3.Pool.InitializeCalldata
import Benchmarks.UniswapV3.Pool.InitializePrefixTrace
import Benchmarks.UniswapV3.Pool.InitializeFinishTrace
import Benchmarks.UniswapV3.Pool.OracleInitializeTrace
import Benchmarks.UniswapV3.Pool.OracleInitializeStaticTrace

/-!
# UniswapV3Pool `initialize(uint160)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2218; reach lemma `uniswapV3PoolReachInitializeBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `initialize(uint160)`: the theorem `Correct.lean` routes selector 25 to. -/
theorem uniswapV3PoolInitializeBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 25)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 25) rfl hsel
  have hd : dispatchMsg contract I.calldata = some initializeTransition := by
    apply uniswapV3PoolDispatch_initialize <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 36 ≤ I.calldata.size
  · let price := initializePriceWord I.calldata
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hp : price.toNat < 2 ^ 160 := initializePriceWord_lt _
    have hdec := initializeDecode hlen
    obtain ⟨k, C, rd⟩ := uniswapV3PoolInitializeDecodedX
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen
    rcases initializeGuardX (v := v) rd (by simp) with
      ⟨rdBad, hzero⟩ | ⟨hzero, kGuard, CGuard, rdGuard⟩
    · exact rdBad.reEquivExecutionRevert hcode hd hdec
        (initializeRevertsAlreadyInitialized v evm price hwv hzero)
    · rcases initializeBeforeOracleX (v := v) rdGuard hp (by simp) with
        ⟨rdBad, hbad⟩ | ⟨hv, hs, kOracle, COracle, rdOracle⟩
      · exact rdBad.reEquivExecutionRevert hcode hd hdec
          (initializeRevertsTick v evm price hwv hzero hp hbad)
      · cases hperm : I.perm with
        | false =>
          have rdStatic := oracleInitializeStaticX (v := v) rdOracle hperm (by simp)
          exact rdStatic.reEquivStaticHalt hcode hd hdec
            (initializeStatic v evm price hwv hzero hp hv hs hperm)
        | true =>
          obtain ⟨kAfter, CAfter, awAfter, hsAfter, rdAfter⟩ := oracleInitializeX (v := v)
            rdOracle (evm := evm) SourceState.init hperm
            (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide) (by simp)
          have htime : oracleInitializeTime (UInt256.ofNat I.header.timestamp) =
              blockTimestampWord I := by
            exact u256_land_comm _ _
          rw [htime] at hsAfter rdAfter
          obtain ⟨kDone, CDone, memDone, awDone, hsDone, rdDone⟩ := initializeFinishX (v := v)
            rdAfter hsAfter hperm hp
            (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide) (by simp)
          have rdRet := uniswapV3PoolBlocks.uniswapV3Pool_block_857
            (immWords := wordsOf (immStore v)) (by simp) rdDone
          exact rdRet.reEquivExecutionGen hcode hd hdec
            (initializeReturns v evm price hwv hzero hp hv hs) rfl
            (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))
  · have hshort : I.calldata.size < 36 := by omega
    have rdBad := uniswapV3PoolInitializeShortX
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort
    exact rdBad.reEquivDecodingFailed hcode hd (initializeDecodeShort hsz hshort)

end Benchmarks.UniswapV3.Pool
