import Benchmarks.UniswapV3.Pool.IncreaseTrace
import Benchmarks.UniswapV3.Pool.IncreaseCalldata

/-!
# UniswapV3Pool `increaseObservationCardinalityNext(uint16)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 824; reach lemma `uniswapV3PoolReachIncreaseObservationCardinalityNextBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `increaseObservationCardinalityNext(uint16)`: the theorem `Correct.lean` routes selector 5 to. -/
theorem uniswapV3PoolIncreaseObservationCardinalityNextBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 5)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 5) rfl hsel
  have hd : dispatchMsg contract I.calldata = some increaseTransition := by
    apply uniswapV3PoolDispatch_increaseObservationCardinalityNext <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 36 ≤ I.calldata.size
  · let next := increaseRequestedWord I.calldata
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := increaseDecode hlen
    have hnext := increaseRequestedWord_lt I.calldata
    obtain ⟨_, _, rdDecoded⟩ := uniswapV3PoolIncreaseDecodedX
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen
    rcases increaseReadLockX (v := v) rdDecoded (by simp) with
      ⟨rdRevert, hlocked⟩ | ⟨hunlocked, _, _, rdLock⟩
    · exact rdRevert.reEquivExecutionRevert hcode hd hdec
        (increaseRevertsLocked v evm next hwv hlocked)
    · cases hperm : I.perm with
      | false =>
          exact (increaseLockStaticX (v := v) rdLock hperm (by simp)).reEquivStaticHalt hcode hd hdec
            (increaseStatic v evm next hwv hunlocked hperm)
      | true =>
          have hs : SourceState evm I σ evm := ⟨rfl, rfl, rfl⟩
          rcases increaseLockDelegateX (v := v) rdLock hs hperm (by simp) with
            ⟨rdRevert, hdelegate⟩ | ⟨hself, _, _, rdReady⟩
          · exact rdRevert.reEquivExecutionRevert hcode hd hdec
              (increaseDelegateReverts v evm next hwv hunlocked hdelegate)
          · let locked := storeSlot0Unlocked evm false
            have henv : locked.executionEnv = I := storeSlot0Unlocked_executionEnv evm false
            have hsLocked : SourceState evm I locked.accountMap locked :=
              ⟨storeSlot0Unlocked_originalAccounts evm false, henv, rfl⟩
            let current := slot0FieldWord 27 2 locked.accountMap locked.executionEnv
            have hcurrent : current.toNat < 2 ^ 16 := slot0CardinalityNext_lt _ _
            obtain ⟨_, _, rdCall⟩ := increaseGrowEntryX (v := v) rdReady (by simp)
            have hf : slot0FieldWord 27 2 locked.accountMap I = current := by
              dsimp only [current]; rw [henv]
            rw [hf] at rdCall
            rcases oracleGrowX (v := v) rdCall hsLocked hperm hcurrent hnext
                (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by simp) with
              ⟨rdRevert, hzero⟩ | ⟨hpos, _, _, rdGrown⟩
            · exact rdRevert.reEquivExecutionRevert hcode hd hdec
                (increaseGrowZeroReverts v evm next hwv hunlocked hself hzero)
            · let grown := oracleGrowState locked current.toNat (next.toNat - current.toNat)
              have hsGrown : SourceState evm I grown.accountMap grown :=
                ⟨(oracleGrowState_originalAccounts locked _ _).trans hsLocked.world,
                  (oracleGrowState_executionEnv locked _ _).trans henv, rfl⟩
              have rdFinal := increaseFinishX (v := v) rdGrown hsGrown hperm hcurrent
                (oracleGrowResult_lt current next hcurrent hnext) (by simp)
              exact rdFinal.reEquivExecutionGen hcode hd hdec
                (increaseReturns v evm next hwv hunlocked hself hnext hpos) rfl
                (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))
  · have hshort : I.calldata.size < 36 := by omega
    exact (uniswapV3PoolIncreaseShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      |>.reEquivDecodingFailed hcode hd (increaseDecodeShort hsz hshort)

end Benchmarks.UniswapV3.Pool
