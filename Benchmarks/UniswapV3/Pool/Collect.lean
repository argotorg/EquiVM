import Benchmarks.UniswapV3.Pool.CollectBodyTrace
import Benchmarks.UniswapV3.Pool.CollectCalldata

/-!
# UniswapV3Pool `collect(address,int24,int24,uint128,uint128)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1276; reach lemma `uniswapV3PoolReachCollectBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `collect(address,int24,int24,uint128,uint128)`: the theorem `Correct.lean` routes selector 10 to. -/
theorem uniswapV3PoolCollectBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 10)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 10) rfl hsel
  have hd : dispatchMsg contract I.calldata = some collectTransition := by
    apply uniswapV3PoolDispatch_collect <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 164 ≤ I.calldata.size
  · let recipient := collectRecipient I.calldata
    let lower := calldataWord I.calldata 36
    let upper := calldataWord I.calldata 68
    let req0 := collectRequestedWord I.calldata false
    let req1 := collectRequestedWord I.calldata true
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := collectDecode hlen
    have hreq0 : req0.toNat < 2 ^ 128 := collectRequestedWord_lt I.calldata false
    have hreq1 : req1.toNat < 2 ^ 128 := collectRequestedWord_lt I.calldata true
    obtain ⟨_, _, rdDecoded⟩ := uniswapV3PoolCollectDecodedX
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen
    rcases collectReadLockX (v := v) rdDecoded (by simp) with
      ⟨rdRevert, hlocked⟩ | ⟨hunlocked, _, _, rdLock⟩
    · exact rdRevert.reEquivExecutionRevert hcode hd hdec
        (collectRevertsLocked v evm recipient lower upper req0 req1 hwv hlocked)
    · cases hperm : I.perm with
      | false =>
          exact (collectLockStaticX (v := v) rdLock hperm (by simp)).reEquivStaticHalt hcode hd hdec
            (collectStatic v evm recipient lower upper req0 req1 hwv hunlocked hperm)
      | true =>
          have hs : SourceState evm I σ evm := ⟨rfl, rfl, rfl⟩
          obtain ⟨awPosition, _, _, rdPosition, hmPosition⟩ := collectPositionX (v := v)
            rdLock hs hperm freshHeapMemory (by decide) (by simp)
          let locked := storeSlot0Unlocked evm false
          let key := positionKey I.source lower upper
          have henv : locked.executionEnv = I := storeSlot0Unlocked_executionEnv evm false
          have hsLocked : SourceState evm I locked.accountMap locked :=
            ⟨storeSlot0Unlocked_originalAccounts evm false, henv, rfl⟩
          let amount0 := minWord req0 (positionOwedWord key false locked.accountMap locked.executionEnv)
          let amount1 := minWord req1 (positionOwedWord key true locked.accountMap locked.executionEnv)
          let locals := (collectAmountsFrame v recipient lower upper req0 req1 key amount0 amount1).locals
          have hprefix := collectAmountsPrefix v evm recipient lower upper req0 req1 hwv hunlocked
          have hvalues := collectAmounts_values v recipient lower upper req0 req1 key amount0 amount1
          have hfit0 : amount0.toNat < 2 ^ 128 := minWord_lt _ _
            (positionOwedWord_lt key false locked.accountMap locked.executionEnv)
          have hfit1 : amount1.toNat < 2 ^ 128 := minWord_lt _ _
            (positionOwedWord_lt key true locked.accountMap locked.executionEnv)
          obtain ⟨_, _, rdAmounts⟩ := collectAmountsX (v := v) rdPosition hreq0 hreq1 (by simp)
          have hf0 : positionOwedWord key false locked.accountMap I =
              positionOwedWord key false locked.accountMap locked.executionEnv := by rw [henv]
          have hf1 : positionOwedWord key true locked.accountMap I =
              positionOwedWord key true locked.accountMap locked.executionEnv := by rw [henv]
          rw [hf0, hf1] at rdAmounts
          rcases collectPaymentsBodyX (v := v) (evm0 := evm) recipient locals rdAmounts hsLocked hperm
              hprefix hvalues hfit0 hfit1 hmPosition
              (by rw [positionGetMem_size _ _ _ _ _ _ (by decide), solcFreePtrMem_size]; decide)
              (positionGetMem_zero_initial I.source lower upper ⟨7⟩) (by decide) (by simp) with
            ⟨rdRevert, hbody⟩ | ⟨evmFinal, localsFinal, hbody, rdFinal⟩
          · exact rdRevert.reEquivExecutionRevert hcode hd hdec hbody
          · exact rdFinal.reEquivExecutionGen hcode hd hdec hbody rfl
              (returnEquiv.returned rfl (uintPairReturnEncoding ⟨128, by decide⟩ ⟨128, by decide⟩
                amount0 amount1 hfit0 hfit1))
  · have hshort : I.calldata.size < 164 := by omega
    exact (uniswapV3PoolCollectShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      |>.reEquivDecodingFailed hcode hd (collectDecodeShort hshort)

end Benchmarks.UniswapV3.Pool
