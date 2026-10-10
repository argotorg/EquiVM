import Benchmarks.UniswapV3.Pool.ObserveDecodeTrace
import Benchmarks.UniswapV3.Pool.ObservePrefixTrace
import Benchmarks.UniswapV3.Pool.ObserveReturnTrace
import Benchmarks.UniswapV3.Pool.ObserveReturnEncoding

/-!
# UniswapV3Pool `observe(uint32[])`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1587; reach lemma `uniswapV3PoolReachObserveBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `observe(uint32[])`: the theorem `Correct.lean` routes selector 16 to. -/
theorem uniswapV3PoolObserveBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 16)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 16) rfl hsel
  have hd : dispatchMsg contract I.calldata = some observeTransition := by
    apply uniswapV3PoolDispatch_observe <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨k0, C0, rdEntry⟩ := uniswapV3PoolReachObserveBody
    (g := Sat256.ofUInt256 g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  rcases observeDecodeX (v := v) rdEntry hsz hsize (by simp) with ⟨hbad, rbad⟩ | ⟨hvalid, k1, C1, r1⟩
  · exact rbad.reEquivDecodingFailed hcode hd (observeDecodeInvalid hbad)
  · have hdec := observeDecodeValid hvalid
    have hn : (oracleObserveCleanAgos (observeRawAgos I.calldata)).length ≤ 2 ^ 64 - 1 := by
      simp only [oracleObserveCleanAgos, List.length_map, observeRawAgos, calldataWordList_length]
      have := hvalid.count
      omega
    rcases observePrefixX (v := v) r1 hvalid.count (lt_of_le_of_lt hvalid.length_word hsize)
      (by simp) with ⟨hself, rbad⟩ | ⟨hself, k2, C2, r2⟩
    · exact rbad.reEquivExecutionRevert hcode hd hdec
        (observeRevertsDelegate v evm _ hwv hself)
    · rcases observeOracleX (v := v) r2 hvalid hsize (by simp) with hoog | (hfail | hout)
      · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
      · obtain ⟨hf, hr⟩ := hfail
        have hbody := observeSourceReverts v evm _ hwv hself hn hf
        rcases hr with hr | hr
        · exact hr.reEquivExecutionRevert hcode hd hdec hbody
        · exact RDinvalid.reEquivExecutionInvalid hcode hr hd hdec hbody
      · obtain ⟨hcard, ⟨out⟩⟩ := hout
        have hbody := observeSourceReturns v evm _ (out.ticks.map Value.int)
          (out.seconds.map Value.int) hwv hself hn hcard (by
            simpa only [List.map_replicate, oracleObserveCleanAgos, List.length_map] using out.run)
        obtain ⟨_, _, _, hbudget⟩ := observeInputMemory I.calldata
          (observeDataStart I.calldata) (observeCount I.calldata) hvalid.count hvalid.payload
        have hbudget' := (hbudget.mono_cost (Nat.zero_le C2)).advance out.cost_bound
        have htl := out.arrays.ticks_length
        have hsl := out.arrays.seconds_length
        have hnraw : (observeRawAgos I.calldata).length = observeCount I.calldata :=
          calldataWordList_length _ _ _
        rcases memoryGasReserveOrOOG
          (reserve := 128 + 32 * (out.ticks.length + out.seconds.length)) out.rd hbudget'
          (le_refl _) out.cover (by rw [htl, hsl, hnraw]; have := hvalid.count; omega)
          with hoog | hb
        · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
        · have r3 := uniswapV3Pool_block_9566 (immWords := wordsOf (immStore v)) (by simp)
            (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) out.rd
          have halo := out.layout.ago_lower
          have hae := out.layout.ago_end
          have hte := out.layout.ticks_end
          have hse := out.layout.seconds_end
          have rret := observeReturnX (v := v) r3 out.heap out.arrays.ticks_mem out.arrays.seconds_mem
            (by omega) (by omega)
            (by simp only [List.length_map, htl]; omega)
            (by simpa only [List.length_map, hsl] using hse)
            (by simpa only [List.length_map, Nat.add_assoc] using hb) (by simp)
          have hwords : observeEncodeWords (out.ticks.map EVM.wordOfInt) (out.seconds.map EVM.wordOfInt) =
              observeReturnWords out.ticks out.seconds := by
            simp only [observeEncodeWords, observeReturnWords, List.length_map]
          rw [hwords] at rret
          exact rret.reEquivExecutionGen hcode hd hdec hbody rfl
            (returnEquiv.returned rfl
              (observeReturnEncoding out.ticks out.seconds out.arrays.ticks_range out.arrays.seconds_range))

end Benchmarks.UniswapV3.Pool
