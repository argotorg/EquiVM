import Benchmarks.UniswapV3.Pool.SnapshotBranchesTrace
import Benchmarks.UniswapV3.Pool.SnapshotCalldata
import Benchmarks.UniswapV3.Pool.CheckTicks

/-!
# UniswapV3Pool `snapshotCumulativesInside(int24,int24)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1910; reach lemma `uniswapV3PoolReachSnapshotCumulativesInsideBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

theorem snapshotDecodedWord_normalize (cd : ByteArray) (offset : Nat) :
    normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat (snapshotDecodedWord cd offset).toNat) =
      snapshotDecodedTick cd offset := by
  have hb := normalizeSint_bounds ⟨24, by decide⟩ (Int.ofNat (calldataWord cd offset).toNat)
  rw [snapshotDecodedWord, signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide),
    normalizeInt_wordOfInt, normalizeSint_eq_self ⟨24, by decide⟩ _ hb.1 hb.2]
  rfl

/-- `snapshotCumulativesInside(int24,int24)`: the theorem `Correct.lean` routes selector 18 to. -/
theorem uniswapV3PoolSnapshotCumulativesInsideBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 18)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 18) rfl hsel
  have hd : dispatchMsg contract I.calldata = some snapshotTransition := by
    apply uniswapV3PoolDispatch_snapshotCumulativesInside <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 68 ≤ I.calldata.size
  · let lower := snapshotDecodedTick I.calldata 4
    let upper := snapshotDecodedTick I.calldata 36
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := snapshotDecode hlen
    obtain ⟨_, _, rdDecoded⟩ := uniswapV3PoolSnapshotDecodedX
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen
    have rdDelegate := uniswapV3Pool_block_9952 (immWords := wordsOf (immStore v)) (by simp)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecoded
    simp only [uniswapV3Pool_block_9952_stack] at rdDelegate
    rcases noDelegateCallX (v := v) rdDelegate
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by simp) with
      ⟨rdFail, hself⟩ | ⟨hself, _, _, rdSelf⟩
    · exact rdFail.reEquivExecutionRevert hcode hd hdec
        (snapshotRevertsDelegate v evm lower upper hwv hself)
    · have rdCheck := uniswapV3Pool_block_9965 (immWords := wordsOf (immStore v)) (by simp)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdSelf
      simp only [uniswapV3Pool_block_9965_stack] at rdCheck
      have hcheck := checkTicksX (v := v) rdCheck
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by simp)
      dsimp only at hcheck
      simp only [snapshotDecodedWord_normalize] at hcheck
      rcases hcheck with ⟨rdFail, hticks⟩ | ⟨hticks, _, _, rdChecked⟩
      · exact rdFail.reEquivExecutionRevert hcode hd hdec
          (snapshotRevertsTicks v evm lower upper hwv hself hticks)
      · obtain ⟨_, _, rdLower⟩ := snapshotMapLowerX (v := v) lower upper rdChecked
          solcFreePtrMem_size freshHeapMemory.active (snapshotDecodedWord_clean I.calldata 4)
          (snapshotDecodedWord_clean I.calldata 36) (by simp)
        have hm := snapshotMapMem_heap freshHeapMemory solcFreePtrMem_size lower upper
        rcases snapshotTickChecksX (v := v) lower upper rdLower (by simp) with
          ⟨rdFail, hl⟩ | ⟨rdFail, hl, hu⟩ | ⟨hl, hu, _, _, rdTicks⟩
        · exact rdFail.reEquivExecutionRevert hcode hd hdec
            (snapshotRevertsLower v evm lower upper hwv hself hticks hl)
        · exact rdFail.reEquivExecutionRevert hcode hd hdec
            (snapshotRevertsUpper v evm lower upper hwv hself hticks hl hu)
        · obtain ⟨_, _, _, rdSlot, hh, hs⟩ := snapshotSlotReadX (v := v) lower upper rdTicks hm
            (by decide) hticks (snapshotDecodedWord_clean I.calldata 4) (by simp)
          rcases snapshotBranchesX (v := v) lower upper rdSlot hh hs (by decide) (by decide)
              hticks (snapshotDecodedWord_clean I.calldata 36) (by simp) with
            ⟨rdFail, hlo, hhi, hindex⟩ | ⟨rdReturn, hindex⟩
          · exact RDinvalid.reEquivExecutionInvalid hcode rdFail hd hdec
              (snapshotRevertsIndex v evm lower upper hwv hself hticks hl hu hlo hhi hindex)
          · obtain ⟨frame, hbody⟩ := snapshotSourceReturns v evm lower upper hwv hself hticks hl hu hindex
            exact rdReturn.reEquivExecutionGen hcode hd hdec hbody rfl
              (returnEquiv.returned rfl (snapshotReturnEncoding lower upper σ I))
  · have hshort : I.calldata.size < 68 := by omega
    exact (uniswapV3PoolSnapshotShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      |>.reEquivDecodingFailed hcode hd (snapshotDecodeShort hsz hshort)

end Benchmarks.UniswapV3.Pool
