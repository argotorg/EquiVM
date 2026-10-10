import Benchmarks.UniswapV3.Pool.BurnBodyTrace
import Benchmarks.UniswapV3.Pool.BurnCalldata
import Benchmarks.UniswapV3.Pool.BurnLockTrace

/-!
# UniswapV3Pool `burn(int24,int24,uint128)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1852; reach lemma `uniswapV3PoolReachBurnBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `burn(int24,int24,uint128)`: the theorem `Correct.lean` routes selector 17 to. -/
theorem uniswapV3PoolBurnBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 17)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 17) rfl hsel
  have hd : dispatchMsg contract I.calldata = some burnTransition := by
    apply uniswapV3PoolDispatch_burn <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  by_cases hlen : 100 ≤ I.calldata.size
  · let a := burnArgs I.calldata
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := burnDecode hlen
    obtain ⟨k0, C0, r0⟩ := uniswapV3PoolBurnDecodedX
      (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hlen
    rcases burnReadLockX (v := v) r0 (by simp) with
      ⟨rr, hlocked⟩ | ⟨hunlocked, k1, C1, r1⟩
    · exact rr.reEquivExecutionRevert hcode hd hdec (burnRevertsLocked v a evm hwv hlocked)
    · cases hperm : I.perm with
      | false =>
          exact (burnLockStaticX (v := v) r1 hperm (by simp)).reEquivStaticHalt hcode hd hdec
            (burnStatic v a evm hwv hunlocked hperm)
      | true =>
          have hs : SourceState evm I σ evm := ⟨rfl, rfl, rfl⟩
          rcases burnBodyX (v := v) a evm hs r1 (burnArgs_fits I.calldata) freshHeapMemory
              (by decide) hwv hunlocked hperm (by simp) with
            ⟨hbody, rr⟩ | ⟨hbody, rr⟩ | ⟨frame, evm', a0, a1, hbody, rr⟩
          · rcases rr with rr | rr
            · exact rr.reEquivExecutionRevert hcode hd hdec hbody
            · exact RDinvalid.reEquivExecutionInvalid hcode rr hd hdec hbody
          · exact rr.reEquivStaticHalt hcode hd hdec hbody
          · exact rr.reEquivExecutionGen hcode hd hdec hbody rfl
              (returnEquiv.returned rfl (uintPairReturnEncoding ⟨256, by decide⟩ ⟨256, by decide⟩
                a0 a1 a0.val.isLt a1.val.isLt))
  · have hshort : I.calldata.size < 100 := by omega
    exact (uniswapV3PoolBurnShortX (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel hshort)
      |>.reEquivDecodingFailed hcode hd (burnDecodeShort hshort)

end Benchmarks.UniswapV3.Pool
