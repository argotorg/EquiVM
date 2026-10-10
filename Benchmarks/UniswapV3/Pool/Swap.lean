import Benchmarks.UniswapV3.Pool.SwapBodyTrace
import Benchmarks.UniswapV3.Pool.SwapDecodeTrace

/-!
# UniswapV3Pool `swap(address,bool,int256,uint160,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 471; reach lemma `uniswapV3PoolReachSwapBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `swap(address,bool,int256,uint160,bytes)`: the theorem `Correct.lean` routes selector 1 to. -/
theorem uniswapV3PoolSwapBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 1) rfl hsel
  have hd : dispatchMsg contract I.calldata = some swapTransition :=
    uniswapV3PoolDispatch_swap (selectorMismatch_of_match hsel (by decide +kernel)) hsel
  obtain ⟨k0, C0, r0⟩ := uniswapV3PoolReachSwapBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨471⟩ [solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k0 C0 at r0
  rcases swapDecodeX (v := v) r0 hsz hsize (by simp) with
    ⟨hbad, rr⟩ | ⟨hvalid, k1, C1, r1⟩
  · exact rr.reEquivDecodingFailed hcode hd (swapDecodeInvalid hbad)
  · let a := swapDecodedArgs I.calldata
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := swapDecodeValid hvalid
    have hs : SourceState evm I σ evm := ⟨rfl, rfl, rfl⟩
    have hlen : (UInt256.ofNat (swapDataLength I.calldata)).toNat = swapDataLength I.calldata :=
      ulit_toNat' _ (by have := hvalid.length; change _ < 2 ^ 256; omega)
    have hstart : (UInt256.ofNat (swapDataStart I.calldata)).toNat = swapDataStart I.calldata :=
      ulit_toNat' _ (lt_of_le_of_lt hvalid.length_word hsize)
    rcases swapBodyX (v := v) a evm hs r1 (swapDecodedArgs_fits I.calldata) hwv
        (by rw [hstart, hlen]; rfl) (by rw [hstart, hlen]; exact hvalid.payload)
        (by rw [hlen]; exact hvalid.length) (by simp) with
      hoog | (⟨hbody, rr⟩ | (⟨hbody, rr⟩ | ⟨frame, evm', a0, a1, hbody, rr, h0, h1⟩))
    · exact reEquiv_outOfGas (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
    · rcases rr with rr | rr
      · exact rr.reEquivExecutionRevert hcode hd hdec hbody
      · exact RDinvalid.reEquivExecutionInvalid hcode rr hd hdec hbody
    · exact rr.reEquivStaticHalt hcode hd hdec hbody
    · exact rr.reEquivExecutionGen hcode hd hdec hbody rfl
        (returnEquiv.returned rfl (swapReturnEncoding a0 a1 h0 h1))

end Benchmarks.UniswapV3.Pool
