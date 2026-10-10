import Benchmarks.UniswapV3.Pool.MintBodyTrace
import Benchmarks.UniswapV3.Pool.MintDecodeTrace
import Benchmarks.UniswapV3.Pool.MintLockTrace

/-!
# UniswapV3Pool `mint(address,int24,int24,uint128,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 948; reach lemma `uniswapV3PoolReachMintBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `mint(address,int24,int24,uint128,bytes)`: the theorem `Correct.lean` routes selector 7 to. -/
theorem uniswapV3PoolMintBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 7)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 7) rfl hsel
  have hd : dispatchMsg contract I.calldata = some mintTransition := by
    apply uniswapV3PoolDispatch_mint <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  obtain ⟨k0, C0, r0⟩ := uniswapV3PoolReachMintBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨948⟩ [solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k0 C0 at r0
  rcases mintDecodeX (v := v) r0 hsz hsize (by simp) with
    ⟨hbad, rr⟩ | ⟨hvalid, k1, C1, r1⟩
  · exact rr.reEquivDecodingFailed hcode hd (mintDecodeInvalid hbad)
  · let a := mintDecodedArgs I.calldata
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := mintDecodeValid hvalid
    rcases mintReadLockX (v := v) r1 (by simp) with
      ⟨rr, hlocked⟩ | ⟨hunlocked, k2, C2, r2⟩
    · exact rr.reEquivExecutionRevert hcode hd hdec (mintRevertsLocked v a evm hwv hlocked)
    · cases hperm : I.perm with
      | false =>
          exact (mintLockStaticX (v := v) r2 hperm (by simp)).reEquivStaticHalt hcode hd hdec
            (mintStatic v a evm hwv hunlocked hperm)
      | true =>
          have hs : SourceState evm I σ evm := ⟨rfl, rfl, rfl⟩
          have hlen : (UInt256.ofNat (mintDataLength I.calldata)).toNat = mintDataLength I.calldata :=
            ulit_toNat' _ (by have := hvalid.length; change _ < 2 ^ 256; omega)
          have hstart : (UInt256.ofNat (mintDataStart I.calldata)).toNat = mintDataStart I.calldata :=
            ulit_toNat' _ (lt_of_le_of_lt hvalid.length_word hsize)
          rcases mintBodyX (v := v) a evm hs r2 (mintDecodedArgs_fits I.calldata) hwv hunlocked
              hperm (by rw [hstart, hlen]; rfl) (by rw [hstart, hlen]; exact hvalid.payload)
              (by rw [hlen]; exact hvalid.length) (by simp) with
            ⟨hbody, rr⟩ | ⟨hbody, rr⟩ | ⟨frame, evm', a0, a1, hbody, rr⟩
          · rcases rr with rr | rr
            · exact rr.reEquivExecutionRevert hcode hd hdec hbody
            · exact RDinvalid.reEquivExecutionInvalid hcode rr hd hdec hbody
          · exact rr.reEquivStaticHalt hcode hd hdec hbody
          · exact rr.reEquivExecutionGen hcode hd hdec hbody rfl
              (returnEquiv.returned rfl (uintPairReturnEncoding ⟨256, by decide⟩ ⟨256, by decide⟩
                a0 a1 a0.val.isLt a1.val.isLt))

end Benchmarks.UniswapV3.Pool
