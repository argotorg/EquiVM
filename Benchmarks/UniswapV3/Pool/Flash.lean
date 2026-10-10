import Benchmarks.UniswapV3.Pool.FlashBodyTail
import Benchmarks.UniswapV3.Pool.FlashStart
import Benchmarks.UniswapV3.Pool.FlashDecodeTrace
import Benchmarks.UniswapV3.Pool.BalanceFreshMemory

/-!
# UniswapV3Pool `flash(address,uint256,uint256,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1136; reach lemma `uniswapV3PoolReachFlashBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

set_option maxRecDepth 2000000

/-- `flash(address,uint256,uint256,bytes)`: the theorem `Correct.lean` routes selector 9 to. -/
theorem uniswapV3PoolFlashBody {σ σ₀ A I} {g : UInt256} (v : UniswapV3PoolImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (uniswapV3PoolSelBytes 9)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (uniswapV3PoolSelBytes 9) rfl hsel
  have hd : dispatchMsg contract I.calldata = some flashTransition := by
    apply uniswapV3PoolDispatch_flash <;>
      first | exact hsel | exact selectorMismatch_of_match hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachFlashBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hwv hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
    ⟨1136⟩ [solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C at rdEntry
  rcases flashDecodeX (v := v) rdEntry hsz hsize (by simp) with
    ⟨hbad, rdBad⟩ | ⟨hvalid, kDecoded, CDecoded, rdDecoded⟩
  · exact rdBad.reEquivDecodingFailed hcode hd (flashDecodeInvalid hbad)
  · let a := flashDecodedArgs I.calldata
    let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hdec := flashDecodeValid hvalid
    rcases flashStartX (v := v) a rdDecoded SourceState.init hwv (by simp) with
      ⟨rdBad, hsourceBad⟩ | ⟨rdStatic, hsourceStatic⟩ |
        ⟨hperm, kReady, CReady, hsReady, hsourceStart, rdReady⟩
    · exact rdBad.reEquivExecutionRevert hcode hd hdec hsourceBad
    · exact rdStatic.reEquivStaticHalt hcode hd hdec hsourceStatic
    · have hlen : (UInt256.ofNat (flashDataLength I.calldata)).toNat =
          flashDataLength I.calldata := ulit_toNat' _ (by
        have h := hvalid.length
        change _ < 2 ^ 256
        omega)
      have hstart : (UInt256.ofNat (flashDataStart I.calldata)).toNat =
          flashDataStart I.calldata := ulit_toNat' _ (lt_of_le_of_lt hvalid.length_word hsize)
      rcases flashBodyTailX (v := v) a rdReady hsReady hperm freshHeapMemory
          (balanceCopyBuild_fresh_zero I.codeOwner)
          (by rw [hstart, hlen]; rfl) (by rw [hstart, hlen]; exact hvalid.payload)
          (by rw [hlen]; exact hvalid.length) (poolLiquidityWord_lt _ _) (by decide) (by simp) with
        ⟨rdBad, hsourceBad⟩ | ⟨evmFinal, localsFinal, hsourceTail, rdFinal⟩
      · apply rdBad.reEquivExecutionRevert hcode hd hdec
        apply ExecFuncBody.execBlockRevert
        rw [← List.take_append_drop 6 flashTransition.body]
        exact execBlock_append_ok hsourceStart hsourceBad
      · have hsource : ExecTransitionBody config contract evm (flashLocals a) flashTransition.body
            (.returned {contract := contract, locals := localsFinal, immutables := immStore v}
              evmFinal none) (immStore v) := by
          apply ExecFuncBody.execBlockOK
          rw [← List.take_append_drop 6 flashTransition.body]
          exact execBlock_append_ok hsourceStart hsourceTail
        exact rdFinal.reEquivExecutionGen hcode hd hdec hsource rfl
          (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))

end Benchmarks.UniswapV3.Pool
