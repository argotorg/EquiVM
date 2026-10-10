import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.UnlockDecodeTrace
import Benchmarks.UniswapV4PoolManager.UnlockBodyTrace

/-!
# PoolManager `unlock(bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 8810; reach lemma `poolManagerReachUnlockBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 5000

/-- `unlock(bytes)`: the theorem `Correct.lean` routes selector 14 to. -/
theorem poolManagerUnlockBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 14)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 14) rfl hsel
  have hd : dispatchMsg contract I.calldata = some unlockTransition := by
    apply poolManagerDispatch_unlock <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, hC, rdEntry⟩ := poolManagerReachUnlockBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8810⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdDecode := poolManagerBlocks.poolManager_block_8810_fallthrough (by simp) hwv rdEntry
    rcases unlockDecodeTrace v (by simp) hsz hsize rdDecode with ⟨hbad, hr⟩ | ⟨hb, k', C', hcost, rdBody⟩
    · exact hr.reEquivDecodingFailed hcode hd (decodeCalldata_bytes_none "data" hbad)
    · let args := (∅ : Store).insert "data" (.bytes (calldataBytesPayload I.calldata))
      let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let f := calldataFrame contract args (immStore v) evm
      have hdec : decodeCalldataWithMode config.abiDecodeMode (unlockTransition.params.map Param.name)
          (transitionSignature unlockTransition).paramTypes I.calldata = some args :=
        decodeCalldata_bytes_ok "data" hb
      have hdata : f.locals.get? "data" = some (.bytes (calldataBytesPayload I.calldata)) :=
        (store_get_ne _ _ (by decide : ("__calldata" == "data") = false)).trans (store_get_self _ _ _)
      rcases unlockBodyTrace (g := Sat256.ofUInt256 g) (evm := evm) (f := f) v (by simp) rfl rfl rfl hdata hb hGas
        (by change 561 ≤ C'; omega) entryMemory_size entryMemory_load64 rdBody with hoog | ⟨result, hs, ht⟩
      · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
      · have hbody : ExecTransitionBody config contract evm args unlockTransition.body result (immStore v) :=
          nonpayableCalldataBody hwv (by change I.calldata.size < 2^255+4; have hh := hb.2.1; omega) hs
        exact bytesResultTrace_refinement hcode hd hdec hbody ht rfl rfl rfl
  · have rdRevert := poolManagerBlocks.poolManager_block_8810_taken (by simp) hwv
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd (fun _ => bodyReverts_nonPayable hwv)

end Benchmarks.UniswapV4PoolManager
