import Benchmarks.Safe.FallbackDispatch
import Benchmarks.Safe.FallbackSource
import Benchmarks.Safe.FallbackTrace
import Benchmarks.Safe.FallbackRefinement
import Benchmarks.Safe.FallbackGas
import Benchmarks.Safe.RawZeroCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeFallbackBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hnonempty : I.calldata.size ≠ 0)
    (hdispatch : selectorDispatchMsg contract I.calldata = none) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨R, k, C, hlen, h535⟩ := safeReachFallback (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hsize hnonempty hdispatch
  have hreceive : receiveDispatchMsg contract I.calldata = none := by
    simp only [receiveDispatchMsg, hnonempty, if_false]
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let handler := solcSlotWord σ I fallbackHandlerSlot
  have hh : fallbackHandler evm = handler := storageLoad_eq_solcSlotWord evm I _
  by_cases hv : I.weiValue = ⟨0⟩
  · have h546 := safeRuntime_block_535_taken (by omega) (by rw [hv]; decide)
      (by jump_dest) h535
    by_cases hz : handler = ⟨0⟩
    · obtain ⟨_, _, h587⟩ := safeRuntime_block_546_fallthrough (by omega) hz h546
      have hret := safeRuntime_block_587 (by
        simp only [safeRuntime_block_546_fallthrough_stack, List.length_cons]
        omega) h587
      have hbody := safeFallbackZero evm hv (hh.trans hz)
      exact RDret.reEquivElim hcode hret fun _ _ hΞ ↦
        reEquivFallbackExecution hdispatch hreceive rfl rfl rfl hbody
          (.success hΞ rfl rfl (.rawBytes rfl))
    · obtain ⟨_, _, h588⟩ := safeRuntime_block_546_taken (by omega) hz (by jump_dest) h546
      change RD safeBytecode I (.ofUInt256 g) evm ⟨588⟩ (handler :: R)
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ _ _ at h588
      by_cases hsmall : I.calldata.size < 2 ^ 138
      · obtain ⟨aw, gasArg, k', C', h614⟩ := safeFallbackPrepare h588 (by omega)
        obtain ⟨evm', σ', z, out, aw', k'', C'', hcall, hee, hacc, h615, hout⟩ :=
          rawZeroCallTrace h614 (by native_decide) (by simp; omega)
        have hin : (UInt256.ofNat I.calldata.size + UInt256.ofNat 20).toNat =
            I.calldata.size + 20 := by
          exact uadd_ofNat_toNat hsize (by decide) (by
            change I.calldata.size + 20 < 2 ^ 256
            omega)
        rw [accountAddress_ofUInt256_eq_ofNat_toNat, hin,
          show (⟨128⟩ : UInt256).toNat = 128 from rfl,
          fallbackMemory_read I hnonempty hsmall, ← hh] at hcall
        rw [callOutputMem_zero] at h615
        change RD safeBytecode I (.ofUInt256 g) evm ⟨615⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨128⟩ :: handler :: R)
          (fallbackMemory I) aw' out σ' k'' C'' at h615
        have hn : fallbackHandler evm ≠ ⟨0⟩ := by rwa [hh]
        cases z with
        | false =>
            have hrev := safeFallbackRevert h615 (by omega) hout
            have hbody := safeFallbackCallFailure hv hn hcall
            exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
              reEquivFallbackExecution hdispatch hreceive rfl rfl rfl hbody (.revert hΞ rfl)
        | true =>
            have hret := safeFallbackReturn h615 (by omega) hout
              (by rw [fallbackMemory_size I hnonempty hsmall]; omega)
            have hbody := safeFallbackCallSuccess hv hn hcall
            exact reEquivReturnElim hcode hret fun _ _ hΞ ↦
              reEquivFallbackExecution hdispatch hreceive rfl rfl rfl hbody
                (.success hΞ rfl hacc.symm (.rawBytes rfl))
      · have hoog := safeFallbackHugeOOG h588 (by omega) hsize (by omega)
        exact reEquiv_outOfGas (xi_error_of_X_sat_local
          (by rw [← hcode] at hoog; exact hoog))
  · have h543 := safeRuntime_block_535_fallthrough (by omega) (isZero_eq_zero_of_ne hv) h535
    have hrev := safeRuntime_block_543 (by
      simp only [safeRuntime_block_535_fallthrough_stack, List.length_cons]
      omega) h543
    have hbody := safeFallbackValueRevert evm hv
    exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
      reEquivFallbackExecution hdispatch hreceive rfl rfl rfl hbody (.revert hΞ rfl)

/-- Unmatched nonempty calldata follows the raw-return fallback. -/
theorem safeFallbackRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hnonempty : I.calldata.size ≠ 0)
    (hdispatch : selectorDispatchMsg contract I.calldata = none) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeFallbackBodyCore hcode hsize hnonempty hdispatch

end Benchmarks.Safe
