import Benchmarks.Safe.ViaIR.FallbackDispatch
import Benchmarks.Safe.ViaIR.FallbackSource
import Benchmarks.Safe.ViaIR.FallbackTrace
import Benchmarks.Safe.ViaIR.FallbackRefinement
import Benchmarks.Safe.ViaIR.FallbackGas
import Benchmarks.Safe.ViaIR.RawZeroCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeFallbackBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hnonempty : I.calldata.size ≠ 0)
    (hdispatch : selectorDispatchMsg contract I.calldata = none) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨R, k, C, hlen, h21⟩ := safeReachFallback (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hsize hnonempty hdispatch
  have hreceive : receiveDispatchMsg contract I.calldata = none := by
    simp only [receiveDispatchMsg, hnonempty, if_false]
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let handler := solcSlotWord σ I fallbackHandlerSlot
  have hh : fallbackHandler evm = handler := storageLoad_eq_solcSlotWord evm I _
  by_cases hv : I.weiValue = ⟨0⟩
  · have h26 := safeRuntime_block_21_fallthrough (by omega) hv h21
    by_cases hz : handler = ⟨0⟩
    · obtain ⟨_, _, h109⟩ := safeRuntime_block_26_taken (by omega)
        (by change UInt256.isZero handler ≠ ⟨0⟩; rw [hz]; decide) (by jump_dest) h26
      have hret := safeRuntime_block_109 (by
        simp only [safeRuntime_block_26_taken_stack, List.length_cons]
        omega) h109
      have hbody := safeFallbackZero (fork := fork) evm hv (hh.trans hz)
      exact RDret.reEquivElim hcode hret fun _ _ hΞ ↦
        reEquivFallbackExecution hdispatch hreceive rfl rfl rfl hbody
          (.success hΞ rfl rfl (.rawBytes rfl))
    · obtain ⟨_, _, h66⟩ := safeRuntime_block_26_fallthrough (by omega)
        (isZero_eq_zero_of_ne hz) h26
      change RD fork safeBytecode I (.ofUInt256 g) evm ⟨66⟩ (handler :: R)
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ _ _ at h66
      by_cases hsmall : I.calldata.size < 2 ^ 138
      · obtain ⟨aw, gasArg, k', C', h92⟩ := safeFallbackPrepare h66 (by omega)
        obtain ⟨evm', σ', z, out, aw', k'', C'', hcall, hee, hacc, h93, hout⟩ :=
          rawZeroCallTrace h92 (by native_decide) (by simp; omega)
        have hin : (UInt256.ofNat I.calldata.size + UInt256.ofNat 20).toNat =
            I.calldata.size + 20 := by
          exact uadd_ofNat_toNat hsize (by decide) (by
            change I.calldata.size + 20 < 2 ^ 256
            omega)
        rw [accountAddress_ofUInt256_eq_ofNat_toNat, hin,
          show (⟨128⟩ : UInt256).toNat = 128 from rfl,
          fallbackMemory_read I hnonempty hsmall, ← hh] at hcall
        rw [callOutputMem_zero] at h93
        change RD fork safeBytecode I (.ofUInt256 g) evm ⟨93⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨128⟩ :: R)
          (fallbackMemory I) aw' out σ' k'' C'' at h93
        have hn : fallbackHandler evm ≠ ⟨0⟩ := by rwa [hh]
        cases z with
        | false =>
            have hrev := safeFallbackRevert h93 (by omega) hout
            have hbody := safeFallbackCallFailure hv hn hcall
            exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
              reEquivFallbackExecution hdispatch hreceive rfl rfl rfl hbody (.revert hΞ rfl)
        | true =>
            have hret := safeFallbackReturn h93 (by omega) hout
              (by rw [fallbackMemory_size I hnonempty hsmall]; omega)
            have hbody := safeFallbackCallSuccess hv hn hcall
            exact reEquivReturnElim hcode hret fun _ _ hΞ ↦
              reEquivFallbackExecution hdispatch hreceive rfl rfl rfl hbody
                (.success hΞ rfl hacc.symm (.rawBytes rfl))
      · have hoog := safeFallbackHugeOOG h66 (by omega) hsize (by omega)
        exact reEquiv_outOfGas (xi_error_of_X_sat_local
          (by rw [← hcode] at hoog; exact hoog))
  · have h111 := safeRuntime_block_21_taken (by omega) hv (by jump_dest) h21
    have hrev := safeRuntime_block_111 (by omega) h111
    have hbody := safeFallbackValueRevert (fork := fork) evm hv
    exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
      reEquivFallbackExecution hdispatch hreceive rfl rfl rfl hbody (.revert hΞ rfl)

/-- Unmatched nonempty calldata follows the raw-return fallback. -/
theorem safeFallbackRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hnonempty : I.calldata.size ≠ 0)
    (hdispatch : selectorDispatchMsg contract I.calldata = none) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeFallbackBodyCore hcode hsize hnonempty hdispatch

end Benchmarks.Safe.ViaIR
