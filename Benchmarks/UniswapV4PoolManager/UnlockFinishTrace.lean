import Benchmarks.UniswapV4PoolManager.UnlockSource
import Benchmarks.UniswapV4PoolManager.UnlockCallTrace
import Benchmarks.UniswapV4PoolManager.UnlockAllocationFailureGas
import Benchmarks.UniswapV4PoolManager.BytesResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem unlockCallbackResult_trace {code : ByteArray} {g : Sat256} {s0 evm : State}
    {f : Frame} {out : ByteArray} (h : unlockReturnResultTrace code g s0 evm out) :
    bytesResultTrace code g s0 (unlockCallbackResult f evm true out) := by
  unfold unlockReturnResultTrace at h
  unfold unlockCallbackResult
  by_cases hb : BytesReturnBounds out
  · rw [if_pos ⟨rfl, hb⟩, unlockAfterCallbackResult]
    rw [if_pos hb] at h
    split <;> rename_i hz
    · simpa only [if_pos hz, bytesResultTrace] using h
    · simpa only [if_neg hz, bytesResultTrace] using h
  · rw [if_neg (fun h => hb h.2)]
    rw [if_neg hb] at h
    exact h

theorem unlockFinishTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata data : ByteArray} {aw ending saved : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀) (hp : I.perm = true)
    (hf : f.contract = contract) (hc : f.locals.get? "caller" = some (.address I.source))
    (hd : f.locals.get? "data" = some (.bytes data))
    (hr : f.locals.get? "result" = some (.bytes .empty))
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hpaid : 940+Cₘ aw ≤ C) (hmem : 160 ≤ mem.size)
    (hrequest : mem.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat =
      unlockCallbackSelector++bytesReturnEncoding data)
    (hsmall : (mem.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat).size ≤ maxReturnDataSizeByGas)
    (h : RD (deployedRuntime v) I g s0 ⟨9029⟩
      (ending :: ⟨160⟩ :: ⟨160⟩ :: ⟨0⟩ :: ⟨160⟩ :: saved :: R) mem aw rdata evm.accountMap k C) :
    (X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
      ∃ result, ExecFuncBody config f evm (unlockTransition.body.drop 8) result ∧
        bytesResultTrace (deployedRuntime v) g s0 result := by
  have hencode : config.externalABI.encode? "unlockCallback" [.bytes data] =
      some (mem.readWithPadding 160 (UInt256.sub ending ⟨160⟩).toNat) := by
    rw [hrequest]
    exact unlockCallbackEncode _
  rcases unlockCallTrace v (by simp only [List.length_cons]; omega) hI hσ0 hencode hsmall h with
    hoog | ⟨evm', z, out, hcall, hI', _, hout, ht⟩
  · exact .inl hoog
  have hb := unlockCallbackBody hf (by rw [hI']; exact hp) hc hd hr hcall
  cases z with
  | false =>
    exact .inr ⟨_, hb, by simpa only [unlockCallbackResult, Bool.false_eq_true,
      false_and, if_false, bytesResultTrace] using ht⟩
  | true =>
    obtain ⟨w, k', C', hcost, rd⟩ := ht
    rcases unlockReturnTrace v hstack hI' hp hout hmem rd with hfail | hret
    · let w' : ZeroCallGasEvidence evm I.source (unlockCallbackSelector++bytesReturnEncoding data)
          evm' true out := ⟨w.inputGas, w.returnedGas, w.inputSubstate, by rw [← hrequest]; exact w.theta⟩
      exact .inl (unlockAllocationFailure_outOfGas v w' hgas hout (by
        change 1094+_+w.spent ≤ C'
        omega) hfail)
    · exact .inr ⟨_, hb, unlockCallbackResult_trace hret⟩

end Benchmarks.UniswapV4PoolManager
