import Benchmarks.UniswapV4PoolManager.UnlockAllocationGas
import Benchmarks.UniswapV4PoolManager.UnlockReplyFootprint
import Benchmarks.UniswapV4PoolManager.CallbackMemoryGas
import Benchmarks.UniswapV4PoolManager.CallbackOperationGas
import Benchmarks.UniswapV4PoolManager.UnlockPrecompile

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem unlockAllocationBounds_small {out : ByteArray} (hb : BytesReturnBounds out)
    (hs : out.size ≤ 64) (first : Bool) : unlockAllocationBounds out first := by
  have ho : (UInt256.ofNat out.size).toNat = out.size :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hp : (unlockRawEnd out).toNat = 160+paddedSize out.size := by
    rw [allocationEnd_toNat _ _ (by rw [ho]; change 160+out.size+31 < 2^256; omega), ho]
    rfl
  have he := unlockDecodedEnd_toNat (by omega : out.size < 2^138) hb
  have hl : (unlockReturnLength out).toNat ≤ 64 := by
    have h := hb.2.2.2.2.2
    change (calldataWord out 0).toNat+32+(unlockReturnLength out).toNat ≤ out.size at h
    omega
  have hpad := paddedSize_le_add31 out.size
  have hpad' := paddedSize_le_add31 (unlockReturnLength out).toNat
  cases first with
  | true =>
    change 160 ≤ (unlockRawEnd out).toNat ∧ (unlockRawEnd out).toNat ≤ 2^64-1
    rw [hp]
    omega
  | false =>
    change (unlockRawEnd out).toNat ≤ (unlockDecodedEnd out).toNat ∧
      (unlockDecodedEnd out).toNat ≤ 2^64-1
    rw [hp, he]
    omega

/-- Every allocation failure after a successful ordinary EVM callback exhausts the permitted gas. -/
theorem unlockAllocationFailure_nonprecompile {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {out data : ByteArray} {aw : UInt256} {C : Nat} {target : AccountAddress}
    (v : PoolManagerImmutables)
    (w : ZeroCallGasEvidence evm target data evm' true out) (hn : target ∉ π)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hout : out.size < 2^138) (hpaid : 1094+Cₘ aw+w.spent ≤ C)
    (h : UnlockAllocationFailure (deployedRuntime v) I g s0 evm'.accountMap out aw C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  obtain ⟨hb, first, mem', aw', k', C', R, hbad, hs, hw, hc, rd⟩ := h
  cases first with
  | true =>
    exact unlockRawAllocationGas v hgas hout hbad (by omega) hw hc rd
  | false =>
    change ¬AllocationBounds (unlockRawEnd out) (bytesAllocationSize (unlockReturnLength out)) at hbad
    change C+352+3*((out.size+31)/32)+Cₘ aw' ≤ C'+Cₘ aw at hc
    rcases unlockSecondAllocation_range hout hb hbad with hlarge | ⟨hlo, hhi, hlen, hlen', hoff, hoff'⟩
    · have hp := w.memoryCost_le_spent hn
      exact unlockLargeReplyAllocationGas v hgas hout hlarge (by omega) hw hc rd
    · have hf := unlockCriticalReplyFootprint hb hlen hlen' hoff hoff'
      have hp := w.returnWork_le_spent hn (by rw [hf]; omega)
      rw [hf] at hp
      exact unlockCriticalReplyAllocationGas v hs hgas hout hlo (by omega) hw hc rd

/-- Capacity panic after any successful unlock callback is an out-of-gas path. -/
theorem unlockAllocationFailure_outOfGas {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {out data : ByteArray} {aw : UInt256} {C : Nat} {target : AccountAddress}
    (v : PoolManagerImmutables)
    (w : ZeroCallGasEvidence evm target (unlockCallbackSelector++bytesReturnEncoding data) evm' true out)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (hout : out.size < 2^138) (hpaid : 1094+Cₘ aw+w.spent ≤ C)
    (h : UnlockAllocationFailure (deployedRuntime v) I g s0 evm'.accountMap out aw C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  by_cases hp : target ∈ π
  · obtain ⟨hb, first, _, _, _, _, _, hbad, _⟩ := h
    exact (hbad (unlockAllocationBounds_small hb (w.unlock_precompile_size hp hb) first)).elim
  · exact unlockAllocationFailure_nonprecompile v w hp hgas hout hpaid h

end Benchmarks.UniswapV4PoolManager
