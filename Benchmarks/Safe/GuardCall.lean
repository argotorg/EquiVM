import Benchmarks.Safe.GuardTrace
import Benchmarks.Safe.TypedStaticCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeGuardCall {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {k C : Nat} {aw gasArg guard : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g (initState σ σ₀ g A I) ⟨6083⟩
      (gasArg :: guard :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: R)
      (guardCallMemory .transaction) aw ByteArray.empty σ k C)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      typedCallViaEVM config (initState σ σ₀ g A I) (AccountAddress.ofNat guard.toNat)
        "supportsInterface" 0 [guardInterfaceValue .transaction] (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧
      RD safeBytecode I g (initState σ σ₀ g A I) ⟨6084⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) ((guardOutputMemory .transaction) out) aw' out σ' k' C' ∧
      out.size < 2 ^ 138 := by
  obtain ⟨evm', σ', z, out, aw', k', C', hc, hee, hacc, hr, hout⟩ :=
    typedStaticCallTrace h (by native_decide) (guardInterfaceEncoding (kind := .transaction))
      (guardCallInputSize (kind := .transaction)) hov
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size :=
    callOutputLength (lt_trans hout (by decide))
  simp only [callOutputMem, hlen] at hr
  exact ⟨evm', σ', z, out, aw', k', C', hc, hee, hacc, hr, hout⟩

end Benchmarks.Safe
