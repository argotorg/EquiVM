import Benchmarks.Safe.V0_cdb2eb5.ModuleGuardTrace
import Benchmarks.Safe.V0_cdb2eb5.TypedStaticCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V0_cdb2eb5

theorem safeModuleGuardCall {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {k C : Nat} {aw gasArg guard : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g (initState σ σ₀ g A I) ⟨5739⟩
      (gasArg :: guard :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: R)
      (guardCallMemory .moduleGuard) aw ByteArray.empty σ k C)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray) (aw' : UInt256)
      (k' C' : Nat),
      typedCallViaEVM fork config (initState σ σ₀ g A I) (AccountAddress.ofNat guard.toNat)
        "supportsInterface" 0 [guardInterfaceValue .moduleGuard] (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧
      RD fork safeBytecode I g (initState σ σ₀ g A I) ⟨5740⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: R) ((guardOutputMemory .moduleGuard) out) aw' out σ' k' C' ∧
      out.size < 2 ^ 138 := by
  obtain ⟨evm', σ', z, out, aw', k', C', hc, hee, hacc, hr, hout⟩ :=
    typedStaticCallTrace h (by native_decide) (guardInterfaceEncoding (kind := .moduleGuard))
      (guardCallInputSize (kind := .moduleGuard)) hov
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size :=
    callOutputLength (lt_trans hout (by decide))
  simp only [callOutputMem, hlen] at hr
  exact ⟨evm', σ', z, out, aw', k', C', hc, hee, hacc, hr, hout⟩

end Benchmarks.Safe.V0_cdb2eb5
