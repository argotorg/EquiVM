import Benchmarks.Safe.ModuleGuardCall
import Benchmarks.Safe.GuardRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeModuleGuardFinish {σ σ₀ σ' : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {guard : UInt256} {evm' : EVM.State} {locals : Store} {mem out : ByteArray}
    {aw : UInt256} {k C : Nat} {R : List UInt256}
    (hcode : I.code = safeBytecode)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setmoduleguardTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      (setmoduleguardTransition.params.map Param.name)
      (transitionSignature setmoduleguardTransition).paramTypes
      I.calldata = some (guardArgs .moduleGuard guard))
    (hc : guard.toNat < EVM.addressModulus) (hv : I.weiValue = ⟨0⟩)
    (ha : I.source = I.codeOwner)
    (hg : locals["moduleGuard"]? = some (.address (AccountAddress.ofNat guard.toNat)))
    (hb : locals.get? "_moduleGuard" = none) (hee : evm'.executionEnv = I)
    (hacc : evm'.accountMap = σ')
    (hcheck : ExecStmt config (guardFrame .moduleGuard guard) (initState σ σ₀ (.ofUInt256 g) A I)
      (guardCheck .moduleGuard)
      (.ok { contract := contract, locals := locals } evm'))
    (h : RD safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨5908⟩
      (guard :: ⟨664⟩ :: R) mem aw out σ' k C)
    (hov : R.length + 6 ≤ 1024) : runtimeRefinementFor config contract σ σ₀ g A I := by
  exact guardFinish (kind := .moduleGuard) hcode hdispatch hdec hc hv ha hg hb hee hacc hcheck
    (fun hp ↦ safeModuleGuardStoreStatic h (by simp; omega) hp)
    (fun hp ↦ safeModuleGuardStoreTrace h hov hp)

end Benchmarks.Safe
