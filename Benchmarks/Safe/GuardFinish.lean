import Benchmarks.Safe.GuardCall
import Benchmarks.Safe.GuardRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeGuardFinish {σ σ₀ σ' : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    {guard : UInt256} {evm' : EVM.State} {locals : Store} {mem out : ByteArray}
    {aw : UInt256} {k C : Nat} {R : List UInt256}
    (hcode : I.code = safeBytecode)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setguardTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      (setguardTransition.params.map Param.name) (transitionSignature setguardTransition).paramTypes
      I.calldata = some (guardArgs .transaction guard))
    (hc : guard.toNat < EVM.addressModulus) (hv : I.weiValue = ⟨0⟩)
    (ha : I.source = I.codeOwner)
    (hg : locals["guard"]? = some (.address (AccountAddress.ofNat guard.toNat)))
    (hb : locals.get? "_guard" = none) (hee : evm'.executionEnv = I)
    (hacc : evm'.accountMap = σ')
    (hcheck : ExecStmt config (guardFrame .transaction guard) (initState σ σ₀ (.ofUInt256 g) A I)
      (guardCheck .transaction)
      (.ok { contract := contract, locals := locals } evm'))
    (h : RD safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨6158⟩
      (guard :: ⟨664⟩ :: R) mem aw out σ' k C)
    (hov : R.length + 6 ≤ 1024) : runtimeRefinementFor config contract σ σ₀ g A I := by
  exact guardFinish (kind := .transaction) hcode hdispatch hdec hc hv ha hg hb hee hacc hcheck
    (fun hp ↦ safeGuardStoreStatic h (by simp; omega) hp)
    (fun hp ↦ safeGuardStoreTrace h hov hp)

end Benchmarks.Safe
