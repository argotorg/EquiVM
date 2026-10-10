import Benchmarks.Morpho.MetaMorphoV1_1.TransferInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.TransferRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.TransferStatic

/-! Runtime interface for a transfer called after other storage updates. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem transferFunctionReturn {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {sender recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hgood : transferAllowed evm sender recipient value) (hperm : evm.executionEnv.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨12728⟩
      (UInt256.ofNat sender.toNat :: UInt256.ofNat recipient.toNat :: value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ret R
      mem' aw' rdata (balanceMoveState evm sender recipient value).accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := transferReachBalance v (by omega) hgood.1 hgood.2.1 rd
  obtain ⟨aw2, k2, C2, h2⟩ := transferReadBalance v
    (by simp only [List.length_cons]; omega) hgood.2.2 h1
  obtain ⟨aw3, k3, C3, h3⟩ := transferStoreReturn v hstack hperm hret h2
  rw [← balanceMoveState_accounts] at h3
  exact ⟨_, aw3, k3, C3, h3⟩

theorem transferFunctionRevert {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {sender recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hbad : ¬ transferAllowed evm sender recipient value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨12728⟩
      (UInt256.ofNat sender.toNat :: UInt256.ofNat recipient.toNat :: value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases haddr : sender ≠ ⟨0, by decide⟩ ∧ recipient ≠ ⟨0, by decide⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := transferReachBalance v (by omega) haddr.1 haddr.2 rd
    exact transferRevertBalance v (by simp only [List.length_cons]; omega)
      (fun h ↦ hbad ⟨haddr.1, haddr.2, h⟩) h1
  · exact transferRevertAddress v (by omega) haddr rd

theorem transferFunctionStatic {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {sender recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hgood : transferAllowed evm sender recipient value) (hperm : evm.executionEnv.perm = false)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨12728⟩
      (UInt256.ofNat sender.toNat :: UInt256.ofNat recipient.toNat :: value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    RDstatic (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := transferReachBalance v (by omega) hgood.1 hgood.2.1 rd
  obtain ⟨aw2, k2, C2, h2⟩ := transferReadBalance v
    (by simp only [List.length_cons]; omega) hgood.2.2 h1
  exact transferStoreStatic v hstack hperm h2

end Benchmarks.Morpho.MetaMorphoV1_1
