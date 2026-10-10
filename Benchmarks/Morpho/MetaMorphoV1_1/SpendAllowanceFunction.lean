import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceStore
import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceStatic

/-! Runtime interface for the shared allowance-spending helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem allowanceWord_accounts (evm : State) (owner spender : AccountAddress) :
    allowanceWord evm owner spender =
      codeOwnerStorageWord evm.executionEnv evm.accountMap (approvalSlot owner spender) := rfl

theorem spendAllowanceFunctionReturn {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {owner spender : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hgood : spendAllowanceAllowed evm owner spender value)
    (hwrite : allowanceWord evm owner spender = unlimitedAllowance ∨ evm.executionEnv.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨12530⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ret R
      mem' aw' rdata (spendAllowanceState evm owner spender value).accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := spendAllowanceLookup v
    (by simp only [List.length_cons]; omega) rd
  rw [← allowanceWord_accounts] at h1
  by_cases hmax : allowanceWord evm owner spender = unlimitedAllowance
  · rw [if_pos hmax] at h1
    rw [spendAllowanceState, if_pos hmax]
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12579_packed
      (immWords := wordsOf (immStore v)) (by omega) hret h1
    exact ⟨_, aw2, k2, C2, h2⟩
  · rw [if_neg hmax] at h1
    have hg := hgood.resolve_left hmax
    obtain ⟨aw2, k2, C2, h2⟩ := spendAllowanceReachStore v
      (by simp only [List.length_cons]; omega) hg h1
    obtain ⟨aw3, k3, C3, h3⟩ := spendAllowanceStoreReturn v (by omega)
      (hwrite.resolve_left hmax) hret h2
    rw [spendAllowanceState, if_neg hmax, approvalState, storageStore_accountMap]
    exact ⟨_, aw3, k3, C3, h3⟩

theorem spendAllowanceFunctionRevert {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {owner spender : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hbad : ¬ spendAllowanceAllowed evm owner spender value)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨12530⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := spendAllowanceLookup v
    (by simp only [List.length_cons]; omega) rd
  rw [← allowanceWord_accounts, if_neg (fun h ↦ hbad (.inl h))] at h1
  exact spendAllowanceRevertGuard v (by simp only [List.length_cons]; omega)
    (fun h ↦ hbad (.inr h)) h1

theorem spendAllowanceFunctionStatic {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {owner spender : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hgood : spendAllowanceAllowed evm owner spender value)
    (hfinite : allowanceWord evm owner spender ≠ unlimitedAllowance)
    (hperm : evm.executionEnv.perm = false)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨12530⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    RDstatic (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := spendAllowanceLookup v
    (by simp only [List.length_cons]; omega) rd
  rw [← allowanceWord_accounts, if_neg hfinite] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := spendAllowanceReachStore v
    (by simp only [List.length_cons]; omega) (hgood.resolve_left hfinite) h1
  exact spendAllowanceStoreStatic v (by omega) hperm h2

end Benchmarks.Morpho.MetaMorphoV1_1
