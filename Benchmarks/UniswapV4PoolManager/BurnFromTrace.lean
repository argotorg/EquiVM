import Benchmarks.UniswapV4PoolManager.BurnAllowanceStatic
import Benchmarks.UniswapV4PoolManager.BurnFromSource

/-! The complete internal burnFrom trace, including allowance and balance failures. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

@[irreducible] def burnFromTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (sender id amount : UInt256) : Prop :=
  if transferFromNeedsAllowance evm sender then
    let allowed := transferFromAllowed evm sender id
    if allowed = maxAllowanceWord then balanceBurnTraceResult v I g s0 evm sender id amount else
    if amount.toNat ≤ allowed.toNat then
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else
      balanceBurnTraceResult v I g s0 (transferFromAllowancePost evm sender id amount) sender id amount
    else RDrev (deployedRuntime v) g s0
  else balanceBurnTraceResult v I g s0 evm sender id amount

theorem burnFromTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {mem rdata : ByteArray} {aw sender id amount extra : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96)
    (hI : evm.executionEnv = I) (hcs : sender.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨955⟩ (burnFromStack sender id amount (extra :: R)) mem aw rdata evm.accountMap k C) :
    burnFromTraceResult v I g s0 evm sender id amount := by
  have hop : operatorWord evm sender (accountWord I.source) =
      UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) evm.accountMap I) ⟨255⟩ := by
    rw [operatorWord, storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])]
    rfl
  have hneedIff : transferFromNeedsAllowance evm sender ↔
      accountWord I.source ≠ sender ∧
        UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) evm.accountMap I) ⟨255⟩ = ⟨0⟩ := by
    simp only [transferFromNeedsAllowance, hI, hop]
  have hread : transferFromAllowed evm sender id =
      solcSlotWordAt (allowanceSlot sender (accountWord I.source) id) evm.accountMap I := by
    unfold transferFromAllowed
    rw [hI]
    exact storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])
  rw [burnFromTraceResult]
  generalize hallowed : transferFromAllowed evm sender id = allowed at hread ⊢
  by_cases hneed : transferFromNeedsAllowance evm sender
  · rw [if_pos hneed]
    obtain ⟨awo, ko, Co, h1010⟩ := burnNeedAllowanceTrace v
      (by simp only [List.length_cons]; omega) hmem hcs (hneedIff.mp hneed) h
    have hmemO : (transferFromOperatorMemory I sender mem).size = 96 := nestedMappingMemory_size _ _ _ hmem
    obtain ⟨awa, ka, Ca, hcheck⟩ := burnAllowanceReadTrace v
      (by simp only [List.length_cons]; omega) hmemO h1010
    rw [← hread] at hcheck
    have hmemA : (transferFromAllowanceMemory I sender id (transferFromOperatorMemory I sender mem)).size = 96 :=
      tripleMappingMemory_size _ _ _ _ hmemO
    have hj972 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 972) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    by_cases hmax : allowed = maxAllowanceWord
    · rw [if_pos hmax] at hcheck ⊢
      have hbalance := poolManagerBlocks.poolManager_block_1106
        (by change R.length + 1 + 6 + 2 ≤ 1024; omega) hj972 hcheck
      exact balanceBurnTrace v (by simp only [List.length_cons]; omega) hmemA hI hbalance
    · rw [if_neg hmax] at hcheck ⊢
      have hjSub : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12269) = true := by
        rw [deployedRuntime_jumps]; jump_dest
      have hsub := poolManagerBlocks.poolManager_block_1113
        (by change R.length + 1 + 6 + 4 ≤ 1024; omega) hjSub hcheck
      by_cases hfit : amount.toNat ≤ allowed.toNat
      · rw [if_pos hfit]
        have hjStore : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 1122) = true := by
          rw [deployedRuntime_jumps]; jump_dest
        obtain ⟨ks, Cs, hstore⟩ := checkedSubPass v
          (by simp only [balanceBurnStack, List.length_cons]; omega) hfit hjStore hsub
        by_cases hp : I.perm = false
        · rw [if_pos hp]
          exact burnAllowanceStaticTrace (by omega) hp hstore
        · rw [if_neg hp]
          obtain ⟨awf, kf, Cf, hbalance⟩ := burnAllowanceStoreTrace v (by omega) hmemA
            (Bool.eq_true_of_not_eq_false hp) hstore
          have hacc : sstoreAccountMap I.codeOwner evm.accountMap (allowanceSlot sender (accountWord I.source) id)
              (UInt256.sub allowed amount) = (transferFromAllowancePost evm sender id amount).accountMap := by
            rw [transferFromAllowancePost, storageStore_accountMap, hI, hallowed]
          rw [hacc] at hbalance
          have hmemS := tripleMappingMemory_size sender (accountWord I.source) id ⟨5⟩ hmemA
          exact balanceBurnTrace v (by simp only [List.length_cons]; omega) hmemS
            ((storageStore_executionEnv _ _ _ _).trans hI) hbalance
      · rw [if_neg hfit]
        exact checkedSubReverts v (by simp only [balanceBurnStack, List.length_cons]; omega) (Nat.lt_of_not_ge hfit) hsub
  · rw [if_neg hneed]
    obtain ⟨mem', aw', k', C', hmem', hbalance⟩ := burnSkipAllowanceTrace v
      (by simp only [List.length_cons]; omega) hmem hcs (hneedIff.not.mp hneed) h
    exact balanceBurnTrace v (by simp only [List.length_cons]; omega) hmem' hI hbalance

end Benchmarks.UniswapV4PoolManager
