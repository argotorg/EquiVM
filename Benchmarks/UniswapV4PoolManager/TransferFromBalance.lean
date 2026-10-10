import Benchmarks.UniswapV4PoolManager.TransferFromTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

/-- All authorization branches join here, with the account map produced by authorization. -/
theorem transferFromBalanceCore {σ σ₀ A I} {g : UInt256}
    {evm : EVM.State} {f : Frame} {args : Store}
    {sender receiver id amount : UInt256} {mem : ByteArray} {aw : UInt256}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v)
    (hd : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = some args)
    (henv : evm.executionEnv = I) (hc : receiver.toNat < EVM.addressModulus)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96)
    (hptr : memLoad ⟨64⟩ mem = ⟨160⟩)
    (hbody : ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      args transferFromTransition.body (balanceTransferResult f evm sender receiver id amount) (immStore v))
    (h : RD (deployedRuntime v) I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨537⟩
      (transferFromStack sender receiver id amount R) mem aw .empty evm.accountMap k C) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  obtain ⟨aws, ks, Cs, rdSub⟩ := transferFromBalanceLoadTrace v hstack hmem h
  have hload : balanceWord evm sender id = solcSlotWordAt (balanceSlot sender id) evm.accountMap I :=
    storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (congrArg ExecutionEnv.codeOwner henv)
  rw [← hload] at rdSub
  rw [balanceTransferResult, henv] at hbody
  by_cases hsub : amount.toNat ≤ (balanceWord evm sender id).toNat
  · rw [if_pos hsub] at hbody
    have hj570 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 570) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    obtain ⟨kd, Cd, rdStore⟩ := checkedSubPass v
      (by simp only [transferFromStack, List.length_cons]; omega) hsub hj570 rdSub
    cases hperm : I.perm with
    | false =>
      rw [if_pos hperm] at hbody
      have hstatic := transferFromBalanceStaticTrace v
        (by simp only [transferFromStack, List.length_cons]; omega) hperm rdStore
      exact hstatic.reEquivStaticHalt hcode hd hdec hbody
    | true =>
      have hpfalse : ¬ I.perm = false := by simp only [hperm, Bool.true_eq_false, not_false_eq_true]
      rw [if_neg hpfalse] at hbody
      let evm1 := balanceTransferDebited evm sender id amount
      have henv1 : evm1.executionEnv = I := (balancePost_env _ _ _ _).trans henv
      have hacc1 : sstoreAccountMap I.codeOwner evm.accountMap (balanceSlot sender id)
          (UInt256.sub (balanceWord evm sender id) amount) = evm1.accountMap := by
        change _ = (Solm.EVM.storageStore evm evm.executionEnv.codeOwner _ _).accountMap
        rw [henv]
        exact (storageStore_accountMap _ _ _ _).symm
      have hmem1 := nestedMappingMemory_size sender id ⟨4⟩ hmem
      obtain ⟨awr, kr, Cr, rdAdd⟩ := transferFromBalanceCreditTrace v hstack hmem1 hc hperm rdStore
      have hload2 : balanceWord evm1 receiver id = solcSlotWordAt (balanceSlot receiver id)
          (sstoreAccountMap I.codeOwner evm.accountMap (balanceSlot sender id)
            (UInt256.sub (balanceWord evm sender id) amount)) I := by
        rw [hacc1]
        exact storageLoad_codeOwner_eq_solcSlotWordAt evm1 I _ (congrArg ExecutionEnv.codeOwner henv1)
      rw [← hload2] at rdAdd
      by_cases hadd : (balanceWord evm1 receiver id).toNat + amount.toNat < UInt256.size
      · rw [if_pos hadd] at hbody
        have hj607 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 607) = true := by
          rw [deployedRuntime_jumps]; jump_dest
        obtain ⟨kf, Cf, rdFinal⟩ := checkedAddPass v
          (by simp only [List.length_cons]; omega) hadd hj607 rdAdd
        have hmem2 := nestedMappingMemory_size receiver id ⟨4⟩ hmem1
        have hptr2 : memLoad ⟨64⟩ (nestedMappingMemory receiver id ⟨4⟩
            (nestedMappingMemory sender id ⟨4⟩ mem)) = ⟨160⟩ := by
          rw [nestedMappingMemory_load64 _ _ _ hmem1, nestedMappingMemory_load64 _ _ _ hmem, hptr]
        have hret := transferFromBalanceReturnTrace v hstack hmem2 hptr2 hperm rdFinal
        have hacc2 : sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner evm.accountMap (balanceSlot sender id)
              (UInt256.sub (balanceWord evm sender id) amount))
            (balanceSlot receiver id) (balanceWord evm1 receiver id + amount) =
            (balanceTransferPost evm sender receiver id amount).accountMap := by
          rw [hacc1]
          change _ = (Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner _ _).accountMap
          rw [henv1]
          exact (storageStore_accountMap _ _ _ _).symm
        exact hret.reEquivExecutionGen hcode hd hdec hbody hacc2
          (returnEquiv_of_encode (boolReturnEncoding true))
      · rw [if_neg hadd] at hbody
        exact (checkedAddReverts v (by simp only [List.length_cons]; omega)
          (Nat.le_of_not_gt hadd) rdAdd).reEquivExecutionRevert hcode hd hdec hbody
  · rw [if_neg hsub] at hbody
    exact (checkedSubReverts v (by simp only [transferFromStack, List.length_cons]; omega)
      (Nat.lt_of_not_ge hsub) rdSub).reEquivExecutionRevert hcode hd hdec hbody

end Benchmarks.UniswapV4PoolManager
