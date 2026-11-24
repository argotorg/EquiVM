import Benchmarks.CurveVault.AllowanceSpendSites
import Benchmarks.CurveVault.Arithmetic
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultAllowanceSpendEVM (flow : VaultAllowanceSpendFlow) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner old value : UInt256} {R : List UInt256}
    (hsize : flow.allowanceOffset + 32 ≤ mem.size)
    (hmo : memLoad (UInt256.ofNat flow.ownerOffset) mem = owner)
    (hma : memLoad (UInt256.ofNat flow.allowanceOffset) mem = old)
    (hmv : flow.amount I mem = value) (hstack : R.length + 5 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.entry) R mem aw rdata σ k C) :
    (value.toNat ≤ old.toNat ∧ ∃ aw' k' C',
      RD fork vaultBytecode I g s0 (UInt256.ofNat 7939) (UInt256.ofNat flow.next :: R)
        (vaultApproveArguments mem owner (UInt256.ofNat I.source.val) (UInt256.sub old value)) aw' rdata σ k' C') ∨
    (old.toNat < value.toNat ∧ RDrev fork vaultBytecode g s0) := by
  let spender := UInt256.ofNat I.source.val
  let prepared := vaultSupplyArguments mem owner spender
  have hframe := vaultSupplyArguments_frame mem owner spender
  have ha0 : memLoad (UInt256.ofNat flow.allowanceOffset) prepared = old :=
    (hframe.load _ (by cases flow <;> decide +kernel) (by cases flow <;> decide +kernel)
      hsize (by cases flow <;> decide +kernel)).trans hma
  have hv0 : flow.amount I prepared = value := by
    cases flow
    · exact hmv
    · exact (hframe.load 672 (by omega) (by decide +kernel) (by exact le_trans (by decide +kernel) hsize)
        (by decide +kernel)).trans hmv
    · exact hmv
  by_cases hsub : value.toNat ≤ old.toNat
  swap
  · have hlt : old.toNat < value.toNat := by omega
    refine Or.inr ⟨hlt, ?_⟩
    cases flow with
    | transferFrom =>
      dsimp only [VaultAllowanceSpendFlow.ownerOffset, VaultAllowanceSpendFlow.allowanceOffset] at hmo ha0
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_5804_taken_packed hstack
        (by
          rw [hmo]
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 256) prepared)
            (VaultAllowanceSpendFlow.amount .transferFrom I prepared)) (memLoad (UInt256.ofNat 256) prepared) ≠ _
          rw [ha0, hv0, u256_sub_underflow_gt _ _ hlt]
          decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_5804_taken_stack, List.length_cons]; omega) rdFail
    | withdraw =>
      dsimp only [VaultAllowanceSpendFlow.ownerOffset, VaultAllowanceSpendFlow.allowanceOffset] at hmo ha0
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_4506_taken_packed hstack
        (by
          rw [hmo]
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 704) prepared)
            (VaultAllowanceSpendFlow.amount .withdraw I prepared)) (memLoad (UInt256.ofNat 704) prepared) ≠ _
          rw [ha0, hv0, u256_sub_underflow_gt _ _ hlt]
          decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_4506_taken_stack, List.length_cons]; omega) rdFail
    | redeem =>
      dsimp only [VaultAllowanceSpendFlow.ownerOffset, VaultAllowanceSpendFlow.allowanceOffset] at hmo ha0
      obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_5179_taken_packed hstack
        (by
          rw [hmo]
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) prepared)
            (VaultAllowanceSpendFlow.amount .redeem I prepared)) (memLoad (UInt256.ofNat 640) prepared) ≠ _
          rw [ha0, hv0, u256_sub_underflow_gt _ _ hlt]
          decide +kernel) (by native_decide) h
      exact vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_5179_taken_stack, List.length_cons]; omega) rdFail
  have hprepared : ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat flow.prepared)
      (UInt256.sub old value :: value :: old :: R) prepared aw' rdata σ k' C' := by
    cases flow with
    | transferFrom =>
      dsimp only [VaultAllowanceSpendFlow.ownerOffset, VaultAllowanceSpendFlow.allowanceOffset] at hmo ha0
      obtain ⟨aw', k', C', rdNext⟩ := vaultBlocks.vault_block_5804_fallthrough_packed hstack
        (by
          rw [hmo]
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 256) prepared)
            (VaultAllowanceSpendFlow.amount .transferFrom I prepared)) (memLoad (UInt256.ofNat 256) prepared) = _
          rw [ha0, hv0]
          exact ugt_zero (by rw [usub_toNat hsub]; omega)) h
      simp only [vaultBlocks.vault_block_5804_fallthrough_stack,
        vaultBlocks.vault_block_5804_fallthrough_memory] at rdNext
      rw [hmo] at rdNext
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 5831)
        (UInt256.sub (memLoad (UInt256.ofNat 256) prepared) (VaultAllowanceSpendFlow.amount .transferFrom I prepared) ::
          VaultAllowanceSpendFlow.amount .transferFrom I prepared :: memLoad (UInt256.ofNat 256) prepared :: R)
        prepared aw' rdata σ k' C' at rdNext
      rw [ha0, hv0] at rdNext
      exact ⟨aw', k', C', rdNext⟩
    | withdraw =>
      dsimp only [VaultAllowanceSpendFlow.ownerOffset, VaultAllowanceSpendFlow.allowanceOffset] at hmo ha0
      obtain ⟨aw', k', C', rdNext⟩ := vaultBlocks.vault_block_4506_fallthrough_packed hstack
        (by
          rw [hmo]
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 704) prepared)
            (VaultAllowanceSpendFlow.amount .withdraw I prepared)) (memLoad (UInt256.ofNat 704) prepared) = _
          rw [ha0, hv0]
          exact ugt_zero (by rw [usub_toNat hsub]; omega)) h
      simp only [vaultBlocks.vault_block_4506_fallthrough_stack,
        vaultBlocks.vault_block_4506_fallthrough_memory] at rdNext
      rw [hmo] at rdNext
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 4535)
        (UInt256.sub (memLoad (UInt256.ofNat 704) prepared) (VaultAllowanceSpendFlow.amount .withdraw I prepared) ::
          VaultAllowanceSpendFlow.amount .withdraw I prepared :: memLoad (UInt256.ofNat 704) prepared :: R)
        prepared aw' rdata σ k' C' at rdNext
      rw [ha0, hv0] at rdNext
      exact ⟨aw', k', C', rdNext⟩
    | redeem =>
      dsimp only [VaultAllowanceSpendFlow.ownerOffset, VaultAllowanceSpendFlow.allowanceOffset] at hmo ha0
      obtain ⟨aw', k', C', rdNext⟩ := vaultBlocks.vault_block_5179_fallthrough_packed hstack
        (by
          rw [hmo]
          change UInt256.gt (UInt256.sub (memLoad (UInt256.ofNat 640) prepared)
            (VaultAllowanceSpendFlow.amount .redeem I prepared)) (memLoad (UInt256.ofNat 640) prepared) = _
          rw [ha0, hv0]
          exact ugt_zero (by rw [usub_toNat hsub]; omega)) h
      simp only [vaultBlocks.vault_block_5179_fallthrough_stack,
        vaultBlocks.vault_block_5179_fallthrough_memory] at rdNext
      rw [hmo] at rdNext
      change RD fork vaultBytecode I g s0 (UInt256.ofNat 5207)
        (UInt256.sub (memLoad (UInt256.ofNat 640) prepared) (VaultAllowanceSpendFlow.amount .redeem I prepared) ::
          VaultAllowanceSpendFlow.amount .redeem I prepared :: memLoad (UInt256.ofNat 640) prepared :: R)
        prepared aw' rdata σ k' C' at rdNext
      rw [ha0, hv0] at rdNext
      exact ⟨aw', k', C', rdNext⟩
  obtain ⟨aw', k', C', rdPrepared⟩ := hprepared
  refine Or.inl ⟨hsub, ?_⟩
  cases flow
  · exact vaultBlocks.vault_block_5831_packed (by omega) (by native_decide) rdPrepared
  · exact vaultBlocks.vault_block_4535_packed (by omega) (by native_decide) rdPrepared
  · exact vaultBlocks.vault_block_5207_packed (by omega) (by native_decide) rdPrepared

end Benchmarks.CurveVault
