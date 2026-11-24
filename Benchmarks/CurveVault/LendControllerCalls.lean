import Benchmarks.CurveVault.ControllerCalls
import Benchmarks.CurveVault.RuntimeBlocks_005
import Benchmarks.CurveVault.RuntimeBlocks_006
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem vaultLendDebtCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_controller" = none)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1117) R mem aw rdata σ k C) :
    vaultControllerCallOutcome fork s0 evm I g locals "controller_total_debt" "debt" "total_debt"
      (UInt256.ofNat 1162) (codeOwnerStorageWord I σ ⟨3⟩ :: R)
      (vaultBlocks.vault_block_1117_memory (mem := mem)) (UInt256.ofNat 288) := by
  obtain ⟨gasArg, k', C', rd⟩ := vaultBlocks.vault_block_1117 hstack h
  apply vaultControllerWordCall hs hbase (by simp only [List.length_cons]; omega)
    (by native_decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rd
  · change ABI.encodeCallWithSelector? (selectorBytes 0x31 0xdc 0x3c 0xa8) [] [] = _
    exact vyperNullaryCallData _ _ mem 288 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num)))
  · exact toByteArray_write_size_ge_off_add32 _ _ 288
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num)))
  · intro out h32
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_ok out h32]; rfl
  · intro out hshort
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_short out hshort]; rfl
  · intro mem' aw' out σ' k'' C'' h32 hwide rdCall
    have rdSize := vaultBlocks.vault_block_1142_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
    have rdNext := vaultBlocks.vault_block_1153_fallthrough
      (by simp only [vaultBlocks.vault_block_1142_taken_stack, List.length_cons]; omega)
      (ult_zero (by rw [ulit_toNat' _ hwide]; exact h32)) rdSize
    exact ⟨_, _, rdNext⟩
  · intro mem' aw' out σ' k'' C'' rdCall
    have rdFail := vaultBlocks.vault_block_1142_fallthrough
      (by simp only [List.length_cons]; omega) rfl rdCall
    exact vaultBlocks.vault_block_1146
      (by simp only [vaultBlocks.vault_block_1142_fallthrough_stack, List.length_cons]; omega) rdFail
  · intro mem' aw' out σ' k'' C'' hshort rdCall
    have rdSize := vaultBlocks.vault_block_1142_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
    have rdFail := vaultBlocks.vault_block_1153_taken
      (by simp only [vaultBlocks.vault_block_1142_taken_stack, List.length_cons]; omega)
      (by rw [ult_one (by rw [ulit_toNat' _ (lt_trans hshort (by decide +kernel))]; exact hshort)]; decide +kernel)
      (by native_decide) rdSize
    exact vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1142_taken_stack, List.length_cons]; omega) rdFail

theorem vaultLendAdminCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {numerator total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_controller" = none)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1313) (total :: numerator :: R) mem aw rdata σ k C) :
    vaultControllerCallOutcome fork s0 evm I g locals "controller_admin_percentage" "admin_pct" "admin_percentage"
      (UInt256.ofNat 1369) (codeOwnerStorageWord I σ ⟨3⟩ :: R)
      (vaultBlocks.vault_block_1313_memory (mem := mem) (x0 := total) (x1 := numerator)) (UInt256.ofNat 352) := by
  obtain ⟨gasArg, k', C', rd⟩ := vaultBlocks.vault_block_1313 hstack h
  apply vaultControllerWordCall hs hbase (by simp only [List.length_cons]; omega)
    (by native_decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rd
  · change ABI.encodeCallWithSelector? (selectorBytes 0x10 0x59 0xfc 0xbd) [] [] = _
    exact vyperNullaryCallData _ _ ((UInt256.div numerator total).toByteArray.write 0 mem 288 32) 352 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num)))
  · exact toByteArray_write_size_ge_off_add32 _ _ 352
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by norm_num)))
  · intro out h32
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_ok out h32]; rfl
  · intro out hshort
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_short out hshort]; rfl
  · intro mem' aw' out σ' k'' C'' h32 hwide rdCall
    have rdSize := vaultBlocks.vault_block_1349_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
    have rdNext := vaultBlocks.vault_block_1360_fallthrough
      (by simp only [vaultBlocks.vault_block_1349_taken_stack, List.length_cons]; omega)
      (ult_zero (by rw [ulit_toNat' _ hwide]; exact h32)) rdSize
    exact ⟨_, _, rdNext⟩
  · intro mem' aw' out σ' k'' C'' rdCall
    have rdFail := vaultBlocks.vault_block_1349_fallthrough
      (by simp only [List.length_cons]; omega) rfl rdCall
    exact vaultBlocks.vault_block_1353
      (by simp only [vaultBlocks.vault_block_1349_fallthrough_stack, List.length_cons]; omega) rdFail
  · intro mem' aw' out σ' k'' C'' hshort rdCall
    have rdSize := vaultBlocks.vault_block_1349_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
    have rdFail := vaultBlocks.vault_block_1360_taken
      (by simp only [vaultBlocks.vault_block_1349_taken_stack, List.length_cons]; omega)
      (by rw [ult_one (by rw [ulit_toNat' _ (lt_trans hshort (by decide +kernel))]; exact hshort)]; decide +kernel)
      (by native_decide) rdSize
    exact vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_1349_taken_stack, List.length_cons]; omega) rdFail

end Benchmarks.CurveVault
