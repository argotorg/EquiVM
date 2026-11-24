import Benchmarks.CurveVault.ControllerCalls
import Benchmarks.CurveVault.RuntimeBlocks_029
import Benchmarks.CurveVault.RuntimeBlocks_030
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem vaultAvailableBalanceCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_controller" = none)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7819) R mem aw rdata σ k C) :
    vaultControllerCallOutcome fork s0 evm I g locals "controller_available_balance" "__c0" "available_balance"
      (UInt256.ofNat 7862) (codeOwnerStorageWord I σ ⟨3⟩ :: R)
      (vaultBlocks.vault_block_7819_memory (mem := mem)) (UInt256.ofNat 128) := by
  obtain ⟨gasArg, k', C', rd⟩ := vaultBlocks.vault_block_7819 hstack h
  apply vaultControllerWordCall hs hbase (by simp only [List.length_cons]; omega)
    (by native_decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rd
  · change ABI.encodeCallWithSelector? (selectorBytes 0x09 0x23 0x14 0xda) [] [] = _
    exact vyperNullaryCallData _ _ mem 128 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by norm_num)))
  · exact toByteArray_write_size_ge_off_add32 _ _ 128
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by norm_num)))
  · intro out h32
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_ok out h32]; rfl
  · intro out hshort
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_short out hshort]; rfl
  · intro mem' aw' out σ' k'' C'' h32 hwide rdCall
    have rdSize := vaultBlocks.vault_block_7842_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
    have rdNext := vaultBlocks.vault_block_7853_fallthrough
      (by simp only [vaultBlocks.vault_block_7842_taken_stack, List.length_cons]; omega)
      (ult_zero (by rw [ulit_toNat' _ hwide]; exact h32)) rdSize
    exact ⟨_, _, rdNext⟩
  · intro mem' aw' out σ' k'' C'' rdCall
    have rdFail := vaultBlocks.vault_block_7842_fallthrough
      (by simp only [List.length_cons]; omega) rfl rdCall
    exact vaultBlocks.vault_block_7846
      (by simp only [vaultBlocks.vault_block_7842_fallthrough_stack, List.length_cons]; omega) rdFail
  · intro mem' aw' out σ' k'' C'' hshort rdCall
    have rdSize := vaultBlocks.vault_block_7842_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
    have rdFail := vaultBlocks.vault_block_7853_taken
      (by simp only [vaultBlocks.vault_block_7842_taken_stack, List.length_cons]; omega)
      (by rw [ult_one (by rw [ulit_toNat' _ (lt_trans hshort (by decide +kernel))]; exact hshort)]; decide +kernel)
      (by native_decide) rdSize
    exact vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7842_taken_stack, List.length_cons]; omega) rdFail

theorem vaultAvailableFeesCall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x0 : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_controller" = none)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7862) (x0 :: R) mem aw rdata σ k C) :
    vaultControllerCallOutcome fork s0 evm I g locals "controller_admin_fees" "__c1" "admin_fees"
      (UInt256.ofNat 7912) (codeOwnerStorageWord I σ ⟨3⟩ :: R)
      (vaultBlocks.vault_block_7862_memory (mem := mem)) (UInt256.ofNat 192) := by
  obtain ⟨gasArg, k', C', rd⟩ := vaultBlocks.vault_block_7862 hstack h
  apply vaultControllerWordCall hs hbase (by simp only [List.length_cons]; omega)
    (by native_decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ rd
  · change ABI.encodeCallWithSelector? (selectorBytes 0x1b 0x18 0x00 0xe3) [] [] = _
    exact vyperNullaryCallData _ _ ((memLoad (UInt256.ofNat 128) mem).toByteArray.write 0 mem 64 32) 192 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by norm_num)))
  · exact toByteArray_write_size_ge_off_add32 _ _ 192
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by norm_num)))
  · intro out h32
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_ok out h32]; rfl
  · intro out hshort
    change (ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out).map (fun v => [v]) = _
    rw [decodeReturn_vyper_uint256_short out hshort]; rfl
  · intro mem' aw' out σ' k'' C'' h32 hwide rdCall
    have rdSize := vaultBlocks.vault_block_7892_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
    have rdNext := vaultBlocks.vault_block_7903_fallthrough
      (by simp only [vaultBlocks.vault_block_7892_taken_stack, List.length_cons]; omega)
      (ult_zero (by rw [ulit_toNat' _ hwide]; exact h32)) rdSize
    exact ⟨_, _, rdNext⟩
  · intro mem' aw' out σ' k'' C'' rdCall
    have rdFail := vaultBlocks.vault_block_7892_fallthrough
      (by simp only [List.length_cons]; omega) rfl rdCall
    exact vaultBlocks.vault_block_7896
      (by simp only [vaultBlocks.vault_block_7892_fallthrough_stack, List.length_cons]; omega) rdFail
  · intro mem' aw' out σ' k'' C'' hshort rdCall
    have rdSize := vaultBlocks.vault_block_7892_taken
      (by simp only [List.length_cons]; omega) (by decide +kernel) (by native_decide) rdCall
    have rdFail := vaultBlocks.vault_block_7903_taken
      (by simp only [vaultBlocks.vault_block_7892_taken_stack, List.length_cons]; omega)
      (by rw [ult_one (by rw [ulit_toNat' _ (lt_trans hshort (by decide +kernel))]; exact hshort)]; decide +kernel)
      (by native_decide) rdSize
    exact vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_7892_taken_stack, List.length_cons]; omega) rdFail

end Benchmarks.CurveVault
