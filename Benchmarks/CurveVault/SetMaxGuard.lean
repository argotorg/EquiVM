import Benchmarks.CurveVault.SetMaxAdminCall
import Benchmarks.CurveVault.AddressWord

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultSetMaxGuardExpr : Expr := .binary .or
  (.binary .eq (.env .caller) (.var "factory_admin"))
  (.binary .eq (.env .caller) (.storage {base := "_factory", steps := []}))

theorem vaultSetMaxGuardSource (evm : State) (locals : Store) (admin factory : AccountAddress)
    (hadmin : locals.get? "factory_admin" = some (.address admin))
    (hfactory : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "_factory", steps := []}) = .ok (.address factory)) :
    evalExpr? config {contract := contract, locals := locals} evm vaultSetMaxGuardExpr =
      .ok (.bool (decide (evm.executionEnv.source = admin) || decide (evm.executionEnv.source = factory))) := by
  have ha : evalExpr? config {contract := contract, locals := locals} evm (.var "factory_admin") =
      .ok (.address admin) := by
    rw [evalExpr?]
    simp only [hadmin, EvalResult.ofOption]
  by_cases heq : evm.executionEnv.source = admin <;>
    simp [vaultSetMaxGuardExpr, evalExpr?, ha, hfactory, envValue, evalBinaryOp?,
      EvalResult.bind, pure, bind, value_address_beq, heq]

theorem vaultSetMaxGuard {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {locals : Store} {admin unused1 unused2 : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hbase : locals.get? "_factory" = none)
    (hadmin : locals.get? "factory_admin" = some (.address (AccountAddress.ofNat admin.toNat)))
    (hcanon : admin.toNat < EVM.addressModulus)
    (hfactory : (codeOwnerStorageWord I σ ⟨4⟩).toNat < EVM.addressModulus)
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 932) (admin :: unused1 :: unused2 :: R) mem aw rdata σ k C) :
    (evalExpr? config {contract := contract, locals := locals} evm vaultSetMaxGuardExpr = .ok (.bool true) ∧
      ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 966) R
        (admin.toByteArray.write 0 mem 128 32) aw' rdata σ k' C') ∨
    (evalExpr? config {contract := contract, locals := locals} evm vaultSetMaxGuardExpr = .ok (.bool false) ∧
      RDrev fork vaultBytecode g s0) := by
  have hf := vaultFactoryEval evm locals hbase
  rw [hs.storageRead, accountAddress_ofUInt256_eq_ofNat_toNat] at hf
  have heval := vaultSetMaxGuardSource evm locals _ _ hadmin hf
  change evalExpr? config {contract := contract, locals := locals} evm vaultSetMaxGuardExpr =
    .ok (.bool (decide (evm.executionEnv.source = AccountAddress.ofNat admin.toNat) ||
      decide (evm.executionEnv.source = AccountAddress.ofNat (codeOwnerStorageWord I σ ⟨4⟩).toNat))) at heval
  rw [hs.env] at heval
  have hword : memLoad (UInt256.ofNat 128) (admin.toByteArray.write 0 mem (UInt256.ofNat 128).toNat 32) = admin :=
    memLoad_write_back _ _ 128 (by decide +kernel)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 128 (by omega)))
  by_cases ha : UInt256.ofNat I.source.val = admin
  · have rd947 := vaultBlocks.vault_block_932_fallthrough hstack
      (by rw [hword, ha, u256_xor_self]; rfl) h
    have rd960 := vaultBlocks.vault_block_947 (by simp only [vaultBlocks.vault_block_932_fallthrough_stack]; omega)
      (by native_decide) rd947
    have rd966 := vaultBlocks.vault_block_960_fallthrough
      (by simp only [vaultBlocks.vault_block_932_fallthrough_stack]; omega) (by decide +kernel) rd960
    refine Or.inl ⟨?_, _, _, _, rd966⟩
    have haa : I.source = AccountAddress.ofNat admin.toNat :=
      ((addressOfWord_eq_iff hcanon _).mpr ha.symm).symm
    rw [heval]
    simp only [haa, decide_true, Bool.true_or]
  · have rd953 := vaultBlocks.vault_block_932_taken hstack
      (by rw [hword]; exact u256_xor_ne_zero_of_ne ha) (by native_decide) h
    obtain ⟨_, _, rd960⟩ := vaultBlocks.vault_block_953
      (by simp only [vaultBlocks.vault_block_932_taken_stack]; omega) rd953
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 960)
      (UInt256.isZero (UInt256.xor (UInt256.ofNat I.source.val) (codeOwnerStorageWord I σ ⟨4⟩)) :: R)
      _ _ rdata σ _ _ at rd960
    have haa : I.source ≠ AccountAddress.ofNat admin.toNat :=
      fun he => ha (((addressOfWord_eq_iff hcanon _).mp he.symm).symm)
    by_cases hf : UInt256.ofNat I.source.val = codeOwnerStorageWord I σ ⟨4⟩
    · have rd966 := vaultBlocks.vault_block_960_fallthrough (by omega)
        (by rw [hf, u256_xor_self]; rfl) rd960
      refine Or.inl ⟨?_, _, _, _, rd966⟩
      have hfa : I.source = AccountAddress.ofNat (codeOwnerStorageWord I σ ⟨4⟩).toNat :=
        ((addressOfWord_eq_iff hfactory _).mpr hf.symm).symm
      rw [heval]
      simp only [hfa, decide_true, Bool.or_true]
    · have rdFail := vaultBlocks.vault_block_960_taken (by omega)
        (by rw [isZero_xor_eq_zero_of_ne hf]; decide +kernel) (by native_decide) rd960
      have hrev := vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_960_taken_stack]; omega) rdFail
      refine Or.inr ⟨?_, hrev⟩
      have hfa : I.source ≠ AccountAddress.ofNat (codeOwnerStorageWord I σ ⟨4⟩).toNat :=
        fun he => hf (((addressOfWord_eq_iff hfactory _).mp he.symm).symm)
      rw [heval]
      simp only [haa, hfa, decide_false, Bool.false_or]

end Benchmarks.CurveVault
