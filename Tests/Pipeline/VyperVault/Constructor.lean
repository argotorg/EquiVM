import Tests.Pipeline.VyperVault.Helpers
import Tests.Pipeline.VyperVault.CreationBlocks_001

variable {fork : Ethereum.Fork}

/-!
# VyperVault constructor correctness

The init code checks `callvalue`, stores `msg.sender` as the `OWNER` immutable word after the
runtime copy (memory offset 1429) and returns the runtime followed by the immutable section.
The Stele constructor is `require(msg.value == 0); OWNER = msg.sender;`; the returned bytes are
`immutableLayout.deployed vyperVaultBytecode` of its final immutables.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem ctorBody_eq : contract.ctor.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .setImmutable "OWNER" (.env .caller)] := by rfl

/-- The constructor's final immutables. -/
abbrev ctorImms (I : ExecutionEnv) : Store :=
  (initialImmutables contract).insert "OWNER" (.address I.source)

theorem ctorImms_fit (I : ExecutionEnv) : immutablesFit contract (ctorImms I) := by
  intro d hd
  rw [show contract.immutables = [⟨"OWNER", .address⟩] from rfl] at hd
  simp at hd
  subst hd
  exact ⟨.address I.source, store_get_self _ _ _, by simp [elemValueFits]⟩

/-- The bytes the init code returns: the runtime followed by the `OWNER` word. -/
theorem ctorOutput (I : ExecutionEnv) :
    ((vyperVaultCreationBytecode.write 36
        ((UInt256.ofNat I.source.val).toByteArray.write 0 ByteArray.empty 1429 32) 0 1429).readWithPadding 0 1461) =
      vyperVaultBytecode ++ (UInt256.ofNat I.source.val).toByteArray := by
  have hsrc : vyperVaultCreationBytecode.size = 1465 := by native_decide
  have hrt : vyperVaultCreationBytecode.extract 36 (36 + 1429) = vyperVaultBytecode := by native_decide
  have hbase : (UInt256.ofNat I.source.val).toByteArray.write 0 ByteArray.empty 1429 32 =
      ByteArray.zeroes 1429 ++ (UInt256.ofNat I.source.val).toByteArray := by
    rw [toByteArray_write_eq _ _ 1429 (Nat.zero_le _) (lt_usize _ (by decide)), empty_append]
    rfl
  have hbsz : (ByteArray.zeroes 1429 ++ (UInt256.ofNat I.source.val).toByteArray).size = 1461 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
  have hempty : (ByteArray.zeroes 1429 ++ (UInt256.ofNat I.source.val).toByteArray).extract 0 0 = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero _ (by rw [ByteArray.size_extract]; omega)
  have hw : (UInt256.ofNat I.source.val).toByteArray.extract 0 32 = (UInt256.ofNat I.source.val).toByteArray := by
    rw [← toByteArray_size (UInt256.ofNat I.source.val)]; exact byteArray_extract_self _
  rw [hbase, write_eq_gen_from _ _ 36 0 1429 (by decide) (by rw [hsrc]) (by rw [hbsz]; omega), hrt, hempty,
    empty_append, extract_append_right_window _ _ _ _ (by rw [ByteArray_zeroes_size]), ByteArray_zeroes_size, hbsz]
  simp only [Nat.zero_add, Nat.sub_self, show (1461 : Nat) - 1429 = 32 from rfl, hw]
  have hfin : (vyperVaultBytecode ++ (UInt256.ofNat I.source.val).toByteArray).size = 1461 := by
    rw [ByteArray.size_append, vyperVaultBytecode_size, toByteArray_size]
  rw [readWithPadding_eq_extract' (vyperVaultBytecode ++ (UInt256.ofNat I.source.val).toByteArray) 0 1461
    (by norm_num) (by norm_num) (by rw [hfin]), Nat.zero_add, ← hfin]
  exact byteArray_extract_self _

theorem vyperVaultConstructorCorrect :
    typedConstructorRefinement config vyperVaultCreationBytecode contract (immutableLayout.deployed vyperVaultBytecode) := by
  intro fork _hfork σ σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm
  have hlen : args.length = contract.ctor.params.length :=
    emptyCtorDeployment_args_length (hself := rfl) (hparams := rfl) hdeploy
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hlen
  subst hargs
  have hinit : deployedInitcode = vyperVaultCreationBytecode :=
    emptyCtorDeployment_eq_initcode (hself := rfl) (hparams := rfl) hdeploy
  have hcodeC : I.code = vyperVaultCreationBytecode := hcode.trans hinit
  have hcode' : I.code = vyperVaultCreationBytecode ++ ByteArray.empty := by
    rw [hcodeC, ByteArray.append_empty]
  have rd0 := RD.normalizePC (pc' := UInt256.ofNat 0)
    (RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode') rfl
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := vyperVaultCreationBlocks.vyperVaultCreation_block_0_fallthrough (by simp) (by rw [hwv]; rfl) rd0
    have rd2 := vyperVaultCreationBlocks.vyperVaultCreation_block_10 (by simp) rd1
    rw [ByteArray.append_empty, ulit_toNat' 36 (by decide), ulit_toNat' 1429 (by decide),
      ulit_toNat' 0 (by decide), ulit_toNat' 1461 (by decide), ctorOutput] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ contract.ctor.body
        (.returned { contract := contract, locals := ∅, immutables := ctorImms I }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) none) (initialImmutables contract) := by
      rw [ctorBody_eq]
      exact ExecFuncBody.execBlockOK (ExecBlock.consNormal
        (ExecStmt.requireTrue (evalCallvalueEq_true (by simpa [initState] using hwv)))
        (ExecBlock.consNormal (ExecStmt.setImmutable (evalExpr_caller _) (by rfl) (by simp [elemValueFits]))
          ExecBlock.nil))
    rcases rd2 with hoog | ⟨s, hX, hacc⟩
    · exact typedConstructorRefinementFor.outOfGas
        (by simpa using Xi_error_of_X (by rw [← hcodeC] at hoog; exact hoog))
    · have hxi := Xi_success_of_X (by rw [← hcodeC] at hX; exact hX)
      rw [hacc] at hxi
      exact typedConstructorRefinementFor.execution (by simpa using hxi)
        (steleCtorExec.intro rfl (by rfl) (by rfl) hbody)
        (ctorResultEquiv.success rfl rfl rfl (by
          show vyperVaultBytecode ++ (UInt256.ofNat I.source.val).toByteArray =
            immutableLayout.deployed vyperVaultBytecode (ctorImms I)
          rw [deployed_of_fit (ctorImms_fit I), suffixWords_OWNER, wordsOf_OWNER (store_get_self _ _ _)]
          rfl))
        (ctorImms_fit I)
  · have rd1 := vyperVaultCreationBlocks.vyperVaultCreation_block_0_taken (by simp) (fun h => hwv h)
      (by apply D_J_contains_append_left; native_decide) rd0
    have rd2 := vyperVaultCreationBlocks.vyperVaultCreation_block_32
      (show ([] : List UInt256).length + 2 ≤ 1024 by decide) rd1
    rcases rd2.xiResult hcode' with hoog | ⟨g', o, hxi⟩
    · exact typedConstructorRefinementFor.outOfGas (by simpa using hoog)
    · exact typedConstructorRefinementFor.execution (by simpa using hxi)
        (steleCtorExec.intro rfl (by rfl) (by rfl) (by
          rw [ctorBody_eq]
          exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert
            (ExecStmt.requireFalse (evalCallvalueEq_false (by simpa [initState] using hwv))))))
        (ctorResultEquiv.revert rfl rfl) trivial

end Tests.Pipeline.VyperVault
