import Tests.Pipeline.VyperRegistry.Helpers
import Tests.Pipeline.VyperRegistry.CreationBlocks_001
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-!
# Registry constructor correctness

The init code checks `callvalue`, calls `ownable.__init__` (pc 5 → 35: `SSTORE 0 ← caller`,
returning to pc 12), stores `nextId := 1` (slot 19) and returns the runtime (`CODECOPY` from
offset 44, 1685 bytes).  The Stele constructor is
`require(msg.value == 0); ownable___init__(); nextId = 1;` with no immutables, so the deployed
code is the constant `registryBytecode`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

theorem ctorBody_eq : contract.ctor.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .internalCall "ownable___init__" [] "__c0",
     .assign .storage { base := "nextId", steps := [] } (.intLit 1)] := by rfl

def initCallee : CallableDecl :=
  { params := [], returnType := [], body := [.assign .storage ownerRef (.env .caller)] }

theorem initCallee_lookup : lookupCallable? contract "ownable___init__" = some initCallee := by rfl

theorem noImmutables : contract.immutables = [] := by rfl

/-- The bytes the init code returns: the runtime, copied from offset 44 of the creation code. -/
theorem ctorOutput :
    ((registryCreationBytecode.write 44 ByteArray.empty 0 1685).readWithPadding 0 1685) = registryBytecode := by
  native_decide

theorem registryConstructorCorrect :
    typedConstructorRefinement config registryCreationBytecode contract (fun _ => registryBytecode) := by
  intro fork _hfork σ σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm
  have hlen : args.length = contract.ctor.params.length :=
    emptyCtorDeployment_args_length (hself := rfl) (hparams := rfl) hdeploy
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hlen
  subst hargs
  have hinit : deployedInitcode = registryCreationBytecode :=
    emptyCtorDeployment_eq_initcode (hself := rfl) (hparams := rfl) hdeploy
  have hcodeC : I.code = registryCreationBytecode := hcode.trans hinit
  have hcode' : I.code = registryCreationBytecode ++ ByteArray.empty := by
    rw [hcodeC, ByteArray.append_empty]
  have rd0 := RD.normalizePC (pc' := UInt256.ofNat 0)
    (RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode') rfl
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := registryCreationBlocks.registryCreation_block_0_fallthrough (by simp) (by rw [hwv]; rfl) rd0
    have rd2 := registryCreationBlocks.registryCreation_block_5 (by simp) (by native_decide) rd1
    simp only [registryCreationBlocks.registryCreation_block_5_stack] at rd2
    obtain ⟨_, _, rd3⟩ := registryCreationBlocks.registryCreation_block_35 (by simp) hperm (by native_decide) rd2
    simp only [registryCreationBlocks.registryCreation_block_35_stack] at rd3
    have rd4 := registryCreationBlocks.registryCreation_block_12 (by simp) hperm rd3
    rw [ByteArray.append_empty, ulit_toNat' 44 (by decide), ulit_toNat' 0 (by decide), ulit_toNat' 1685 (by decide),
      ctorOutput] at rd4
    -- Stele
    have hassignOwner : ∀ (F : Frame), F.contract = contract → F.locals.get? "ownable_owner" = none →
        assignStorageRef? config F (initState σ σ₀ (Sat256.ofUInt256 g) A I) .storage ownerRef (.address I.source) =
          .ok (F, Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩
            (UInt256.ofNat I.source.val)) := by
      intro F hF hb
      apply assignStorageRef_storage_vyper_scalar_value (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "ownable_owner", steps := [] })
        (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem .address) (loc := vyperWordLoc ⟨0⟩ .address) (hbase := hb)
        (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by rw [hF]; rfl) (hloc := rfl)
      rw [storageLocStore_vyperWord_address]
      rfl
    set evm1 := Stele.EVM.storageStore (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩ (UInt256.ofNat I.source.val)
      with hevm1
    have hs1 : SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (UInt256.ofNat I.source.val)) evm1 := SourceState.init.storageWrite _ _
    have hassignNext : ∀ (F : Frame), F.contract = contract → F.locals.get? "nextId" = none →
        assignStorageRef? config F evm1 .storage { base := "nextId", steps := [] } (uint256Value (UInt256.ofNat 1)) =
          .ok (F, Stele.EVM.storageStore evm1 I.codeOwner (UInt256.ofNat 19) (UInt256.ofNat 1)) := by
      intro F hF hb
      apply assignStorageRef_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "nextId", steps := [] })
        (hleaf := Or.inl ⟨_, rfl⟩) (ty := .elem (.int (.uint ⟨256, by decide⟩))) (loc := vyperUint256Loc (UInt256.ofNat 19))
        (hbase := hb) (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (hty := by rw [hF]; rfl) (hloc := rfl)
      erw [storageLocStore_uint256, hs1.env]
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ contract.ctor.body
        (.returned { contract := contract, locals := (∅ : Store).insert "__c0" .unit, immutables := initialImmutables contract }
          (Stele.EVM.storageStore evm1 I.codeOwner (UInt256.ofNat 19) (UInt256.ofNat 1)) none) (initialImmutables contract) := by
      rw [ctorBody_eq]
      exact ExecFuncBody.execBlockOK (ExecBlock.consNormal
        (ExecStmt.requireTrue (evalCallvalueEq_true (by simpa [initState] using hwv)))
        (ExecBlock.consNormal (ExecStmt.internalCallReturn (callee := initCallee) rfl initCallee_lookup rfl
          (ExecFuncBody.execBlockOK (ExecBlock.consNormal
            (ExecStmt.assign (hperm := by first | assumption | exact Or.inr ‹_› | exact Or.inl rfl) (evalExpr_caller _) (hassignOwner _ rfl (by simp))) ExecBlock.nil)))
          (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr (by simpa only [hs1.env] using hperm)) (evalExpr_intLit_word _ 1 (by decide)) (hassignNext _ rfl (by show ((∅ : Store).insert "__c0" .unit).get? "nextId" = none; simp)))
            ExecBlock.nil)))
    rcases rd4 with hoog | ⟨s, hX, hacc⟩
    · exact typedConstructorRefinementFor.outOfGas
        (by simpa using Xi_error_of_X (by rw [← hcodeC] at hoog; exact hoog))
    · have hxi := Xi_success_of_X (by rw [← hcodeC] at hX; exact hX)
      rw [hacc] at hxi
      exact typedConstructorRefinementFor.execution (by simpa using hxi)
        (steleCtorExec.intro rfl (by rfl) (by rfl) hbody)
        (ctorResultEquiv.success rfl rfl ((hs1.storageWrite _ _).accounts) rfl)
        (ctorImmutablesFit_noImmutables noImmutables)
  · have rd1 := registryCreationBlocks.registryCreation_block_0_taken (by simp) (fun h => hwv h) (by native_decide) rd0
    have rd2 := registryCreationBlocks.registryCreation_block_40 (by simp) rd1
    rcases rd2.xiResult hcode' with hoog | ⟨g', o, hxi⟩
    · exact typedConstructorRefinementFor.outOfGas (by simpa using hoog)
    · exact typedConstructorRefinementFor.execution (by simpa using hxi)
        (steleCtorExec.intro rfl (by rfl) (by rfl) (by
          rw [ctorBody_eq]
          exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert
            (ExecStmt.requireFalse (evalCallvalueEq_false (by simpa [initState] using hwv))))))
        (ctorResultEquiv.revert rfl rfl) (ctorImmutablesFit_noImmutables noImmutables)

end Tests.Pipeline.VyperRegistry
