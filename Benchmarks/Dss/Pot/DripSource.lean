import Benchmarks.Dss.Pot.DripCommon

/-!
# MakerDAO/Sky DSS Pot `drip()` — Solm-source-side `ExecTransitionBody` leaf lemmas

For each control-flow leaf of `dripTransition.body`, a fact
`ExecTransitionBody config contract evm0 ∅ dripTransition.body <result>` where
`evm0 = initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I`.

The `_rpow` result is supplied to the leaves as a hypothesis `hrpow` (the core obtains it from
`rpowFunctionCoupled`); the checked-arithmetic `_rmul`/`_sub`/`_mul` bodies are discharged with the
`Arith.lean` `ExecFuncBody` lemmas; and the external `vat.suck` call is supplied as a
`typedCallViaEVM` hypothesis.  The two storage `assign`s (`chi := tmp` slot 4, `rho := now` slot 7)
mutate the EVM state, so the later `Pie`/`vat`/`vow` reads are threaded through the twice-stored
state and reduced back to the original words with the storage-store/load preservation lemmas.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## Threaded value words (functions of `σ`, `I`, and the given `pow`) -/

/-- `now - rho` (the second `_rpow` argument), well-defined once `now ≥ rho`. -/
abbrev dripSubNowRho (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (dripNowWord I) (dripRhoWord σ I)

/-- `tmp = _rmul(pow, chi) = (pow * chi) / ONE`. -/
abbrev dripTmpVal (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) : UInt256 :=
  UInt256.div (pow * dripChiWord σ I) potRay

/-- `chi_ = _sub(tmp, chi) = tmp - chi`. -/
abbrev dripChiDeltaVal (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) : UInt256 :=
  UInt256.sub (dripTmpVal σ I pow) (dripChiWord σ I)

/-- `rad = _mul(Pie, chi_) = Pie * chi_`. -/
abbrev dripRadVal (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) : UInt256 :=
  dripPieWord σ I * dripChiDeltaVal σ I pow

/-! ## Threaded locals frames -/

abbrev dripPowFrameLocals (pow : UInt256) : Store :=
  (∅ : Store).insert "pow" (.int (Int.ofNat pow.toNat))

abbrev dripTmpFrameLocals (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) : Store :=
  (dripPowFrameLocals pow).insert "tmp" (.int (Int.ofNat (dripTmpVal σ I pow).toNat))

abbrev dripChiDeltaFrameLocals (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) : Store :=
  (dripTmpFrameLocals σ I pow).insert "chi_" (.int (Int.ofNat (dripChiDeltaVal σ I pow).toNat))

abbrev dripRadFrameLocals (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) : Store :=
  (dripChiDeltaFrameLocals σ I pow).insert "rad" (.int (Int.ofNat (dripRadVal σ I pow).toNat))

abbrev dripSuckFrameLocals (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) : Store :=
  (dripRadFrameLocals σ I pow).insert "_suckRet" .unit

/-! ## Threaded EVM states (the two scalar stores mutate storage) -/

/-- After `chi := tmp` (slot 4). -/
abbrev dripEvmChi (evm0 : EVM.State) (tmp : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨4⟩ tmp

/-- After `chi := tmp` then `rho := now` (slot 7). -/
abbrev dripEvmRho (evm0 : EVM.State) (tmp now : UInt256) : EVM.State :=
  Solm.EVM.storageStore (dripEvmChi evm0 tmp)
    (dripEvmChi evm0 tmp).executionEnv.codeOwner ⟨7⟩ now

/-! ## Frame `get?` projections -/

theorem dripSuckFrameLocals_get_tmp (σ : AccountMap) (I : ExecutionEnv) (pow : UInt256) :
    (dripSuckFrameLocals σ I pow).get? "tmp" =
      some (.int (Int.ofNat (dripTmpVal σ I pow).toNat)) := by
  simp only [dripSuckFrameLocals, dripRadFrameLocals, dripChiDeltaFrameLocals, dripTmpFrameLocals,
    dripPowFrameLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

/-! ## Storage-word bridge on the initial state -/

/-- On `evm0`, a code-owner storage read at `slot` is the layout word `potSlotWord slot σ I`. -/
theorem dripEvm0_load {cA gh bl σ σ₀ A I} {g : UInt256} (slot : UInt256) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner slot =
      potSlotWord slot σ I := by
  have hco : (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
      I.codeOwner := rfl
  rw [hco, codeOwnerStorageWord_initState]
  rfl

/-- The `chi := tmp`/`rho := now` stores don't touch slots `≠ 4, 7`, so a later read there is still
`potSlotWord slot σ I`. -/
theorem dripEvmRho_load {cA gh bl σ σ₀ A I} {g : UInt256} {tmp now : UInt256} (slot : UInt256)
    (h4 : slot ≠ (⟨4⟩ : UInt256)) (h7 : slot ≠ (⟨7⟩ : UInt256)) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    Solm.EVM.storageLoad (dripEvmRho evm0 tmp now) (dripEvmRho evm0 tmp now).executionEnv.codeOwner
        slot = potSlotWord slot σ I := by
  intro evm0
  have hChiEnv : (dripEvmChi evm0 tmp).executionEnv.codeOwner = evm0.executionEnv.codeOwner := by
    simp only [dripEvmChi, storageStore_executionEnv]
  have hRhoEnv : (dripEvmRho evm0 tmp now).executionEnv.codeOwner =
      evm0.executionEnv.codeOwner := by
    simp only [dripEvmRho, dripEvmChi, storageStore_executionEnv]
  rw [hRhoEnv]
  -- peel the slot-7 store
  rw [show dripEvmRho evm0 tmp now =
        Solm.EVM.storageStore (dripEvmChi evm0 tmp) evm0.executionEnv.codeOwner ⟨7⟩ now by
    simp only [dripEvmRho, hChiEnv]]
  rw [storageLoad_storageStore_ne _ _ h7]
  -- peel the slot-4 store
  rw [show dripEvmChi evm0 tmp =
        Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨4⟩ tmp from rfl]
  rw [storageLoad_storageStore_ne _ _ h4]
  exact dripEvm0_load slot

/-! ## Solm-side scalar storage reads (parameterized over the locals frame) -/

theorem evalExpr_potDsrOfLocals {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "dsr" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage dsrRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)) :=
  evalExpr_storage_scalar_value (slot := dsrRef)
    (er := ({ base := "dsr", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨3⟩)
    hbase
    (by simp [dsrRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (potStorageLocLoad_uint256 evm ⟨3⟩)

theorem evalExpr_potChiOfLocals {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "chi" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage chiRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩).toNat)) :=
  evalExpr_storage_scalar_value (slot := chiRef)
    (er := ({ base := "chi", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    hbase
    (by simp [chiRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (potStorageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_potPieOfLocals {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "Pie" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage PieRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) :=
  evalExpr_storage_scalar_value (slot := PieRef)
    (er := ({ base := "Pie", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨2⟩)
    hbase
    (by simp [PieRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (potStorageLocLoad_uint256 evm ⟨2⟩)

/-! ## Solm-side address storage reads -/

theorem evalExpr_potVatOfLocals {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
          solcAddrMask).toNat)) :=
  evalExpr_storage_scalar_value (slot := vatRef)
    (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨5⟩)
    hbase
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (potStorageLocLoad_address_offset0 evm ⟨5⟩)

theorem evalExpr_potVowOfLocals {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vowRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
          solcAddrMask).toNat)) :=
  evalExpr_storage_scalar_value (slot := vowRef)
    (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨6⟩)
    hbase
    (by simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (potStorageLocLoad_address_offset0 evm ⟨6⟩)

/-! ## Solm-side scalar storage writes (`chi := tmp`, `rho := now`) -/

theorem evalStorageRef_drip_chi (evm : EVM.State) {locals : Store} :
    evalStorageRef config { contract := contract, locals := locals } evm chiRef =
      .ok ({ base := "chi", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, chiRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_drip_rho (evm : EVM.State) {locals : Store} :
    evalStorageRef config { contract := contract, locals := locals } evm rhoRef =
      .ok ({ base := "rho", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, rhoRef, EvalResult.bind, pure, bind]

theorem dripAssignChi (evm : EVM.State) {locals : Store} (tmp : UInt256)
    (hbase : locals.get? "chi" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
        .storage chiRef (.int (Int.ofNat tmp.toNat)) =
      .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ tmp) := by
  apply assignStorageRef_storage_scalar (ty := uint256St) (loc := wordLoc ⟨4⟩)
    hbase (evalStorageRef_drip_chi evm)
    (by simp [storageTypeAt?, contract, storageDecls, uint256St]) (by rfl)
  exact potStorageLocStore_uint256 evm ⟨4⟩ tmp

theorem dripAssignRho (evm : EVM.State) {locals : Store} (now : UInt256)
    (hbase : locals.get? "rho" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
        .storage rhoRef (.int (Int.ofNat now.toNat)) =
      .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩ now) := by
  apply assignStorageRef_storage_scalar (ty := uint256St) (loc := wordLoc ⟨7⟩)
    hbase (evalStorageRef_drip_rho evm)
    (by simp [storageTypeAt?, contract, storageDecls, uint256St]) (by rfl)
  exact potStorageLocStore_uint256 evm ⟨7⟩ now

end Benchmarks.Dss.Pot
