import Benchmarks.Dss.Cure.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cure

/-! ## `cage()` -/

theorem cureDispatchCage {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 1)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes, cureAmtSelectorBytes,
    cureCageSelectorBytes]
  native_decide

theorem cureDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem evalExpr_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_add256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_add256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (add256 x y) =
      .revert := by
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_sub256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem evalExpr_sub256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .revert := by
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro hle
  exact False.elim (not_le.mpr hlt hle)

theorem evalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem evalExpr_le_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : a.toNat ≤ b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hle

abbrev uintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev uintBinaryLocalsZ (x y z : UInt256) : Store :=
  (uintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

theorem uintBinaryLocals_get_x (x y : UInt256) :
    (uintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocals, store_get_self]

theorem uintBinaryLocals_get_y (x y : UInt256) :
    (uintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [uintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem uintBinaryLocalsZ_get_x (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_ne _ _ (by decide), uintBinaryLocals_get_x]

theorem uintBinaryLocalsZ_get_z (x y z : UInt256) :
    (uintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [uintBinaryLocalsZ, store_get_self]

theorem execAddFunctionReturn (evm : EVM.State) {x y sum : UInt256}
    (hsum : sum = x + y) (hfit : x.toNat + y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      addFunction.body
      (.returned { contract := contract, locals := uintBinaryLocalsZ x y sum } evm
        (some [.int (Int.ofNat sum.toNat)])) := by
  let locals := uintBinaryLocals x y
  let localsZ := uintBinaryLocalsZ x y sum
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hAdd :
      evalExpr? config { contract := contract, locals := locals } evm
        (add256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat sum.toNat)) :=
    evalExpr_add256_ok hx hy hsum hfit
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat sum.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := sum) (uintBinaryLocalsZ_get_z x y sum)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x) (uintBinaryLocalsZ_get_x x y sum)
  have hsumNat : sum.toNat = x.toNat + y.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .ge (.var "z") (.var "x")) = .ok (.bool true) :=
    evalExpr_ge_uint256_true hz hxZ (by rw [hsumNat]; omega)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (add256 (.var "x") (.var "y")),
          .require (.binary .ge (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat sum.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hAdd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [addFunction, checkedAddUintInto, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem execAddFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      addFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hAddRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (add256 (.var "x") (.var "y")) = .revert :=
    evalExpr_add256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (add256 (.var "x") (.var "y")),
          .require (.binary .ge (.var "z") (.var "x")),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hAddRev)
  simpa [addFunction, checkedAddUintInto, locals] using ExecFuncBody.execBlockRevert hblock

theorem execSubFunctionReturn (evm : EVM.State) {x y diff : UInt256}
    (hdiff : diff = UInt256.sub x y) (hle : y.toNat ≤ x.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      subFunction.body
      (.returned { contract := contract, locals := uintBinaryLocalsZ x y diff } evm
        (some [.int (Int.ofNat diff.toNat)])) := by
  let locals := uintBinaryLocals x y
  let localsZ := uintBinaryLocalsZ x y diff
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hSub :
      evalExpr? config { contract := contract, locals := locals } evm
        (sub256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat diff.toNat)) :=
    evalExpr_sub256_ok hx hy hdiff hle
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat diff.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := diff) (uintBinaryLocalsZ_get_z x y diff)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x) (uintBinaryLocalsZ_get_x x y diff)
  have hdiffNat : diff.toNat = x.toNat - y.toNat := by
    rw [hdiff, usub_toNat hle]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .le (.var "z") (.var "x")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hz hxZ (by rw [hdiffNat]; omega)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat diff.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hSub) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [subFunction, checkedSubUintInto, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem execSubFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hlt : x.toNat < y.toNat) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      subFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (uintBinaryLocals_get_y x y)
  have hSubRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (sub256 (.var "x") (.var "y")) = .revert :=
    evalExpr_sub256_revert hx hy hlt
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (sub256 (.var "x") (.var "y")),
          .require (.binary .le (.var "z") (.var "x")),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hSubRev)
  simpa [subFunction, checkedSubUintInto, locals] using ExecFuncBody.execBlockRevert hblock

theorem cureReachCageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 1)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨632⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x69245009⟩ :=
    cureSelWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨0x69245009⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h114⟩ := cureReachMidLowFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨632⟩ 0 h114 (fun j hj => cureMidLowArmsWellFormed j (by omega))
    (fun j hj => by omega)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

@[reducible] def solcNoArgsExternalEntryWf
    (code : ByteArray) (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p7 := p4 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p7 = some (.JUMP, .none)

theorem RD.solcNoArgsExternalEntry {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret routine sel : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc [sel] mem aw rdata acc k C)
    (hwf : solcNoArgsExternalEntryWf code pc ret routine)
    (hroutine : (D_J code 0).contains routine = true) :
    ∃ k' C', RD code ee g s0 routine [ret, sel] mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd4, hd7⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd7 := rd4.push2 routine hd4 (by evm_ov)
  exact ⟨_, _, rd7.jump hd7 hroutine (by evm_ov)⟩

theorem assign_cageLiveStorage (evm : EVM.State) {locals : Store} (value : UInt256)
    (hbase : locals.get? "live" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩ value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm liveRef =
        .ok cureLiveEvaledRef := by
    simp [cureLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
      pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨1⟩) (.int (Int.ofNat value.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨1⟩ value
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨1⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, cureLiveEvaledRef])
    (hstore := hstore)

theorem cureCageSourceLiveStorePrefix {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩) :
    let locals : Store := ∅
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨1⟩ ⟨0⟩
    ExecBlock config { contract := contract, locals := locals } evm0
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) ::
        .require (.binary .eq (.storage liveRef) (.intLit 1)) ::
        [ .assign .storage liveRef (.intLit 0) ])
      (.ok { contract := contract, locals := locals } evmLive) := by
  intro locals evm0 evmLive
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simp [locals]) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by simp [locals]) hlive
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage liveRef (.int 0) =
          .ok ({ contract := contract, locals := locals }, evmLive) := by
    simpa [evmLive] using
      assign_cageLiveStorage evm0 (locals := locals) (⟨0⟩ : UInt256) (by simp [locals])
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive)
    ExecBlock.nil

abbrev cageTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

abbrev cageWaitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cureSlotWord ⟨3⟩ σ I

abbrev cageWhenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  cageTimestampWord I + cageWaitWord σ I

theorem evalExpr_cageTimestamp {evm : EVM.State} {locals : Store} :
    evalExpr? config { contract := contract, locals := locals }
      evm (.env .timestamp) =
        .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) := by
  simp [evalExpr?, envValue, pure]

theorem evalExpr_cageWaitAfterLiveStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store} (hbase : locals.get? "wait" = none) :
    let evm0 := initState cA gh bl σ σ₀ g A I
    let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨1⟩ ⟨0⟩
    evalExpr? config { contract := contract, locals := locals } evmLive (.storage waitRef) =
      .ok (.int (Int.ofNat (cageWaitWord σ I).toNat)) := by
  intro evm0 evmLive
  rw [evalExpr_storage_scalar
    (er := ({ base := "wait", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨3⟩)]
  · rw [cureStorageLocLoad_uint256]
    have hload :
        Solm.EVM.storageLoad evmLive evmLive.executionEnv.codeOwner ⟨3⟩ =
          Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨3⟩ := by
      simpa [evmLive, evm0, initState, storageStore_executionEnv] using
        storageLoad_storageStore_ne evm0 I.codeOwner (readSlot := ⟨3⟩)
          (writeSlot := ⟨1⟩) (val := ⟨0⟩) (by native_decide)
    rw [hload]
    simp [cageWaitWord, cureSlotWord, solcSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage]
  · exact hbase
  · simp [waitRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

theorem assign_cageWhenStorage (evm : EVM.State) {locals : Store} (value : UInt256)
    (hbase : locals.get? "when" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage whenRef (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm whenRef =
        .ok ({ base := "when", steps := [] } : EvaledStorageRef) := by
    simp [whenRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨4⟩) (.int (Int.ofNat value.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨4⟩ value
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨4⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem cureCageSourceBodyOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hfit : (cageTimestampWord I).toNat + (cageWaitWord σ I).toNat < UInt256.size) :
    let locals : Store := ∅
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨1⟩ ⟨0⟩
    let sum := cageWhenWord σ I
    let localsWhen := locals.insert "when_" (.int (Int.ofNat sum.toNat))
    let evmWhen := Solm.EVM.storageStore evmLive I.codeOwner ⟨4⟩ sum
    ExecTransitionBody config contract evm0 locals cageTransition.body
      (.returned { contract := contract, locals := localsWhen } evmWhen none) := by
  intro locals evm0 evmLive sum localsWhen evmWhen
  have hprefix := cureCageSourceLiveStorePrefix (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have htimestamp :
      evalExpr? config { contract := contract, locals := locals } evmLive (.env .timestamp) =
        .ok (.int (Int.ofNat (cageTimestampWord I).toNat)) := by
    simpa [locals, evmLive, evm0, cageTimestampWord, storageStore_executionEnv] using
      evalExpr_cageTimestamp (evm := evmLive) (locals := locals)
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evmLive (.storage waitRef) =
        .ok (.int (Int.ofNat (cageWaitWord σ I).toNat)) := by
    simpa [locals, evmLive, evm0] using
      evalExpr_cageWaitAfterLiveStore (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals])
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evmLive
        [.env .timestamp, .storage waitRef] =
          .ok [.int (Int.ofNat (cageTimestampWord I).toNat),
            .int (Int.ofNat (cageWaitWord σ I).toNat)] := by
    simp [evalExprs?, htimestamp, hwait, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat (cageTimestampWord I).toNat),
            .int (Int.ofNat (cageWaitWord σ I).toNat)] =
        some (uintBinaryLocals (cageTimestampWord I) (cageWaitWord σ I)) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hcall :
      ExecStmt config { contract := contract, locals := locals } evmLive
        (.internalCall "_add" [.env .timestamp, .storage waitRef] "when_")
        (.ok { contract := contract, locals := localsWhen } evmLive) := by
    have hbody := execAddFunctionReturn (evm := evmLive)
      (x := cageTimestampWord I) (y := cageWaitWord σ I) (sum := sum)
      (by simp [sum, cageWhenWord]) hfit
    simpa [locals, localsWhen, sum, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals })
        (evm := evmLive) (calleeEvm := evmLive) (name := "_add") (retVar := "when_")
        (args := [.env .timestamp, .storage waitRef])
        (argVals := [.int (Int.ofNat (cageTimestampWord I).toNat),
          .int (Int.ofNat (cageWaitWord σ I).toNat)])
        (callee := addFunction)
        (locals := uintBinaryLocals (cageTimestampWord I) (cageWaitWord σ I))
        (calleeSolm :=
          { contract := contract
            locals := uintBinaryLocalsZ (cageTimestampWord I) (cageWaitWord σ I) sum })
        (value := some [.int (Int.ofNat sum.toNat)])
        hargs (by rfl) hbind hbody)
  have hwhenVar :
      evalExpr? config { contract := contract, locals := localsWhen } evmLive (.var "when_") =
        .ok (.int (Int.ofNat sum.toNat)) := by
    simpa [localsWhen] using evalExpr_varUInt256 (evm := evmLive)
      (locals := localsWhen) (name := "when_") (value := sum) (by simp [localsWhen])
  have hassignWhen :
      assignStorageRef? config { contract := contract, locals := localsWhen } evmLive
        .storage whenRef (.int (Int.ofNat sum.toNat)) =
          .ok ({ contract := contract, locals := localsWhen }, evmWhen) := by
    have hbaseWhen : localsWhen.get? "when" = none := by
      change (locals.insert "when_" (.int (Int.ofNat sum.toNat))).get? "when" = none
      rw [store_get_ne]
      · simp [locals]
      · decide
    simpa [evmWhen, evmLive, evm0, initState, storageStore_executionEnv] using
      assign_cageWhenStorage evmLive (locals := localsWhen) sum
      hbaseWhen
  have htail :
      ExecBlock config { contract := contract, locals := locals } evmLive
        [ .internalCall "_add" [.env .timestamp, .storage waitRef] "when_",
          .assign .storage whenRef (.var "when_") ]
        (.ok { contract := contract, locals := localsWhen } evmWhen) := by
    refine ExecBlock.consNormal hcall ?_
    exact ExecBlock.consNormal (ExecStmt.assign hwhenVar hassignWhen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 cageTransition.body
        (.ok { contract := contract, locals := localsWhen } evmWhen) := by
    simpa [cageTransition, nonpayable, auth, evm0, evmLive] using
      execBlock_append hprefix htail
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK hblock

theorem cureCageSourceBodyReverts_add {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hover : UInt256.size ≤ (cageTimestampWord I).toNat + (cageWaitWord σ I).toNat) :
    let locals : Store := ∅
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals cageTransition.body .reverted := by
  intro locals evm0
  let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨1⟩ ⟨0⟩
  have hprefix := cureCageSourceLiveStorePrefix (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauth hlive
  have htimestamp :
      evalExpr? config { contract := contract, locals := locals } evmLive (.env .timestamp) =
        .ok (.int (Int.ofNat (cageTimestampWord I).toNat)) := by
    simpa [locals, evmLive, evm0, cageTimestampWord, storageStore_executionEnv] using
      evalExpr_cageTimestamp (evm := evmLive) (locals := locals)
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evmLive (.storage waitRef) =
        .ok (.int (Int.ofNat (cageWaitWord σ I).toNat)) := by
    simpa [locals, evmLive, evm0] using
      evalExpr_cageWaitAfterLiveStore (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals])
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evmLive
        [.env .timestamp, .storage waitRef] =
          .ok [.int (Int.ofNat (cageTimestampWord I).toNat),
            .int (Int.ofNat (cageWaitWord σ I).toNat)] := by
    simp [evalExprs?, htimestamp, hwait, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat (cageTimestampWord I).toNat),
            .int (Int.ofNat (cageWaitWord σ I).toNat)] =
        some (uintBinaryLocals (cageTimestampWord I) (cageWaitWord σ I)) := by
    simp [addFunction, uint256, bindParams?, uintBinaryLocals]
  have hcall :
      ExecStmt config { contract := contract, locals := locals } evmLive
        (.internalCall "_add" [.env .timestamp, .storage waitRef] "when_") .reverted := by
    have hbody := execAddFunctionRevert (evm := evmLive)
      (x := cageTimestampWord I) (y := cageWaitWord σ I) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evmLive) (name := "_add") (retVar := "when_")
      (args := [.env .timestamp, .storage waitRef])
      (argVals := [.int (Int.ofNat (cageTimestampWord I).toNat),
        .int (Int.ofNat (cageWaitWord σ I).toNat)])
      (callee := addFunction)
      (locals := uintBinaryLocals (cageTimestampWord I) (cageWaitWord σ I))
      hargs (by rfl) hbind hbody
  have htail :
      ExecBlock config { contract := contract, locals := locals } evmLive
        [ .internalCall "_add" [.env .timestamp, .storage waitRef] "when_",
          .assign .storage whenRef (.var "when_") ] .reverted :=
    ExecBlock.consRevert hcall
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 cageTransition.body
        .reverted := by
    simpa [cageTransition, nonpayable, auth, evm0, evmLive] using
      execBlock_append hprefix htail
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

@[reducible] def cureCageLiveStoreWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.SSTORE, .none)

@[reducible] def cureCageLiveStoreOutPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  p5 + ⟨1⟩

theorem RD.cureCageLiveStore {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : cureCageLiveStoreWf code pc)
    (hperm : ee.perm = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (cureCageLiveStoreOutPc pc) (ret :: R) mem
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨1⟩ ⟨0⟩) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd5⟩
  have rdPrefix := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨0⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov)]
  obtain ⟨_, _, rdStore⟩ := rdPrefix.sstore hperm hd5 (by evm_ov)
  exact ⟨_, _, by simpa [cureCageLiveStoreOutPc] using rdStore⟩

theorem cureCageReachAfterLiveStore {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 1))
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩) :
    ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2742⟩
      [⟨484⟩, cureSelWord I]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩ ⟨0⟩) k C := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 1) rfl hsel
  obtain ⟨_, _, hbodyEntry⟩ := cureReachCageBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  obtain ⟨_, _, hentry⟩ := RD.solcNoArgsExternalEntry
    (code := cureBytecode) (pc := ⟨632⟩) (ret := ⟨484⟩) (routine := ⟨2575⟩)
    hbodyEntry
    (by
      unfold solcNoArgsExternalEntryWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [cureCallerWardsSlot, cureSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
    (code := cureBytecode) (pc := ⟨2575⟩) (okPc := ⟨2665⟩)
    (key := ⟨484⟩) (ret := cureSelWord I) (R := [])
    (by simpa using hentry)
    (by
      unfold cureAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ I ⟨1⟩ = ⟨1⟩ := by
    simpa [cureSlotWord] using hlive
  obtain ⟨_, _, hafterLive⟩ := RD.cureLiveGuardOk
    (code := cureBytecode) (pc := ⟨2665⟩) (okPc := ⟨2736⟩)
    (key := ⟨484⟩) (ret := cureSelWord I) (R := [])
    hafterAuth
    (by
      unfold cureLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)
  obtain ⟨_, _, hafterStore⟩ := RD.cureCageLiveStore
    (code := cureBytecode) (pc := ⟨2736⟩) (ret := ⟨484⟩) (R := [cureSelWord I])
    hafterLive
    (by
      unfold cureCageLiveStoreWf
      repeat' first | apply And.intro | native_decide)
    hperm (by simp)
  exact ⟨_, _, by simpa [cureCageLiveStoreOutPc] using hafterStore⟩

abbrev cureCageEventTopic : UInt256 :=
  ⟨15846720854843032105251646702598932867924719938341352344186736728916659600346⟩

theorem RD.cureCageSuccessTail {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD cureBytecode I g s0 ⟨2742⟩ [⟨484⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩ ⟨0⟩) k C)
    (hperm : I.perm = true)
    (hfit :
      (cageTimestampWord I).toNat + (cageWaitWord σ I).toNat < UInt256.size) :
    RDret cureBytecode g s0
      (cA, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨1⟩ ⟨0⟩)
        ⟨4⟩ (cageWhenWord σ I))
      ByteArray.empty := by
  let mem := twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem
  have hwaitLive :
      (((sstoreAccountMap I.codeOwner σ ⟨1⟩ ⟨0⟩).find? I.codeOwner).option
          (⟨0⟩ : UInt256) (fun acc => acc.storage.findD ⟨3⟩ (⟨0⟩ : UInt256))) =
        cageWaitWord σ I := by
    simpa [cageWaitWord, cureSlotWord, solcSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨3⟩ ⟨1⟩ ⟨0⟩
        (by native_decide)
  have rd2744 := evm_run h with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2745₀⟩ := rd2744.sload (by native_decide) (by simp)
  have rd2745 := rd2745₀
  rw [hwaitLive] at rd2745
  have rd2754 := evm_run rd2745 with [
    raw push2 ⟨2755⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by simp),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨3749⟩ (by native_decide) (by evm_ov)]
  have rd3749 := rd2754.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd2755⟩ := RD.solcCheckedAddSuccess
      (code := cureBytecode) (ee := I) (g := g) (s0 := s0)
      (pc := ⟨3749⟩) (okPc := ⟨3743⟩) (a := cageTimestampWord I)
      (b := cageWaitWord σ I) (ret := ⟨2755⟩) (R := [⟨484⟩, sel])
      rd3749
      (by
        unfold solcCheckedAddSuccessWf
        repeat' first | apply And.intro | native_decide)
      hfit (by jump_dest) (by jump_dest) (by simp)
  have hsum :
      cageTimestampWord I + cageWaitWord σ I = cageWhenWord σ I := by
    rfl
  rw [hsum] at rd2755
  have rd2758 := evm_run rd2755 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2759⟩ := rd2758.sstore hperm (by native_decide) (by simp)
  have hmem : mem.size = 96 := by
    simpa [mem] using twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩
      solcFreePtrMem_size
  have hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem] using twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩
      solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rd2761 := evm_run rd2759 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov)]
  have rd2762 := rd2761.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost hmload64 (by native_decide) (by evm_ov)
  have rd2795 := rd2762.pushConst cureCageEventTopic
    (op := .PUSH32) (width := 32) (by decide) (by native_decide) (by evm_ov)
  have rd2799 := evm_run rd2795 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2800 := RD.log1 0 (UInt256.ofNat 3) rd2799
    (by native_decide) hperm mem_cost (by native_decide) (by evm_ov)
  have rd2801 := rd2800.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rdStop := rd2801.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rdStop (by native_decide) (by evm_ov)

theorem RD.cureCageAddRevertTail {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD cureBytecode I g s0 ⟨2742⟩ [⟨484⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩ ⟨0⟩) k C)
    (hover : UInt256.size ≤
      (cageTimestampWord I).toNat + (cageWaitWord σ I).toNat) :
    RDrev cureBytecode g s0 := by
  let mem := twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem
  have hwaitLive :
      (((sstoreAccountMap I.codeOwner σ ⟨1⟩ ⟨0⟩).find? I.codeOwner).option
          (⟨0⟩ : UInt256) (fun acc => acc.storage.findD ⟨3⟩ (⟨0⟩ : UInt256))) =
        cageWaitWord σ I := by
    simpa [cageWaitWord, cureSlotWord, solcSlotWord] using
      sstoreAccountMap_storage_findD_ne σ I.codeOwner ⟨3⟩ ⟨1⟩ ⟨0⟩
        (by native_decide)
  have rd2744 := evm_run h with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2745₀⟩ := rd2744.sload (by native_decide) (by simp)
  have rd2745 := rd2745₀
  rw [hwaitLive] at rd2745
  have rd2754 := evm_run rd2745 with [
    raw push2 ⟨2755⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw timestamp (by native_decide) (by simp),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨3749⟩ (by native_decide) (by evm_ov)]
  have rd3749 := rd2754.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hmem : mem.size = 96 := by
    simpa [mem] using twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩
      solcFreePtrMem_size
  have hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem] using twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩
      solcFreePtrMem_size solcFreePtrMem_read64
  exact RD.solcCheckedAddStringRevert
    (code := cureBytecode) (ee := I) (g := g) (s0 := s0)
    (pc := ⟨3749⟩) (okPc := ⟨3743⟩)
    (len := ⟨17⟩)
    (rawWord := ⟨22955032233328820198124048709524453617527⟩)
    (shift := ⟨120⟩)
    (word := UInt256.shiftLeft
      (⟨22955032233328820198124048709524453617527⟩ : UInt256) ⟨120⟩)
    (op := .PUSH17) (width := 17)
    (a := cageTimestampWord I) (b := cageWaitWord σ I)
    (ret := ⟨2755⟩) (R := [⟨484⟩, sel])
    rd3749
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf solcCheckedArithmeticRevertPc
      repeat' first | apply And.intro | native_decide)
    (by decide)
    hover
    (by rfl)
    hmem hread64 (by simp)

theorem cureCageBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let sel := cureSelWord I
  let callerSlot := cureCallerWardsSlot I
  let locals : Store := ∅
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 1) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    cureDispatchCage hsel
  have hdecode :
      decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
        (transitionSignature cageTransition).paramTypes I.calldata = some locals := by
    simpa [locals] using cureDecode_cage hsz4
  obtain ⟨_, _, hbodyEntry⟩ := cureReachCageBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  obtain ⟨_, _, hentry⟩ := RD.solcNoArgsExternalEntry
    (code := cureBytecode) (pc := ⟨632⟩) (ret := ⟨484⟩) (routine := ⟨2575⟩)
    hbodyEntry
    (by
      unfold solcNoArgsExternalEntryWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest)
  have hcallerWord : cureSlotWord callerSlot σ_evm I = cureSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hliveWord : cureSlotWord ⟨1⟩ σ_evm I = cureSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hwaitWord : cageWaitWord σ_evm I = cageWaitWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  by_cases hauthEvm : cureSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : cureSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
    obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
      (code := cureBytecode) (pc := ⟨2575⟩) (okPc := ⟨2665⟩)
      (key := ⟨484⟩) (ret := sel) (R := [])
      (by simpa [sel] using hentry)
      (by
        unfold cureAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)
    by_cases hliveEvm : cureSlotWord ⟨1⟩ σ_evm I = ⟨1⟩
    · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I = ⟨1⟩ := by
        rw [← hliveWord]
        exact hliveEvm
      by_cases hfitEvm :
          (cageTimestampWord I).toNat + (cageWaitWord σ_evm I).toNat < UInt256.size
      · have hfitSolm :
            (cageTimestampWord I).toNat + (cageWaitWord σ_solm I).toNat <
              UInt256.size := by
          rwa [← hwaitWord]
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let evmLive := Solm.EVM.storageStore evm0 I.codeOwner ⟨1⟩ ⟨0⟩
        let sumSolm := cageWhenWord σ_solm I
        let localsWhen := locals.insert "when_" (.int (Int.ofNat sumSolm.toNat))
        let evmWhen := Solm.EVM.storageStore evmLive I.codeOwner ⟨4⟩ sumSolm
        have hbody :
            ExecTransitionBody config contract evm0 locals cageTransition.body
              (.returned { contract := contract, locals := localsWhen } evmWhen none) := by
          simpa [locals, evm0, evmLive, sumSolm, localsWhen, evmWhen] using
            cureCageSourceBodyOk (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm hfitSolm
        obtain ⟨_, _, hafterLiveStore⟩ := cureCageReachAfterLiveStore
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hsize hperm hwv hsel hauthEvm hliveEvm
        have hret := RD.cureCageSuccessTail
          (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (sel := sel) hafterLiveStore hperm hfitEvm
        have hsumEq : cageWhenWord σ_evm I = cageWhenWord σ_solm I := by
          simp [cageWhenWord, hwaitWord]
        have hcreated :
            (cA, sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ ⟨0⟩) ⟨4⟩
                (cageWhenWord σ_evm I)).1 = evmWhen.createdAccounts := by
          simp [evmWhen, evmLive, evm0, initState, storageStore_createdAccounts]
        have haccounts :
            accountMapEquiv
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ_evm ⟨1⟩ ⟨0⟩) ⟨4⟩
                (cageWhenWord σ_evm I))
              evmWhen.accountMap := by
          simpa [evmWhen, evmLive, evm0, initState, storageStore_accountMap, hsumEq] using
            accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner
              ⟨1⟩ ⟨0⟩ ⟨4⟩ (cageWhenWord σ_evm I) hAccounts
        have henc : returnEquiv ByteArray.empty none cageTransition.returnType := by
          rw [show cageTransition.returnType = [] by rfl]
          exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          hcreated haccounts henc
      · have hoverEvm :
            UInt256.size ≤ (cageTimestampWord I).toNat + (cageWaitWord σ_evm I).toNat :=
          Nat.le_of_not_lt hfitEvm
        have hoverSolm :
            UInt256.size ≤ (cageTimestampWord I).toNat + (cageWaitWord σ_solm I).toNat := by
          rwa [← hwaitWord]
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody : ExecTransitionBody config contract evm0 locals cageTransition.body .reverted := by
          simpa [locals, evm0] using
            cureCageSourceBodyReverts_add (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hliveSolm hoverSolm
        obtain ⟨_, _, hafterLiveStore⟩ := cureCageReachAfterLiveStore
          (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hsize hperm hwv hsel hauthEvm hliveEvm
        have hrev := RD.cureCageAddRevertTail
          (cA := cA) (σ := σ_evm) (I := I) (g := Sat256.ofUInt256 g)
          (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          (sel := sel) hafterLiveStore hoverEvm
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hliveEvm (by rw [hliveWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals cageTransition.body .reverted := by
        have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hauthSolm
        have hguardLive := cureLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals]) hliveSolm
        have hblock :
            ExecBlock config { contract := contract, locals := locals } evm0
              [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                .require (.binary .eq (.storage liveRef) (.intLit 1)),
                .assign .storage liveRef (.intLit 0),
                .internalCall "_add" [.env .timestamp, .storage waitRef] "when_",
                .assign .storage whenRef (.var "when_") ]
              .reverted := by
          refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
          · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
          refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
          exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
        simpa [ExecTransitionBody, cageTransition, nonpayable, auth, evm0, locals] using
          ExecFuncBody.execBlockRevert hblock
      have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ ≠ ⟨1⟩ := by
        simpa [cureSlotWord] using hliveEvm
      have hmemAuth :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hread64 :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ :=
        twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
          solcFreePtrMem_read64
      have hrev := RD.cureLiveGuardRevert
        (code := cureBytecode) (pc := ⟨2665⟩) (okPc := ⟨2736⟩)
        (key := ⟨484⟩) (ret := sel) (R := []) hafterAuth
        (by
          unfold cureLiveGuardWf
          repeat' first | apply And.intro | native_decide)
        (by
          unfold solcErrorStringRevertTailWf cureLiveGuardTailPc cureNotLiveRawWord
          repeat' first | apply And.intro | native_decide)
        hliveSolc hmemAuth hread64 (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : cureSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals cageTransition.body .reverted := by
      have hguard := cureAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .assign .storage liveRef (.intLit 0),
          .internalCall "_add" [.env .timestamp, .storage waitRef] "when_",
          .assign .storage whenRef (.var "when_")])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, cageTransition, nonpayable, auth, evm0, locals] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
    have hrev := RD.cureAuthCheckRevert
      (code := cureBytecode) (pc := ⟨2575⟩) (okPc := ⟨2665⟩)
      (key := ⟨484⟩) (ret := sel) (R := [])
      (by simpa [sel] using hentry)
      (by
        unfold cureAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcErrorStringRevertTailWf cureAuthTailPc cureNotAuthorizedRawWord
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by simp)
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Cure
