import Benchmarks.Dss.Spot.PokeDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

theorem execPokeTrueArithmeticReturns (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size) (hlo32 : 32 ≤ out.size)
    (henv : evm.executionEnv = I) {valScaled spot1 spot2 : UInt256}
    (hvalScaled : valScaled = pokePeekValWord out * pokeBillion)
    (hfitVal : (pokePeekValWord out).toNat * pokeBillion.toNat < UInt256.size)
    (hfitPar : valScaled.toNat *
        pokeRay.toNat < UInt256.size)
    (hparNe : pokeParWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hspot1 :
      spot1 = UInt256.div (valScaled * pokeRay)
        (pokeParWord evm.accountMap evm.executionEnv))
    (hfitMat : spot1.toNat * pokeRay.toNat < UInt256.size)
    (hmatNe : pokeMatWord evm.accountMap I ≠ ⟨0⟩)
    (hspot2 : spot2 = UInt256.div (spot1 * pokeRay) (pokeMatWord evm.accountMap I)) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
        [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
          .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
            "spot2",
          .assign .localVar { base := "spot" } (.var "spot2") ])
      (.ok { contract := contract, locals := pokeSpotAssignedLocals I out valScaled spot1 spot2 }
        evm) := by
  let locals0 := pokeSpotLocals I out ⟨0⟩
  let localsV := pokeValScaledLocals I out valScaled
  let par := pokeParWord evm.accountMap evm.executionEnv
  let mat := pokeMatWord evm.accountMap I
  have hvalCast :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (.cast (.var "val") uint256St) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    simpa [locals0] using evalExpr_pokeValCastUInt256 evm I out hlo32
  have hBillionLit :
      evalExpr? config { contract := contract, locals := locals0 } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hMul :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (mul256 (.cast (.var "val") uint256St) (.intLit billion)) =
          .ok (.int (Int.ofNat valScaled.toNat)) :=
    evalExpr_spot_mul256_ok hvalCast hBillionLit hvalScaled hfitVal
  have hValScaledStmt :
      ExecStmt config { contract := contract, locals := locals0 } evm
        (.letDecl "valScaled" (some uint256)
          (mul256 (.cast (.var "val") uint256St) (.intLit billion)))
        (.ok { contract := contract, locals := localsV } evm) := by
    simpa [locals0, localsV, pokeValScaledLocals] using ExecStmt.letDecl hMul
  have hValScaledVar :
      evalExpr? config { contract := contract, locals := localsV } evm (.var "valScaled") =
        .ok (.int (Int.ofNat valScaled.toNat)) := by
    simpa [localsV] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsV) (name := "valScaled") (value := valScaled)
      (pokeValScaledLocals_get_valScaled I out valScaled)
  have hBillionLitV :
      evalExpr? config { contract := contract, locals := localsV } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hZeroLitV :
      evalExpr? config { contract := contract, locals := localsV } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hBillionEqZero :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .eq (.intLit billion) (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_spot_eq_int_false hBillionLitV hZeroLitV
    norm_num [pokeBillion_toNat]
  have hDivCheck :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .div (.var "valScaled") (.intLit billion)) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    have hdivWord : UInt256.div valScaled pokeBillion = pokePeekValWord out := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : valScaled.toNat = (pokePeekValWord out).toNat * pokeBillion.toNat := by
        rw [hvalScaled, umul_toNat (pokePeekValWord out) pokeBillion hfitVal]
      have hBillionPos : 0 < pokeBillion.toNat := by
        rw [pokeBillion_toNat]
        norm_num
      rw [hprod]
      simpa [Nat.mul_comm] using
        Nat.mul_div_right (pokePeekValWord out).toNat hBillionPos
    have h := evalExpr_spot_div_uint256_ok (evm := evm) (locals := localsV)
      (x := .var "valScaled") (y := .intLit billion)
      (a := valScaled) (b := pokeBillion) (q := UInt256.div valScaled pokeBillion)
      hValScaledVar hBillionLitV (by native_decide) rfl
    simpa [hdivWord] using h
  have hRightCheck :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .eq
          (.binary .div (.var "valScaled") (.intLit billion))
          (.cast (.var "val") uint256St)) = .ok (.bool true) := by
    have hvalCastV :
        evalExpr? config { contract := contract, locals := localsV } evm
          (.cast (.var "val") uint256St) =
            .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
      simpa [localsV] using
        evalExpr_pokeValCastUInt256_ofLocals (evm := evm) (locals := localsV)
          (out := out) (pokeValScaledLocals_get_val I out valScaled) hlo32
    exact evalExpr_spot_eq_int_true hDivCheck hvalCastV rfl
  have hReq :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .or
          (.binary .eq (.intLit billion) (.intLit 0))
          (.binary .eq (.binary .div (.var "valScaled") (.intLit billion))
            (.cast (.var "val") uint256St))) = .ok (.bool true) :=
    evalExpr_spot_or_false_right hBillionEqZero hRightCheck
  have hPar :
      evalExpr? config { contract := contract, locals := localsV } evm (.storage parRef) =
        .ok (.int (Int.ofNat par.toNat)) := by
    simpa [localsV, par] using
      evalExpr_pokeStorageParOfLocals (evm := evm) (locals := localsV)
        (pokeValScaledLocals_get_par I out valScaled)
  have hRdiv1Args :
      evalExprs? config { contract := contract, locals := localsV } evm
        [.var "valScaled", .storage parRef] =
          .ok [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)] := by
    simp [evalExprs?, hValScaledVar, hPar, EvalResult.bind, bind, pure]
  have hlookupRdiv : lookupCallable? contract "rdiv" = some rdivFunction.toCallable := by
    rfl
  have hbindRdiv1 :
      bindParams? rdivFunction.params
          [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)] =
        some (spotUintBinaryLocals valScaled par) := by
    simp [rdivFunction, uint256, bindParams?, spotUintBinaryLocals]
  have hRdiv1Stmt :
      ExecStmt config { contract := contract, locals := localsV } evm
        (.internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1")
        (.ok { contract := contract, locals := pokeSpot1Locals I out valScaled spot1 }
          evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := localsV })
      (evm := evm) (name := "rdiv") (retVar := "spot1")
      (args := [.var "valScaled", .storage parRef])
      (argVals := [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)])
      (callee := rdivFunction) (locals := spotUintBinaryLocals valScaled par)
      hRdiv1Args hlookupRdiv hbindRdiv1
      (execSpotRdivFunctionReturn evm (x := valScaled) (y := par)
        (prod := valScaled * pokeRay) (q := spot1) rfl hfitPar hparNe
        (by simpa [par] using hspot1))
    simpa [resumeAfterInternalCall, localsV, pokeSpot1Locals, par] using h
  let locals1 := pokeSpot1Locals I out valScaled spot1
  have hSpot1Var :
      evalExpr? config { contract := contract, locals := locals1 } evm (.var "spot1") =
        .ok (.int (Int.ofNat spot1.toNat)) := by
    simpa [locals1] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals1) (name := "spot1") (value := spot1)
      (pokeSpot1Locals_get_spot1 I out valScaled spot1)
  have hMat :
      evalExpr? config { contract := contract, locals := locals1 } evm
        (.storage (ilksF (.var "ilk") "mat")) =
          .ok (.int (Int.ofNat mat.toNat)) := by
    simpa [locals1, mat] using
      evalExpr_pokeStorageMatOfLocals (evm := evm) (I := I) (locals := locals1)
        hsz36 henv
        (pokeSpot1Locals_get_ilk I out valScaled spot1)
        (pokeSpot1Locals_get_ilks I out valScaled spot1)
  have hRdiv2Args :
      evalExprs? config { contract := contract, locals := locals1 } evm
        [.var "spot1", .storage (ilksF (.var "ilk") "mat")] =
          .ok [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)] := by
    simp [evalExprs?, hSpot1Var, hMat, EvalResult.bind, bind, pure]
  have hbindRdiv2 :
      bindParams? rdivFunction.params
          [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)] =
        some (spotUintBinaryLocals spot1 mat) := by
    simp [rdivFunction, uint256, bindParams?, spotUintBinaryLocals]
  have hRdiv2Stmt :
      ExecStmt config { contract := contract, locals := locals1 } evm
        (.internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
          "spot2")
        (.ok { contract := contract, locals := pokeSpot2Locals I out valScaled spot1 spot2 }
          evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals1 })
      (evm := evm) (name := "rdiv") (retVar := "spot2")
      (args := [.var "spot1", .storage (ilksF (.var "ilk") "mat")])
      (argVals := [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)])
      (callee := rdivFunction) (locals := spotUintBinaryLocals spot1 mat)
      hRdiv2Args hlookupRdiv hbindRdiv2
      (execSpotRdivFunctionReturn evm (x := spot1) (y := mat)
        (prod := spot1 * pokeRay) (q := spot2) rfl hfitMat hmatNe
        (by simpa [mat] using hspot2))
    simpa [resumeAfterInternalCall, locals1, pokeSpot2Locals, mat] using h
  let locals2 := pokeSpot2Locals I out valScaled spot1 spot2
  have hSpot2Var :
      evalExpr? config { contract := contract, locals := locals2 } evm (.var "spot2") =
        .ok (.int (Int.ofNat spot2.toNat)) := by
    simpa [locals2] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals2) (name := "spot2") (value := spot2)
      (pokeSpot2Locals_get_spot2 I out valScaled spot1 spot2)
  have hAssign :
      assignStorageRef? config { contract := contract, locals := locals2 } evm .localVar
          { base := "spot" } (.int (Int.ofNat spot2.toNat)) =
        .ok ({ contract := contract, locals := pokeSpotAssignedLocals I out valScaled spot1 spot2 }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, locals2,
      pokeSpotAssignedLocals, pokeSpot2Locals]
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal hValScaledStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
  refine ExecBlock.consNormal hRdiv1Stmt ?_
  refine ExecBlock.consNormal (by simpa [locals1] using hRdiv2Stmt) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hSpot2Var hAssign) ExecBlock.nil

theorem execPokeTrueValScaledOverflowReverts
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hlo32 : 32 ≤ out.size)
    (hover : UInt256.size ≤ (pokePeekValWord out).toNat * pokeBillion.toNat) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
        [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
          .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
            "spot2",
          .assign .localVar { base := "spot" } (.var "spot2") ])
      .reverted := by
  let locals0 := pokeSpotLocals I out ⟨0⟩
  have hvalCast :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (.cast (.var "val") uint256St) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    simpa [locals0] using evalExpr_pokeValCastUInt256 evm I out hlo32
  have hBillionLit :
      evalExpr? config { contract := contract, locals := locals0 } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hMulRev :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (mul256 (.cast (.var "val") uint256St) (.intLit billion)) = .revert :=
    evalExpr_spot_mul256_revert hvalCast hBillionLit hover
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)

set_option maxHeartbeats 1000000 in
theorem execPokeTrueRdivParMulOverflowReverts
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hlo32 : 32 ≤ out.size) {valScaled : UInt256}
    (hvalScaled : valScaled = pokePeekValWord out * pokeBillion)
    (hfitVal : (pokePeekValWord out).toNat * pokeBillion.toNat < UInt256.size)
    (hoverPar : UInt256.size ≤ valScaled.toNat * pokeRay.toNat) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
        [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
          .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
            "spot2",
          .assign .localVar { base := "spot" } (.var "spot2") ])
      .reverted := by
  let locals0 := pokeSpotLocals I out ⟨0⟩
  let localsV := pokeValScaledLocals I out valScaled
  let par := pokeParWord evm.accountMap evm.executionEnv
  have hvalCast :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (.cast (.var "val") uint256St) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    simpa [locals0] using evalExpr_pokeValCastUInt256 evm I out hlo32
  have hBillionLit :
      evalExpr? config { contract := contract, locals := locals0 } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hMul :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (mul256 (.cast (.var "val") uint256St) (.intLit billion)) =
          .ok (.int (Int.ofNat valScaled.toNat)) := by
    exact evalExpr_spot_mul256_ok hvalCast hBillionLit hvalScaled hfitVal
  have hValScaledStmt :
      ExecStmt config { contract := contract, locals := locals0 } evm
        (.letDecl "valScaled" (some uint256)
          (mul256 (.cast (.var "val") uint256St) (.intLit billion)))
        (.ok { contract := contract, locals := localsV } evm) := by
    simpa [locals0, localsV, pokeValScaledLocals] using
      (ExecStmt.letDecl
        (cfg := config) (solm := { contract := contract, locals := locals0 })
        (evm := evm) (name := "valScaled") (ty := some uint256)
        (expr := mul256 (.cast (.var "val") uint256St) (.intLit billion))
        (value := .int (Int.ofNat valScaled.toNat)) hMul)
  have hValScaledVar :
      evalExpr? config { contract := contract, locals := localsV } evm (.var "valScaled") =
        .ok (.int (Int.ofNat valScaled.toNat)) := by
    simpa [localsV] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsV) (name := "valScaled") (value := valScaled)
      (pokeValScaledLocals_get_valScaled I out valScaled)
  have hBillionLitV :
      evalExpr? config { contract := contract, locals := localsV } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hZeroLitV :
      evalExpr? config { contract := contract, locals := localsV } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hBillionEqZero :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .eq (.intLit billion) (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_spot_eq_int_false hBillionLitV hZeroLitV
    norm_num [pokeBillion_toNat]
  have hDivCheck :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .div (.var "valScaled") (.intLit billion)) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    have hdivWord : UInt256.div valScaled pokeBillion = pokePeekValWord out := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : valScaled.toNat = (pokePeekValWord out).toNat * pokeBillion.toNat := by
        rw [hvalScaled, umul_toNat (pokePeekValWord out) pokeBillion hfitVal]
      have hBillionPos : 0 < pokeBillion.toNat := by
        rw [pokeBillion_toNat]
        norm_num
      rw [hprod]
      simpa [Nat.mul_comm] using
        Nat.mul_div_right (pokePeekValWord out).toNat hBillionPos
    have h := evalExpr_spot_div_uint256_ok (evm := evm) (locals := localsV)
      (x := .var "valScaled") (y := .intLit billion)
      (a := valScaled) (b := pokeBillion) (q := UInt256.div valScaled pokeBillion)
      hValScaledVar hBillionLitV (by native_decide) rfl
    simpa [hdivWord] using h
  have hRightCheck :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .eq
          (.binary .div (.var "valScaled") (.intLit billion))
          (.cast (.var "val") uint256St)) = .ok (.bool true) := by
    have hvalCastV :
        evalExpr? config { contract := contract, locals := localsV } evm
          (.cast (.var "val") uint256St) =
            .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
      simpa [localsV] using
        evalExpr_pokeValCastUInt256_ofLocals (evm := evm) (locals := localsV)
          (out := out) (pokeValScaledLocals_get_val I out valScaled) hlo32
    exact evalExpr_spot_eq_int_true hDivCheck hvalCastV rfl
  have hReq :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .or
          (.binary .eq (.intLit billion) (.intLit 0))
          (.binary .eq (.binary .div (.var "valScaled") (.intLit billion))
            (.cast (.var "val") uint256St))) = .ok (.bool true) :=
    evalExpr_spot_or_false_right hBillionEqZero hRightCheck
  have hPar :
      evalExpr? config { contract := contract, locals := localsV } evm (.storage parRef) =
        .ok (.int (Int.ofNat par.toNat)) := by
    simpa [localsV, par] using
      evalExpr_pokeStorageParOfLocals (evm := evm) (locals := localsV)
        (pokeValScaledLocals_get_par I out valScaled)
  have hRdiv1Args :
      evalExprs? config { contract := contract, locals := localsV } evm
        [.var "valScaled", .storage parRef] =
          .ok [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)] := by
    simp [evalExprs?, hValScaledVar, hPar, EvalResult.bind, bind, pure]
  have hlookupRdiv : lookupCallable? contract "rdiv" = some rdivFunction.toCallable := by
    rfl
  have hbindRdiv1 :
      bindParams? rdivFunction.params
          [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)] =
        some (spotUintBinaryLocals valScaled par) := by
    simp [rdivFunction, uint256, bindParams?, spotUintBinaryLocals]
  have hRdiv1Stmt :
      ExecStmt config { contract := contract, locals := localsV } evm
        (.internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1") .reverted :=
    internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := localsV })
      (evm := evm) (name := "rdiv") (retVar := "spot1")
      (args := [.var "valScaled", .storage parRef])
      (argVals := [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)])
      (callee := rdivFunction) (locals := spotUintBinaryLocals valScaled par)
      hRdiv1Args hlookupRdiv hbindRdiv1
      (execSpotRdivFunctionRevertMul evm (x := valScaled) (y := par) hoverPar)
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal hValScaledStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
  exact ExecBlock.consRevert hRdiv1Stmt

set_option maxHeartbeats 1000000 in
theorem execPokeTrueRdivParDivZeroReverts
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hlo32 : 32 ≤ out.size) {valScaled : UInt256}
    (hvalScaled : valScaled = pokePeekValWord out * pokeBillion)
    (hfitVal : (pokePeekValWord out).toNat * pokeBillion.toNat < UInt256.size)
    (hfitPar : valScaled.toNat * pokeRay.toNat < UInt256.size)
    (hparZero : pokeParWord evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
        [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
          .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
            "spot2",
          .assign .localVar { base := "spot" } (.var "spot2") ])
      .reverted := by
  let locals0 := pokeSpotLocals I out ⟨0⟩
  let localsV := pokeValScaledLocals I out valScaled
  let par := pokeParWord evm.accountMap evm.executionEnv
  have hvalCast :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (.cast (.var "val") uint256St) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    simpa [locals0] using evalExpr_pokeValCastUInt256 evm I out hlo32
  have hBillionLit :
      evalExpr? config { contract := contract, locals := locals0 } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hMul :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (mul256 (.cast (.var "val") uint256St) (.intLit billion)) =
          .ok (.int (Int.ofNat valScaled.toNat)) := by
    exact evalExpr_spot_mul256_ok hvalCast hBillionLit hvalScaled hfitVal
  have hValScaledStmt :
      ExecStmt config { contract := contract, locals := locals0 } evm
        (.letDecl "valScaled" (some uint256)
          (mul256 (.cast (.var "val") uint256St) (.intLit billion)))
        (.ok { contract := contract, locals := localsV } evm) := by
    simpa [locals0, localsV, pokeValScaledLocals] using
      (ExecStmt.letDecl
        (cfg := config) (solm := { contract := contract, locals := locals0 })
        (evm := evm) (name := "valScaled") (ty := some uint256)
        (expr := mul256 (.cast (.var "val") uint256St) (.intLit billion))
        (value := .int (Int.ofNat valScaled.toNat)) hMul)
  have hValScaledVar :
      evalExpr? config { contract := contract, locals := localsV } evm (.var "valScaled") =
        .ok (.int (Int.ofNat valScaled.toNat)) := by
    simpa [localsV] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsV) (name := "valScaled") (value := valScaled)
      (pokeValScaledLocals_get_valScaled I out valScaled)
  have hBillionLitV :
      evalExpr? config { contract := contract, locals := localsV } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hZeroLitV :
      evalExpr? config { contract := contract, locals := localsV } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hBillionEqZero :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .eq (.intLit billion) (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_spot_eq_int_false hBillionLitV hZeroLitV
    norm_num [pokeBillion_toNat]
  have hDivCheck :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .div (.var "valScaled") (.intLit billion)) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    have hdivWord : UInt256.div valScaled pokeBillion = pokePeekValWord out := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : valScaled.toNat = (pokePeekValWord out).toNat * pokeBillion.toNat := by
        rw [hvalScaled, umul_toNat (pokePeekValWord out) pokeBillion hfitVal]
      have hBillionPos : 0 < pokeBillion.toNat := by
        rw [pokeBillion_toNat]
        norm_num
      rw [hprod]
      simpa [Nat.mul_comm] using
        Nat.mul_div_right (pokePeekValWord out).toNat hBillionPos
    have h := evalExpr_spot_div_uint256_ok (evm := evm) (locals := localsV)
      (x := .var "valScaled") (y := .intLit billion)
      (a := valScaled) (b := pokeBillion) (q := UInt256.div valScaled pokeBillion)
      hValScaledVar hBillionLitV (by native_decide) rfl
    simpa [hdivWord] using h
  have hRightCheck :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .eq
          (.binary .div (.var "valScaled") (.intLit billion))
          (.cast (.var "val") uint256St)) = .ok (.bool true) := by
    have hvalCastV :
        evalExpr? config { contract := contract, locals := localsV } evm
          (.cast (.var "val") uint256St) =
            .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
      simpa [localsV] using
        evalExpr_pokeValCastUInt256_ofLocals (evm := evm) (locals := localsV)
          (out := out) (pokeValScaledLocals_get_val I out valScaled) hlo32
    exact evalExpr_spot_eq_int_true hDivCheck hvalCastV rfl
  have hReq :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .or
          (.binary .eq (.intLit billion) (.intLit 0))
          (.binary .eq (.binary .div (.var "valScaled") (.intLit billion))
            (.cast (.var "val") uint256St))) = .ok (.bool true) :=
    evalExpr_spot_or_false_right hBillionEqZero hRightCheck
  have hPar :
      evalExpr? config { contract := contract, locals := localsV } evm (.storage parRef) =
        .ok (.int (Int.ofNat par.toNat)) := by
    simpa [localsV, par] using
      evalExpr_pokeStorageParOfLocals (evm := evm) (locals := localsV)
        (pokeValScaledLocals_get_par I out valScaled)
  have hRdiv1Args :
      evalExprs? config { contract := contract, locals := localsV } evm
        [.var "valScaled", .storage parRef] =
          .ok [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)] := by
    simp [evalExprs?, hValScaledVar, hPar, EvalResult.bind, bind, pure]
  have hlookupRdiv : lookupCallable? contract "rdiv" = some rdivFunction.toCallable := by
    rfl
  have hbindRdiv1 :
      bindParams? rdivFunction.params
          [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)] =
        some (spotUintBinaryLocals valScaled par) := by
    simp [rdivFunction, uint256, bindParams?, spotUintBinaryLocals]
  have hRdiv1Stmt :
      ExecStmt config { contract := contract, locals := localsV } evm
        (.internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1") .reverted :=
    internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := localsV })
      (evm := evm) (name := "rdiv") (retVar := "spot1")
      (args := [.var "valScaled", .storage parRef])
      (argVals := [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)])
      (callee := rdivFunction) (locals := spotUintBinaryLocals valScaled par)
      hRdiv1Args hlookupRdiv hbindRdiv1
      (execSpotRdivFunctionRevertDivZero evm (x := valScaled) (y := par)
        (prod := valScaled * pokeRay) rfl hfitPar (by simpa [par] using hparZero))
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal hValScaledStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
  exact ExecBlock.consRevert hRdiv1Stmt

set_option maxHeartbeats 1000000 in
theorem execPokeTrueAfterRdivParThenRdivMatReverts
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hlo32 : 32 ≤ out.size) {valScaled spot1 : UInt256}
    (hvalScaled : valScaled = pokePeekValWord out * pokeBillion)
    (hfitVal : (pokePeekValWord out).toNat * pokeBillion.toNat < UInt256.size)
    (hfitPar : valScaled.toNat * pokeRay.toNat < UInt256.size)
    (hparNe : pokeParWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hspot1 :
      spot1 = UInt256.div (valScaled * pokeRay)
        (pokeParWord evm.accountMap evm.executionEnv))
    (hRdiv2Stmt :
      ExecStmt config { contract := contract, locals := pokeSpot1Locals I out valScaled spot1 } evm
        (.internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
          "spot2")
        .reverted) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
        [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
          .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
            "spot2",
          .assign .localVar { base := "spot" } (.var "spot2") ])
      .reverted := by
  let locals0 := pokeSpotLocals I out ⟨0⟩
  let localsV := pokeValScaledLocals I out valScaled
  let locals1 := pokeSpot1Locals I out valScaled spot1
  let par := pokeParWord evm.accountMap evm.executionEnv
  have hvalCast :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (.cast (.var "val") uint256St) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    simpa [locals0] using evalExpr_pokeValCastUInt256 evm I out hlo32
  have hBillionLit :
      evalExpr? config { contract := contract, locals := locals0 } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hMul :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (mul256 (.cast (.var "val") uint256St) (.intLit billion)) =
          .ok (.int (Int.ofNat valScaled.toNat)) := by
    exact evalExpr_spot_mul256_ok hvalCast hBillionLit hvalScaled hfitVal
  have hValScaledStmt :
      ExecStmt config { contract := contract, locals := locals0 } evm
        (.letDecl "valScaled" (some uint256)
          (mul256 (.cast (.var "val") uint256St) (.intLit billion)))
        (.ok { contract := contract, locals := localsV } evm) := by
    simpa [locals0, localsV, pokeValScaledLocals] using
      (ExecStmt.letDecl
        (cfg := config) (solm := { contract := contract, locals := locals0 })
        (evm := evm) (name := "valScaled") (ty := some uint256)
        (expr := mul256 (.cast (.var "val") uint256St) (.intLit billion))
        (value := .int (Int.ofNat valScaled.toNat)) hMul)
  have hValScaledVar :
      evalExpr? config { contract := contract, locals := localsV } evm (.var "valScaled") =
        .ok (.int (Int.ofNat valScaled.toNat)) := by
    simpa [localsV] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsV) (name := "valScaled") (value := valScaled)
      (pokeValScaledLocals_get_valScaled I out valScaled)
  have hBillionLitV :
      evalExpr? config { contract := contract, locals := localsV } evm (.intLit billion) =
        .ok (.int (Int.ofNat pokeBillion.toNat)) := by
    simp [evalExpr?, pure, billion_eq_pokeBillion_toNat]
  have hZeroLitV :
      evalExpr? config { contract := contract, locals := localsV } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hBillionEqZero :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .eq (.intLit billion) (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_spot_eq_int_false hBillionLitV hZeroLitV
    norm_num [pokeBillion_toNat]
  have hDivCheck :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .div (.var "valScaled") (.intLit billion)) =
          .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
    have hdivWord : UInt256.div valScaled pokeBillion = pokePeekValWord out := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : valScaled.toNat = (pokePeekValWord out).toNat * pokeBillion.toNat := by
        rw [hvalScaled, umul_toNat (pokePeekValWord out) pokeBillion hfitVal]
      have hBillionPos : 0 < pokeBillion.toNat := by
        rw [pokeBillion_toNat]
        norm_num
      rw [hprod]
      simpa [Nat.mul_comm] using
        Nat.mul_div_right (pokePeekValWord out).toNat hBillionPos
    have h := evalExpr_spot_div_uint256_ok (evm := evm) (locals := localsV)
      (x := .var "valScaled") (y := .intLit billion)
      (a := valScaled) (b := pokeBillion) (q := UInt256.div valScaled pokeBillion)
      hValScaledVar hBillionLitV (by native_decide) rfl
    simpa [hdivWord] using h
  have hRightCheck :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .eq
          (.binary .div (.var "valScaled") (.intLit billion))
          (.cast (.var "val") uint256St)) = .ok (.bool true) := by
    have hvalCastV :
        evalExpr? config { contract := contract, locals := localsV } evm
          (.cast (.var "val") uint256St) =
            .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
      simpa [localsV] using
        evalExpr_pokeValCastUInt256_ofLocals (evm := evm) (locals := localsV)
          (out := out) (pokeValScaledLocals_get_val I out valScaled) hlo32
    exact evalExpr_spot_eq_int_true hDivCheck hvalCastV rfl
  have hReq :
      evalExpr? config { contract := contract, locals := localsV } evm
        (.binary .or
          (.binary .eq (.intLit billion) (.intLit 0))
          (.binary .eq (.binary .div (.var "valScaled") (.intLit billion))
            (.cast (.var "val") uint256St))) = .ok (.bool true) :=
    evalExpr_spot_or_false_right hBillionEqZero hRightCheck
  have hPar :
      evalExpr? config { contract := contract, locals := localsV } evm (.storage parRef) =
        .ok (.int (Int.ofNat par.toNat)) := by
    simpa [localsV, par] using
      evalExpr_pokeStorageParOfLocals (evm := evm) (locals := localsV)
        (pokeValScaledLocals_get_par I out valScaled)
  have hRdiv1Args :
      evalExprs? config { contract := contract, locals := localsV } evm
        [.var "valScaled", .storage parRef] =
          .ok [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)] := by
    simp [evalExprs?, hValScaledVar, hPar, EvalResult.bind, bind, pure]
  have hlookupRdiv : lookupCallable? contract "rdiv" = some rdivFunction.toCallable := by
    rfl
  have hbindRdiv1 :
      bindParams? rdivFunction.params
          [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)] =
        some (spotUintBinaryLocals valScaled par) := by
    simp [rdivFunction, uint256, bindParams?, spotUintBinaryLocals]
  have hRdiv1Stmt :
      ExecStmt config { contract := contract, locals := localsV } evm
        (.internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1")
        (.ok { contract := contract, locals := locals1 } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := localsV })
      (evm := evm) (name := "rdiv") (retVar := "spot1")
      (args := [.var "valScaled", .storage parRef])
      (argVals := [.int (Int.ofNat valScaled.toNat), .int (Int.ofNat par.toNat)])
      (callee := rdivFunction) (locals := spotUintBinaryLocals valScaled par)
      hRdiv1Args hlookupRdiv hbindRdiv1
      (execSpotRdivFunctionReturn evm (x := valScaled) (y := par)
        (prod := valScaled * pokeRay) (q := spot1) rfl hfitPar hparNe
        (by simpa [par] using hspot1))
    simpa [resumeAfterInternalCall, localsV, locals1, pokeSpot1Locals, par] using h
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal hValScaledStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
  refine ExecBlock.consNormal hRdiv1Stmt ?_
  exact ExecBlock.consRevert (by simpa [locals1] using hRdiv2Stmt)

theorem execPokeTrueRdivMatMulOverflowReverts
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size) (hlo32 : 32 ≤ out.size)
    (henv : evm.executionEnv = I) {valScaled spot1 : UInt256}
    (hvalScaled : valScaled = pokePeekValWord out * pokeBillion)
    (hfitVal : (pokePeekValWord out).toNat * pokeBillion.toNat < UInt256.size)
    (hfitPar : valScaled.toNat * pokeRay.toNat < UInt256.size)
    (hparNe : pokeParWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hspot1 :
      spot1 = UInt256.div (valScaled * pokeRay)
        (pokeParWord evm.accountMap evm.executionEnv))
    (hoverMat : UInt256.size ≤ spot1.toNat * pokeRay.toNat) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
        [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
          .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
            "spot2",
          .assign .localVar { base := "spot" } (.var "spot2") ])
      .reverted := by
  let locals1 := pokeSpot1Locals I out valScaled spot1
  let mat := pokeMatWord evm.accountMap I
  have hSpot1Var :
      evalExpr? config { contract := contract, locals := locals1 } evm (.var "spot1") =
        .ok (.int (Int.ofNat spot1.toNat)) := by
    simpa [locals1] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals1) (name := "spot1") (value := spot1)
      (pokeSpot1Locals_get_spot1 I out valScaled spot1)
  have hMat :
      evalExpr? config { contract := contract, locals := locals1 } evm
        (.storage (ilksF (.var "ilk") "mat")) =
          .ok (.int (Int.ofNat mat.toNat)) := by
    simpa [locals1, mat] using
      evalExpr_pokeStorageMatOfLocals (evm := evm) (I := I) (locals := locals1)
        hsz36 henv
        (pokeSpot1Locals_get_ilk I out valScaled spot1)
        (pokeSpot1Locals_get_ilks I out valScaled spot1)
  have hRdiv2Args :
      evalExprs? config { contract := contract, locals := locals1 } evm
        [.var "spot1", .storage (ilksF (.var "ilk") "mat")] =
          .ok [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)] := by
    simp [evalExprs?, hSpot1Var, hMat, EvalResult.bind, bind, pure]
  have hlookupRdiv : lookupCallable? contract "rdiv" = some rdivFunction.toCallable := by
    rfl
  have hbindRdiv2 :
      bindParams? rdivFunction.params
          [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)] =
        some (spotUintBinaryLocals spot1 mat) := by
    simp [rdivFunction, uint256, bindParams?, spotUintBinaryLocals]
  have hRdiv2Stmt :
      ExecStmt config { contract := contract, locals := locals1 } evm
        (.internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
          "spot2")
        .reverted :=
    internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals1 })
      (evm := evm) (name := "rdiv") (retVar := "spot2")
      (args := [.var "spot1", .storage (ilksF (.var "ilk") "mat")])
      (argVals := [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)])
      (callee := rdivFunction) (locals := spotUintBinaryLocals spot1 mat)
      hRdiv2Args hlookupRdiv hbindRdiv2
      (execSpotRdivFunctionRevertMul evm (x := spot1) (y := mat) hoverMat)
  exact execPokeTrueAfterRdivParThenRdivMatReverts evm I out hlo32
    hvalScaled hfitVal hfitPar hparNe hspot1 hRdiv2Stmt

theorem execPokeTrueRdivMatDivZeroReverts
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size) (hlo32 : 32 ≤ out.size)
    (henv : evm.executionEnv = I) {valScaled spot1 : UInt256}
    (hvalScaled : valScaled = pokePeekValWord out * pokeBillion)
    (hfitVal : (pokePeekValWord out).toNat * pokeBillion.toNat < UInt256.size)
    (hfitPar : valScaled.toNat * pokeRay.toNat < UInt256.size)
    (hparNe : pokeParWord evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hspot1 :
      spot1 = UInt256.div (valScaled * pokeRay)
        (pokeParWord evm.accountMap evm.executionEnv))
    (hfitMat : spot1.toNat * pokeRay.toNat < UInt256.size)
    (hmatZero : pokeMatWord evm.accountMap I = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
        [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
          .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
            "spot2",
          .assign .localVar { base := "spot" } (.var "spot2") ])
      .reverted := by
  let locals1 := pokeSpot1Locals I out valScaled spot1
  let mat := pokeMatWord evm.accountMap I
  have hSpot1Var :
      evalExpr? config { contract := contract, locals := locals1 } evm (.var "spot1") =
        .ok (.int (Int.ofNat spot1.toNat)) := by
    simpa [locals1] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals1) (name := "spot1") (value := spot1)
      (pokeSpot1Locals_get_spot1 I out valScaled spot1)
  have hMat :
      evalExpr? config { contract := contract, locals := locals1 } evm
        (.storage (ilksF (.var "ilk") "mat")) =
          .ok (.int (Int.ofNat mat.toNat)) := by
    simpa [locals1, mat] using
      evalExpr_pokeStorageMatOfLocals (evm := evm) (I := I) (locals := locals1)
        hsz36 henv
        (pokeSpot1Locals_get_ilk I out valScaled spot1)
        (pokeSpot1Locals_get_ilks I out valScaled spot1)
  have hRdiv2Args :
      evalExprs? config { contract := contract, locals := locals1 } evm
        [.var "spot1", .storage (ilksF (.var "ilk") "mat")] =
          .ok [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)] := by
    simp [evalExprs?, hSpot1Var, hMat, EvalResult.bind, bind, pure]
  have hlookupRdiv : lookupCallable? contract "rdiv" = some rdivFunction.toCallable := by
    rfl
  have hbindRdiv2 :
      bindParams? rdivFunction.params
          [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)] =
        some (spotUintBinaryLocals spot1 mat) := by
    simp [rdivFunction, uint256, bindParams?, spotUintBinaryLocals]
  have hRdiv2Stmt :
      ExecStmt config { contract := contract, locals := locals1 } evm
        (.internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
          "spot2")
        .reverted :=
    internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals1 })
      (evm := evm) (name := "rdiv") (retVar := "spot2")
      (args := [.var "spot1", .storage (ilksF (.var "ilk") "mat")])
      (argVals := [.int (Int.ofNat spot1.toNat), .int (Int.ofNat mat.toNat)])
      (callee := rdivFunction) (locals := spotUintBinaryLocals spot1 mat)
      hRdiv2Args hlookupRdiv hbindRdiv2
      (execSpotRdivFunctionRevertDivZero evm (x := spot1) (y := mat)
        (prod := spot1 * pokeRay) rfl hfitMat (by simpa [mat] using hmatZero))
  exact execPokeTrueAfterRdivParThenRdivMatReverts evm I out hlo32
    hvalScaled hfitVal hfitPar hparNe hspot1 hRdiv2Stmt
end Benchmarks.Dss.Spot
