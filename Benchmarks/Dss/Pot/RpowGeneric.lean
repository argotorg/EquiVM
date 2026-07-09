import Benchmarks.Dss.Pot.Rpow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Pot

set_option maxHeartbeats 1000000

theorem uInt256_land_one_eq_zero_of_even {n : UInt256} (heven : n.toNat % 2 = 0) :
    UInt256.land n ⟨1⟩ = ⟨0⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, heven]
  native_decide

theorem uInt256_land_one_eq_one_of_odd {n : UInt256} (hodd : n.toNat % 2 ≠ 0) :
    UInt256.land n ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, potUInt256One_toNat]
  have hlt : n.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

theorem RD.potDripRpowToLoop
    {cA gh bl σ σ₀ A I} {g b n x : UInt256} {aw : UInt256}
    {mem out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hx : x ≠ ⟨0⟩)
    (rd2352 : RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2352⟩
      (b :: n :: x :: ⟨1926⟩ :: R)
      mem aw out acc k C) :
    let half := UInt256.div b ⟨2⟩
    let z := if n.toNat % 2 = 0 then b else x
    let n' := UInt256.div n ⟨2⟩
    ∃ scratch k' C', RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2395⟩
      (half :: scratch :: z :: b :: n' :: x :: ⟨1926⟩ :: R)
      mem aw out acc k' C' := by
  intro half z n'
  have rd2361 := evm_run rd2352 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2512⟩ (by native_decide) (by evm_ov)]
  have hxNonzero : UInt256.isZero x = ⟨0⟩ := isZero_eq_zero_of_ne hx
  have rd2362 := rd2361.jumpiNT (by native_decide) hxNonzero (by evm_ov)
  have rd2371 := evm_run rd2362 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2379⟩ (by native_decide) (by evm_ov)]
  by_cases heven : n.toNat % 2 = 0
  · have hland : UInt256.land n ⟨1⟩ = ⟨0⟩ :=
      uInt256_land_one_eq_zero_of_even heven
    have hoddZero : UInt256.isZero (UInt256.land n ⟨1⟩) ≠ ⟨0⟩ := by
      rw [hland]
      decide
    have rd2379 := rd2371.jumpiT (by native_decide) hoddZero (by jump_dest) (by evm_ov)
    have rd2395 := evm_run rd2379 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
      raw dup6 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap5 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    exact ⟨x, _, _, by simpa [half, z, n', heven] using rd2395⟩
  · have hland : UInt256.land n ⟨1⟩ = ⟨1⟩ :=
      uInt256_land_one_eq_one_of_odd heven
    have hoddNonzero : UInt256.isZero (UInt256.land n ⟨1⟩) = ⟨0⟩ := by
      rw [hland]
      decide
    have rd2372 := rd2371.jumpiNT (by native_decide) hoddNonzero (by evm_ov)
    have rd2383pre := evm_run rd2372 with [
      raw dup6 (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push2 ⟨2383⟩ (by native_decide) (by evm_ov)]
    have rd2383 := rd2383pre.jump (by native_decide) (by jump_dest) (by evm_ov)
    have rd2395 := evm_run rd2383 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
      raw dup4 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
      raw dup6 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap5 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    exact ⟨x, _, _, by simpa [half, z, n', heven] using rd2395⟩

theorem execRpowFunctionReturnXNonzeroWithLoop
    (evm : EVM.State) {x n b xFinal zFinal : UInt256} {localsFinal : Store}
    (hxz : x ≠ ⟨0⟩)
    (hfinalStore :
      RpowLoopStore xFinal ⟨0⟩ b zFinal (UInt256.div b ⟨2⟩) localsFinal)
    (hwhile :
      ExecStmt config
        { contract := contract,
          locals :=
            rpowLocalsZHN x n b (if n.toNat % 2 = 0 then b else x)
              (UInt256.div b ⟨2⟩) (UInt256.div n ⟨2⟩) }
        evm (.while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody)
        (.ok { contract := contract, locals := localsFinal } evm)) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
      rpowFunction.body
      (.returned { contract := contract, locals := localsFinal } evm
        (some [.int (Int.ofNat zFinal.toNat)])) := by
  let locals := uintTernaryLocals x n b
  let z := if n.toNat % 2 = 0 then b else x
  let half := UInt256.div b ⟨2⟩
  let n' := UInt256.div n ⟨2⟩
  let localsZ := rpowLocalsZ x n b z
  let localsZH := rpowLocalsZH x n b z half
  let localsLoop := rpowLocalsZHN x n b z half n'
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintTernaryLocals_get_x x n b)
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := n) (uintTernaryLocals_get_n x n b)
  have hb :
      evalExpr? config { contract := contract, locals := locals } evm (.var "base") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "base") (value := b) (uintTernaryLocals_get_b x n b)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have htwoLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, potUInt256Two_toNat]
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hx hzeroLit
    intro hbad
    exact hxz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hMod :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hn htwoLit
      (by simp [potUInt256Two_toNat])
      (by
        rw [potUInt256Two_toNat]
        norm_num)
  have hZExpr :
      evalExpr? config { contract := contract, locals := locals } evm
        (.ite (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
          (.var "base") (.var "x")) = .ok (.int (Int.ofNat z.toNat)) := by
    by_cases heven : n.toNat % 2 = 0
    · have hModEq :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
            .ok (.bool true) := by
        simpa [heven] using evalExpr_eq_int_true hMod hzeroLit (by simp [heven])
      simpa [z, heven] using evalExpr_ite_true hModEq hb
    · have hModEq :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
            .ok (.bool false) := by
        apply evalExpr_eq_int_false hMod hzeroLit
        intro hbad
        exact heven (Int.ofNat.inj hbad)
      simpa [z, heven] using evalExpr_ite_false hModEq hx
  have hbZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "base") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [localsZ, z] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "base") (value := b) (rpowLocalsZ_get_b x n b z)
  have htwoLitZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, potUInt256Two_toNat]
  have hHalfExpr :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "base") (.intLit 2)) = .ok (.int (Int.ofNat half.toNat)) :=
    evalExpr_div_uint256_ok hbZ htwoLitZ (by native_decide) rfl
  have hnZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [localsZH, half, z] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZH) (name := "n") (value := n) (rpowLocalsZH_get_n x n b z half)
  have htwoLitZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, potUInt256Two_toNat]
  have hDivN :
      evalExpr? config { contract := contract, locals := localsZH } evm
        (.binary .div (.var "n") (.intLit 2)) = .ok (.int (Int.ofNat n'.toNat)) := by
    simpa [n'] using evalExpr_div_uint256_ok hnZH htwoLitZH potUInt256Two_ne_zero rfl
  have hAssignN :
      assignStorageRef? config { contract := contract, locals := localsZH } evm .localVar
          { base := "n" } (.int (Int.ofNat n'.toNat)) =
        .ok ({ contract := contract, locals := localsLoop }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsLoop,
      rpowLocalsZHN, localsZH, rpowLocalsZH]
  have hzDone :
      evalExpr? config { contract := contract, locals := localsFinal } evm (.var "z") =
        .ok (.int (Int.ofNat zFinal.toNat)) := hfinalStore.eval_z
  have hElseBlock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256)
            (.ite
              (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
              (.var "base")
              (.var "x")),
          .letDecl "half" (some uint256) (.binary .div (.var "base") (.intLit 2)),
          .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
          .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsFinal } evm
          (some [.int (Int.ofNat zFinal.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hZExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hHalfExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivN hAssignN) ?_
    refine ExecBlock.consNormal (by simpa [localsLoop, z, half, n'] using hwhile) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzDone))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := localsFinal } evm
          (some [.int (Int.ofNat zFinal.toNat)])) := by
    simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteFalse hxZero hElseBlock)
  simpa [locals] using ExecFuncBody.execBlockRet hblock

theorem execRpowFunctionRevertXNonzeroWithLoop
    (evm : EVM.State) {x n b : UInt256}
    (hxz : x ≠ ⟨0⟩)
    (hwhile :
      ExecStmt config
        { contract := contract,
          locals :=
            rpowLocalsZHN x n b (if n.toNat % 2 = 0 then b else x)
              (UInt256.div b ⟨2⟩) (UInt256.div n ⟨2⟩) }
        evm (.while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody) .reverted) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
      rpowFunction.body .reverted := by
  let locals := uintTernaryLocals x n b
  let z := if n.toNat % 2 = 0 then b else x
  let half := UInt256.div b ⟨2⟩
  let n' := UInt256.div n ⟨2⟩
  let localsZ := rpowLocalsZ x n b z
  let localsZH := rpowLocalsZH x n b z half
  let localsLoop := rpowLocalsZHN x n b z half n'
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (uintTernaryLocals_get_x x n b)
  have hn :
      evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := n) (uintTernaryLocals_get_n x n b)
  have hb :
      evalExpr? config { contract := contract, locals := locals } evm (.var "base") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "base") (value := b) (uintTernaryLocals_get_b x n b)
  have hzeroLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have htwoLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, potUInt256Two_toNat]
  have hxZero :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_eq_int_false hx hzeroLit
    intro hbad
    exact hxz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
  have hMod :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hn htwoLit
      (by simp [potUInt256Two_toNat])
      (by
        rw [potUInt256Two_toNat]
        norm_num)
  have hZExpr :
      evalExpr? config { contract := contract, locals := locals } evm
        (.ite (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
          (.var "base") (.var "x")) = .ok (.int (Int.ofNat z.toNat)) := by
    by_cases heven : n.toNat % 2 = 0
    · have hModEq :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
            .ok (.bool true) := by
        simpa [heven] using evalExpr_eq_int_true hMod hzeroLit (by simp [heven])
      simpa [z, heven] using evalExpr_ite_true hModEq hb
    · have hModEq :
          evalExpr? config { contract := contract, locals := locals } evm
            (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
            .ok (.bool false) := by
        apply evalExpr_eq_int_false hMod hzeroLit
        intro hbad
        exact heven (Int.ofNat.inj hbad)
      simpa [z, heven] using evalExpr_ite_false hModEq hx
  have hbZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "base") =
        .ok (.int (Int.ofNat b.toNat)) := by
    simpa [localsZ, z] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "base") (value := b) (rpowLocalsZ_get_b x n b z)
  have htwoLitZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, potUInt256Two_toNat]
  have hHalfExpr :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "base") (.intLit 2)) = .ok (.int (Int.ofNat half.toNat)) :=
    evalExpr_div_uint256_ok hbZ htwoLitZ (by native_decide) rfl
  have hnZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.var "n") =
        .ok (.int (Int.ofNat n.toNat)) := by
    simpa [localsZH, half, z] using evalExpr_varUInt256 (evm := evm)
      (locals := localsZH) (name := "n") (value := n) (rpowLocalsZH_get_n x n b z half)
  have htwoLitZH :
      evalExpr? config { contract := contract, locals := localsZH } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, potUInt256Two_toNat]
  have hDivN :
      evalExpr? config { contract := contract, locals := localsZH } evm
        (.binary .div (.var "n") (.intLit 2)) = .ok (.int (Int.ofNat n'.toNat)) := by
    simpa [n'] using evalExpr_div_uint256_ok hnZH htwoLitZH potUInt256Two_ne_zero rfl
  have hAssignN :
      assignStorageRef? config { contract := contract, locals := localsZH } evm .localVar
          { base := "n" } (.int (Int.ofNat n'.toNat)) =
        .ok ({ contract := contract, locals := localsLoop }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsLoop,
      rpowLocalsZHN, localsZH, rpowLocalsZH]
  have hElseBlock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256)
            (.ite
              (.binary .eq (.binary .mod (.var "n") (.intLit 2)) (.intLit 0))
              (.var "base")
              (.var "x")),
          .letDecl "half" (some uint256) (.binary .div (.var "base") (.intLit 2)),
          .assign .localVar { base := "n" } (.binary .div (.var "n") (.intLit 2)),
          .while (.binary .ne (.var "n") (.intLit 0)) rpowLoopBody,
          .return [.var "z"] ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hZExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hHalfExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDivN hAssignN) ?_
    exact ExecBlock.consRevert (by simpa [localsLoop, z, half, n'] using hwhile)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        .reverted := by
    simpa [rpowFunction] using ExecBlock.consRevert (ExecStmt.iteFalse hxZero hElseBlock)
  simpa [locals] using ExecFuncBody.execBlockRevert hblock

theorem rpowFunctionCoupled
    {cA gh bl σ σ₀ A I} {g x n b : UInt256} {aw : UInt256}
    {evm : EVM.State} {mem out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hx : x ≠ ⟨0⟩)
    (hb : b ≠ ⟨0⟩)
    (rd2352 : RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2352⟩
      (b :: n :: x :: ⟨1926⟩ :: R)
      mem aw out acc k C) :
    (∃ xFinal zFinal localsFinal k' C',
      RpowLoopStore xFinal ⟨0⟩ b zFinal (UInt256.div b ⟨2⟩) localsFinal ∧
      ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
        rpowFunction.body
        (.returned { contract := contract, locals := localsFinal } evm
          (some [.int (Int.ofNat zFinal.toNat)])) ∧
      RD potBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1926⟩
        (zFinal :: R) mem aw out acc k' C') ∨
    (ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
        rpowFunction.body .reverted ∧
      RDrev potBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) := by
  let half := UInt256.div b ⟨2⟩
  let z := if n.toNat % 2 = 0 then b else x
  let n' := UInt256.div n ⟨2⟩
  let localsLoop := rpowLocalsZHN x n b z half n'
  obtain ⟨scratch, kLoop, CLoop, rd2395⟩ :=
    RD.potDripRpowToLoop
      (R := R) (b := b) (n := n) (x := x) hRlen hx rd2352
  have hstoreLoop : RpowLoopStore x n' b z half localsLoop := by
    simpa [localsLoop] using RpowLoopStore.rpowLocalsZHN x n b z half n'
  have hloop :=
    rpowLoopCoupled
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (evm := evm) (R := R) (hRlen := hRlen)
      (hstore := hstoreLoop) (hb := hb) (hle := Nat.le_refl n'.toNat)
      (rd2395 := by simpa [half, z, n'] using rd2395)
  cases hloop with
  | inl hret =>
      rcases hret with
        ⟨xFinal, zFinal, localsFinal, k', C', hfinalStore, hwhile, rd1926⟩
      have hbody :
          ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
            rpowFunction.body
            (.returned { contract := contract, locals := localsFinal } evm
              (some [.int (Int.ofNat zFinal.toNat)])) :=
        execRpowFunctionReturnXNonzeroWithLoop (evm := evm)
          (x := x) (n := n) (b := b) hx
          (by simpa [half] using hfinalStore)
          (by simpa [localsLoop, z, half, n'] using hwhile)
      exact .inl ⟨xFinal, zFinal, localsFinal, k', C',
        by simpa [half] using hfinalStore, hbody, rd1926⟩
  | inr hrev =>
      rcases hrev with ⟨hwhile, hrdRev⟩
      have hbody :
          ExecFuncBody config { contract := contract, locals := uintTernaryLocals x n b } evm
            rpowFunction.body .reverted :=
        execRpowFunctionRevertXNonzeroWithLoop (evm := evm)
          (x := x) (n := n) (b := b) hx
          (by simpa [localsLoop, z, half, n'] using hwhile)
      exact .inr ⟨hbody, hrdRev⟩

end Benchmarks.Dss.Pot
