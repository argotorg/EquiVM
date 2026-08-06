import Benchmarks.Dss.Jug.ArithmeticLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Jug

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
    refine ExecBlock.consNormal (ExecStmt.letDecl_uint256_word hAdd) ?_
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

abbrev diffValue (x y : UInt256) : Int :=
  normalizeInt int256Int (EVM.signed x - EVM.signed y)

theorem evalExpr_diffValue {evm : EVM.State} {locals : Store} {x y : UInt256}
    (hx : evalExpr? config { contract := contract, locals } evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config { contract := contract, locals } evm (.var "y") =
      .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? config { contract := contract, locals } evm
      (s256 (.binary (.sub (.sint ⟨256, by decide⟩) .wrapping)
        (.cast (.var "x") int256St) (.cast (.var "y") int256St))) =
      .ok (.int (diffValue x y)) := by
  have hsub := evalExpr_wrapping_sub_sint256_words_ok hx hy
  have hbounds := normalizeInt_sint256_bounds (EVM.signed x - EVM.signed y)
  exact evalExpr_s256_ok (by simpa [diffValue, int256Int, int256St] using hsub)
    (by simpa [diffValue, int256Int] using hbounds.1)
    (by simpa [diffValue, int256Int] using hbounds.2)

theorem signed_eq_of_le_maxInt256 (word : UInt256)
    (hmax : (word.toNat : Int) ≤ maxInt256) :
    EVM.signed word = Int.ofNat word.toNat := by
  unfold maxInt256 at hmax
  have hlt : word.toNat < EVM.twoPow 255 := by
    apply Int.ofNat_lt.mp
    have : (word.toNat : Int) < (2 : Int) ^ 255 := by
      omega
    simpa [EVM.twoPow] using this
  unfold EVM.signed
  rw [if_pos]
  · rfl
  · simpa [EVM.signBit, Ethereum.UInt256.toNat] using hlt

theorem execDiffFunctionReturn (evm : EVM.State) {x y : UInt256}
    (hxMax : (x.toNat : Int) ≤ maxInt256) (hyMax : (y.toNat : Int) ≤ maxInt256) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      diffFunction.body
      (.returned
        { contract := contract,
          locals := uintBinaryLocalsIntZ x y ((x.toNat : Int) - (y.toNat : Int)) } evm
        (some [.int ((x.toNat : Int) - (y.toNat : Int))])) := by
  let locals := uintBinaryLocals x y
  let z : Int := (x.toNat : Int) - (y.toNat : Int)
  let localsZ := uintBinaryLocalsIntZ x y z
  have hx := evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "x")
    (value := x) (by simpa [locals] using uintBinaryLocals_get_x x y)
  have hy := evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "y")
    (value := y) (by simpa [locals] using uintBinaryLocals_get_y x y)
  have hxSigned := signed_eq_of_le_maxInt256 x hxMax
  have hySigned := signed_eq_of_le_maxInt256 y hyMax
  unfold maxInt256 at hxMax hyMax
  have hpow : Int.ofNat (EVM.twoPow 255) = (2 : Int) ^ 255 := by
    norm_num [EVM.twoPow]
  have hlo : -Int.ofNat (EVM.twoPow 255) ≤ z := by
    have hxNonneg : 0 ≤ (x.toNat : Int) := Int.natCast_nonneg _
    rw [hpow]
    dsimp [z]
    omega
  have hhi : z < Int.ofNat (EVM.twoPow 255) := by
    have hyNonneg : 0 ≤ (y.toNat : Int) := Int.natCast_nonneg _
    rw [hpow]
    dsimp [z]
    omega
  have hdiff : diffValue x y = z := by
    unfold diffValue int256Int
    rw [hxSigned, hySigned]
    exact normalizeInt_sint256_eq_self _ (by simpa [z] using hlo) (by simpa [z] using hhi)
  have hlet := evalExpr_diffValue hx hy
  rw [hdiff] at hlet
  have hxZ := evalExpr_varInt (evm := evm) (locals := localsZ) (name := "x")
    (value := Int.ofNat x.toNat) (by simpa [localsZ] using uintBinaryLocalsIntZ_get_x x y z)
  have hyZ := evalExpr_varInt (evm := evm) (locals := localsZ) (name := "y")
    (value := Int.ofNat y.toNat) (by simpa [localsZ] using uintBinaryLocalsIntZ_get_y x y z)
  have hzZ := evalExpr_varInt (evm := evm) (locals := localsZ) (name := "z") (value := z)
    (by simpa [localsZ] using uintBinaryLocalsIntZ_get_z x y z)
  have hmax : evalExpr? config { contract := contract, locals := localsZ } evm
      (.intLit maxInt256) = .ok (.int maxInt256) := by simp [evalExpr?, pure]
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some int256)
            (s256 (.binary (.sub (.sint ⟨256, by decide⟩) .wrapping)
              (.cast (.var "x") int256St) (.cast (.var "y") int256St))),
          .require (.binary .le (.var "x") (.intLit maxInt256)),
          .require (.binary .le (.var "y") (.intLit maxInt256)),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm (some [.int z])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl_sint256 hlet hlo hhi) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_le_int_true hxZ hmax hxMax)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_le_int_true hyZ hmax hyMax)) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzZ))
  simpa [diffFunction, locals, localsZ, z] using ExecFuncBody.execBlockRet hblock

theorem execDiffFunctionRevertXBound (evm : EVM.State) {x y : UInt256}
    (hxGt : maxInt256 < (x.toNat : Int)) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      diffFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  let z := diffValue x y
  let localsZ := uintBinaryLocalsIntZ x y z
  have hx := evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "x")
    (value := x) (by simpa [locals] using uintBinaryLocals_get_x x y)
  have hy := evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "y")
    (value := y) (by simpa [locals] using uintBinaryLocals_get_y x y)
  have hlet := evalExpr_diffValue hx hy
  have hbounds := normalizeInt_sint256_bounds (EVM.signed x - EVM.signed y)
  have hxZ := evalExpr_varInt (evm := evm) (locals := localsZ) (name := "x")
    (value := Int.ofNat x.toNat) (by simpa [localsZ] using uintBinaryLocalsIntZ_get_x x y z)
  have hmax : evalExpr? config { contract := contract, locals := localsZ } evm
      (.intLit maxInt256) = .ok (.int maxInt256) := by simp [evalExpr?, pure]
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some int256)
            (s256 (.binary (.sub (.sint ⟨256, by decide⟩) .wrapping)
              (.cast (.var "x") int256St) (.cast (.var "y") int256St))),
          .require (.binary .le (.var "x") (.intLit maxInt256)),
          .require (.binary .le (.var "y") (.intLit maxInt256)),
          .return [.var "z"] ] .reverted := by
    refine ExecBlock.consNormal
      (ExecStmt.letDecl_sint256 hlet
        (by simpa [z, diffValue, int256Int] using hbounds.1)
        (by simpa [z, diffValue, int256Int] using hbounds.2)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_le_int_false hxZ hmax hxGt))
  simpa [diffFunction, locals, localsZ, z] using ExecFuncBody.execBlockRevert hblock

theorem execDiffFunctionRevertYBound (evm : EVM.State) {x y : UInt256}
    (hxMax : (x.toNat : Int) ≤ maxInt256) (hyGt : maxInt256 < (y.toNat : Int)) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      diffFunction.body .reverted := by
  let locals := uintBinaryLocals x y
  let z := diffValue x y
  let localsZ := uintBinaryLocalsIntZ x y z
  have hx := evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "x")
    (value := x) (by simpa [locals] using uintBinaryLocals_get_x x y)
  have hy := evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "y")
    (value := y) (by simpa [locals] using uintBinaryLocals_get_y x y)
  have hlet := evalExpr_diffValue hx hy
  have hbounds := normalizeInt_sint256_bounds (EVM.signed x - EVM.signed y)
  have hxZ := evalExpr_varInt (evm := evm) (locals := localsZ) (name := "x")
    (value := Int.ofNat x.toNat) (by simpa [localsZ] using uintBinaryLocalsIntZ_get_x x y z)
  have hyZ := evalExpr_varInt (evm := evm) (locals := localsZ) (name := "y")
    (value := Int.ofNat y.toNat) (by simpa [localsZ] using uintBinaryLocalsIntZ_get_y x y z)
  have hmax : evalExpr? config { contract := contract, locals := localsZ } evm
      (.intLit maxInt256) = .ok (.int maxInt256) := by simp [evalExpr?, pure]
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some int256)
            (s256 (.binary (.sub (.sint ⟨256, by decide⟩) .wrapping)
              (.cast (.var "x") int256St) (.cast (.var "y") int256St))),
          .require (.binary .le (.var "x") (.intLit maxInt256)),
          .require (.binary .le (.var "y") (.intLit maxInt256)),
          .return [.var "z"] ] .reverted := by
    refine ExecBlock.consNormal
      (ExecStmt.letDecl_sint256 hlet
        (by simpa [z, diffValue, int256Int] using hbounds.1)
        (by simpa [z, diffValue, int256Int] using hbounds.2)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_le_int_true hxZ hmax hxMax)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_le_int_false hyZ hmax hyGt))
  simpa [diffFunction, locals, localsZ, z] using ExecFuncBody.execBlockRevert hblock

theorem execDiffFunctionRevertOperandBound (evm : EVM.State) {x y : UInt256}
    (hbad : (x.toNat : Int) - (y.toNat : Int) < -((2 : Int) ^ 255) ∨
      (x.toNat : Int) - (y.toNat : Int) ≥ (2 : Int) ^ 255) :
    ExecFuncBody config { contract := contract, locals := uintBinaryLocals x y } evm
      diffFunction.body .reverted := by
  by_cases hxMax : (x.toNat : Int) ≤ maxInt256
  · apply execDiffFunctionRevertYBound evm hxMax
    rcases hbad with hlow | hhigh
    · have hxNonneg : 0 ≤ (x.toNat : Int) := Int.natCast_nonneg _
      unfold maxInt256
      omega
    · have hyNonneg : 0 ≤ (y.toNat : Int) := Int.natCast_nonneg _
      unfold maxInt256 at hxMax ⊢
      omega
  · exact execDiffFunctionRevertXBound evm (lt_of_not_ge hxMax)

end Benchmarks.Dss.Jug
