import Reasoning.SolmArithmetic
import Reasoning.WordArithmetic

/-!
# Exponentiation local-variable frames

The two namespaces retain the source algorithms' distinct names for the base variable:
`RpowB` uses `"b"`, and `RpowBase` uses `"base"`. Evaluation facts are independent of
the enclosing contract and configuration.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace Reasoning.Theory.RpowB

abbrev uintTernaryLocals (x n b : UInt256) : Store :=
  ((((∅ : Store).insert "b" (.int (Int.ofNat b.toNat))).insert "n"
    (.int (Int.ofNat n.toNat))).insert "x" (.int (Int.ofNat x.toNat)))

abbrev rpowLocalsZ (x n b z : UInt256) : Store :=
  (uintTernaryLocals x n b).insert "z" (.int (Int.ofNat z.toNat))

abbrev rpowLocalsZH (x n b z half : UInt256) : Store :=
  (rpowLocalsZ x n b z).insert "half" (.int (Int.ofNat half.toNat))

abbrev rpowLocalsZHN (x n b z half n' : UInt256) : Store :=
  (rpowLocalsZH x n b z half).insert "n" (.int (Int.ofNat n'.toNat))

theorem uintTernaryLocals_get_x (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintTernaryLocals, store_get_self]

theorem uintTernaryLocals_get_n (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [uintTernaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem uintTernaryLocals_get_b (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "b" = some (.int (Int.ofNat b.toNat)) := by
  rw [uintTernaryLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem rpowLocalsZ_get_b (x n b z : UInt256) :
    (rpowLocalsZ x n b z).get? "b" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZ, store_get_ne _ _ (by decide), uintTernaryLocals_get_b]

theorem rpowLocalsZ_get_n (x n b z : UInt256) :
    (rpowLocalsZ x n b z).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [rpowLocalsZ, store_get_ne _ _ (by decide), uintTernaryLocals_get_n]

theorem rpowLocalsZH_get_b (x n b z half : UInt256) :
    (rpowLocalsZH x n b z half).get? "b" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZH, store_get_ne _ _ (by decide), rpowLocalsZ_get_b]

theorem rpowLocalsZH_get_n (x n b z half : UInt256) :
    (rpowLocalsZH x n b z half).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [rpowLocalsZH, store_get_ne _ _ (by decide), rpowLocalsZ_get_n]

theorem rpowLocalsZHN_get_n (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "n" = some (.int (Int.ofNat n'.toNat)) := by
  rw [rpowLocalsZHN, store_get_self]

theorem rpowLocalsZHN_get_z (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH,
    store_get_ne _ _ (by decide), rpowLocalsZ, store_get_self]

theorem rpowLocalsZHN_get_x (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH,
    store_get_ne _ _ (by decide), rpowLocalsZ, store_get_ne _ _ (by decide),
    uintTernaryLocals_get_x]

theorem rpowLocalsZHN_get_b (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "b" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH_get_b]

theorem rpowLocalsZHN_get_half (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "half" =
      some (.int (Int.ofNat half.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH, store_get_self]

structure RpowLoopStore (x n b z half : UInt256) (locals : Store) : Prop where
  get_x : locals.get? "x" = some (.int (Int.ofNat x.toNat))
  get_n : locals.get? "n" = some (.int (Int.ofNat n.toNat))
  get_b : locals.get? "b" = some (.int (Int.ofNat b.toNat))
  get_z : locals.get? "z" = some (.int (Int.ofNat z.toNat))
  get_half : locals.get? "half" = some (.int (Int.ofNat half.toNat))

theorem RpowLoopStore.rpowLocalsZHN (x n b z half n' : UInt256) :
    RpowLoopStore x n' b z half (rpowLocalsZHN x n b z half n') where
  get_x := rpowLocalsZHN_get_x x n b z half n'
  get_n := rpowLocalsZHN_get_n x n b z half n'
  get_b := rpowLocalsZHN_get_b x n b z half n'
  get_z := rpowLocalsZHN_get_z x n b z half n'
  get_half := rpowLocalsZHN_get_half x n b z half n'

theorem RpowLoopStore.insert_ne {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (name : Ident) (value : Value)
    (hx : (name == "x") = false) (hn : (name == "n") = false)
    (hb : (name == "b") = false) (hz : (name == "z") = false)
    (hhalf : (name == "half") = false) :
    RpowLoopStore x n b z half (locals.insert name value) where
  get_x := by rw [store_get_ne locals (k := name) (a := "x") value hx, h.get_x]
  get_n := by rw [store_get_ne locals (k := name) (a := "n") value hn, h.get_n]
  get_b := by rw [store_get_ne locals (k := name) (a := "b") value hb, h.get_b]
  get_z := by rw [store_get_ne locals (k := name) (a := "z") value hz, h.get_z]
  get_half := by rw [store_get_ne locals (k := name) (a := "half") value hhalf, h.get_half]

theorem RpowLoopStore.set_x {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (x' : UInt256) :
    RpowLoopStore x' n b z half (locals.insert "x" (.int (Int.ofNat x'.toNat))) where
  get_x := store_get_self locals "x" (.int (Int.ofNat x'.toNat))
  get_n := by
    rw [store_get_ne locals (k := "x") (a := "n") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_n]
  get_b := by
    rw [store_get_ne locals (k := "x") (a := "b") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_b]
  get_z := by
    rw [store_get_ne locals (k := "x") (a := "z") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_z]
  get_half := by
    rw [store_get_ne locals (k := "x") (a := "half") (.int (Int.ofNat x'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.set_z {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (z' : UInt256) :
    RpowLoopStore x n b z' half (locals.insert "z" (.int (Int.ofNat z'.toNat))) where
  get_x := by
    rw [store_get_ne locals (k := "z") (a := "x") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_x]
  get_n := by
    rw [store_get_ne locals (k := "z") (a := "n") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_n]
  get_b := by
    rw [store_get_ne locals (k := "z") (a := "b") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_b]
  get_z := store_get_self locals "z" (.int (Int.ofNat z'.toNat))
  get_half := by
    rw [store_get_ne locals (k := "z") (a := "half") (.int (Int.ofNat z'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.set_n {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (n' : UInt256) :
    RpowLoopStore x n' b z half (locals.insert "n" (.int (Int.ofNat n'.toNat))) where
  get_x := by
    rw [store_get_ne locals (k := "n") (a := "x") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_x]
  get_n := store_get_self locals "n" (.int (Int.ofNat n'.toNat))
  get_b := by
    rw [store_get_ne locals (k := "n") (a := "b") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_b]
  get_z := by
    rw [store_get_ne locals (k := "n") (a := "z") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_z]
  get_half := by
    rw [store_get_ne locals (k := "n") (a := "half") (.int (Int.ofNat n'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.eval_x {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "x") (value := x) h.get_x

theorem RpowLoopStore.eval_n {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "n") =
      .ok (.int (Int.ofNat n.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "n") (value := n) h.get_n

theorem RpowLoopStore.eval_b {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "b") =
      .ok (.int (Int.ofNat b.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "b") (value := b) h.get_b

theorem RpowLoopStore.eval_z {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "z") =
      .ok (.int (Int.ofNat z.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "z") (value := z) h.get_z

theorem RpowLoopStore.eval_half {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "half") =
      .ok (.int (Int.ofNat half.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "half") (value := half)
    h.get_half

theorem RpowLoopStore.eval_while_false {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x ⟨0⟩ b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_false h.eval_n hzeroLit rfl

theorem RpowLoopStore.eval_while_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) (hnz : n ≠ ⟨0⟩) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool true) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  apply evalExpr_ne_int_true h.eval_n hzeroLit
  intro hbad
  exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))

theorem RpowLoopStore.eval_odd_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (hstore : RpowLoopStore x n b z half locals)
    (hodd : n.toNat % 2 ≠ 0) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
        .ok (.bool true) := by
  have htwoLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, uInt256Two_toNat]
  have hmod :
      evalExpr? cfg { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hstore.eval_n htwoLit
      (by simp [uInt256Two_toNat])
      (by
        rw [uInt256Two_toNat]
        norm_num)
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_true hmod hzeroLit (by
    intro hbad
    apply hodd
    exact Nat.cast_injective hbad)

end Reasoning.Theory.RpowB

namespace Reasoning.Theory.RpowBase

abbrev uintTernaryLocals (x n b : UInt256) : Store :=
  ((((∅ : Store).insert "base" (.int (Int.ofNat b.toNat))).insert "n"
    (.int (Int.ofNat n.toNat))).insert "x" (.int (Int.ofNat x.toNat)))

abbrev rpowLocalsZ (x n b z : UInt256) : Store :=
  (uintTernaryLocals x n b).insert "z" (.int (Int.ofNat z.toNat))

abbrev rpowLocalsZH (x n b z half : UInt256) : Store :=
  (rpowLocalsZ x n b z).insert "half" (.int (Int.ofNat half.toNat))

abbrev rpowLocalsZHN (x n b z half n' : UInt256) : Store :=
  (rpowLocalsZH x n b z half).insert "n" (.int (Int.ofNat n'.toNat))

theorem uintTernaryLocals_get_x (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [uintTernaryLocals, store_get_self]

theorem uintTernaryLocals_get_n (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [uintTernaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem uintTernaryLocals_get_b (x n b : UInt256) :
    (uintTernaryLocals x n b).get? "base" = some (.int (Int.ofNat b.toNat)) := by
  rw [uintTernaryLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem rpowLocalsZ_get_b (x n b z : UInt256) :
    (rpowLocalsZ x n b z).get? "base" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZ, store_get_ne _ _ (by decide), uintTernaryLocals_get_b]

theorem rpowLocalsZ_get_n (x n b z : UInt256) :
    (rpowLocalsZ x n b z).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [rpowLocalsZ, store_get_ne _ _ (by decide), uintTernaryLocals_get_n]

theorem rpowLocalsZH_get_b (x n b z half : UInt256) :
    (rpowLocalsZH x n b z half).get? "base" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZH, store_get_ne _ _ (by decide), rpowLocalsZ_get_b]

theorem rpowLocalsZH_get_n (x n b z half : UInt256) :
    (rpowLocalsZH x n b z half).get? "n" = some (.int (Int.ofNat n.toNat)) := by
  rw [rpowLocalsZH, store_get_ne _ _ (by decide), rpowLocalsZ_get_n]

theorem rpowLocalsZHN_get_n (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "n" = some (.int (Int.ofNat n'.toNat)) := by
  rw [rpowLocalsZHN, store_get_self]

theorem rpowLocalsZHN_get_z (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH,
    store_get_ne _ _ (by decide), rpowLocalsZ, store_get_self]

theorem rpowLocalsZHN_get_x (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH,
    store_get_ne _ _ (by decide), rpowLocalsZ, store_get_ne _ _ (by decide),
    uintTernaryLocals_get_x]

theorem rpowLocalsZHN_get_b (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "base" = some (.int (Int.ofNat b.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH_get_b]

theorem rpowLocalsZHN_get_half (x n b z half n' : UInt256) :
    (rpowLocalsZHN x n b z half n').get? "half" =
      some (.int (Int.ofNat half.toNat)) := by
  rw [rpowLocalsZHN, store_get_ne _ _ (by decide), rpowLocalsZH, store_get_self]

structure RpowLoopStore (x n b z half : UInt256) (locals : Store) : Prop where
  get_x : locals.get? "x" = some (.int (Int.ofNat x.toNat))
  get_n : locals.get? "n" = some (.int (Int.ofNat n.toNat))
  get_b : locals.get? "base" = some (.int (Int.ofNat b.toNat))
  get_z : locals.get? "z" = some (.int (Int.ofNat z.toNat))
  get_half : locals.get? "half" = some (.int (Int.ofNat half.toNat))

theorem RpowLoopStore.rpowLocalsZHN (x n b z half n' : UInt256) :
    RpowLoopStore x n' b z half (rpowLocalsZHN x n b z half n') where
  get_x := rpowLocalsZHN_get_x x n b z half n'
  get_n := rpowLocalsZHN_get_n x n b z half n'
  get_b := rpowLocalsZHN_get_b x n b z half n'
  get_z := rpowLocalsZHN_get_z x n b z half n'
  get_half := rpowLocalsZHN_get_half x n b z half n'

theorem RpowLoopStore.insert_ne {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (name : Ident) (value : Value)
    (hx : (name == "x") = false) (hn : (name == "n") = false)
    (hb : (name == "base") = false) (hz : (name == "z") = false)
    (hhalf : (name == "half") = false) :
    RpowLoopStore x n b z half (locals.insert name value) where
  get_x := by rw [store_get_ne locals (k := name) (a := "x") value hx, h.get_x]
  get_n := by rw [store_get_ne locals (k := name) (a := "n") value hn, h.get_n]
  get_b := by rw [store_get_ne locals (k := name) (a := "base") value hb, h.get_b]
  get_z := by rw [store_get_ne locals (k := name) (a := "z") value hz, h.get_z]
  get_half := by rw [store_get_ne locals (k := name) (a := "half") value hhalf, h.get_half]

theorem RpowLoopStore.set_x {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (x' : UInt256) :
    RpowLoopStore x' n b z half (locals.insert "x" (.int (Int.ofNat x'.toNat))) where
  get_x := store_get_self locals "x" (.int (Int.ofNat x'.toNat))
  get_n := by
    rw [store_get_ne locals (k := "x") (a := "n") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_n]
  get_b := by
    rw [store_get_ne locals (k := "x") (a := "base") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_b]
  get_z := by
    rw [store_get_ne locals (k := "x") (a := "z") (.int (Int.ofNat x'.toNat)) (by decide),
      h.get_z]
  get_half := by
    rw [store_get_ne locals (k := "x") (a := "half") (.int (Int.ofNat x'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.set_z {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (z' : UInt256) :
    RpowLoopStore x n b z' half (locals.insert "z" (.int (Int.ofNat z'.toNat))) where
  get_x := by
    rw [store_get_ne locals (k := "z") (a := "x") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_x]
  get_n := by
    rw [store_get_ne locals (k := "z") (a := "n") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_n]
  get_b := by
    rw [store_get_ne locals (k := "z") (a := "base") (.int (Int.ofNat z'.toNat)) (by decide),
      h.get_b]
  get_z := store_get_self locals "z" (.int (Int.ofNat z'.toNat))
  get_half := by
    rw [store_get_ne locals (k := "z") (a := "half") (.int (Int.ofNat z'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.set_n {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) (n' : UInt256) :
    RpowLoopStore x n' b z half (locals.insert "n" (.int (Int.ofNat n'.toNat))) where
  get_x := by
    rw [store_get_ne locals (k := "n") (a := "x") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_x]
  get_n := store_get_self locals "n" (.int (Int.ofNat n'.toNat))
  get_b := by
    rw [store_get_ne locals (k := "n") (a := "base") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_b]
  get_z := by
    rw [store_get_ne locals (k := "n") (a := "z") (.int (Int.ofNat n'.toNat)) (by decide),
      h.get_z]
  get_half := by
    rw [store_get_ne locals (k := "n") (a := "half") (.int (Int.ofNat n'.toNat))
      (by decide), h.get_half]

theorem RpowLoopStore.eval_x {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "x") (value := x) h.get_x

theorem RpowLoopStore.eval_n {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "n") =
      .ok (.int (Int.ofNat n.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "n") (value := n) h.get_n

theorem RpowLoopStore.eval_b {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "base") =
      .ok (.int (Int.ofNat b.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "base") (value := b) h.get_b

theorem RpowLoopStore.eval_z {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "z") =
      .ok (.int (Int.ofNat z.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "z") (value := z) h.get_z

theorem RpowLoopStore.eval_half {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var "half") =
      .ok (.int (Int.ofNat half.toNat)) :=
  evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "half") (value := half)
    h.get_half

theorem RpowLoopStore.eval_while_false {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x ⟨0⟩ b z half locals) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_false h.eval_n hzeroLit rfl

theorem RpowLoopStore.eval_while_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) (hnz : n ≠ ⟨0⟩) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool true) := by
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  apply evalExpr_ne_int_true h.eval_n hzeroLit
  intro hbad
  exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))

theorem RpowLoopStore.eval_odd_true {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {x n b z half : UInt256}
    {locals : Store} (hstore : RpowLoopStore x n b z half locals)
    (hodd : n.toNat % 2 ≠ 0) :
    evalExpr? cfg { contract := contract, locals := locals } evm
      (.binary .ne (.binary .mod (.var "n") (.intLit 2)) (.intLit 0)) =
        .ok (.bool true) := by
  have htwoLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 2) =
        .ok (.int (Int.ofNat (⟨2⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure, uInt256Two_toNat]
  have hmod :
      evalExpr? cfg { contract := contract, locals := locals } evm
        (.binary .mod (.var "n") (.intLit 2)) =
          .ok (.int (Int.ofNat (n.toNat % 2))) := by
    exact evalExpr_mod_int_ok hstore.eval_n htwoLit
      (by simp [uInt256Two_toNat])
      (by
        rw [uInt256Two_toNat]
        norm_num)
  have hzeroLit :
      evalExpr? cfg { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact evalExpr_ne_int_true hmod hzeroLit (by
    intro hbad
    apply hodd
    exact Nat.cast_injective hbad)

end Reasoning.Theory.RpowBase

