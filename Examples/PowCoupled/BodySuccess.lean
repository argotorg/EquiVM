import Examples.Pow.Correct
import Reasoning.Refinement

/-!
# Pow coupled-state experiment

This file tries the new concrete coupled-state refinement style on the successful suffix of
`pow2`: start at the loop head, prove the Solm loop and bytecode loop progress together, then
finish through the bytecode return encoder.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace PowCoupled

noncomputable section

set_option maxRecDepth 10000

private abbrev u0 : UInt256 := ⟨0⟩
private abbrev u1 : UInt256 := ⟨1⟩
private abbrev u2 : UInt256 := ⟨2⟩
private abbrev u3 : UInt256 := UInt256.ofNat 3
private abbrev u71 : UInt256 := ⟨71⟩
private abbrev u117 : UInt256 := ⟨117⟩
private abbrev u126 : UInt256 := ⟨126⟩
private abbrev u132 : UInt256 := ⟨132⟩
private abbrev u142 : UInt256 := ⟨142⟩

private abbrev loopStack (N i : ℕ) (sel : UInt256) : List UInt256 :=
  [UInt256.ofNat i, UInt256.ofNat (2 ^ i), u0, UInt256.ofNat N, u71, sel]

private abbrev afterRStack (N i : ℕ) (sel : UInt256) : List UInt256 :=
  [UInt256.ofNat i, UInt256.ofNat (2 ^ (i + 1)), u0, UInt256.ofNat N, u71, sel]

private abbrev exitStack (N : ℕ) (sel : UInt256) : List UInt256 :=
  [UInt256.ofNat N, UInt256.ofNat (2 ^ N), u0, UInt256.ofNat N, u71, sel]

private def cursorAt (pc : UInt256) (stack : List UInt256)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := pc, stack := stack, mem := solcFreePtrMem, aw := u3, rdata := ByteArray.empty,
    world := world }

def PowLoopRel (N : ℕ) (sel : UInt256) (v : ℕ) : StateRel :=
  fun cur frame _evm =>
    ∃ i : ℕ,
      N - i = v ∧ i ≤ N ∧
      cur.stack = loopStack N i sel ∧
      cur.mem = solcFreePtrMem ∧ cur.aw = u3 ∧ cur.rdata = ByteArray.empty ∧
      frame.locals.get? "i" = some (.int (Int.ofNat i)) ∧
      frame.locals.get? "r" = some (.int (Int.ofNat (2 ^ i))) ∧
      frame.locals.get? "n" = some (.int (Int.ofNat N))

def PowBodyRel (N : ℕ) (sel : UInt256) (v : ℕ) : StateRel :=
  fun cur frame _evm =>
    ∃ i : ℕ,
      N - i = v + 1 ∧ i < N ∧
      cur.stack = loopStack N i sel ∧
      cur.mem = solcFreePtrMem ∧ cur.aw = u3 ∧ cur.rdata = ByteArray.empty ∧
      frame.locals.get? "i" = some (.int (Int.ofNat i)) ∧
      frame.locals.get? "r" = some (.int (Int.ofNat (2 ^ i))) ∧
      frame.locals.get? "n" = some (.int (Int.ofNat N))

def PowAfterRRel (N : ℕ) (sel : UInt256) (v : ℕ) : StateRel :=
  fun cur frame _evm =>
    ∃ i : ℕ,
      N - i = v + 1 ∧ i < N ∧
      cur.stack = afterRStack N i sel ∧
      cur.mem = solcFreePtrMem ∧ cur.aw = u3 ∧ cur.rdata = ByteArray.empty ∧
      frame.locals.get? "i" = some (.int (Int.ofNat i)) ∧
      frame.locals.get? "r" = some (.int (Int.ofNat (2 ^ (i + 1)))) ∧
      frame.locals.get? "n" = some (.int (Int.ofNat N))

def PowExitRel (N : ℕ) (sel : UInt256) : StateRel :=
  fun cur frame _evm =>
    cur.stack = exitStack N sel ∧
    cur.mem = solcFreePtrMem ∧ cur.aw = u3 ∧ cur.rdata = ByteArray.empty ∧
    frame.locals.get? "r" = some (.int (Int.ofNat (2 ^ N))) ∧
    frame.locals.get? "n" = some (.int (Int.ofNat N))

private theorem ofNat_add_one {i : ℕ} (hi : i + 1 < UInt256.size) :
    (UInt256.ofNat i + u1).toNat = i + 1 := by
  have hi0 : i < UInt256.size := by omega
  have hto : (UInt256.ofNat i).toNat = i := ulit_toNat' i hi0
  simpa [u1, hto] using add1_toNat (i := UInt256.ofNat i) (by rw [hto]; exact hi)

private theorem mul2_ofNat_pow {i : ℕ} (hi : i + 1 < 256) :
    UInt256.mul (UInt256.ofNat (2 ^ i)) u2 = UInt256.ofNat (2 ^ (i + 1)) := by
  apply u256_inj
  have hsize : 2 * (UInt256.ofNat (2 ^ i)).toNat < UInt256.size := by
    rw [show (UInt256.ofNat (2 ^ i)).toNat = 2 ^ i from ofNat_pow_toNat (by omega)]
    rw [show 2 * 2 ^ i = 2 ^ (i + 1) from by rw [pow_succ]; ring]
    exact pow_lt_size hi
  rw [mul2_toNat hsize]
  rw [show (UInt256.ofNat (2 ^ i)).toNat = 2 ^ i from ofNat_pow_toNat (by omega)]
  rw [show (UInt256.ofNat (2 ^ (i + 1))).toNat = 2 ^ (i + 1) from ofNat_pow_toNat hi]
  rw [pow_succ]
  ring

private theorem add1_ofNat {i : ℕ} (hi : i + 1 < UInt256.size) :
    UInt256.ofNat i + u1 = UInt256.ofNat (i + 1) := by
  apply u256_inj
  rw [ofNat_add_one hi]
  exact (ulit_toNat' (i + 1) hi).symm

set_option maxHeartbeats 2000000 in
theorem powCoupled_loopSuffix_success {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {N : ℕ} {sel : UInt256} (hN : N < 256) :
    ∀ st : CoupledState powBytecode ee g s0 (PowLoopRel N sel N) u117,
      CoupledState.refines st powConfig
        [.while Pow.powLoopCond Pow.powLoopBody, .return (.var "r")]
        (transitionPost powBytecode ee g s0 (some Pow.uint256) (fun _ _ _ => False)) := by
  intro st
  refine CoupledState.refines.whileLoopIndexedBody
    (code := powBytecode) (ee := ee) (g := g) (s0 := s0) (cfg := powConfig)
    (loopPc := u117) (bodyPc := u126) (exitPc := u142)
    (Rloop := PowLoopRel N sel) (Rbody := PowBodyRel N sel) (Rexit := PowExitRel N sel)
    (Post := transitionPost powBytecode ee g s0 (some Pow.uint256) (fun _ _ _ => False))
    (cond := Pow.powLoopCond) (body := Pow.powLoopBody) (rest := [.return (.var "r")])
    ?hfalse ?htrue ?hbody ?hrest N st
  · intro st0
    rcases st0.hrel with ⟨i, hvar, hile, hstack, hmem, haw, hrdata, hi, hr, hn⟩
    have hieq : i = N := by omega
    subst i
    have hcond : evalExpr? powConfig st0.frame st0.evm Pow.powLoopCond = .ok (.bool false) := by
      rw [Pow.powLoopCond, Pow.evalLt hi hn,
        decide_eq_false (by simp only [Int.ofNat_eq_natCast, Nat.cast_lt]; omega)]
    have hlt : UInt256.lt (UInt256.ofNat N) (UInt256.ofNat N) = u0 := by
      exact ult_zero (by omega)
    have hRD0 : RD powBytecode ee g s0 u117 (loopStack N N sel) solcFreePtrMem u3
        ByteArray.empty st0.cur.world st0.k st0.C :=
      st0.toRD hstack hmem haw hrdata
    have rdExit := evm_run hRD0 with [
      jumpdest, dup4, dup2, lt, iszero, push2 ⟨142⟩,
      jumpiT (by rw [hlt]; decide) (by jump_dest) ]
    exact ⟨cursorAt u142 (exitStack N sel) st0.cur.world, _, _, hcond, rfl, rdExit,
      st0.hworld, ⟨rfl, rfl, rfl, rfl, by simpa [exitStack] using hr, hn⟩⟩
  · intro v stLoop
    rcases stLoop.hrel with ⟨i, hvar, hile, hstack, hmem, haw, hrdata, hi, hr, hn⟩
    have hltNat : i < N := by omega
    have hcond : evalExpr? powConfig stLoop.frame stLoop.evm Pow.powLoopCond = .ok (.bool true) := by
      rw [Pow.powLoopCond, Pow.evalLt hi hn,
        decide_eq_true (by simp only [Int.ofNat_eq_natCast, Nat.cast_lt]; omega)]
    have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat N) = u1 := by
      exact ult_one (by
        rw [ulit_toNat' i (by exact lt_size_of_lt256 (by omega)),
          ulit_toNat' N (lt_size_of_lt256 hN)]
        exact hltNat)
    have hRD0 : RD powBytecode ee g s0 u117 (loopStack N i sel) solcFreePtrMem u3
        ByteArray.empty stLoop.cur.world stLoop.k stLoop.C :=
      stLoop.toRD hstack hmem haw hrdata
    have rdBody := evm_run hRD0 with [
      jumpdest, dup4, dup2, lt, iszero, push2 ⟨142⟩,
      jumpiNT (by rw [hlt]; decide) ]
    exact ⟨cursorAt u126 (loopStack N i sel) stLoop.cur.world, _, _, hcond, rfl, rdBody,
      stLoop.hworld, ⟨i, hvar, hltNat, rfl, rfl, rfl, rfl, hi, hr, hn⟩⟩
  · intro v stBody
    rcases stBody.hrel with ⟨i, hvar, hlt, hstack, hmem, haw, hrdata, hi, hr, hn⟩
    have hpowInt : (Int.ofNat (2 ^ i) * 2 : Int) = Int.ofNat (2 ^ (i + 1)) := by
      simp only [Int.ofNat_eq_natCast]
      push_cast [pow_succ]
      ring
    set frameR : Frame :=
      { stBody.frame with
        locals := stBody.frame.locals.insert "r" (.int (Int.ofNat (2 ^ (i + 1)))) }
      with hframeR
    have hstmtR : ExecStmt powConfig stBody.frame stBody.evm
        (.letDecl "r" (some Pow.uint256) (.binary .mul (.var "r") (.intLit 2)))
        (.ok frameR stBody.evm) := by
      rw [hframeR, ← hpowInt]
      exact ExecStmt.letDecl (by rw [Pow.evalMul2 hr])
    have hRD0 : RD powBytecode ee g s0 u126 (loopStack N i sel) solcFreePtrMem u3
        ByteArray.empty stBody.cur.world stBody.k stBody.C :=
      stBody.toRD hstack hmem haw hrdata
    have hmul : UInt256.mul (UInt256.ofNat (2 ^ i)) u2 = UInt256.ofNat (2 ^ (i + 1)) :=
      mul2_ofNat_pow (by omega)
    have rdR := evm_run hRD0 with [
      push1 ⟨2⟩, dup3, mul, swap2, pop ]
    rw [hmul] at rdR
    have hrelR : PowAfterRRel N sel v (cursorAt u132 (afterRStack N i sel) stBody.cur.world)
        frameR stBody.evm := by
      refine ⟨i, hvar, hlt, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · rw [hframeR, store_get_ne _ _ (by decide), hi]
      · rw [hframeR, store_get_self]
      · rw [hframeR, store_get_ne _ _ (by decide), hn]
    let stR : CoupledState powBytecode ee g s0 (PowAfterRRel N sel v) u132 :=
      CoupledState.reached (cursorAt u132 (afterRStack N i sel) stBody.cur.world)
        _ _ frameR stBody.evm rfl rdR stBody.hworld hrelR
    refine CoupledState.refines.consNormalAt
      (s := .letDecl "r" (some Pow.uint256) (.binary .mul (.var "r") (.intLit 2)))
      (rest := [.letDecl "i" (some Pow.uint256) (.binary .add (.var "i") (.intLit 1))])
      stBody stR hstmtR ?_
    rcases stR.hrel with ⟨i, hvar, hlt, hstack, hmem, haw, hrdata, hi, hr, hn⟩
    have hInt : (Int.ofNat i + 1 : Int) = Int.ofNat (i + 1) := by
      simp only [Int.ofNat_eq_natCast]
      push_cast
      ring
    set frameI : Frame :=
      { stR.frame with locals := stR.frame.locals.insert "i" (.int (Int.ofNat (i + 1))) }
      with hframeI
    have hstmtI : ExecStmt powConfig stR.frame stR.evm
        (.letDecl "i" (some Pow.uint256) (.binary .add (.var "i") (.intLit 1)))
        (.ok frameI stR.evm) := by
      rw [hframeI, ← hInt]
      exact ExecStmt.letDecl (by rw [Pow.evalAdd1 hi])
    have hRD0 : RD powBytecode ee g s0 u132 (afterRStack N i sel) solcFreePtrMem u3
        ByteArray.empty stR.cur.world stR.k stR.C :=
      stR.toRD hstack hmem haw hrdata
    have hadd : UInt256.ofNat i + u1 = UInt256.ofNat (i + 1) :=
      add1_ofNat (lt_size_of_lt256 (by omega))
    have rdLoop := evm_run hRD0 with [
      push1 ⟨1⟩, dup2, add, swap1, pop, push2 ⟨117⟩,
      jump (by jump_dest) ]
    rw [hadd] at rdLoop
    have hrelLoop : PowLoopRel N sel v
        (cursorAt u117 (loopStack N (i + 1) sel) stR.cur.world) frameI stR.evm := by
      refine ⟨i + 1, by omega, by omega, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · rw [hframeI, store_get_self]
      · rw [hframeI, store_get_ne _ _ (by decide), hr]
      · rw [hframeI, store_get_ne _ _ (by decide), hn]
    let stLoop : CoupledState powBytecode ee g s0 (PowLoopRel N sel v) u117 :=
      CoupledState.reached (cursorAt u117 (loopStack N (i + 1) sel) stR.cur.world)
        _ _ frameI stR.evm rfl rdLoop stR.hworld hrelLoop
    refine CoupledState.refines.consNormalAt
      (s := .letDecl "i" (some Pow.uint256) (.binary .add (.var "i") (.intLit 1)))
      (rest := []) stR stLoop hstmtI ?_
    exact ⟨.ok stLoop.frame stLoop.evm, ExecBlock.nil,
      stLoop.cur, stLoop.k, stLoop.C, stLoop.hpc, stLoop.hRD, stLoop.hworld, stLoop.hrel⟩
  · intro stExit
    rcases stExit.hrel with ⟨hstack, hmem, haw, hrdata, hr, _hn⟩
    have hstmt : ExecStmt powConfig stExit.frame stExit.evm (.return (.var "r"))
        (.returned stExit.frame stExit.evm (some (.int (Int.ofNat (2 ^ N))))) :=
      ExecStmt.return (by rw [Pow.evalVar hr])
    have hRD0 : RD powBytecode ee g s0 u142 (exitStack N sel) solcFreePtrMem u3
        ByteArray.empty stExit.cur.world stExit.k stExit.C :=
      stExit.toRD hstack hmem haw hrdata
    have rdRet : RDret powBytecode g s0 stExit.cur.world
        (UInt256.toByteArray (UInt256.ofNat (2 ^ N))) :=
      hRD0.routineexit (by jump_dest)
          (by simp only [List.length_cons, List.length_nil]; omega)
        |>.routineencode (by simp only [List.length_cons, List.length_nil]; omega)
    rw [stExit.hworld] at rdRet
    exact CoupledState.refines.returnTransition stExit hstmt rdRet
      (returnEquiv_of_encode (Pow.powReturnEncoding hN))

end

end PowCoupled
