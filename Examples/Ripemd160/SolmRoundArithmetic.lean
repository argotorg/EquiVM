import Examples.Ripemd160.SolmParser

/-!
# RIPEMD-160 Solm round arithmetic

Local evaluation lemmas used by the authored compression loops.  Solm integer addition is exact,
so the source expressions are related to `UInt256` only under the small bounds supplied by the
32-bit compression invariant.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

theorem evalWordAdd {L : Store} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (hxy : x.toNat + y.toNat < UInt256.size)
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (wordValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (wordValue y)) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .add a b) =
      .ok (wordValue (x + y)) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?, wordValue, uadd_toNat]
  rw [show UInt256.size = 2 ^ 256 from by decide, Nat.mod_eq_of_lt (by
    simpa [UInt256.size] using hxy)]
  norm_num

theorem evalMask32 {L : Store} {evm : EVM.State} {a mask : Expr} {x : UInt256}
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (wordValue x))
    (hmask : evalExpr? config { contract := contract, locals := L } evm mask =
      .ok (wordValue mask32Word)) :
    evalExpr? config { contract := contract, locals := L } evm (.binary .bitAnd a mask) =
      .ok (wordValue (UInt256.land mask32Word x)) := by
  simpa [u256_land_comm] using evalBitAnd ha hmask

def roundWords (X : Fin 16 -> UInt256) : List Value :=
  List.ofFn fun i => wordValue (X i)

@[simp] theorem roundWords_length (X : Fin 16 -> UInt256) :
    (roundWords X).length = 16 := by
  simp [roundWords]

theorem roundWords_get (X : Fin 16 -> UInt256) (i : Nat) (hi : i < 16) :
    (roundWords X)[i] = wordValue (X ⟨i, hi⟩) := by
  unfold roundWords
  rw [List.getElem_ofFn]

theorem evalRoundWord {L : Store} {evm : EVM.State} {idx : Expr}
    (X : Fin 16 -> UInt256) (i : Nat) (hi : i < 16)
    (hwords : L.get? "words" = some (.array (roundWords X)))
    (hidx : evalExpr? config { contract := contract, locals := L } evm idx =
      .ok (wordValue (UInt256.ofNat i))) :
    evalExpr? config { contract := contract, locals := L } evm
      (.index (.var "words") idx) = .ok (wordValue (X ⟨i, hi⟩)) := by
  have hiSize : i < UInt256.size := lt_trans hi (by decide)
  have hidx' : evalExpr? config { contract := contract, locals := L } evm idx =
      .ok (.int (Int.ofNat i)) := by
    simpa only [wordValue, ulit_toNat' i hiSize] using hidx
  simp only [evalExpr?, EvalResult.ofOption, hwords, hidx', EvalResult.bind, bind,
    evalIndex?, roundWords_length]
  rw [if_pos]
  · rw [show (Int.ofNat i).toNat = i from rfl]
    rw [lookupNth_getElem _ i (by simp [hi])]
    change normalizeRawBoolWord? ((roundWords X)[i]) =
      .ok (wordValue (X ⟨i, hi⟩))
    rw [roundWords_get X i hi]
    rfl
  · exact ⟨Int.natCast_nonneg _, by simpa using hi⟩

theorem execLetWord {L : Store} {evm : EVM.State} {name : Ident} {ty : Option ABIType}
    {expr : Expr} {x : UInt256}
    (heval : evalExpr? config { contract := contract, locals := L } evm expr =
      .ok (wordValue x)) :
    ExecStmt config { contract := contract, locals := L } evm (.letDecl name ty expr)
      (.ok { contract := contract, locals := L.insert name (wordValue x) } evm) :=
  ExecStmt.letDecl heval

theorem assignLocalValue {L : Store} {evm : EVM.State} {name : Ident}
    {old value : Value} (hget : L.get? name = some old) :
    assignStorageRef? config { contract := contract, locals := L } evm
      .localVar { base := name } value =
      .ok ({ contract := contract, locals := L.insert name value }, evm) := by
  rw [assignStorageRef?, hget]
  simp only [updateLocalPath?, EvalResult.bind, bind, pure]

theorem execAssignLocal {L : Store} {evm : EVM.State} {name : Ident}
    {old value : Value} {expr : Expr}
    (hget : L.get? name = some old)
    (heval : evalExpr? config { contract := contract, locals := L } evm expr = .ok value) :
    ExecStmt config { contract := contract, locals := L } evm
      (.assign .localVar { base := name } expr)
      (.ok { contract := contract, locals := L.insert name value } evm) :=
  ExecStmt.assign heval (assignLocalValue hget)

def sourceRoundNext (s : RuntimeLineState) (x : UInt256) (round : Nat)
    (rotationRow boolF constant : UInt256) : UInt256 :=
  UInt256.land
    (runtimeRol32
      (UInt256.land
        (s.a + UInt256.land boolF mask32Word + x + constant)
        mask32Word)
      (runtimeRowEntry rotationRow (UInt256.ofNat round)) + s.e)
    mask32Word

def sourcePureRound (s : RuntimeLineState) (x : UInt256) (round : Nat)
    (rotationRow boolF constant : UInt256) : RuntimeLineState :=
  { a := s.e
    b := sourceRoundNext s x round rotationRow boolF constant
    c := s.b
    d := runtimeRol32 s.c ⟨10⟩
    e := s.d }

theorem sourceRoundNext_eq_runtime (s : RuntimeLineState) (x : UInt256) (round : Nat)
    (row rotationRow boolF constant : UInt256) :
    sourceRoundNext s x round rotationRow boolF constant =
      runtimePureRoundNext s x (UInt256.ofNat round) row rotationRow boolF constant := by
  unfold sourceRoundNext runtimePureRoundNext
  rw [u256_land_comm
    (runtimeRol32
      (UInt256.land
        (s.a + UInt256.land boolF mask32Word + x + constant) mask32Word)
      (runtimeRowEntry rotationRow (UInt256.ofNat round)) + s.e)
    mask32Word]
  congr 1
  congr 1
  rw [u256_land_comm
    (s.a + UInt256.land boolF mask32Word + x + constant) mask32Word]
  congr 1
  rw [u256_land_comm boolF mask32Word]
  apply congrArg (UInt256.land mask32Word)
  rw [u256_add_comm s.a (UInt256.land mask32Word boolF)]

theorem sourcePureRound_eq_runtime (s : RuntimeLineState) (x : UInt256) (round : Nat)
    (row rotationRow boolF constant : UInt256) :
    sourcePureRound s x round rotationRow boolF constant =
      runtimePureRound s x (UInt256.ofNat round) row rotationRow boolF constant := by
  simp [sourcePureRound, runtimePureRound, sourceRoundNext_eq_runtime s x round row]

end Ripemd160
