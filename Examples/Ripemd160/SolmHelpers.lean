import Examples.Ripemd160.Spec
import Examples.Ripemd160.HashPure
import Examples.Ripemd160.HashDigest
import Reasoning.SolmBody

/-!
# RIPEMD-160 Solm helper functions

Big-step proofs for the explicit, straight-line helper functions used by the authored Solm hash.
All results are ordinary Solm integer values; no RIPEMD primitive is present in the configuration.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000

namespace Ripemd160

abbrev wordValue (x : UInt256) : Value := .int (Int.ofNat x.toNat)

def xyzLocals (x y z : UInt256) : Store :=
  (((∅ : Store).insert "z" (wordValue z)).insert "y" (wordValue y)).insert "x" (wordValue x)

@[simp] theorem xyzLocals_x (x y z : UInt256) :
    (xyzLocals x y z).get? "x" = some (wordValue x) := by
  simp only [xyzLocals]
  rw [store_get_self]

@[simp] theorem xyzLocals_y (x y z : UInt256) :
    (xyzLocals x y z).get? "y" = some (wordValue y) := by
  simp only [xyzLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]

@[simp] theorem xyzLocals_z (x y z : UInt256) :
    (xyzLocals x y z).get? "z" = some (wordValue z) := by
  simp only [xyzLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem word_toNat_xor (x y : UInt256) :
    (UInt256.xor x y).toNat = x.toNat ^^^ y.toNat := by
  rw [uxor_toNat, Nat.mod_eq_of_lt]
  change x.toNat ^^^ y.toNat < 2 ^ 256
  exact Nat.xor_lt_two_pow (by change x.val.val < 2 ^ 256; exact x.val.isLt)
    (by change y.val.val < 2 ^ 256; exact y.val.isLt)

theorem word_toNat_lor (x y : UInt256) :
    (UInt256.lor x y).toNat = Nat.lor x.toNat y.toNat := by
  rw [u256_lor_toNat, Nat.mod_eq_of_lt]
  change Nat.lor x.toNat y.toNat < 2 ^ 256
  exact Nat.or_lt_two_pow (by change x.val.val < 2 ^ 256; exact x.val.isLt)
    (by change y.val.val < 2 ^ 256; exact y.val.isLt)

theorem wordInt_lt (x : UInt256) :
    (Int.ofNat x.toNat) < (EVM.wordModulus : Int) := by
  change Int.ofNat x.toNat < Int.ofNat UInt256.size
  simpa only [Int.ofNat_eq_natCast, Nat.cast_lt] using x.val.isLt

theorem wordComplement_int (x : UInt256) :
    (EVM.wordModulus : Int) - 1 - Int.ofNat x.toNat =
      Int.ofNat (UInt256.size - 1 - x.toNat) := by
  rw [show EVM.wordModulus = UInt256.size from rfl]
  have htop : 1 ≤ UInt256.size := by decide
  have hx : x.toNat ≤ UInt256.size - 1 := Nat.le_pred_of_lt x.val.isLt
  change Int.ofNat UInt256.size - Int.ofNat 1 - Int.ofNat x.toNat = _
  calc
    _ = Int.ofNat (UInt256.size - 1) - Int.ofNat x.toNat :=
      congrArg (fun q : Int => q - Int.ofNat x.toNat) (Int.ofNat_sub htop).symm
    _ = _ := (Int.ofNat_sub hx).symm

theorem evalBitXor {L : Store} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (wordValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (wordValue y)) :
    evalExpr? config { contract := contract, locals := L } evm
      (.binary .bitXor a b) = .ok (wordValue (UInt256.xor x y)) := by
  have hx := wordInt_lt x
  have hy := wordInt_lt y
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?]
  rw [if_pos]
  · simp only [wordValue, word_toNat_xor]
    rfl
  · exact ⟨Int.natCast_nonneg _, hx, Int.natCast_nonneg _, hy⟩

theorem evalBitAnd {L : Store} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (wordValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (wordValue y)) :
    evalExpr? config { contract := contract, locals := L } evm
      (.binary .bitAnd a b) = .ok (wordValue (UInt256.land x y)) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?]
  rw [if_pos]
  · simp only [wordValue, uland_toNat]
    rfl
  · exact ⟨Int.natCast_nonneg _, wordInt_lt x, Int.natCast_nonneg _, wordInt_lt y⟩

theorem evalBitOr {L : Store} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (wordValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b = .ok (wordValue y)) :
    evalExpr? config { contract := contract, locals := L } evm
      (.binary .bitOr a b) = .ok (wordValue (UInt256.lor x y)) := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?]
  rw [if_pos]
  · simp only [wordValue, word_toNat_lor]
    rfl
  · exact ⟨Int.natCast_nonneg _, wordInt_lt x, Int.natCast_nonneg _, wordInt_lt y⟩

theorem evalBitNot {L : Store} {evm : EVM.State} {a : Expr} {x : UInt256}
    (hx32 : x.toNat < 2 ^ 32)
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (wordValue x)) :
    evalExpr? config { contract := contract, locals := L } evm
      (.unary .bitNot a) = .ok (wordValue (UInt256.lnot x)) := by
  simp only [evalExpr?, ha, EvalResult.bind, bind, evalUnaryOp?, wordValue]
  rw [if_pos]
  · rw [lnot_toNat_small x hx32]
    simp only [EvalResult.ofOption]
    change EvalResult.ok (Value.int ((EVM.wordModulus : Int) - 1 - Int.ofNat x.toNat)) =
      EvalResult.ok (Value.int (Int.ofNat (UInt256.size - 1 - x.toNat)))
    rw [wordComplement_int]
  · exact ⟨Int.natCast_nonneg _, wordInt_lt x⟩

theorem evalWordVar {L : Store} {evm : EVM.State} {a : Ident} {x : UInt256}
    (ha : L.get? a = some (wordValue x)) :
    evalExpr? config { contract := contract, locals := L } evm (.var a) = .ok (wordValue x) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [ha]

theorem evalWordLit {L : Store} {evm : EVM.State} (n : Nat) (hn : n < UInt256.size) :
    evalExpr? config { contract := contract, locals := L } evm (.intLit (Int.ofNat n)) =
      .ok (wordValue (UInt256.ofNat n)) := by
  simp only [evalExpr?, wordValue]
  rw [ulit_toNat' n hn]
  rfl

theorem evalShl {L : Store} {evm : EVM.State} {a b : Expr} {x : UInt256} (n : Nat)
    (hn : n < 256)
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (wordValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b =
      .ok (wordValue (UInt256.ofNat n))) :
    evalExpr? config { contract := contract, locals := L } evm
      (.binary .shl a b) =
      .ok (wordValue (UInt256.shiftLeft x (UInt256.ofNat n))) := by
  have hnSize : n < UInt256.size := lt_trans hn (by decide)
  have hb' : evalExpr? config { contract := contract, locals := L } evm b =
      .ok (.int (Int.ofNat n)) := by
    simpa only [wordValue, ulit_toNat' n hnSize] using hb
  simp only [evalExpr?, ha, hb', EvalResult.bind, bind, evalBinaryOp?]
  rw [if_pos, if_neg (by
    intro h
    change Int.ofNat 256 ≤ Int.ofNat n at h
    have : 256 ≤ n := Int.ofNat_le.mp h
    omega)]
  · simp only [wordValue]
    rw [ushl_ofNat_toNat x n hn]
    rw [show (Int.ofNat x.toNat).toNat = x.toNat from rfl,
      show (Int.ofNat n).toNat = n from rfl,
      show EVM.wordModulus = UInt256.size from rfl]
    simp [Nat.shiftLeft_eq]
  · exact ⟨Int.natCast_nonneg _, wordInt_lt x, Int.natCast_nonneg _⟩

theorem evalShr {L : Store} {evm : EVM.State} {a b : Expr} {x : UInt256} (n : Nat)
    (hn : n < 256)
    (ha : evalExpr? config { contract := contract, locals := L } evm a = .ok (wordValue x))
    (hb : evalExpr? config { contract := contract, locals := L } evm b =
      .ok (wordValue (UInt256.ofNat n))) :
    evalExpr? config { contract := contract, locals := L } evm
      (.binary .shr a b) =
      .ok (wordValue (UInt256.shiftRight x (UInt256.ofNat n))) := by
  have hnSize : n < UInt256.size := lt_trans hn (by decide)
  have hb' : evalExpr? config { contract := contract, locals := L } evm b =
      .ok (.int (Int.ofNat n)) := by
    simpa only [wordValue, ulit_toNat' n hnSize] using hb
  simp only [evalExpr?, ha, hb', EvalResult.bind, bind, evalBinaryOp?]
  rw [if_pos, if_neg (by
    intro h
    change Int.ofNat 256 ≤ Int.ofNat n at h
    have : 256 ≤ n := Int.ofNat_le.mp h
    omega)]
  · simp only [wordValue]
    rw [ushr_ofNat_toNat x n hn]
    rw [show (Int.ofNat x.toNat).toNat = x.toNat from rfl,
      show (Int.ofNat n).toNat = n from rfl]
    simp [Nat.shiftRight_eq_div_pow]
  · exact ⟨Int.natCast_nonneg _, wordInt_lt x, Int.natCast_nonneg _⟩

def xnLocals (x : UInt256) (n : Nat) : Store :=
  ((∅ : Store).insert "n" (wordValue (UInt256.ofNat n))).insert "x" (wordValue x)

theorem xnLocals_x (x : UInt256) (n : Nat) :
    (xnLocals x n).get? "x" = some (wordValue x) := by
  simp only [xnLocals]
  rw [store_get_self]

theorem xnLocals_n (x : UInt256) (n : Nat) :
    (xnLocals x n).get? "n" = some (wordValue (UInt256.ofNat n)) := by
  simp only [xnLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem evalSub32 (evm : EVM.State) (x : UInt256) (n : Nat) (hn : n ≤ 32) :
    evalExpr? config { contract := contract, locals := xnLocals x n } evm
      (.binary .sub (.intLit 32) (.var "n")) =
      .ok (wordValue (UInt256.ofNat (32 - n))) := by
  have hnSize : n < UInt256.size := lt_of_le_of_lt hn (by decide)
  have hsubSize : 32 - n < UInt256.size := lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption]
  rw [show (xnLocals x n).get? "n" = some (wordValue (UInt256.ofNat n)) from xnLocals_n x n]
  simp only [wordValue, ulit_toNat' n hnSize, ulit_toNat' (32 - n) hsubSize]
  change EvalResult.ok (Value.int (Int.ofNat 32 - Int.ofNat n)) =
    EvalResult.ok (Value.int (Int.ofNat (32 - n)))
  exact congrArg (fun q : Int => EvalResult.ok (Value.int q)) (Int.ofNat_sub hn).symm

theorem rotl32BodyReturns (evm : EVM.State) (x : UInt256) (n : Nat)
    (hn : n < 16) :
    ExecFuncBody config { contract := contract, locals := xnLocals x n } evm
      (rotl32Function).body
      (.returned { contract := contract, locals := xnLocals x n } evm
        (some [wordValue (runtimeRol32 x (UInt256.ofNat n))])) := by
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm [.return [_]] _
  apply ABlock.start.returns
  have hx := evalWordVar (evm := evm) (xnLocals_x x n)
  have hnEval := evalWordVar (evm := evm) (xnLocals_n x n)
  have hleft := evalShl n (by omega) hx hnEval
  have hright := evalShr (32 - n) (by omega) hx (evalSub32 evm x n (by omega))
  have hmask := evalWordLit (L := xnLocals x n) (evm := evm) 0xffffffff (by decide)
  have hmaskWord : UInt256.ofNat 0xffffffff = mask32Word := by native_decide
  simpa [runtimeRol32, hmaskWord, u256_sub_32_ofNat n (by omega), u256_land_comm] using
    evalBitAnd (evalBitOr hleft hright) hmask

def rowIndexLocals (row : UInt256) (idx : Nat) : Store :=
  ((∅ : Store).insert "idx" (wordValue (UInt256.ofNat idx))).insert "row" (wordValue row)

theorem rowIndexLocals_row (row : UInt256) (idx : Nat) :
    (rowIndexLocals row idx).get? "row" = some (wordValue row) := by
  simp only [rowIndexLocals]
  rw [store_get_self]

theorem rowIndexLocals_idx (row : UInt256) (idx : Nat) :
    (rowIndexLocals row idx).get? "idx" = some (wordValue (UInt256.ofNat idx)) := by
  simp only [rowIndexLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]

def sourceRowEntry (row : UInt256) (idx : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight row (UInt256.ofNat (60 - idx * 4))) (UInt256.ofNat 15)

theorem evalNibbleShift (evm : EVM.State) (row : UInt256) (idx : Nat) (hi : idx < 16) :
    evalExpr? config { contract := contract, locals := rowIndexLocals row idx } evm
      (.binary .sub (.intLit 60) (.binary .mul (.var "idx") (.intLit 4))) =
      .ok (wordValue (UInt256.ofNat (60 - idx * 4))) := by
  have hiSize : idx < UInt256.size := lt_trans hi (by decide)
  have hs : 60 - idx * 4 < UInt256.size := lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption]
  rw [show (rowIndexLocals row idx).get? "idx" =
    some (wordValue (UInt256.ofNat idx)) from rowIndexLocals_idx row idx]
  simp only [wordValue, ulit_toNat' idx hiSize, ulit_toNat' (60 - idx * 4) hs]
  change EvalResult.ok (Value.int (Int.ofNat 60 - Int.ofNat idx * 4)) =
    EvalResult.ok (Value.int (Int.ofNat (60 - idx * 4)))
  have hle : idx * 4 ≤ 60 := by omega
  have hmul : Int.ofNat idx * 4 = Int.ofNat (idx * 4) := by norm_num
  rw [hmul]
  exact congrArg (fun q : Int => EvalResult.ok (Value.int q)) (Int.ofNat_sub hle).symm

theorem sourceRowEntry_eq_runtime (row : UInt256) (idx : Nat) (hi : idx < 16) :
    sourceRowEntry row idx = runtimeRowEntry row (UInt256.ofNat idx) := by
  have harg :
      (⟨60⟩ - UInt256.shiftLeft (UInt256.land (UInt256.ofNat idx) ⟨15⟩) ⟨2⟩ : UInt256) =
        UInt256.ofNat (60 - idx * 4) := by
    interval_cases idx <;> native_decide
  have hmask : (⟨15⟩ : UInt256) = UInt256.ofNat 15 := by native_decide
  unfold sourceRowEntry runtimeRowEntry
  rw [harg, hmask]

theorem nibbleBodyReturns (evm : EVM.State) (row : UInt256) (idx : Nat) (hi : idx < 16) :
    ExecFuncBody config { contract := contract, locals := rowIndexLocals row idx } evm
      (nibbleFunction).body
      (.returned { contract := contract, locals := rowIndexLocals row idx } evm
        (some [wordValue (runtimeRowEntry row (UInt256.ofNat idx))])) := by
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm [.return [_]] _
  apply ABlock.start.returns
  have hrow := evalWordVar (evm := evm) (rowIndexLocals_row row idx)
  have hshift := evalNibbleShift evm row idx hi
  have hshr := evalShr (60 - idx * 4) (by omega) hrow hshift
  have hmask := evalWordLit (L := rowIndexLocals row idx) (evm := evm) 15 (by decide)
  have h := evalBitAnd hshr hmask
  change evalExpr? config _ evm _ = .ok (wordValue (sourceRowEntry row idx)) at h
  rw [sourceRowEntry_eq_runtime row idx hi] at h
  exact h

def paddedLocals (data : ByteArray) (pos bitLen paddedLen : Nat) : Store :=
  ((((∅ : Store).insert "paddedLen" (.int (Int.ofNat paddedLen))).insert
    "bitLen" (.int (Int.ofNat bitLen))).insert "pos" (.int (Int.ofNat pos))).insert
    "data" (.bytes data)

theorem paddedLocals_data (data : ByteArray) (pos bitLen paddedLen : Nat) :
    (paddedLocals data pos bitLen paddedLen).get? "data" = some (.bytes data) := by
  simp only [paddedLocals]
  rw [store_get_self]

theorem paddedLocals_pos (data : ByteArray) (pos bitLen paddedLen : Nat) :
    (paddedLocals data pos bitLen paddedLen).get? "pos" = some (.int (Int.ofNat pos)) := by
  simp only [paddedLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem paddedLocals_bitLen (data : ByteArray) (pos bitLen paddedLen : Nat) :
    (paddedLocals data pos bitLen paddedLen).get? "bitLen" = some (.int (Int.ofNat bitLen)) := by
  simp only [paddedLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem paddedLocals_paddedLen (data : ByteArray) (pos bitLen paddedLen : Nat) :
    (paddedLocals data pos bitLen paddedLen).get? "paddedLen" = some (.int (Int.ofNat paddedLen)) := by
  simp only [paddedLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem lookupNth_getElem {α : Type u} (xs : List α) (i : Nat) (hi : i < xs.length) :
    lookupNth? xs i = some xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [lookupNth?]
          simpa using ih i (by simpa using hi)

theorem evalPaddedDataByte (evm : EVM.State) (data : ByteArray)
    (pos bitLen paddedLen : Nat) (hp : pos < data.size) :
    evalExpr? config { contract := contract, locals := paddedLocals data pos bitLen paddedLen } evm
      (.cast (.index (.var "data") (.var "pos"))
        (.elem (.int (.uint ⟨8, by decide⟩)))) =
      .ok (.int (Int.ofNat (data[pos]'hp).toNat)) := by
  simp only [evalExpr?, EvalResult.bind, bind, EvalResult.ofOption]
  rw [paddedLocals_data, paddedLocals_pos]
  simp only [EvalResult.bind, bind]
  change (do
    let value ← evalByteIndex? data.toList (Int.ofNat pos)
    EvalResult.ofOption .typeError
      (castValue? value (.elem (.int (.uint ⟨8, by decide⟩))))) = _
  unfold evalByteIndex?
  have hlen : data.toList.length = data.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by simp), if_pos (by rwa [hlen])]
  simp only [show (Int.ofNat pos).toNat = pos from rfl, Option.map_eq_map]
  have hpList : pos < data.toList.length := by rwa [hlen]
  rw [lookupNth_getElem data.toList pos hpList]
  have hget : data.toList[pos] = data[pos] := by
    have hpA : pos < data.data.size := by exact hp
    simpa only [byteArray_toList_eq] using Array.getElem_toList hpA
  rw [hget]
  simp only [EvalResult.bind, bind, EvalResult.ofOption]
  norm_num [castValue?, fixedBytesToNat?, fixedBytesValid, fixedBytesSize,
    Ethereum.fromBytesBigEndian, Ethereum.fromBytes']

theorem evalPaddedPosLtLen (evm : EVM.State) (data : ByteArray)
    (pos bitLen paddedLen : Nat) :
    evalExpr? config { contract := contract, locals := paddedLocals data pos bitLen paddedLen } evm
      (.binary .lt (.var "pos") (.arrayLength .localVar { base := "data", steps := [] })) =
      .ok (.bool (decide (pos < data.size))) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption]
  rw [paddedLocals_pos, paddedLocals_data]
  simp [readLocalPath?, pure]

theorem evalPaddedPosEqLen (evm : EVM.State) (data : ByteArray)
    (pos bitLen paddedLen : Nat) :
    evalExpr? config { contract := contract, locals := paddedLocals data pos bitLen paddedLen } evm
      (.binary .eq (.var "pos") (.arrayLength .localVar { base := "data", steps := [] })) =
      .ok (.bool (Int.ofNat pos == Int.ofNat data.size)) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption]
  rw [paddedLocals_pos, paddedLocals_data]
  simp [readLocalPath?, pure]

theorem evalPaddedPosGeTail (evm : EVM.State) (data : ByteArray)
    (pos bitLen paddedLen : Nat) (hpad : 8 ≤ paddedLen) :
    evalExpr? config { contract := contract, locals := paddedLocals data pos bitLen paddedLen } evm
      (.binary .ge (.var "pos") (.binary .sub (.var "paddedLen") (.intLit 8))) =
      .ok (.bool (decide (paddedLen - 8 ≤ pos))) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption]
  rw [paddedLocals_pos, paddedLocals_paddedLen]
  have hcast := Int.ofNat_sub hpad
  simp only
  rw [show Int.ofNat paddedLen - 8 = Int.ofNat (paddedLen - 8) by
    simpa using hcast.symm]
  simp only [Int.ofNat_eq_natCast, Nat.cast_le]

theorem evalPaddedLengthShift (evm : EVM.State) (data : ByteArray)
    (pos bitLen paddedLen : Nat) (hpad : 8 ≤ paddedLen) (htail : paddedLen - 8 ≤ pos)
    (hshiftSize : (pos - (paddedLen - 8)) * 8 < UInt256.size) :
    let q := pos - (paddedLen - 8)
    evalExpr? config { contract := contract, locals := paddedLocals data pos bitLen paddedLen } evm
      (.binary .mul (.intLit 8)
        (.binary .sub (.var "pos") (.binary .sub (.var "paddedLen") (.intLit 8)))) =
      .ok (wordValue (UInt256.ofNat (q * 8))) := by
  dsimp only
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption]
  rw [paddedLocals_pos, paddedLocals_paddedLen]
  simp only [wordValue, ulit_toNat' _ hshiftSize]
  have hpadCast := Int.ofNat_sub hpad
  have htailCast := Int.ofNat_sub htail
  change EvalResult.ok (Value.int (8 * (Int.ofNat pos - (Int.ofNat paddedLen - 8)))) =
    EvalResult.ok (Value.int (Int.ofNat ((pos - (paddedLen - 8)) * 8)))
  have h1 : Int.ofNat paddedLen - 8 = Int.ofNat (paddedLen - 8) := by
    simpa using hpadCast.symm
  rw [h1]
  have h2 : Int.ofNat pos - Int.ofNat (paddedLen - 8) =
      Int.ofNat (pos - (paddedLen - 8)) := htailCast.symm
  rw [h2]
  congr 3
  exact Int.mul_comm _ _

def sourceLengthByteWord (bitLen q : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight (UInt256.ofNat bitLen) (UInt256.ofNat (q * 8)))
    (UInt256.ofNat 255)

theorem evalPaddedLengthByte (evm : EVM.State) (data : ByteArray)
    (pos bitLen paddedLen : Nat) (hpad : 8 ≤ paddedLen)
    (htail : paddedLen - 8 ≤ pos) (hpos : pos < paddedLen)
    (hbitSize : bitLen < UInt256.size) :
    let q := pos - (paddedLen - 8)
    evalExpr? config { contract := contract, locals := paddedLocals data pos bitLen paddedLen } evm
      (.binary .bitAnd
        (.binary .shr (.var "bitLen")
          (.binary .mul (.intLit 8)
            (.binary .sub (.var "pos") (.binary .sub (.var "paddedLen") (.intLit 8)))))
        (.intLit 255)) = .ok (wordValue (sourceLengthByteWord bitLen q)) := by
  dsimp only
  let q := pos - (paddedLen - 8)
  have hq : q < 8 := by dsimp [q]; omega
  have hqSize : q * 8 < UInt256.size :=
    lt_trans (by omega : q * 8 < 64) (by decide)
  have hbitLookup : (paddedLocals data pos bitLen paddedLen).get? "bitLen" =
      some (wordValue (UInt256.ofNat bitLen)) := by
    rw [paddedLocals_bitLen]
    simp only [wordValue, ulit_toNat' bitLen hbitSize]
  have hbit := evalWordVar (evm := evm) hbitLookup
  have hshift := evalPaddedLengthShift evm data pos bitLen paddedLen hpad htail hqSize
  have hshr := evalShr (q * 8) (by omega) hbit hshift
  have hmask := evalWordLit
    (L := paddedLocals data pos bitLen paddedLen) (evm := evm) 255 (by decide)
  simpa [sourceLengthByteWord, q] using evalBitAnd hshr hmask

theorem natByte_mod64 (n q : Nat) (hq : q < 8) :
    ((n >>> (q * 8)) &&& 255) = (((n % 2 ^ 64) >>> (q * 8)) &&& 255) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hi : i < 8
  · rw [Nat.testBit_mod_two_pow]
    simp [show q * 8 + i < 64 by omega]
  · have hpow : 255 < 2 ^ i :=
      lt_of_lt_of_le (by norm_num : 255 < 2 ^ 8)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hpow]
    simp

theorem sourceLengthByteWord_model (data : ByteArray) (pos : Nat)
    (hsmall : data.size ≤ maxFallbackCalldataSize)
    (hpad : 8 ≤ Model.paddedLength data.size)
    (htail : Model.paddedLength data.size - 8 ≤ pos)
    (hpos : pos < Model.paddedLength data.size) :
    let q := pos - (Model.paddedLength data.size - 8)
    (sourceLengthByteWord (data.size * 8) q).toNat =
      (Model.bitLength data.size >>> (q * 8)) &&& 255 := by
  dsimp only
  let q := pos - (Model.paddedLength data.size - 8)
  have hq : q < 8 := by dsimp [q]; omega
  unfold sourceLengthByteWord
  rw [uland_toNat, ushr_ofNat_toNat _ _ (by omega),
    ulit_toNat' (data.size * 8) (by
      rw [show UInt256.size = 2 ^ 256 by decide]
      unfold maxFallbackCalldataSize at hsmall
      omega),
    ulit_toNat' 255 (by decide)]
  unfold Model.bitLength
  simpa [q] using natByte_mod64 (data.size * 8) q hq

theorem paddedLength_ge64 (n : Nat) : 64 ≤ Model.paddedLength n := by
  unfold Model.paddedLength
  have hdiv : 1 ≤ (n + 72) / 64 := by
    rw [Nat.le_div_iff_mul_le (by decide)]
    omega
  omega

theorem paddedByteBodyReturns (evm : EVM.State) (data : ByteArray) (pos : Nat)
    (hsmall : data.size ≤ maxFallbackCalldataSize)
    (hpos : pos < Model.paddedLength data.size) :
    let bitLen := data.size * 8
    let paddedLen := Model.paddedLength data.size
    ExecFuncBody config { contract := contract, locals := paddedLocals data pos bitLen paddedLen }
      evm (paddedByteFunction).body
      (.returned { contract := contract, locals := paddedLocals data pos bitLen paddedLen } evm
        (some [.int (Int.ofNat (Model.paddedByte data pos))])) := by
  dsimp only
  let bitLen := data.size * 8
  let paddedLen := Model.paddedLength data.size
  have hpad64 : 64 ≤ paddedLen := by
    simpa [paddedLen] using paddedLength_ge64 data.size
  have hpad : 8 ≤ paddedLen := by omega
  have hbitSize : bitLen < UInt256.size := by
    dsimp [bitLen]
    rw [show UInt256.size = 2 ^ 256 by decide]
    unfold maxFallbackCalldataSize at hsmall
    omega
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm
    [ .ite (.binary .lt (.var "pos") (.arrayLength .localVar { base := "data", steps := [] }))
        [.return [.cast (.index (.var "data") (.var "pos"))
          (.elem (.int (.uint ⟨8, by decide⟩)))]] [],
      .ite (.binary .eq (.var "pos") (.arrayLength .localVar { base := "data", steps := [] }))
        [.return [.intLit 128]] [],
      .ite (.binary .ge (.var "pos")
          (.binary .sub (.var "paddedLen") (.intLit 8)))
        [.return [.binary .bitAnd
          (.binary .shr (.var "bitLen")
            (.binary .mul (.intLit 8)
              (.binary .sub (.var "pos")
                (.binary .sub (.var "paddedLen") (.intLit 8)))))
          (.intLit 255)]] [],
      .return [.intLit 0] ] _
  by_cases hdata : pos < data.size
  · apply ExecBlock.consReturn
    apply ExecStmt.iteTrue
    · simpa [decide_eq_true hdata] using
        evalPaddedPosLtLen evm data pos bitLen paddedLen
    · apply ExecBlock.consReturn
      apply ExecStmt.return
      have he := evalPaddedDataByte evm data pos bitLen paddedLen hdata
      have hm : Model.paddedByte data pos = (data[pos]'hdata).toNat := by
        simp [Model.paddedByte, hdata]
      simpa [hm, evalExprs?_singleton] using evalExprs?_singleton he
  · apply ExecBlock.consNormal
    · exact ExecStmt.iteFalse (by
        simpa [decide_eq_false hdata] using
          evalPaddedPosLtLen evm data pos bitLen paddedLen)
        ExecBlock.nil
    by_cases hmarker : pos = data.size
    · apply ExecBlock.consReturn
      apply ExecStmt.iteTrue
      · simpa [hmarker] using evalPaddedPosEqLen evm data pos bitLen paddedLen
      · apply ExecBlock.consReturn
        apply ExecStmt.return
        have hm : Model.paddedByte data pos = 128 := by
          simp [Model.paddedByte, hdata, hmarker]
        simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure, hm]
    · apply ExecBlock.consNormal
      · exact ExecStmt.iteFalse (by
          rw [evalPaddedPosEqLen evm data pos bitLen paddedLen]
          simp [hmarker])
          ExecBlock.nil
      by_cases htail : paddedLen - 8 ≤ pos
      · apply ExecBlock.consReturn
        apply ExecStmt.iteTrue
        · rw [evalPaddedPosGeTail evm data pos bitLen paddedLen hpad]
          rw [decide_eq_true (by omega)]
        · apply ExecBlock.consReturn
          apply ExecStmt.return
          have he := evalPaddedLengthByte evm data pos bitLen paddedLen hpad htail hpos hbitSize
          have hw := sourceLengthByteWord_model data pos hsmall hpad htail hpos
          dsimp only at he hw
          have hm : Model.paddedByte data pos =
              (Model.bitLength data.size >>>
                ((pos - (paddedLen - 8)) * 8)) &&& 255 := by
            simp [Model.paddedByte, hdata, hmarker, htail, paddedLen]
          change evalExpr? config _ evm _ = .ok (.int (Int.ofNat
            (sourceLengthByteWord bitLen (pos - (paddedLen - 8))).toNat)) at he
          have hw' : (sourceLengthByteWord bitLen (pos - (paddedLen - 8))).toNat =
              (Model.bitLength data.size >>> ((pos - (paddedLen - 8)) * 8)) &&& 255 := by
            simpa [bitLen, paddedLen] using hw
          rw [hw'] at he
          simpa [bitLen, paddedLen, hm, evalExprs?_singleton] using evalExprs?_singleton he
      · apply ExecBlock.consNormal
        · exact ExecStmt.iteFalse (by
            rw [evalPaddedPosGeTail evm data pos bitLen paddedLen hpad]
            rw [decide_eq_false (by omega)])
            ExecBlock.nil
        apply ExecBlock.consReturn
        apply ExecStmt.return
        have hm : Model.paddedByte data pos = 0 := by
          simp [Model.paddedByte, hdata, hmarker, htail, paddedLen]
        simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure, hm]

theorem f0BodyReturns (evm : EVM.State) (x y z : UInt256) :
    ExecFuncBody config { contract := contract, locals := xyzLocals x y z } evm (f0Function).body
      (.returned { contract := contract, locals := xyzLocals x y z } evm
        (some [wordValue (UInt256.xor (UInt256.xor x y) z)])) := by
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm [.return [_]] _
  apply ABlock.start.returns
  exact evalBitXor (evalBitXor (evalWordVar (xyzLocals_x x y z))
    (evalWordVar (xyzLocals_y x y z))) (evalWordVar (xyzLocals_z x y z))

theorem f1BodyReturns (evm : EVM.State) (x y z : UInt256)
    (hx32 : x.toNat < 2 ^ 32) :
    ExecFuncBody config { contract := contract, locals := xyzLocals x y z } evm (f1Function).body
      (.returned { contract := contract, locals := xyzLocals x y z } evm
        (some [wordValue (UInt256.lor (UInt256.land x y) (UInt256.land (UInt256.lnot x) z))])) := by
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm [.return [_]] _
  apply ABlock.start.returns
  exact evalBitOr
    (evalBitAnd (evalWordVar (xyzLocals_x x y z)) (evalWordVar (xyzLocals_y x y z)))
    (evalBitAnd (evalBitNot hx32 (evalWordVar (xyzLocals_x x y z)))
      (evalWordVar (xyzLocals_z x y z)))

theorem f2BodyReturns (evm : EVM.State) (x y z : UInt256)
    (hy32 : y.toNat < 2 ^ 32) :
    ExecFuncBody config { contract := contract, locals := xyzLocals x y z } evm (f2Function).body
      (.returned { contract := contract, locals := xyzLocals x y z } evm
        (some [wordValue (UInt256.xor (UInt256.lor x (UInt256.lnot y)) z)])) := by
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm [.return [_]] _
  apply ABlock.start.returns
  exact evalBitXor
    (evalBitOr (evalWordVar (xyzLocals_x x y z))
      (evalBitNot hy32 (evalWordVar (xyzLocals_y x y z))))
    (evalWordVar (xyzLocals_z x y z))

theorem f3BodyReturns (evm : EVM.State) (x y z : UInt256)
    (hz32 : z.toNat < 2 ^ 32) :
    ExecFuncBody config { contract := contract, locals := xyzLocals x y z } evm (f3Function).body
      (.returned { contract := contract, locals := xyzLocals x y z } evm
        (some [wordValue (UInt256.lor (UInt256.land x z) (UInt256.land y (UInt256.lnot z)))])) := by
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm [.return [_]] _
  apply ABlock.start.returns
  exact evalBitOr
    (evalBitAnd (evalWordVar (xyzLocals_x x y z)) (evalWordVar (xyzLocals_z x y z)))
    (evalBitAnd (evalWordVar (xyzLocals_y x y z))
      (evalBitNot hz32 (evalWordVar (xyzLocals_z x y z))))

theorem f4BodyReturns (evm : EVM.State) (x y z : UInt256)
    (hz32 : z.toNat < 2 ^ 32) :
    ExecFuncBody config { contract := contract, locals := xyzLocals x y z } evm (f4Function).body
      (.returned { contract := contract, locals := xyzLocals x y z } evm
        (some [wordValue (UInt256.xor x (UInt256.lor y (UInt256.lnot z)))])) := by
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm [.return [_]] _
  apply ABlock.start.returns
  exact evalBitXor (evalWordVar (xyzLocals_x x y z))
    (evalBitOr (evalWordVar (xyzLocals_y x y z))
      (evalBitNot hz32 (evalWordVar (xyzLocals_z x y z))))

def gLocals (g : Nat) : Store := (∅ : Store).insert "g" (.int (Int.ofNat g))

def rowLookupBody (c0 c1 c2 c3 c4 : Int) : List Stmt :=
  [ .ite (.binary .eq (.var "g") (.intLit 0)) [.return [.intLit c0]] [],
    .ite (.binary .eq (.var "g") (.intLit 1)) [.return [.intLit c1]] [],
    .ite (.binary .eq (.var "g") (.intLit 2)) [.return [.intLit c2]] [],
    .ite (.binary .eq (.var "g") (.intLit 3)) [.return [.intLit c3]] [],
    .return [.intLit c4] ]

def rowAt (c0 c1 c2 c3 c4 : Int) : Nat → Int
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => c3
  | _ => c4

theorem evalGEq (evm : EVM.State) (g n : Nat) :
    evalExpr? config { contract := contract, locals := gLocals g } evm
      (.binary .eq (.var "g") (.intLit (Int.ofNat n))) =
      .ok (.bool (Int.ofNat g == Int.ofNat n)) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption]
  rw [show (gLocals g).get? "g" = some (.int (Int.ofNat g)) by
    simp only [gLocals]; rw [store_get_self]]
  simp

theorem rowLookupBodyReturns (evm : EVM.State) (c0 c1 c2 c3 c4 : Int)
    (g : Nat) (hg : g < 5) :
    ExecFuncBody config { contract := contract, locals := gLocals g } evm
      (rowLookupBody c0 c1 c2 c3 c4)
      (.returned { contract := contract, locals := gLocals g } evm
        (some [.int (rowAt c0 c1 c2 c3 c4 g)])) := by
  interval_cases g <;> apply ExecFuncBody.execBlockRet
  · exact ExecBlock.consReturn (ExecStmt.iteTrue (by simpa using evalGEq evm 0 0)
      (ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, rowAt,
        EvalResult.bind, bind, pure]))))
  · exact ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 1 0) ExecBlock.nil)
      (ExecBlock.consReturn (ExecStmt.iteTrue (by simpa using evalGEq evm 1 1)
        (ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, rowAt,
          EvalResult.bind, bind, pure])))))
  · exact ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 2 0) ExecBlock.nil)
      (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 2 1) ExecBlock.nil)
        (ExecBlock.consReturn (ExecStmt.iteTrue (by simpa using evalGEq evm 2 2)
          (ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, rowAt,
            EvalResult.bind, bind, pure]))))))
  · exact ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 3 0) ExecBlock.nil)
      (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 3 1) ExecBlock.nil)
        (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 3 2) ExecBlock.nil)
          (ExecBlock.consReturn (ExecStmt.iteTrue (by simpa using evalGEq evm 3 3)
            (ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, rowAt,
              EvalResult.bind, bind, pure])))))))
  · exact ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 4 0) ExecBlock.nil)
      (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 4 1) ExecBlock.nil)
        (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 4 2) ExecBlock.nil)
          (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa using evalGEq evm 4 3) ExecBlock.nil)
            (ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, rowAt,
              EvalResult.bind, bind, pure]))))))

theorem wordRowLBodyReturns (evm : EVM.State) (g : Nat) (hg : g < 5) :
    ExecFuncBody config { contract := contract, locals := gLocals g } evm
      (wordRowLFunction).body
      (.returned { contract := contract, locals := gLocals g } evm
        (some [.int (Int.ofNat (Model.leftWordRow g))])) := by
  change ExecFuncBody config _ evm
    (rowLookupBody 0x0123456789abcdef 0x74d1a6f3c0952eb8 0x3ae49f812706db5c
      0x19ba08c4d37fe562 0x40597c2ae138b6fd) _
  interval_cases g <;> norm_num [rowAt, Model.leftWordRow] at * <;>
    exact rowLookupBodyReturns evm
      0x0123456789abcdef 0x74d1a6f3c0952eb8 0x3ae49f812706db5c
      0x19ba08c4d37fe562 0x40597c2ae138b6fd _ (by omega)

theorem rotRowLBodyReturns (evm : EVM.State) (g : Nat) (hg : g < 5) :
    ExecFuncBody config { contract := contract, locals := gLocals g } evm
      (rotRowLFunction).body
      (.returned { contract := contract, locals := gLocals g } evm
        (some [.int (Int.ofNat (Model.leftRotationRow g))])) := by
  change ExecFuncBody config _ evm
    (rowLookupBody 0xbefc5879bdef6798 0x768db97f7cf9b7dc 0xbd67e9dfe8d65c75
      0xbcefef989e56865c 0x9f5b68dc5cdeb856) _
  interval_cases g <;> norm_num [rowAt, Model.leftRotationRow] at * <;>
    exact rowLookupBodyReturns evm
      0xbefc5879bdef6798 0x768db97f7cf9b7dc 0xbd67e9dfe8d65c75
      0xbcefef989e56865c 0x9f5b68dc5cdeb856 _ (by omega)

theorem wordRowRBodyReturns (evm : EVM.State) (g : Nat) (hg : g < 5) :
    ExecFuncBody config { contract := contract, locals := gLocals g } evm
      (wordRowRFunction).body
      (.returned { contract := contract, locals := gLocals g } evm
        (some [.int (Int.ofNat (Model.rightWordRow g))])) := by
  change ExecFuncBody config _ evm
    (rowLookupBody 0x5e7092b4d6f81a3c 0x6b370d5aef8c4912 0xf5137e69b8c2a04d
      0x86413bf05c2d97ae 0xcfa4158762de039b) _
  interval_cases g <;> norm_num [rowAt, Model.rightWordRow] at * <;>
    exact rowLookupBodyReturns evm
      0x5e7092b4d6f81a3c 0x6b370d5aef8c4912 0xf5137e69b8c2a04d
      0x86413bf05c2d97ae 0xcfa4158762de039b _ (by omega)

theorem rotRowRBodyReturns (evm : EVM.State) (g : Nat) (hg : g < 5) :
    ExecFuncBody config { contract := contract, locals := gLocals g } evm
      (rotRowRFunction).body
      (.returned { contract := contract, locals := gLocals g } evm
        (some [.int (Int.ofNat (Model.rightRotationRow g))])) := by
  change ExecFuncBody config _ evm
    (rowLookupBody 0x899bdff5778beec6 0x9df7c89b77c76fdb 0x97fb866ecd5edd75
      0xf58bee6e69c9c5f8 0x85c9c5e68d65fdbb) _
  interval_cases g <;> norm_num [rowAt, Model.rightRotationRow] at * <;>
    exact rowLookupBodyReturns evm
      0x899bdff5778beec6 0x9df7c89b77c76fdb 0x97fb866ecd5edd75
      0xf58bee6e69c9c5f8 0x85c9c5e68d65fdbb _ (by omega)

def xLocals (x : UInt256) : Store := (∅ : Store).insert "x" (wordValue x)

@[simp] theorem xLocals_x (x : UInt256) :
    (xLocals x).get? "x" = some (wordValue x) := by
  simp only [xLocals]
  rw [store_get_self]

def sourceSwap32 (x : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.lor
        (UInt256.shiftLeft (UInt256.land x (UInt256.ofNat 0xff)) (UInt256.ofNat 24))
        (UInt256.shiftLeft
          (UInt256.land (UInt256.shiftRight x (UInt256.ofNat 8)) (UInt256.ofNat 0xff))
          (UInt256.ofNat 16)))
      (UInt256.shiftLeft
        (UInt256.land (UInt256.shiftRight x (UInt256.ofNat 16)) (UInt256.ofNat 0xff))
        (UInt256.ofNat 8)))
    (UInt256.land (UInt256.shiftRight x (UInt256.ofNat 24)) (UInt256.ofNat 0xff))

theorem sourceSwap32_toNat (x : UInt256) :
    (sourceSwap32 x).toNat =
      ((x.toNat &&& 0xff) <<< 24) |||
      (((x.toNat >>> 8) &&& 0xff) <<< 16) |||
      (((x.toNat >>> 16) &&& 0xff) <<< 8) |||
      ((x.toNat >>> 24) &&& 0xff) := by
  unfold sourceSwap32
  simp only [word_toNat_lor]
  rw [ushl_ofNat_toNat, ushl_ofNat_toNat, ushl_ofNat_toNat] <;> norm_num
  simp only [uland_toNat]
  rw [ushr_ofNat_toNat, ushr_ofNat_toNat, ushr_ofNat_toNat] <;> norm_num
  rw [show (UInt256.ofNat 0xff).toNat = 0xff by decide]
  have h24 : (x.toNat &&& 255) <<< 24 < UInt256.size := by
    rw [Nat.shiftLeft_eq]
    have h : x.toNat &&& 255 ≤ 255 := Nat.and_le_right
    norm_num [UInt256.size]
    omega
  have h16 : (x.toNat >>> 8 &&& 255) <<< 16 < UInt256.size := by
    rw [Nat.shiftLeft_eq]
    have h : x.toNat >>> 8 &&& 255 ≤ 255 := Nat.and_le_right
    norm_num [UInt256.size]
    omega
  have h8 : (x.toNat >>> 16 &&& 255) <<< 8 < UInt256.size := by
    rw [Nat.shiftLeft_eq]
    have h : x.toNat >>> 16 &&& 255 ≤ 255 := Nat.and_le_right
    norm_num [UInt256.size]
    omega
  rw [Nat.mod_eq_of_lt h24, Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h8]
  change ((((x.toNat &&& 255) <<< 24) ||| ((x.toNat >>> 8 &&& 255) <<< 16)) |||
      ((x.toNat >>> 16 &&& 255) <<< 8)) ||| (x.toNat >>> 24 &&& 255) = _
  simp only [Nat.or_assoc]

theorem sourceSwap32_eq_runtime (x : UInt256) (hx : x.toNat < 2 ^ 32) :
    sourceSwap32 x = runtimeSwap32 x := by
  apply u256_inj
  rw [sourceSwap32_toNat, runtimeSwap32_toNat hx]

theorem swap32BodyReturns (evm : EVM.State) (x : UInt256) (hx : x.toNat < 2 ^ 32) :
    ExecFuncBody config { contract := contract, locals := xLocals x } evm
      (swap32Function).body
      (.returned { contract := contract, locals := xLocals x } evm
        (some [wordValue (runtimeSwap32 x)])) := by
  apply ExecFuncBody.execBlockRet
  change ExecBlock config _ evm [.return [_]] _
  apply ABlock.start.returns
  have hxEval := evalWordVar (evm := evm) (xLocals_x x)
  have hff := evalWordLit (L := xLocals x) (evm := evm) 0xff (by norm_num [UInt256.size])
  have h8 := evalWordLit (L := xLocals x) (evm := evm) 8 (by norm_num [UInt256.size])
  have h16 := evalWordLit (L := xLocals x) (evm := evm) 16 (by norm_num [UInt256.size])
  have h24 := evalWordLit (L := xLocals x) (evm := evm) 24 (by norm_num [UInt256.size])
  have hb0 := evalShl 24 (by decide) (evalBitAnd hxEval hff) h24
  have hb1 := evalShl 16 (by decide) (evalBitAnd (evalShr 8 (by decide) hxEval h8) hff) h16
  have hb2 := evalShl 8 (by decide) (evalBitAnd (evalShr 16 (by decide) hxEval h16) hff) h8
  have hb3 := evalBitAnd (evalShr 24 (by decide) hxEval h24) hff
  have hall := evalBitOr (evalBitOr (evalBitOr hb0 hb1) hb2) hb3
  have hs : evalExpr? config { contract := contract, locals := xLocals x } evm
      (.binary .bitOr
        (.binary .bitOr
          (.binary .bitOr
            (.binary .shl (.binary .bitAnd (.var "x") (.intLit 0xff)) (.intLit 24))
            (.binary .shl
              (.binary .bitAnd (.binary .shr (.var "x") (.intLit 8)) (.intLit 0xff))
              (.intLit 16)))
          (.binary .shl
            (.binary .bitAnd (.binary .shr (.var "x") (.intLit 16)) (.intLit 0xff))
            (.intLit 8)))
        (.binary .bitAnd (.binary .shr (.var "x") (.intLit 24)) (.intLit 0xff))) =
      .ok (wordValue (sourceSwap32 x)) := by
    simpa only [sourceSwap32] using hall
  rw [sourceSwap32_eq_runtime x hx] at hs
  exact hs

end Ripemd160
