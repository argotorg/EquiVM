import Benchmarks.UniswapV4PoolManager.EntrySource
import Reasoning.ABIViews

/-! Word casts and calldata values shared by PoolManager source proofs. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: word conversion, ABI decoding, or expression evaluation fact.
theorem fromBytesBigEndian_wordBE (w : UInt256) :
    fromBytesBigEndian (EVM.Word.toBytesBE w) = w.toNat := by
  have h := congrArg fromByteArrayBigEndian (word_toBytesBE_toByteArray_eq_toByteArray w)
  simpa [fromByteArrayBigEndian, byteArray_toList_eq] using
    h.trans (fromByteArrayBigEndian_toByteArray w)

-- LIBRARY CANDIDATE: word conversion, ABI decoding, or expression evaluation fact.
theorem castBytes32ToUint256 (w : UInt256) :
    castValue? (wordBytes32Value w) (.elem (.int (.uint ⟨256, by decide⟩))) =
      some (.int (Int.ofNat w.toNat)) := by
  simp only [castValue?, abiBytes32Width, fixedBytesToNat?, fixedBytesValid,
    fixedBytesSize, word_toBytesBE_length_32, fromBytesBigEndian_wordBE]
  rfl

-- LIBRARY CANDIDATE: word conversion, ABI decoding, or expression evaluation fact.
theorem castUint256ToBytes32 (w : UInt256) :
    castValue? (.int (Int.ofNat w.toNat)) (.elem (.bytes abiBytes32Width)) =
      some (wordBytes32Value w) := by
  simp only [castValue?, Int.ofNat_eq_natCast, Int.not_lt.mpr (Int.natCast_nonneg w.toNat), ↓reduceIte,
    Int.toNat_natCast, EVM.Word.ofNat, u256_ofNat_toNat]
  rfl

-- LIBRARY CANDIDATE: word conversion, ABI decoding, or expression evaluation fact.
theorem decodeCalldataBytes32Word {cd : ByteArray} {name : Ident}
    (hlen : 36 ≤ cd.size) (hhi : cd.size < calldataLimit) :
    decodeCalldata [name] [abiBytes32] cd =
      some ((∅ : Store).insert name (wordBytes32Value (calldataWord cd 4))) := by
  rw [decodeCalldata_bytes32_ok hlen hhi]
  have hword := decode_word_at_eq_any cd 4 hlen
  have hlen' : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (cd.size - 4) = 32
    omega
  change some ((∅ : Store).insert name (.fixedBytes abiBytes32Width _)) =
    some ((∅ : Store).insert name (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE _)))
  simp only [calldataWord, ← hword, toBytesBE_bytesToWord_of_length hlen']

-- LIBRARY CANDIDATE: word conversion, ABI decoding, or expression evaluation fact.
theorem evalCastValue {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr}
    {v out : Value} {ty : StorageType} (he : evalExpr? cfg f evm e = .ok v)
    (hc : castValue? v ty = some out) :
    evalExpr? cfg f evm (.cast e ty) = .ok out := by
  simp only [evalExpr?, he, bind, EvalResult.bind, hc, EvalResult.ofOption]

-- LIBRARY CANDIDATE: word conversion, ABI decoding, or expression evaluation fact.
theorem evalLocalValue {cfg : Config} {f : Frame} {evm : EVM.State}
    {name : Ident} {value : Value} (hget : f.locals.get? name = some value) :
    evalExpr? cfg f evm (.var name) = .ok value := by
  simp only [evalExpr?, hget, EvalResult.ofOption]

-- GENERALIZES Reasoning.Theory.assignLocalVarBase_ok to frames with immutables.
theorem assignLocalValue {cfg : Config} {f : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value} (hget : f.locals.get? name = some old) :
    assignStorageRef? cfg f evm .localVar {base := name} value =
      .ok ({f with locals := f.locals.insert name value}, evm) := by
  simp only [assignStorageRef?, hget, updateLocalPath?, bind, EvalResult.bind, pure]

-- LIBRARY CANDIDATE: fixed bytes comparisons and boolean expression/return encoding.
theorem fixedBytesValue_beq (n : Fin 32) (xs ys : List UInt8) :
    (Value.fixedBytes n xs == Value.fixedBytes n ys) = (xs == ys) := by
  simp [BEq.beq, listUInt8_decide_eq_beq]

-- LIBRARY CANDIDATE: fixed bytes comparisons and boolean expression/return encoding.
theorem evalEqFixedBytes {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr}
    {n : Fin 32} {xs ys : List UInt8}
    (ha : evalExpr? cfg f evm a = .ok (.fixedBytes n xs))
    (hb : evalExpr? cfg f evm b = .ok (.fixedBytes n ys)) :
    evalExpr? cfg f evm (.binary .eq a b) = .ok (.bool (xs == ys)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, fixedBytesValue_beq]

-- LIBRARY CANDIDATE: fixed bytes comparisons and boolean expression/return encoding.
theorem evalOrBool {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {va vb : Bool}
    (ha : evalExpr? cfg f evm a = .ok (.bool va))
    (hb : evalExpr? cfg f evm b = .ok (.bool vb)) :
    evalExpr? cfg f evm (.binary .or a b) = .ok (.bool (va || vb)) := by
  cases va <;> simp only [evalExpr?, ha, hb, bind, EvalResult.bind, pure, Bool.false_or, Bool.true_or]

-- LIBRARY CANDIDATE: fixed bytes comparisons and boolean expression/return encoding.
theorem boolWord_normalize (b : Bool) :
    UInt256.isZero (UInt256.isZero b.toUInt256) = b.toUInt256 := by cases b <;> decide

-- LIBRARY CANDIDATE: fixed bytes comparisons and boolean expression/return encoding.
theorem boolReturnEncoding (b : Bool) :
    encodeReturnValue? (.elem .bool) (.bool b) = some b.toUInt256.toByteArray := by
  cases b
  · exact boolFalseReturnEncoding
  · exact boolTrueReturnEncoding

-- LIBRARY CANDIDATE: canonical EVM address-to-word conversions.
def accountWord (a : AccountAddress) : UInt256 := UInt256.ofNat a.val

theorem accountWord_toNat (a : AccountAddress) : (accountWord a).toNat = a.val :=
  ulit_toNat' _ (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))

theorem accountWord_canonical (a : AccountAddress) : (accountWord a).toNat < EVM.addressModulus := by
  rw [accountWord_toNat]
  exact a.isLt

theorem accountWord_address (a : AccountAddress) : AccountAddress.ofNat (accountWord a).toNat = a := by
  rw [accountWord_toNat]
  exact accountAddress_ofNat_val a

-- LIBRARY CANDIDATE: the compiler rejects every boolean word outside {0, 1}.
theorem boolSubNormalize_zero {w : UInt256} (hc : w = ⟨0⟩ ∨ w = ⟨1⟩) :
    UInt256.sub w (UInt256.isZero (UInt256.isZero w)) = ⟨0⟩ := by
  rcases hc with rfl | rfl <;> decide

-- LIBRARY CANDIDATE: the compiler rejects every boolean word outside {0, 1}.
theorem boolSubNormalize_nonzero {w : UInt256} (hc : ¬ (w = ⟨0⟩ ∨ w = ⟨1⟩)) :
    UInt256.sub w (UInt256.isZero (UInt256.isZero w)) ≠ ⟨0⟩ := by
  intro hz
  have hnz : w ≠ ⟨0⟩ := fun h => hc (Or.inl h)
  have hw := u256_sub_eq_zero_iff_eq.mp hz
  rw [isZero_eq_zero_of_ne hnz] at hw
  exact hc (Or.inr hw)

-- LIBRARY CANDIDATE: low-byte masking preserves a normalized boolean.
theorem boolNormalize_mask (w : UInt256) :
    UInt256.land (UInt256.isZero (UInt256.isZero w)) ⟨255⟩ = UInt256.isZero (UInt256.isZero w) := by
  by_cases h : w = ⟨0⟩
  · subst h; decide
  · rw [isZero_eq_zero_of_ne h]; decide

-- LIBRARY CANDIDATE: equality between canonical address words is address equality.
theorem accountWord_eq_iff (a : AccountAddress) (w : UInt256)
    (hc : w.toNat < EVM.addressModulus) :
    a = AccountAddress.ofNat w.toNat ↔ accountWord a = w := by
  have h := addressOfNat_eq_iff_solcAddrMask_eq (accountWord a) w
  rw [accountWord_address, u256_land_comm solcAddrMask (accountWord a),
    solcAddrMask_clean (accountWord_canonical a), u256_land_comm solcAddrMask w,
    solcAddrMask_clean hc] at h
  exact h

-- LIBRARY CANDIDATE: equality of address-valued expressions.
theorem evalEqAddress {cfg : Config} {f : Frame} {evm : EVM.State} {lhs rhs : Expr}
    {a b : AccountAddress}
    (ha : evalExpr? cfg f evm lhs = .ok (.address a))
    (hb : evalExpr? cfg f evm rhs = .ok (.address b)) :
    evalExpr? cfg f evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  simp only [BEq.beq, Value.address.injEq]

-- LIBRARY CANDIDATE: inequality of address-valued expressions.
theorem evalNeAddress {cfg : Config} {f : Frame} {evm : EVM.State} {lhs rhs : Expr}
    {a b : AccountAddress}
    (ha : evalExpr? cfg f evm lhs = .ok (.address a))
    (hb : evalExpr? cfg f evm rhs = .ok (.address b)) :
    evalExpr? cfg f evm (.binary .ne lhs rhs) = .ok (.bool (decide (a ≠ b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  simp only [BEq.beq, Value.address.injEq, decide_not]

-- LIBRARY CANDIDATE: conjunction and negation of evaluated boolean expressions.
theorem evalAndBool {cfg : Config} {f : Frame} {evm : EVM.State} {a b : Expr} {va vb : Bool}
    (ha : evalExpr? cfg f evm a = .ok (.bool va))
    (hb : evalExpr? cfg f evm b = .ok (.bool vb)) :
    evalExpr? cfg f evm (.binary .and a b) = .ok (.bool (va && vb)) := by
  cases va <;> simp only [evalExpr?, ha, hb, bind, EvalResult.bind, pure, Bool.false_and, Bool.true_and]

theorem evalNotBool {cfg : Config} {f : Frame} {evm : EVM.State} {a : Expr} {va : Bool}
    (ha : evalExpr? cfg f evm a = .ok (.bool va)) :
    evalExpr? cfg f evm (.unary .not a) = .ok (.bool (!va)) := by
  simp only [evalExpr?, ha, bind, EvalResult.bind, evalUnaryOp?, EvalResult.ofOption]

-- LIBRARY CANDIDATE: inequality of unsigned word-valued source expressions.
theorem evalNeWords {cfg : Config} {f : Frame} {evm : EVM.State} {lhs rhs : Expr}
    {a b : UInt256}
    (ha : evalExpr? cfg f evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg f evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg f evm (.binary .ne lhs rhs) = .ok (.bool (decide (a ≠ b))) := by
  have he : (Int.ofNat a.toNat = Int.ofNat b.toNat) ↔ a = b :=
    ⟨fun h => u256_inj (Int.ofNat.inj h), fun h => by rw [h]⟩
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, BEq.beq,
    Value.int.injEq, he, decide_not]

end Benchmarks.UniswapV4PoolManager
