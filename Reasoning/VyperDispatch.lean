import Reasoning.WordArithmetic
import Reasoning.Reach
import Reasoning.VyperImmutables
import Reasoning.Storage
import Reasoning.Vyper
import Reasoning.Dispatch
import Stele.VyperLayout

variable {fork : Ethereum.Fork}

/-!
# Vyper's computed dispatcher

Vyper 0.4 dispatches through a jump table: the selector word is reduced to a bucket index
(`selector % n`, or `selector & mask` when the bucket count is a power of two), the two-byte
entry at `table + 2 * index` is copied into memory, loaded and jumped to.  The lemmas here
turn the bucket index and the table offset into the natural numbers a concrete lookup needs,
and show that the lookup reads the template even when a code suffix (Vyper immutables) is
appended.  `scripts/proof_skeleton.py` instantiates them per contract.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperImmutables

namespace Reasoning.VyperDispatch

/-! ## Selectors -/

/-- A match on one table entry (`selIs I a`) is a miss on every other. -/
theorem selIs_exclusive {cd a b : ByteArray} (hne : (a == b) = false)
    (h : (a == cd.extract 0 4) = true) : ¬ (b == cd.extract 0 4) = true := by
  intro h'
  have e : b = cd.extract 0 4 := byteArray_eq_of_beq h'
  have h2 : (a == b) = true := by rw [e]; exact h
  rw [h2] at hne
  cases hne

/-! ## Reverts under a dispatched transition -/

/-- A reverting run refines a dispatched transition whose body reverts for every argument
    store (the `callvalue ≠ 0` case of a non-payable function, where decoding may or may not
    succeed). -/
theorem RDrev.reEquivOfDispatch {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {immutables : Store} {σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code) (hd : dispatchMsg contract I.calldata = some t)
    (hbody : ∀ callargs, ExecTransitionBody fork cfg contract (initState σ σ₀ g A I) callargs t.body
      .reverted immutables)
    (hrev : RDrev fork code g (initState σ σ₀ g A I))
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeRefinementFor fork cfg contract σ σ₀ g.toUInt256 A I immutables := by
  by_cases hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none
  · exact hrev.reEquivDecodingFailed hcode hd hdec hfallback hreceive
  · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
    exact hrev.reEquivElim hcode fun _ _ hrevert =>
      reEquiv_execution hd hca (hbody callargs) (by rw [hrevert]; exact .revert rfl rfl)
        hfallback hreceive

/-! ## Full-word storage leaves -/

/-- A full-word Vyper leaf reads as the typed view of its storage word. -/
theorem storageLocLoad_vyperWord (evm : EVM.State) (slot : UInt256) (ty : ElemType) :
    storageLocLoad evm (vyperWordLoc slot ty) =
      wordToElem ty (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0
          (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    apply List.take_of_length_le
    rw [(EVM.Word.toBytesLEWithSizeProof (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    decide
  unfold storageLocLoad vyperWordLoc
  simp only [Fin.val_zero, Nat.zero_add]
  congr 1
  apply u256_inj
  show fromBytes' ((EVM.Word.toBytesLEWithSizeProof _).1.extract 0 (32 : Fin 33).val) = _
  rw [htake, fromBytes'_toBytesLEWithSizeProof]

/-! ## Return encodings -/

/-- ABI-encoding an `address` return value is its word. -/
theorem addressReturnEncoding (a : AccountAddress) :
    encodeReturnValue? (.elem .address) (.address a) =
      some (UInt256.toByteArray (EVM.Word.ofNat a.toNat)) :=
  scalarReturnEncoding (t := .address) (w := EVM.Word.ofNat a.toNat) rfl
    (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]; decide)
    (by simp [encodeABIValue?, encodeABIWord?]; rfl)

/-! ## Computed dispatch -/

/-- `sel % n` as the dispatcher computes it, for a nonzero modulus below the word size. -/
theorem mod_eq_ofNat {sel : UInt256} {n m : Nat} (hn : 0 < n) (hn' : n < UInt256.size)
    (hmod : sel.toNat % n = m) :
    UInt256.mod sel (UInt256.ofNat n) = UInt256.ofNat m := by
  apply u256_inj
  unfold UInt256.mod
  have hnv : (UInt256.ofNat n).val.val = n := ulit_toNat' n hn'
  rw [if_neg (by
    intro h
    have := beq_iff_eq.mp h
    have h0 : (UInt256.ofNat n).val.val = 0 := by rw [this]; rfl
    omega)]
  show sel.toNat % (UInt256.ofNat n).val.val = (UInt256.ofNat m).toNat
  rw [hnv, hmod]
  have hm : m < UInt256.size := by
    have : m < n := by rw [← hmod]; exact Nat.mod_lt _ hn
    omega
  exact (ulit_toNat' m hm).symm

/-- `sel & mask` with `mask + 1 = n = 2^b` is `sel % n`. -/
theorem land_eq_ofNat {sel : UInt256} {mask b n m : Nat} (hmask : mask + 1 = 2 ^ b)
    (hn : n = 2 ^ b) (hb : 2 ^ b < UInt256.size) (hmod : sel.toNat % n = m) :
    UInt256.land sel (UInt256.ofNat mask) = UInt256.ofNat m := by
  subst hn
  apply u256_inj
  have hmaskv : (UInt256.ofNat mask).val.val = mask := ulit_toNat' mask (by omega)
  show (Fin.land sel.val (UInt256.ofNat mask).val).val = (UInt256.ofNat m).toNat
  have hm : m < UInt256.size := by
    have : m < 2 ^ b := by rw [← hmod]; exact Nat.mod_lt _ (Nat.two_pow_pos b)
    omega
  rw [ulit_toNat' m hm]
  simp only [Fin.land]
  rw [hmaskv]
  have hmask' : mask = 2 ^ b - 1 := by omega
  show (sel.toNat &&& mask) % UInt256.size = m
  rw [hmask', Nat.and_two_pow_sub_one_eq_mod, hmod]
  exact Nat.mod_eq_of_lt hm

/-- The table offset `t + 2 * idx` of a bucket index below the word size. -/
theorem offset_toNat {idx : UInt256} {t m : Nat} (hidx : idx = UInt256.ofNat m)
    (hsize : t + 2 * m < UInt256.size) :
    ((UInt256.ofNat t) + (UInt256.shiftLeft idx (UInt256.ofNat 1))).toNat = t + 2 * m := by
  subst hidx
  have h1 : (UInt256.ofNat 1 : UInt256) = ⟨1⟩ := rfl
  rw [h1, shiftLeft1_ofNat_eq (by omega)]
  exact uadd_ofNat_toNat (by omega) (by omega) hsize

/-- Copying a window of the template into empty memory ignores the code suffix. -/
theorem write_append_left_empty (a b : ByteArray) (src dest len : Nat) (hlen : len ≠ 0)
    (h : src + len ≤ a.size) :
    (a ++ b).write src ByteArray.empty dest len = a.write src ByteArray.empty dest len := by
  have hab : src + len ≤ (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [copy_padding (a ++ b) ByteArray.empty src dest len hlen hab,
      copy_padding a ByteArray.empty src dest len hlen h]
  have hd : dest ≤ (ByteArray.empty ++ ByteArray.zeroes (dest - ByteArray.empty.size)).size := by
    rw [ByteArray.size_append, ByteArray_zeroes_size]; simp
  rw [copyWindow_eq (a ++ b) _ src dest len hlen hab hd, copyWindow_eq a _ src dest len hlen h hd,
      extract_append_left a b src (src + len) h]

/-! ## Branchless `min` -/

/-- `x ^ (x ^ y) = y`. -/
theorem u256_xor_xor_cancel (a b : UInt256) : UInt256.xor (UInt256.xor a b) a = b := by
  apply u256_inj
  obtain ⟨⟨a, ha⟩⟩ := a
  obtain ⟨⟨b, hb⟩⟩ := b
  simp only [UInt256.xor, Fin.xor, UInt256.toNat]
  have h1 : a ^^^ b < UInt256.size := by
    simpa [UInt256.size] using Nat.xor_lt_two_pow (n := 256) ha hb
  show ((a ^^^ b) % UInt256.size ^^^ a) % UInt256.size = b
  rw [Nat.mod_eq_of_lt h1, Nat.xor_comm a b, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  exact Nat.mod_eq_of_lt hb

/-- `0 ^ x = x`. -/
theorem u256_zero_xor (a : UInt256) : UInt256.xor ⟨0⟩ a = a := by
  apply u256_inj
  obtain ⟨⟨a, ha⟩⟩ := a
  simp only [UInt256.xor, Fin.xor, UInt256.toNat]
  show (0 ^^^ a) % UInt256.size = a
  rw [Nat.zero_xor]
  exact Nat.mod_eq_of_lt ha

/-- `1 * x = x`. -/
theorem u256_one_mul (w : UInt256) : UInt256.mul ⟨1⟩ w = w := by
  apply u256_inj
  rw [u256_mul_toNat]
  obtain ⟨⟨w, hw⟩⟩ := w
  show (1 % UInt256.size * w) % UInt256.size = w
  rw [Nat.mod_eq_of_lt (by decide : 1 < UInt256.size), Nat.one_mul]
  exact Nat.mod_eq_of_lt hw

/-- Vyper's branchless `min(x1, x0)`: `((x1 < x0) * (x0 ^ x1)) ^ x0`. -/
theorem branchlessMin (x0 x1 : UInt256) :
    UInt256.xor (UInt256.mul (UInt256.lt x1 x0) (UInt256.xor x0 x1)) x0 =
      if x1.toNat < x0.toNat then x1 else x0 := by
  split
  · rename_i h
    rw [ult_one h, u256_one_mul, u256_xor_xor_cancel]
  · rename_i h
    rw [ult_zero (by omega), u256_mul_zero_left, u256_zero_xor]

/-! ## Validated small words -/

/-- A word below `2` has no bits above bit 0 (Vyper's `bool` calldata validation). -/
theorem u256_shiftRight1_zero_of_lt (w : UInt256) (h : w.toNat < 2) :
    UInt256.shiftRight w ⟨1⟩ = ⟨0⟩ := by
  apply u256_inj
  cases w with
  | mk val =>
    unfold UInt256.shiftRight
    simp
    change (val >>> 1).val = 0
    rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    have h' : val.val < 2 := h
    show val.val < 2 ^ (1 % UInt256.size)
    rw [Nat.mod_eq_of_lt (by decide : 1 < UInt256.size), pow_one]
    exact h'

theorem u256_lt_two_of_shiftRight1_zero (w : UInt256) (h : UInt256.shiftRight w ⟨1⟩ = ⟨0⟩) :
    w.toNat < 2 := by
  cases w with
  | mk val =>
    unfold UInt256.shiftRight at h
    simp at h
    have hval := congrArg Fin.val h
    simp [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow] at hval
    rw [Nat.mod_eq_of_lt (by decide : 1 < UInt256.size), pow_one] at hval
    exact hval

/-- A validated bool word is the word of its decoded `Bool`. -/
theorem bool_toUInt256_decide (w : UInt256) (h : w.toNat < 2) :
    Bool.toUInt256 (decide (w.toNat = 1)) = w := by
  rcases (by omega : w.toNat = 0 ∨ w.toNat = 1) with h0 | h1
  · rw [decide_eq_false (by omega)]
    apply u256_inj
    rw [h0]
    rfl
  · rw [decide_eq_true h1]
    apply u256_inj
    rw [h1]
    rfl

/-! ## Equality checks through `ISZERO (XOR a b)` -/

theorem u256_xor_self (a : UInt256) : UInt256.xor a a = ⟨0⟩ := by
  apply u256_inj
  obtain ⟨⟨a, ha⟩⟩ := a
  simp only [UInt256.xor, Fin.xor, UInt256.toNat]
  show (a ^^^ a) % UInt256.size = 0
  rw [Nat.xor_self]
  rfl

theorem isZero_xor_ne_zero_of_eq {a b : UInt256} (h : a = b) :
    UInt256.isZero (UInt256.xor a b) ≠ UInt256.ofNat 0 := by
  subst h
  rw [u256_xor_self]
  decide

theorem isZero_xor_eq_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.isZero (UInt256.xor a b) = UInt256.ofNat 0 :=
  isZero_eq_zero_of_ne (u256_xor_ne_zero_of_ne h)

/-- Address words are injective. -/
theorem ofNat_addr_inj {x y : AccountAddress} (h : UInt256.ofNat x.val = UInt256.ofNat y.val) :
    x = y := by
  have hx : x.val < UInt256.size := lt_trans x.isLt (by decide)
  have hy : y.val < UInt256.size := lt_trans y.isLt (by decide)
  have := congrArg UInt256.toNat h
  rw [ulit_toNat' _ hx, ulit_toNat' _ hy] at this
  exact Fin.ext this

/-- Stele's address equality is decidable equality of the addresses. -/
theorem value_address_beq (a b : AccountAddress) :
    (Value.address a == Value.address b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    rw [decide_eq_true rfl]
    exact beq_self_eq_true _
  · rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr (fun e => h (Value.address.inj e))

/-! ## Full-word stores through the Vyper backend -/

/-- A full-word `bool` leaf stores the `Bool`'s word. -/
theorem storageLocStore_vyperWord_bool (evm : EVM.State) (slot : UInt256) (b : Bool) :
    storageLocStore evm (vyperWordLoc slot .bool) (.bool b) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot b.toUInt256) := by
  unfold storageLocStore storageLocWriteWord vyperWordLoc
  simp only [valueToWord, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof b.toUInt256).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = b.toUInt256.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

/-- `assignStorageRef_storage_vyper_scalar` for any scalar value (a `bool`, an address). -/
theorem assignStorageRef_storage_vyper_scalar_value {cfg : Config} {layout : StorageLayout}
    {bounds : VyperBounds} {stele : Frame} {evm evm' : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType}
    {loc : StorageLoc} {value : Value}
    (hbase : stele.locals.get? slot.base = none)
    (her : evalStorageRef cfg stele evm slot = .ok er)
    (hty : storageTypeAt? stele.contract.storage er = some ty)
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hloc : layout er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? cfg stele evm .storage slot value = .ok (stele, evm') := by
  apply assignStorageRef_storage_of_write hbase her hty
  rw [hbackend]
  rcases hleaf with ⟨t, rfl⟩ | ⟨name, rfl⟩
  · simp [vyperStorageBackend, hcheck, vyperWriteRaw?, vyperLeafLoc?, hloc,
      hstore, EvalResult.bind, EvalResult.ofOption, bind]
  · simp [vyperStorageBackend, hcheck, vyperWriteRaw?, vyperLeafLoc?, hloc,
      hstore, EvalResult.bind, EvalResult.ofOption, bind]

/-! ## Frame-generic expression evaluation (checked `uint256` arithmetic, environment reads) -/

theorem evalExpr_callvalue {cfg : Config} {stele : Frame} (evm : EVM.State) :
    evalExpr? cfg stele evm (.env .callvalue) = .ok (uint256Value evm.executionEnv.weiValue) := by
  rw [evalExpr?]; rfl

theorem evalExpr_caller {cfg : Config} {stele : Frame} (evm : EVM.State) :
    evalExpr? cfg stele evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
  rw [evalExpr?]; rfl

theorem evalExpr_intLit_word {cfg : Config} {stele : Frame} (evm : EVM.State) (n : Nat)
    (hn : n < UInt256.size) :
    evalExpr? cfg stele evm (.intLit n) = .ok (uint256Value (UInt256.ofNat n)) := by
  rw [evalExpr?]
  simp only [uint256Value, ulit_toNat' n hn]
  rfl

theorem evalExpr_not_bool {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr} {b : Bool}
    (he : evalExpr? cfg stele evm e = .ok (.bool b)) :
    evalExpr? cfg stele evm (.unary .not e) = .ok (.bool (!b)) := by
  simp [evalExpr?, he, EvalResult.bind, bind, evalUnaryOp?, EvalResult.ofOption]

theorem evalExpr_gt_zero {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr} {a : UInt256}
    (ha : evalExpr? cfg stele evm e = .ok (uint256Value a)) :
    evalExpr? cfg stele evm (.binary .gt e (.intLit 0)) = .ok (.bool (decide (0 < a.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, evalExpr?]
  simp [EvalResult.bind, bind, evalBinaryOp?, uint256Value]

theorem evalExpr_uint256_add {cfg : Config} {stele : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg stele evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg stele evm rhs = .ok (uint256Value b))
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? cfg stele evm (.inRange (.uint ⟨256, by decide⟩) (.binary .add lhs rhs)) =
      .ok (uint256Value (a + b)) := by
  apply evalExpr_uint256_inRange
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp only [Int.ofNat_eq_natCast, Nat.cast_add]

theorem evalExpr_uint256_add_overflow {cfg : Config} {stele : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg stele evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg stele evm rhs = .ok (uint256Value b))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? cfg stele evm (.inRange (.uint ⟨256, by decide⟩) (.binary .add lhs rhs)) = .revert := by
  have hge : Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (by simpa [Nat.cast_add] using hge)

theorem evalExpr_uint256_div {cfg : Config} {stele : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg stele evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg stele evm rhs = .ok (uint256Value b)) (hb0 : b ≠ ⟨0⟩) :
    evalExpr? cfg stele evm (.binary .div lhs rhs) = .ok (uint256Value (UInt256.div a b)) := by
  have hbNat : ¬ b.toNat = 0 := fun h => hb0 (uint256_toNat_eq_zero h)
  simp [evalExpr?, EvalResult.bind, bind, ha, hb, evalBinaryOp?, hbNat, uint256Value, udiv_toNat]

/-- A reverting left operand reverts a non-short-circuit binary expression. -/
theorem evalExpr_binary_revert_left {cfg : Config} {stele : Frame} {evm : EVM.State}
    {op : BinaryOp} {lhs rhs : Expr} (hand : op ≠ BinaryOp.and) (hor : op ≠ BinaryOp.or)
    (h : evalExpr? cfg stele evm lhs = .revert) :
    evalExpr? cfg stele evm (.binary op lhs rhs) = .revert := by
  rw [evalExpr_binary_nonshort hand hor, h]
  rfl

/-! ## Storage views after a store -/

theorem storageLoad_eq_slotWord (evm : EVM.State) (a : AccountAddress) (k : UInt256) :
    Stele.EVM.storageLoad evm a k =
      (evm.accountMap.get? a |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD k ⟨0⟩)) := rfl

/-! ## Word reads around 32-byte writes -/

theorem memLoad_write_back (w : UInt256) (mem : ByteArray) (off : Nat) (hoff : off < UInt256.size)
    (hgap : off - mem.size < USize.size) :
    memLoad (UInt256.ofNat off) (w.toByteArray.write 0 mem off 32) = w := by
  unfold memLoad
  rw [ulit_toNat' off hoff,
    if_neg (by have := toByteArray_write_size_ge_off_add32 w mem off hgap; omega),
    toByteArray_write_read_back_of_gap _ _ _ hgap, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem memLoad_above_write (src M : ByteArray) (d r : Nat) (hsrc : 32 ≤ src.size)
    (hd : d ≤ M.size) (hr : d + 32 ≤ r) (hin : r + 32 ≤ M.size) (hr' : r < UInt256.size) :
    memLoad (UInt256.ofNat r) (src.write 0 M d 32) = memLoad (UInt256.ofNat r) M := by
  unfold memLoad
  rw [ulit_toNat' r hr', byteArray_write_size_of_inBounds _ _ _ _ hsrc (by omega),
    write32_read_above src M d r hsrc hd hr hin]

theorem memLoad_below_write (w : UInt256) (M : ByteArray) (off r : Nat)
    (hread : r + 32 ≤ M.size) (hbelow : r + 32 ≤ off) (hgap : off - M.size < USize.size)
    (hr' : r < UInt256.size) :
    memLoad (UInt256.ofNat r) (w.toByteArray.write 0 M off 32) = memLoad (UInt256.ofNat r) M := by
  unfold memLoad
  rw [ulit_toNat' r hr',
    if_neg (by have := toByteArray_write_size_ge_off_add32 w M off hgap; omega),
    if_neg (by omega), toByteArray_write_read_below_of_gap w M off r hread hbelow hgap]

/-! ## Comparisons, underflow, empty bytes -/

theorem value_int_beq (x y : Int) : (Value.int x == Value.int y) = decide (x = y) := by
  by_cases h : x = y
  · subst h
    rw [decide_eq_true rfl]
    exact beq_self_eq_true _
  · rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr (fun e => h (Value.int.inj e))

theorem evalExpr_ne_words {cfg : Config} {stele : Frame} {evm : EVM.State} {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg stele evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg stele evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg stele evm (.binary .ne lhs rhs) = .ok (.bool (!decide (a.toNat = b.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp [EvalResult.bind, bind, evalBinaryOp?, uint256Value, value_int_beq]

theorem evalExpr_ge_words {cfg : Config} {stele : Frame} {evm : EVM.State} {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg stele evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg stele evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg stele evm (.binary .ge lhs rhs) = .ok (.bool (decide (b.toNat ≤ a.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp [EvalResult.bind, bind, evalBinaryOp?, uint256Value]

theorem evalExpr_uint256_sub_underflow {cfg : Config} {stele : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg stele evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg stele evm rhs = .ok (uint256Value b))
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg stele evm (.inRange (.uint ⟨256, by decide⟩) (.binary .sub lhs rhs)) = .revert := by
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl (by simp only [Int.ofNat_eq_natCast]; omega)

theorem evalExpr_newBytes_zero {cfg : Config} {stele : Frame} (evm : EVM.State) :
    evalExpr? cfg stele evm (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, pure, bind, EvalResult.bind]
  rfl

/-! ## Mapping-slot hashes over a 32-byte scratch memory -/

/-- Writing a word at 32 into a 32-byte memory is the same as writing it into that memory padded
    to 64 bytes. -/
theorem wordAt32Mem_pad32 (k : UInt256) (mem : ByteArray) (hmem : mem.size = 32) :
    wordAt32Mem k mem = wordAt32Mem k (mem ++ ByteArray.zeroes 32) := by
  unfold wordAt32Mem
  have hpad : (mem ++ ByteArray.zeroes 32).size = 64 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, hmem]
  have hself : mem.extract 0 32 = mem := by
    rw [← hmem]; exact byteArray_extract_self mem
  have hk : (UInt256.toByteArray k).extract 0 32 = UInt256.toByteArray k := by
    rw [← toByteArray_size k]; exact byteArray_extract_self _
  have hempty : (mem ++ ByteArray.zeroes 32).extract (32 + 32) (mem ++ ByteArray.zeroes 32).size =
      ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero _ (by rw [ByteArray.size_extract, hpad]; omega)
  rw [toByteArray_write_eq _ _ 32 (by omega) (by rw [hmem]; exact lt_usize _ (by decide)),
    write32_eq _ _ 32 (by rw [toByteArray_size]) (by omega),
    extract_append_left _ _ _ _ (by omega), hself, hk, hempty, ByteArray.append_empty,
    show ByteArray.zeroes (32 - mem.size) = ByteArray.empty from zeroes_zero (by omega),
    ByteArray.append_empty]

/-- Vyper's `keccak256(slot ++ key)` scratch pattern over the dispatcher's 32-byte memory. -/
theorem keccakWord_hash32 (baseSlot : UInt256) (key : KeyValue) (mem : ByteArray) (hmem : mem.size = 32) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      (wordAt0Mem baseSlot (wordAt32Mem (keyValueToWord key) mem)) = vyperMappingSlot baseSlot key := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 64 (by decide), wordAt32Mem_pad32 _ _ hmem]
  exact wordAt0Mem_wordAt32Mem_vyperMappingSlot baseSlot key
    (by rw [ByteArray.size_append, ByteArray_zeroes_size, hmem])

end Reasoning.VyperDispatch
