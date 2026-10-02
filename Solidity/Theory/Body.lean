import Solidity.Semantics
import EVMReasoning.Storage

/-!
# Derivation helpers for function bodies

Small rewriting lemmas used when building `EvalExpr`/`ExecStmt`/`CallFn` derivations by hand:
frame lookups, scalar conversions, zero values, and full-word (`uint256`) storage reads and
writes through a layout.  `storageLocLoad`/`scalarOfAbi` are eliminated by `rw`, never by
definitional unfolding (their unfolding on a symbolic state does not terminate quickly).
-/

namespace Solidity

open Ethereum Reasoning.Theory

abbrev u256Ty : Ty := .uint ⟨256, by decide⟩
abbrev u256Val (n : Nat) : Value := .uint ⟨256, by decide⟩ n

/-! ## The `Op` monad -/

@[simp] theorem Op.pure_eq {α} (a : α) : (pure a : Op α) = some (.ok a) := rfl

/-- Monadic `some a >>= f` (the form `do` produces). -/
theorem Opt.some_bind {α β} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

@[simp] theorem Op.bind_ok {α β} (a : α) (f : α → Op β) : @Bind.bind Op _ α β (some (.ok a)) f = f a := rfl
@[simp] theorem Op.bind_err {α β} (p : Panic) (f : α → Op β) :
    @Bind.bind Op _ α β (some (.error p)) f = some (.error p) := rfl
@[simp] theorem Op.bind_none {α β} (f : α → Op β) : @Bind.bind Op _ α β none f = none := rfl
@[simp] theorem Op.ofOpt_some {α} (a : α) : (Op.ofOpt (some a) : Op α) = some (.ok a) := rfl
@[simp] theorem Op.ofOpt_none {α} : (Op.ofOpt none : Op α) = none := rfl

/-! ## Frames -/

@[simp] theorem Frame.get?_bind (fr : Frame) (x y : Ident) (ty : Ty) (loc : Option DataLoc) (v : Value) :
    (fr.bind x ty loc v).get? y = if (x == y) = true then some { ty := ty, loc := loc, val := v } else fr.get? y := by
  simp [Frame.get?, Frame.bind, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

@[simp] theorem Frame.get?_empty (here : Ident) (rets : List Ident) (x : Ident) :
    ({ here := here, locals := ∅, retVars := rets } : Frame).get? x = none := by
  simp [Frame.get?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

@[simp] theorem Frame.get?_rootFrame (fc : FlatContract) (x : Ident) : (rootFrame fc).get? x = none := by
  simp [Frame.get?, rootFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

@[simp] theorem Frame.get?_setVal (fr : Frame) (x y : Ident) (v : Value) :
    (fr.setVal x v).get? y =
      match fr.get? x with
      | some l => if (x == y) = true then some { l with val := v } else fr.get? y
      | none => fr.get? y := by
  simp only [Frame.setVal, Frame.get?, Std.HashMap.get?_eq_getElem?]
  cases h : fr.locals[x]? with
  | none => simp
  | some l => simp [Std.HashMap.getElem?_insert]

@[simp] theorem retName0 (ty : Ty) : retName 0 ({ ty := ty } : Param) = "#ret0" := rfl

/-- Evaluate frame lookups/updates down to the underlying hash map. -/
syntax "frame_simp" (" [" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| frame_simp) => `(tactic| frame_simp [])
  | `(tactic| frame_simp [$ls,*]) => `(tactic|
      simp [Frame.get?, Frame.bind, Frame.setVal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem?_empty, -getElem?_pos, -getElem?_neg, $ls,*])

/-- A local read, with the value exposed in the conclusion. -/
theorem EvalExpr.localVal {cfg : Config} {o : Oracle} {fc : FlatContract} {fr : Frame} {m : Machine} {x : Ident}
    (ty : Ty) (loc : Option DataLoc) {v : Value} (h : fr.get? x = some { ty := ty, loc := loc, val := v }) :
    EvalExpr cfg o fc fr m (.ident x) (.ok v fr m) :=
  EvalExpr.local h

/-! ## Values -/

@[simp] theorem zeroObj_uint (env : TypeEnv) (fuel n : Nat) (w : ABI.BitWidth) (h : Heap) :
    zeroObj env (fuel + 1) (.uint w) n h = some (.uint w 0, h) := by
  simp [zeroObj, zeroValue]

@[simp] theorem zeroObj_bool (env : TypeEnv) (fuel n : Nat) (h : Heap) :
    zeroObj env (fuel + 1) .bool n h = some (.bool false, h) := by
  simp [zeroObj, zeroValue]

@[simp] theorem toAbi_uint (h : Heap) (fuel : Nat) (w : ABI.BitWidth) (n : Nat) :
    toAbi h (fuel + 1) (.uint w n) = some (.int n) := by
  simp [toAbi, scalarToAbi]

@[simp] theorem toAbi_bool (h : Heap) (fuel : Nat) (b : Bool) :
    toAbi h (fuel + 1) (.bool b) = some (.bool b) := by
  simp [toAbi, scalarToAbi]

@[simp] theorem toAbi_address (h : Heap) (fuel : Nat) (a : EVM.Address) :
    toAbi h (fuel + 1) (.address a) = some (.address a) := by
  simp [toAbi, scalarToAbi]

theorem scalarOfAbi_u256 (env : TypeEnv) (w : UInt256) :
    scalarOfAbi env u256Ty (.int (Int.ofNat w.toNat)) = some (u256Val w.toNat) := by
  have h : w.toNat < 2 ^ 256 := w.val.isLt
  simp [scalarOfAbi]
  omega

theorem scalarOfAbi_u256_nat (env : TypeEnv) (n : Nat) (hn : n < UInt256.size) :
    scalarOfAbi env u256Ty (.int (Int.ofNat n)) = some (u256Val n) := by
  simp [scalarOfAbi]
  exact hn

@[simp] theorem scalarOfAbi_address (env : TypeEnv) (a : EVM.Address) :
    scalarOfAbi env (.address false) (.address a) = some (.address a) := by
  simp [scalarOfAbi]

@[simp] theorem implicitConv_uint (env : TypeEnv) (h : Heap) (n : Nat) :
    implicitConv env h (u256Val n) u256Ty = some (u256Val n, h) := by
  simp [implicitConv]

@[simp] theorem implicitConv_address (env : TypeEnv) (h : Heap) (a : EVM.Address) :
    implicitConv env h (.address a) (.address false) = some (.address a, h) := by
  simp [implicitConv]

@[simp] theorem implicitConv_bool (env : TypeEnv) (h : Heap) (b : Bool) :
    implicitConv env h (.bool b) .bool = some (.bool b, h) := by
  simp [implicitConv]

/-! ## Full-word storage reads and writes -/

/-- `readScalar` of a `uint256` slot: the stored word. -/
theorem readScalar_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (h : cfg.storage.layout er evm = some (uint256Loc slot)) :
    readScalar cfg env evm er u256Ty =
      some (u256Val (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  unfold readScalar
  rw [h, Opt.some_bind, storageLocLoad_uint256, scalarOfAbi_u256]

theorem loadIfScalar_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (h : cfg.storage.layout er evm = some (uint256Loc slot)) :
    loadIfScalar cfg env evm er u256Ty =
      some (u256Val (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  unfold loadIfScalar
  rw [if_pos (by rfl : isValueType env u256Ty = true)]
  exact readScalar_u256 h

/-- `writeScalar` of a `uint256` slot: the stored word. -/
theorem writeScalar_u256 {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (h : cfg.storage.layout er evm = some (uint256Loc slot)) (w : UInt256) :
    writeScalar cfg evm er (u256Val w.toNat) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot w) := by
  unfold writeScalar
  rw [h, Opt.some_bind]
  show (some (ABI.ABIValue.int (Int.ofNat w.toNat)) >>= _) = _
  rw [Opt.some_bind, storageLocStore_uint256]

/-- `writeStorageDeep` of a `uint256` value into a `uint256` slot. -/
theorem writeStorageDeep_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er evm = some (uint256Loc slot)) (fuel : Nat) (w : UInt256) :
    writeStorageDeep cfg env (fuel + 1) evm h er u256Ty (u256Val w.toNat) =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot w)) := by
  rw [writeStorageDeep]
  · simp only [implicitConv_uint, Op.ofOpt, writeScalar_u256 hl]
    rfl
  all_goals intros; simp_all

/-! ## Scalar slots by location -/

theorem readScalar_of_loc {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {loc : Storage.StorageLoc} {v : Value} (hl : cfg.storage.layout er evm = some loc)
    (hv : scalarOfAbi env ty (Storage.storageLocLoad evm loc) = some v) : readScalar cfg env evm er ty = some v := by
  unfold readScalar
  rw [hl, Opt.some_bind, hv]

theorem loadIfScalar_of_loc {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {loc : Storage.StorageLoc} {v : Value} (hval : isValueType env ty = true) (hl : cfg.storage.layout er evm = some loc)
    (hv : scalarOfAbi env ty (Storage.storageLocLoad evm loc) = some v) : loadIfScalar cfg env evm er ty = some v := by
  unfold loadIfScalar
  rw [if_pos hval]
  exact readScalar_of_loc hl hv

/-- A reference type is read as a storage reference. -/
theorem loadIfScalar_ref {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    (hnv : isValueType env ty = false) : loadIfScalar cfg env evm er ty = some (.storageRef er ty) := by
  unfold loadIfScalar
  rw [if_neg (by simp [hnv])]

theorem writeScalar_of_loc {cfg : Config} {evm evm' : EVM.State} {er : Solm.EvaledStorageRef} {loc : Storage.StorageLoc}
    {v : Value} {sv : ABI.ABIValue} (hl : cfg.storage.layout er evm = some loc)
    (hsv : scalarToAbi v = some sv) (hst : Storage.storageLocStore evm loc sv = some evm') :
    writeScalar cfg evm er v = some evm' := by
  unfold writeScalar
  rw [hl, Opt.some_bind, hsv, Opt.some_bind, hst]

theorem readLValue_storage_of {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {ty : Ty} {v : Value} (hload : loadIfScalar cfg env m.evm er ty = some v) :
    readLValue cfg env fr m (.storage er ty) = some (.ok v) := by
  simp [readLValue, hload]

theorem assign_storage_of {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {ty : Ty} {v : Value} {evm' : EVM.State}
    (hw : writeStorageDeep cfg env fuelDefault m.evm m.heap er ty v = some (.ok evm')) :
    assign cfg env fr m (.storage er ty) v = some (.ok (fr, { m with evm := evm' })) := by
  simp [assign, hw]

theorem writeStorageDeep_bool {cfg : Config} {env : TypeEnv} {evm evm' : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} (fuel : Nat) {b : Bool} (hw : writeScalar cfg evm er (.bool b) = some evm') :
    writeStorageDeep cfg env (fuel + 1) evm h er .bool (.bool b) = some (.ok evm') := by
  rw [writeStorageDeep]
  · simp only [implicitConv_bool, Op.ofOpt, hw]
    rfl
  all_goals intros; simp_all

theorem writeStorageDeep_address {cfg : Config} {env : TypeEnv} {evm evm' : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} (fuel : Nat) {a : EVM.Address}
    (hw : writeScalar cfg evm er (.address a) = some evm') :
    writeStorageDeep cfg env (fuel + 1) evm h er (.address false) (.address a) = some (.ok evm') := by
  rw [writeStorageDeep]
  · simp only [implicitConv_address, Op.ofOpt, hw]
    rfl
  all_goals intros; simp_all

/-! ### `bool` at offset 0 -/

theorem readScalar_bool_false {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er evm = some (boolOffset0Loc slot))
    (hz : UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ = ⟨0⟩) :
    readScalar cfg env evm er .bool = some (.bool false) :=
  readScalar_of_loc hl (by rw [storageLocLoad_bool_offset0_false evm slot hz]; rfl)

theorem readScalar_bool_true {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er evm = some (boolOffset0Loc slot))
    (hnz : UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠ ⟨0⟩) :
    readScalar cfg env evm er .bool = some (.bool true) :=
  readScalar_of_loc hl (by rw [storageLocLoad_bool_offset0_true evm slot hnz]; rfl)

theorem writeScalar_bool_true {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (boolOffset0Loc slot)) :
    writeScalar cfg evm er (.bool true) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor (UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩)) ⟨1⟩)) :=
  writeScalar_of_loc hl rfl (storageLocStore_bool_true_offset0 evm slot)

theorem writeScalar_bool_false {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (boolOffset0Loc slot)) :
    writeScalar cfg evm er (.bool false) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.lnot ⟨255⟩))) :=
  writeScalar_of_loc hl rfl (storageLocStore_bool_false_offset0 evm slot)

/-! ### `address` at offset 0 -/

theorem readScalar_address {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er evm = some (addressOffset0Loc slot)) :
    readScalar cfg env evm er (.address false) =
      some (.address (AccountAddress.ofNat
        (UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask).toNat)) :=
  readScalar_of_loc hl (by rw [storageLocLoad_address_offset0]; rfl)

theorem writeScalar_address {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (addressOffset0Loc slot)) (addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    writeScalar cfg evm er (.address (AccountAddress.ofNat addr.toNat)) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) :=
  writeScalar_of_loc hl rfl (storageLocStore_address_offset0 evm slot addr hcanon)

/-! ### `bytes32` -/

theorem readScalar_bytes32 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er evm = some (bytes32Loc slot)) :
    readScalar cfg env evm er (.fixedBytes ⟨31, by decide⟩) =
      some (.fixedBytes ⟨31, by decide⟩
        (EVM.Word.toBytesBE (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) :=
  readScalar_of_loc hl (by rw [storageLocLoad_bytes32]; rfl)

theorem writeScalar_bytes32 {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot word : UInt256}
    (hl : cfg.storage.layout er evm = some (bytes32Loc slot)) (bs : List UInt8)
    (hval : ABI.valueToWord (.fixedBytes ⟨31, by decide⟩ bs) = some word) :
    writeScalar cfg evm er (.fixedBytes ⟨31, by decide⟩ bs) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot word) :=
  writeScalar_of_loc hl rfl (storageLocStore_bytes32 evm slot word _ hval)

/-! ## Arrays and structs -/

theorem dynArrayLength_of_loc {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout (lengthRef er) evm = some (uint256Loc slot)) :
    dynArrayLength cfg evm er = some (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat := by
  unfold dynArrayLength
  rw [hl, Opt.some_bind, storageLocLoad_uint256]
  rfl

theorem storageIndex_dynArray_ok {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {e : Ty} {n i : ℕ} (hlen : dynArrayLength cfg evm er = some n) (hi : i < n) :
    storageIndex cfg env evm h er (.dynArray e) (u256Val i) = some (.ok (elemRef er i, e)) := by
  simp [storageIndex, natOperand, hlen, hi]

theorem storageIndex_dynArray_oob {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {e : Ty} {n i : ℕ} (hlen : dynArrayLength cfg evm er = some n) (hi : n ≤ i) :
    storageIndex cfg env evm h er (.dynArray e) (u256Val i) = some (.error .outOfBounds) := by
  simp [storageIndex, natOperand, hlen, Nat.not_lt.mpr hi]
  rfl

theorem storageIndex_array_ok {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {e : Ty} {n i : ℕ} (hi : i < n) :
    storageIndex cfg env evm h er (.array e n) (u256Val i) = some (.ok (elemRef er i, e)) := by
  simp [storageIndex, natOperand, hi]

theorem storageIndex_array_oob {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {e : Ty} {n i : ℕ} (hi : n ≤ i) :
    storageIndex cfg env evm h er (.array e n) (u256Val i) = some (.error .outOfBounds) := by
  simp [storageIndex, natOperand, Nat.not_lt.mpr hi]
  rfl

theorem storageField_of {env : TypeEnv} {er : Solm.EvaledStorageRef} {q : Option Ident} {n f : Ident}
    {s : StructInfo} {fty : Ty} {f' : Ident}
    (hs : env.struct? q n = some s) (hf : s.fields.find? (·.2 == f) = some (fty, f')) :
    storageField env er (.user q n) f = some (fieldRef er f, fty) := by
  simp [storageField, hs, hf]

theorem storageLength_dynArray {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {e : Ty} {n : ℕ}
    (hlen : dynArrayLength cfg evm er = some n) : storageLength cfg evm er (.dynArray e) = some (.ok n) := by
  simp [storageLength, hlen]

theorem storageLength_array {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {e : Ty} {n : ℕ} :
    storageLength cfg evm er (.array e n) = some (.ok n) := rfl

theorem readScalar_address_offset1 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {hbound : (1 : Fin 32).val + (20 : Fin 33).val - 1 < 32}
    (hl : cfg.storage.layout er evm =
      some { slot := slot, offset := 1, size := 20, hbound := hbound, type := .address }) :
    readScalar cfg env evm er (.address false) =
      some (.address (AccountAddress.ofNat
        (UInt256.land (UInt256.div (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨256⟩)
          solcAddrMask).toNat)) :=
  readScalar_of_loc hl (by rw [storageLocLoad_address_offset1]; rfl)

theorem writeDynArrayLength_of_loc {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout (lengthRef er) evm = some (uint256Loc slot)) (n : ℕ) (hn : n < UInt256.size) :
    writeDynArrayLength cfg evm er n =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat n)) := by
  unfold writeDynArrayLength
  rw [hl, Opt.some_bind]
  have h := storageLocStore_uint256 evm slot (UInt256.ofNat n)
  rw [ulit_toNat' n hn] at h
  exact h

/-- `a.push(v)`: the length slot and the new element. -/
theorem storagePush_some {cfg : Config} {env : TypeEnv} {m : Machine} {er : Solm.EvaledStorageRef} {e : Ty}
    {v : Value} {n : ℕ} {slot : UInt256} {evm₂ : EVM.State}
    (hlen : dynArrayLength cfg m.evm er = some n)
    (hl : cfg.storage.layout (lengthRef er) m.evm = some (uint256Loc slot)) (hn : n + 1 < UInt256.size)
    (hw : writeStorageDeep cfg env fuelDefault
      (Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot (UInt256.ofNat (n + 1))) m.heap
      (elemRef er n) e v = some (.ok evm₂)) :
    storagePush cfg env m er e (some v) = some (.ok { m with evm := evm₂ }) := by
  simp [storagePush, hlen, writeDynArrayLength_of_loc hl (n + 1) hn, hw]

/-- `a.push()`: the length slot only. -/
theorem storagePush_none {cfg : Config} {env : TypeEnv} {m : Machine} {er : Solm.EvaledStorageRef} {e : Ty}
    {n : ℕ} {slot : UInt256}
    (hlen : dynArrayLength cfg m.evm er = some n)
    (hl : cfg.storage.layout (lengthRef er) m.evm = some (uint256Loc slot)) (hn : n + 1 < UInt256.size) :
    storagePush cfg env m er e none =
      some (.ok { m with
        evm := Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot (UInt256.ofNat (n + 1)) }) := by
  simp [storagePush, hlen, writeDynArrayLength_of_loc hl (n + 1) hn]

theorem storagePop_empty {cfg : Config} {env : TypeEnv} {m : Machine} {er : Solm.EvaledStorageRef} {e : Ty}
    (hlen : dynArrayLength cfg m.evm er = some 0) : storagePop cfg env m er e = some (.error .popEmpty) := by
  simp [storagePop, hlen]
  rfl

theorem storagePop_succ {cfg : Config} {env : TypeEnv} {m : Machine} {er : Solm.EvaledStorageRef} {e : Ty}
    {n : ℕ} {slot : UInt256} {evm₁ : EVM.State}
    (hlen : dynArrayLength cfg m.evm er = some (n + 1))
    (hclear : clearStorage cfg env fuelDefault m.evm (elemRef er n) e = some (.ok evm₁))
    (hl : cfg.storage.layout (lengthRef er) evm₁ = some (uint256Loc slot)) (hn : n < UInt256.size) :
    storagePop cfg env m er e =
      some (.ok { m with evm := Storage.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot (UInt256.ofNat n) }) := by
  simp [storagePop, hlen, hclear, writeDynArrayLength_of_loc hl n hn]

/-- `delete x` for a `uint256` slot. -/
theorem clearStorage_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (fuel : ℕ) (hl : cfg.storage.layout er evm = some (uint256Loc slot)) :
    clearStorage cfg env (fuel + 1) evm er u256Ty =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩)) := by
  have hw := writeScalar_u256 hl ⟨0⟩
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl] at hw
  rw [clearStorage]
  all_goals first
    | (simp only [storageTyOf, zeroValue]
       rw [hw]
       rfl)
    | (intros; simp_all)

theorem abiArgs_u256 (cfg : Config) (env : TypeEnv) (m : Machine) (n : Nat) :
    abiArgs cfg env m [u256Ty] [u256Val n] = some (.ok ([.int n], m)) := by
  simp [abiArgs, coerce, fuelDefault]

/-! ## Memory objects -/

@[simp] theorem Heap.get?_alloc_self (h : Heap) (o : HeapObj) : (h.alloc o).1.get? (h.alloc o).2 = some o := by
  simp [Heap.alloc, Heap.get?]

theorem Heap.get?_alloc_lt (h : Heap) (o : HeapObj) {id : ℕ} (hlt : id < h.objs.size) :
    (h.alloc o).1.get? id = h.get? id := by
  simp [Heap.alloc, Heap.get?, Array.getElem?_push_lt hlt]

theorem memField_of {h : Heap} {obj : ℕ} {ty : Ty} {fields : List (Ident × Value)} {f f' : Ident} {v : Value}
    (hget : h.get? obj = some (.struct ty fields)) (hf : fields.find? (·.1 == f) = some (f', v)) :
    memField h obj f = some v := by
  simp [memField, hget, hf]

theorem memLength_array {h : Heap} {obj : ℕ} {e : Ty} {elems : List Value}
    (hget : h.get? obj = some (.array e elems)) : memLength h obj = some elems.length := by
  simp [memLength, hget]

theorem memIndex_array_ok {h : Heap} {obj : ℕ} {e : Ty} {elems : List Value} {i : ℕ}
    (hget : h.get? obj = some (.array e elems)) (hi : i < elems.length) :
    memIndex h obj (u256Val i) = some (.ok elems[i]) := by
  simp [memIndex, natOperand, hget, List.getElem?_eq_getElem hi]

theorem memIndex_array_oob {h : Heap} {obj : ℕ} {e : Ty} {elems : List Value} {i : ℕ}
    (hget : h.get? obj = some (.array e elems)) (hi : elems.length ≤ i) :
    memIndex h obj (u256Val i) = some (.error .outOfBounds) := by
  simp [memIndex, natOperand, hget, List.getElem?_eq_none hi]
  rfl

/-! ## Literals, coercions and increments -/

theorem implicitConv_literal_u256 (env : TypeEnv) (h : Heap) (i : Int) (hd : Option Nat) (h0 : 0 ≤ i)
    (hi : i < 2 ^ 256) : implicitConv env h (.literal i hd) u256Ty = some (u256Val i.toNat, h) := by
  simp [implicitConv, IntTy.inRange, IntTy.min, IntTy.max]
  omega

@[simp] theorem implicitConv_fixedBytes (env : TypeEnv) (h : Heap) (n : Fin 32) (bs : List UInt8) :
    implicitConv env h (.fixedBytes n bs) (.fixedBytes n) = some (.fixedBytes n bs, h) := by
  simp [implicitConv]

theorem coerce_uint (cfg : Config) (env : TypeEnv) (m : Machine) (n : Nat) (loc : Option DataLoc) :
    coerce cfg env m (u256Val n) u256Ty loc = some (.ok (u256Val n, m)) := by
  simp [coerce]

theorem coerce_bool (cfg : Config) (env : TypeEnv) (m : Machine) (b : Bool) (loc : Option DataLoc) :
    coerce cfg env m (.bool b) .bool loc = some (.ok (.bool b, m)) := by
  simp [coerce]

theorem coerce_address (cfg : Config) (env : TypeEnv) (m : Machine) (a : EVM.Address) (loc : Option DataLoc) :
    coerce cfg env m (.address a) (.address false) loc = some (.ok (.address a, m)) := by
  simp [coerce]

theorem coerce_fixedBytes (cfg : Config) (env : TypeEnv) (m : Machine) (n : Fin 32) (bs : List UInt8)
    (loc : Option DataLoc) : coerce cfg env m (.fixedBytes n bs) (.fixedBytes n) loc = some (.ok (.fixedBytes n bs, m)) := by
  simp [coerce]

theorem coerce_literal_u256 (cfg : Config) (env : TypeEnv) (m : Machine) (i : Int) (hd : Option Nat)
    (loc : Option DataLoc) (h0 : 0 ≤ i) (hi : i < 2 ^ 256) :
    coerce cfg env m (.literal i hd) u256Ty loc = some (.ok (u256Val i.toNat, m)) := by
  simp [coerce, implicitConv_literal_u256 env m.heap i hd h0 hi]

/-! ## Arithmetic with number literals

`settle`/`IntTy.inRange`/`IntTy.max` must never be unfolded (by `simp`, `dsimp`, `rfl`, or a
`match` reduction) on an operand containing a numeral: `whnf` of `Int.decLe` against `2 ^ 256 - 1`
recurses through `Nat.sub` on the literal and overflows (elaborator and kernel alike).  Eliminate
them with the lemmas below, whose proofs only see variables. -/

abbrev u256IntTy : IntTy := .uint ⟨256, by decide⟩

def liftArith (t : IntTy) : Except Panic Int → Op Value
  | .ok v => some (.ok (mkInt t v))
  | .error p => some (.error p)

@[simp] theorem liftArith_ok (t : IntTy) (v : Int) : liftArith t (.ok v) = some (.ok (mkInt t v)) := rfl
@[simp] theorem liftArith_error (t : IntTy) (p : Panic) : liftArith t (.error p) = some (.error p) := rfl

theorem settle_u256_ok (r : Int) (h0 : 0 ≤ r) (hr : r < 2 ^ 256) : settle u256IntTy true r = .ok r := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]; omega

theorem settle_u256_overflow (r : Int) (h : ¬ (0 ≤ r ∧ r < 2 ^ 256)) :
    settle u256IntTy true r = .error .overflow := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]; omega

theorem settle_unchecked (t : IntTy) (r : Int) : settle t false r = .ok (t.wrap r) := by simp [settle]

/-- A `uint256` operand meets a number literal: the literal takes `uint256` when it fits. -/
theorem unifyInts_u256_lit (n : Nat) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 2 ^ 256) :
    unifyInts (u256Val n) (.literal k hd) = some (some u256IntTy, (n : Int), k) := by
  simp [unifyInts, Value.int?, IntTy.inRange, IntTy.min, IntTy.max]; omega

theorem unifyInts_u256_u256 (a b : Nat) :
    unifyInts (u256Val a) (u256Val b) = some (some u256IntTy, (a : Int), (b : Int)) := by
  simp [unifyInts, Value.int?, commonIntType, implicitIntConv]

/-- The arithmetic arm of `binop` for an unsigned left operand, once the operands are unified. -/
theorem binop_add_uint_of_unify (c : Bool) (w : ABI.BitWidth) (n : Nat) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.uint w n) b = some (some t, x, y)) :
    binop c .add (.uint w n) b = liftArith t (add t c x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases add t c x y <;> rfl

theorem binop_sub_uint_of_unify (c : Bool) (w : ABI.BitWidth) (n : Nat) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.uint w n) b = some (some t, x, y)) :
    binop c .sub (.uint w n) b = liftArith t (sub t c x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases sub t c x y <;> rfl

theorem binop_mul_uint_of_unify (c : Bool) (w : ABI.BitWidth) (n : Nat) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.uint w n) b = some (some t, x, y)) :
    binop c .mul (.uint w n) b = liftArith t (mul t c x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases mul t c x y <;> rfl

theorem binop_div_uint_of_unify (c : Bool) (w : ABI.BitWidth) (n : Nat) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.uint w n) b = some (some t, x, y)) :
    binop c .div (.uint w n) b = liftArith t (div t c x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases div t c x y <;> rfl

theorem binop_mod_uint_of_unify (c : Bool) (w : ABI.BitWidth) (n : Nat) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.uint w n) b = some (some t, x, y)) :
    binop c .mod (.uint w n) b = liftArith t (mod t x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases mod t x y <;> rfl

theorem binop_add_u256_lit (n : Nat) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 2 ^ 256)
    (hfit : (n : Int) + k < 2 ^ 256) :
    binop true .add (u256Val n) (.literal k hd) = some (.ok (u256Val ((n : Int) + k).toNat)) := by
  rw [binop_add_uint_of_unify true _ n _ (unifyInts_u256_lit n k hd h0 hk), add,
    settle_u256_ok _ (by omega) hfit, liftArith_ok]
  rfl

theorem binop_add_u256_lit_overflow (n : Nat) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 2 ^ 256)
    (hbig : 2 ^ 256 ≤ (n : Int) + k) :
    binop true .add (u256Val n) (.literal k hd) = some (.error .overflow) := by
  rw [binop_add_uint_of_unify true _ n _ (unifyInts_u256_lit n k hd h0 hk), add,
    settle_u256_overflow _ (by omega), liftArith_error]

theorem binop_add_u256_lit1 (n : Nat) (hfit : n + 1 < 2 ^ 256) :
    binop true .add (u256Val n) (.literal 1) = some (.ok (u256Val (n + 1))) := by
  have ht : ((n : Int) + 1).toNat = n + 1 := by omega
  rw [binop_add_u256_lit n 1 none (by omega) (by omega) (by omega), ht]

theorem binop_sub_u256_lit (n : Nat) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 2 ^ 256)
    (hn : n < 2 ^ 256) (hle : k ≤ n) :
    binop true .sub (u256Val n) (.literal k hd) = some (.ok (u256Val ((n : Int) - k).toNat)) := by
  rw [binop_sub_uint_of_unify true _ n _ (unifyInts_u256_lit n k hd h0 hk), sub,
    settle_u256_ok _ (by omega) (by omega), liftArith_ok]
  rfl

theorem binop_sub_u256_lit_underflow (n : Nat) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 2 ^ 256)
    (hlt : (n : Int) < k) :
    binop true .sub (u256Val n) (.literal k hd) = some (.error .overflow) := by
  rw [binop_sub_uint_of_unify true _ n _ (unifyInts_u256_lit n k hd h0 hk), sub,
    settle_u256_overflow _ (by omega), liftArith_error]

theorem binop_sub_u256_lit1 (n : Nat) (hpos : 0 < n) (hn : n < 2 ^ 256) :
    binop true .sub (u256Val n) (.literal 1) = some (.ok (u256Val (n - 1))) := by
  have ht : ((n : Int) - 1).toNat = n - 1 := by omega
  rw [binop_sub_u256_lit n 1 none (by omega) (by omega) hn (by omega), ht]

theorem binop_mul_u256_lit (n : Nat) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 2 ^ 256)
    (hfit : (n : Int) * k < 2 ^ 256) :
    binop true .mul (u256Val n) (.literal k hd) = some (.ok (u256Val ((n : Int) * k).toNat)) := by
  rw [binop_mul_uint_of_unify true _ n _ (unifyInts_u256_lit n k hd h0 hk), mul,
    settle_u256_ok _ (by positivity) hfit, liftArith_ok]
  rfl

theorem wrap_u256_of_lt (r : Int) (h0 : 0 ≤ r) (hr : r < 2 ^ 256) : u256IntTy.wrap r = r := by
  simp only [IntTy.wrap, IntTy.isSigned, IntTy.width, Bool.false_and]
  exact Int.emod_eq_of_lt h0 hr

theorem binop_div_u256_lit (c : Bool) (n : Nat) (k : Int) (hd : Option Nat) (h0 : 0 < k) (hk : k < 2 ^ 256)
    (hn : n < 2 ^ 256) :
    binop c .div (u256Val n) (.literal k hd) = some (.ok (u256Val (n / k.toNat))) := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, k = m := ⟨k.toNat, by omega⟩
  have hnn : (0 : Int) ≤ ((n / m : Nat) : Int) := Int.natCast_nonneg _
  have hlt : ((n / m : Nat) : Int) < 2 ^ 256 := by exact_mod_cast lt_of_le_of_lt (Nat.div_le_self n m) hn
  rw [binop_div_uint_of_unify c _ n _ (unifyInts_u256_lit n m hd (by omega) hk), div, if_neg (by omega),
    Int.tdiv_eq_ediv_of_nonneg (by omega), ← Int.natCast_ediv, Int.toNat_natCast]
  cases c
  · rw [settle_unchecked, wrap_u256_of_lt _ hnn hlt, liftArith_ok]; rfl
  · rw [settle_u256_ok _ hnn hlt, liftArith_ok]; rfl

theorem binop_mod_u256_lit (c : Bool) (n : Nat) (k : Int) (hd : Option Nat) (h0 : 0 < k) (hk : k < 2 ^ 256) :
    binop c .mod (u256Val n) (.literal k hd) = some (.ok (u256Val (n % k.toNat))) := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, k = m := ⟨k.toNat, by omega⟩
  rw [binop_mod_uint_of_unify c _ n _ (unifyInts_u256_lit n m hd (by omega) hk), mod, if_neg (by omega),
    Int.tmod_eq_emod_of_nonneg (by omega), ← Int.natCast_emod, Int.toNat_natCast, liftArith_ok]
  rfl

theorem readLValue_local {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {x : Ident} {l : Local}
    (hx : fr.get? x = some l) : readLValue cfg env fr m (.local x) = some (.ok l.val) := by
  simp [readLValue, hx]

theorem assign_local_u256 {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {x : Ident} (l : Local)
    (hx : fr.get? x = some l) (hty : l.ty = u256Ty) (n : Nat) :
    assign cfg env fr m (.local x) (u256Val n) = some (.ok (fr.setVal x (u256Val n), m)) := by
  simp [assign, coerce, hx, hty]
  try rfl

/-! ## Scopes -/

@[simp] theorem exitScope_get? (fr fr' : Frame) (k : Ident) :
    (fr.exitScope fr').get? k = if fr.locals.contains k then fr'.get? k else none := by
  simp only [Frame.exitScope, Frame.get?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter']
  cases fr'.locals[k]? <;> simp [Option.filter]

@[simp] theorem exitScope_chain (fr fr' : Frame) : (fr.exitScope fr').chain = fr'.chain := rfl
@[simp] theorem exitScope_body (fr fr' : Frame) : (fr.exitScope fr').body = fr'.body := rfl
@[simp] theorem exitScope_unchecked (fr fr' : Frame) : (fr.exitScope fr').unchecked = fr'.unchecked := rfl
@[simp] theorem exitScope_retVars (fr fr' : Frame) : (fr.exitScope fr').retVars = fr'.retVars := rfl
@[simp] theorem exitScope_here (fr fr' : Frame) : (fr.exitScope fr').here = fr'.here := rfl

/-! ## Struct literals and memory arrays -/

/-- A two-field struct literal, each field coerced to its declared type. -/
theorem structObj_two {cfg : Config} {env : TypeEnv} {m : Machine} {sd : StructInfo} {t1 t2 : Ty} {f1 f2 : Ident}
    {v1 v2 v1' v2' : Value}
    (hfields : sd.fields = [(t1, f1), (t2, f2)])
    (hc1 : coerce cfg env m v1 t1 (some .memory) = some (.ok (v1', m)))
    (hc2 : coerce cfg env m v2 t2 (some .memory) = some (.ok (v2', m))) :
    structObj cfg env m sd [v1, v2] =
      some (.ok (.memRef (m.heap.alloc (.struct (.user sd.qual sd.name) [(f1, v1'), (f2, v2')])).2,
        { m with heap := (m.heap.alloc (.struct (.user sd.qual sd.name) [(f1, v1'), (f2, v2')])).1 })) := by
  simp [structObj, hfields, List.foldlM_cons, List.foldlM_nil, hc1, hc2]

/-- A fold that appends one element per input and never touches the heap. -/
theorem foldlM_option_snoc {α β : Type} {g : β → α} {h : Heap} {f : List α × Heap → β → Option (List α × Heap)} :
    ∀ (svs : List β) (acc : List α), (∀ acc sv, sv ∈ svs → f (acc, h) sv = some (acc ++ [g sv], h)) →
      svs.foldlM f (acc, h) = some (acc ++ svs.map g, h)
  | [], acc, _ => by simp
  | sv :: svs, acc, hf => by
    rw [List.foldlM_cons, hf acc sv (List.mem_cons_self ..), Opt.some_bind,
      foldlM_option_snoc svs (acc ++ [g sv]) (fun acc sv hm => hf acc sv (List.mem_cons_of_mem _ hm))]
    simp

theorem ofAbi_fixedBytes (env : TypeEnv) (fuel : Nat) (n : Fin 32) (bs : List UInt8) (h : Heap) :
    ofAbi env (fuel + 1) (.fixedBytes n) (.fixedBytes n bs) h = some (.fixedBytes n bs, h) := by
  simp [ofAbi, scalarOfAbi]

/-- A dynamic array of scalars decoded into memory: one array object holding the converted elements. -/
theorem ofAbi_dynArray_map {env : TypeEnv} {fuel : Nat} {e : Ty} {h : Heap} {svs : List ABI.ABIValue}
    {g : ABI.ABIValue → Value} (hsc : ∀ sv ∈ svs, ofAbi env fuel e sv h = some (g sv, h)) :
    ofAbi env (fuel + 1) (.dynArray e) (.array svs) h =
      some (.memRef (h.alloc (.array e (svs.map g))).2, (h.alloc (.array e (svs.map g))).1) := by
  rw [ofAbi]
  unfold ofAbi.ofArray
  rw [foldlM_option_snoc (g := g) svs [] (fun acc sv hm => by simp [hsc sv hm])]
  simp

/-! ## Mappings -/

@[simp] theorem loadIfScalar_mapping (cfg : Config) (env : TypeEnv) (evm : EVM.State) (er : Solm.EvaledStorageRef)
    (k v : Ty) : loadIfScalar cfg env evm er (.mapping k v) = some (.storageRef er (.mapping k v)) := by
  simp [loadIfScalar, isValueType, leafElemType]

@[simp] theorem storageIndex_mapping_address (cfg : Config) (env : TypeEnv) (evm : EVM.State) (h : Heap)
    (er : Solm.EvaledStorageRef) (v : Ty) (a : EVM.Address) :
    storageIndex cfg env evm h er (.mapping (.address false) v) (.address a) =
      some (.ok (keyRef er (.address a), v)) := by
  simp [storageIndex, keyOf]

theorem readLValue_storage_u256 {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine}
    {er : Solm.EvaledStorageRef} {slot : UInt256} (hl : cfg.storage.layout er m.evm = some (uint256Loc slot)) :
    readLValue cfg env fr m (.storage er u256Ty) =
      some (.ok (u256Val (Storage.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner slot).toNat)) := by
  simp [readLValue, loadIfScalar_u256 hl]

theorem assign_storage_u256 {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine}
    {er : Solm.EvaledStorageRef} {slot : UInt256} (hl : cfg.storage.layout er m.evm = some (uint256Loc slot))
    (w : UInt256) :
    assign cfg env fr m (.storage er u256Ty) (u256Val w.toNat) =
      some (.ok (fr, { m with evm := Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot w })) := by
  simp [assign, fuelDefault, writeStorageDeep_u256 hl]

/-! ## Environment and conversions -/

@[simp] theorem envMember_sender (m : Machine) :
    envMember m "msg" "sender" = some (.address m.evm.executionEnv.source) := rfl

@[simp] theorem explicitConv_lit0_address (env : TypeEnv) (h : Heap) :
    explicitConv env h (.literal 0) (.address false) = some (.ok (.address (EVM.address 0), h)) := by
  simp [explicitConv, implicitConv]

/-! ## Checked `uint256` arithmetic and comparisons -/

theorem binop_ge_u256 (c : Bool) (a b : Nat) :
    binop c .ge (u256Val a) (u256Val b) = some (.ok (.bool (decide (b ≤ a)))) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, cmpInt]

theorem binop_sub_u256_ok (a b : Nat) (ha : a < 2 ^ 256) (h : b ≤ a) :
    binop true .sub (u256Val a) (u256Val b) = some (.ok (u256Val (a - b))) := by
  have ht : ((a : Int) - b).toNat = a - b := by omega
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, sub, settle,
    IntTy.inRange, IntTy.min, IntTy.max, mkInt]
  rw [if_pos (by omega)]
  simp [ht]

theorem binop_sub_u256_underflow (a b : Nat) (h : a < b) :
    binop true .sub (u256Val a) (u256Val b) = some (.error .overflow) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, sub, settle,
    IntTy.inRange, IntTy.min, IntTy.max]
  rw [if_neg (by omega)]
  rfl

theorem binop_add_u256_ok (a b : Nat) (h : a + b < 2 ^ 256) :
    binop true .add (u256Val a) (u256Val b) = some (.ok (u256Val (a + b))) := by
  have ht : ((a : Int) + b).toNat = a + b := by omega
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, add, settle,
    IntTy.inRange, IntTy.min, IntTy.max, mkInt]
  rw [if_pos (by omega)]
  simp [ht]

theorem binop_add_u256_overflow (a b : Nat) (h : 2 ^ 256 ≤ a + b) :
    binop true .add (u256Val a) (u256Val b) = some (.error .overflow) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, add, settle,
    IntTy.inRange, IntTy.min, IntTy.max]
  rw [if_neg (by omega)]
  rfl

theorem binop_lt_u256 (c : Bool) (a b : Nat) :
    binop c .lt (u256Val a) (u256Val b) = some (.ok (.bool (decide (a < b)))) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, cmpInt]

theorem binop_le_u256 (c : Bool) (a b : Nat) :
    binop c .le (u256Val a) (u256Val b) = some (.ok (.bool (decide (a ≤ b)))) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, cmpInt]

theorem binop_gt_u256 (c : Bool) (a b : Nat) :
    binop c .gt (u256Val a) (u256Val b) = some (.ok (.bool (decide (b < a)))) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, cmpInt]

theorem binop_eq_u256 (c : Bool) (a b : Nat) :
    binop c .eq (u256Val a) (u256Val b) = some (.ok (.bool (decide (a = b)))) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, cmpInt]

theorem binop_ne_u256 (c : Bool) (a b : Nat) :
    binop c .ne (u256Val a) (u256Val b) = some (.ok (.bool (!decide (a = b)))) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, cmpInt]

theorem binop_mul_u256_ok (a b : Nat) (h : a * b < 2 ^ 256) :
    binop true .mul (u256Val a) (u256Val b) = some (.ok (u256Val (a * b))) := by
  have hcast : ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) := by simp
  have ht : ((a : Int) * (b : Int)).toNat = a * b := by rw [hcast]; exact Int.toNat_natCast _
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, mul, settle,
    IntTy.inRange, IntTy.min, IntTy.max, mkInt]
  rw [if_pos (by rw [hcast]; omega)]
  simp [ht]

theorem binop_mul_u256_overflow (a b : Nat) (h : 2 ^ 256 ≤ a * b) :
    binop true .mul (u256Val a) (u256Val b) = some (.error .overflow) := by
  have hcast : ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) := by simp
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, mul, settle,
    IntTy.inRange, IntTy.min, IntTy.max]
  rw [if_neg (by rw [hcast]; omega)]
  rfl

theorem binop_div_u256 (c : Bool) (a b : Nat) (ha : a < 2 ^ 256) (hb : b ≠ 0) :
    binop c .div (u256Val a) (u256Val b) = some (.ok (u256Val (a / b))) := by
  have hdiv' : (a : Int) / (b : Int) = ((a / b : Nat) : Int) := (Int.natCast_ediv a b).symm
  have hle : a / b ≤ a := Nat.div_le_self a b
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, div, settle,
    IntTy.inRange, IntTy.min, IntTy.max, IntTy.wrap, IntTy.isSigned, IntTy.width, mkInt, hb]
  have hle' : ((a / b : Nat) : Int) ≤ (a : Int) := Int.ofNat_le.mpr hle
  have ha' : (a : Int) < 2 ^ 256 := Int.ofNat_lt.mpr ha
  have hnn : ((0 : Nat) : Int) ≤ ((a / b : Nat) : Int) := Int.ofNat_le.mpr (Nat.zero_le _)
  rw [hdiv']
  cases c
  · rw [if_neg (by decide), Int.emod_eq_of_lt (by omega) (by omega)]
    show some (Except.ok (Value.uint ⟨256, by decide⟩ ((a / b : Nat) : Int).toNat)) = _
    rw [Int.toNat_natCast]
  · rw [if_pos rfl, if_pos (by omega)]
    show some (Except.ok (Value.uint ⟨256, by decide⟩ ((a / b : Nat) : Int).toNat)) = _
    rw [Int.toNat_natCast]

theorem binop_div_u256_zero (c : Bool) (a : Nat) :
    binop c .div (u256Val a) (u256Val 0) = some (.error .divByZero) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, div]
  rfl

theorem binop_mod_u256 (c : Bool) (a b : Nat) (hb : b ≠ 0) :
    binop c .mod (u256Val a) (u256Val b) = some (.ok (u256Val (a % b))) := by
  have hmod : Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]; exact (Int.natCast_emod a b).symm
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, mod, mkInt, hb]
  rw [hmod, Int.toNat_natCast]

theorem binop_mod_u256_zero (c : Bool) (a : Nat) :
    binop c .mod (u256Val a) (u256Val 0) = some (.error .divByZero) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, mod]
  rfl

/-- Unchecked `+`: wraps modulo `2^256`. -/
theorem binop_add_u256_unchecked (a b : Nat) :
    binop false .add (u256Val a) (u256Val b) = some (.ok (u256Val ((a + b) % 2 ^ 256))) := by
  have hcast : ((a : Int) + (b : Int)) % (2 ^ 256 : Int) = (((a + b) % 2 ^ 256 : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_add]; rfl
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, add, settle,
    IntTy.wrap, IntTy.isSigned, IntTy.width, mkInt]
  rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) = 2 ^ 256 from rfl,
    hcast, Int.toNat_natCast]
  rfl

theorem binop_mul_u256_unchecked (a b : Nat) :
    binop false .mul (u256Val a) (u256Val b) = some (.ok (u256Val ((a * b) % 2 ^ 256))) := by
  have hcast : ((a : Int) * (b : Int)) % (2 ^ 256 : Int) = (((a * b) % 2 ^ 256 : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_mul]; rfl
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, mul, settle,
    IntTy.wrap, IntTy.isSigned, IntTy.width, mkInt]
  rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) = 2 ^ 256 from rfl,
    hcast, Int.toNat_natCast]
  rfl

theorem binop_sub_u256_unchecked (a b : Nat) :
    binop false .sub (u256Val a) (u256Val b) = some (.ok (u256Val ((((a : Int) - b) % 2 ^ 256).toNat))) := by
  simp [binop, adoptBytes, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, sub, settle,
    IntTy.wrap, IntTy.isSigned, IntTy.width, mkInt]

theorem binop_eq_address (c : Bool) (a b : EVM.Address) :
    binop c .eq (.address a) (.address b) = some (.ok (.bool (decide (a.toNat = b.toNat)))) := by
  simp only [binop, toBool, addrNat, cmpNat]
  rfl

theorem binop_ne_address (c : Bool) (a b : EVM.Address) :
    binop c .ne (.address a) (.address b) = some (.ok (.bool (decide (a.toNat ≠ b.toNat)))) := by
  simp only [binop, toBool, addrNat, cmpNat]
  rfl

theorem unop_not (c : Bool) (b : Bool) : unop c .not (.bool b) = some (.ok (.bool (!b))) := rfl

/-! ## Events -/

theorem abiArgs_addr_addr_u256 (cfg : Config) (env : TypeEnv) (m : Machine) (a b : EVM.Address) (n : Nat) :
    abiArgs cfg env m [.address false, .address false, u256Ty] [.address a, .address b, u256Val n] =
      some (.ok ([.address a, .address b, .int n], m)) := by
  simp [abiArgs, coerce, fuelDefault]

/-- `Panic` payloads. -/
theorem Panic.data_overflow : Panic.data .overflow = panicData 0x11 := rfl

/-! ## Packed integer fields -/

theorem scalarOfAbi_uint_of_lt (env : TypeEnv) (w : ABI.BitWidth) (x : ℕ) (hx : x < 2 ^ w.val) :
    scalarOfAbi env (.uint w) (.int (Int.ofNat x)) = some (.uint w x) := by
  simp [scalarOfAbi]
  exact_mod_cast hx

theorem land_mask_toNat_lt (a : UInt256) (k : ℕ) (hk : k ≤ 256) :
    (UInt256.land a (UInt256.ofNat (2 ^ k - 1))).toNat < 2 ^ k := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlt : 2 ^ k - 1 < UInt256.size :=
    lt_of_lt_of_le (Nat.sub_lt hpos one_pos) (Nat.pow_le_pow_right (by decide) hk)
  rw [u256_land_toNat, ulit_toNat' _ hlt]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.and_lt_two_pow _ (Nat.sub_lt hpos one_pos))

theorem isValueType_uint (env : TypeEnv) (w : ABI.BitWidth) : isValueType env (.uint w) = true := rfl

/-- A packed `uintN` field at byte `offset` of a slot (`N = 8 * size`). -/
theorem readScalar_uint_offset {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {offset : Fin 32} {size : Fin 33} {w : ABI.BitWidth} {hbound : offset.val + size.val - 1 < 32}
    (hl : cfg.storage.layout er evm =
      some { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.uint w) })
    (hw : w.val = 8 * size.val) (hoff : 8 * offset.val < 256) :
    readScalar cfg env evm er (.uint w) =
      some (.uint w (UInt256.land
        (UInt256.div (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (256 ^ offset.val)))
        (UInt256.ofNat (256 ^ size.val - 1))).toNat) := by
  have hsize : 8 * size.val ≤ 256 := by have := size.isLt; omega
  refine readScalar_of_loc hl ?_
  rw [storageLocLoad_uint_offset evm slot offset size w hoff hsize]
  apply scalarOfAbi_uint_of_lt
  rw [hw, show (256 : ℕ) ^ size.val - 1 = 2 ^ (8 * size.val) - 1 by simp [Nat.pow_mul]]
  exact land_mask_toNat_lt _ _ hsize

/-- A packed `uintN` field at byte offset 0 of a slot. -/
theorem readScalar_uint_offset0 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {size : Fin 33} {w : ABI.BitWidth} {hbound : (0 : Fin 32).val + size.val - 1 < 32}
    (hl : cfg.storage.layout er evm =
      some { slot := slot, offset := 0, size := size, hbound := hbound, type := .int (.uint w) })
    (hw : w.val = 8 * size.val) :
    readScalar cfg env evm er (.uint w) =
      some (.uint w (UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat (2 ^ (8 * size.val) - 1))).toNat) := by
  have hsize : 8 * size.val ≤ 256 := by have := size.isLt; omega
  refine readScalar_of_loc hl ?_
  rw [storageLocLoad_uint_offset0 evm slot size w hsize]
  apply scalarOfAbi_uint_of_lt
  rw [hw]
  exact land_mask_toNat_lt _ _ hsize

/-- A packed `uintN` field written in place (`N = 8 * size`); `setPackedWordNat` is the new slot word. -/
theorem writeScalar_uint_packed {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    {offset : Fin 32} {size : Fin 33} {w : ABI.BitWidth} {hbound : offset.val + size.val - 1 < 32}
    (hl : cfg.storage.layout er evm =
      some { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.uint w) })
    (n : ℕ) (hn : n < 2 ^ 256) :
    writeScalar cfg evm er (.uint w n) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (setPackedWordNat (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat
          offset.val size.val n))) :=
  writeScalar_of_loc hl rfl (storageLocStore_uint_packed evm slot offset size w n hn)

/-! ## Memory structs written into storage -/

/-- One field of a memory struct written into storage (`writeStorageDeep`'s per-field step). -/
def writeStructField (cfg : Config) (env : TypeEnv) (fuel : ℕ) (h : Heap) (er : Solm.EvaledStorageRef)
    (fields : List (Ident × Value)) (evm : EVM.State) : Ty × Ident → Op EVM.State
  | (fty, fname) =>
    match fty with
    | .mapping .. => pure evm
    | _ =>
      match fields.find? (·.1 == fname) with
      | some (_, fv) => writeStorageDeep cfg env fuel evm h (fieldRef er fname) fty fv
      | none => Op.stuck

/-- `s = S(...)` for a memory struct: the declared fields are written one by one. -/
theorem writeStorageDeep_struct {cfg : Config} {env : TypeEnv} {fuel : ℕ} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {q : Option Ident} {n : Ident} {id : ℕ} {sty : Ty} {fields : List (Ident × Value)}
    {sd : StructInfo} (hget : h.get? id = some (.struct sty fields)) (hs : env.struct? q n = some sd) :
    writeStorageDeep cfg env (fuel + 1) evm h er (.user q n) (.memRef id) =
      sd.fields.foldlM (writeStructField cfg env fuel h er fields) evm := by
  rw [writeStorageDeep.eq_def]
  simp only [hget, hs]
  rfl

theorem writeStructField_u256 (cfg : Config) (env : TypeEnv) (fuel : ℕ) (h : Heap) (er : Solm.EvaledStorageRef)
    (fields : List (Ident × Value)) (evm : EVM.State) (fname fname' : Ident) (fv : Value)
    (hfind : fields.find? (·.1 == fname) = some (fname', fv)) :
    writeStructField cfg env fuel h er fields evm (u256Ty, fname) =
      writeStorageDeep cfg env fuel evm h (fieldRef er fname) u256Ty fv := by
  simp [writeStructField, hfind]

theorem writeStructField_mapping (cfg : Config) (env : TypeEnv) (fuel : ℕ) (h : Heap) (er : Solm.EvaledStorageRef)
    (fields : List (Ident × Value)) (evm : EVM.State) (k v : Ty) (fname : Ident) :
    writeStructField cfg env fuel h er fields evm (.mapping k v, fname) = pure evm := rfl

theorem writeStructField_scalar (cfg : Config) (env : TypeEnv) (fuel : ℕ) (h : Heap) (er : Solm.EvaledStorageRef)
    (fields : List (Ident × Value)) (evm : EVM.State) (fty : Ty) (fname fname' : Ident) (fv : Value)
    (hnm : ∀ k v, fty ≠ .mapping k v) (hfind : fields.find? (·.1 == fname) = some (fname', fv)) :
    writeStructField cfg env fuel h er fields evm (fty, fname) =
      writeStorageDeep cfg env fuel evm h (fieldRef er fname) fty fv := by
  cases fty <;> simp [writeStructField, hfind]
  exact absurd rfl (hnm _ _)

/-! ## ABI types and values of expression results (`abi.encode*`, `keccak256`) -/

@[simp] theorem abiTyOfValue_uint (env : TypeEnv) (h : Heap) (w : ABI.BitWidth) (n : ℕ) :
    abiTyOfValue env h (.uint w n) = some (.elem (.int (.uint w))) := rfl

@[simp] theorem abiTyOfValue_address (env : TypeEnv) (h : Heap) (a : EVM.Address) :
    abiTyOfValue env h (.address a) = some (.elem .address) := rfl

@[simp] theorem abiTyOfValue_bool (env : TypeEnv) (h : Heap) (b : Bool) :
    abiTyOfValue env h (.bool b) = some (.elem .bool) := rfl

@[simp] theorem abiTyOfValue_fixedBytes (env : TypeEnv) (h : Heap) (n : Fin 32) (bs : List UInt8) :
    abiTyOfValue env h (.fixedBytes n bs) = some (.elem (.bytes n)) := rfl

@[simp] theorem abiTyOfValue_strLit (env : TypeEnv) (h : Heap) (s : ByteArray) :
    abiTyOfValue env h (.strLit s) = some .string := by
  simp [abiTyOfValue]

theorem abiTyOfValue_memBytes {env : TypeEnv} {h : Heap} {id : ℕ} {s : Bool} {d : ByteArray}
    (hget : h.get? id = some (.bytes s d)) :
    abiTyOfValue env h (.memRef id) = some (if s then .string else .bytes) := by
  simp [abiTyOfValue, hget]

@[simp] theorem toAbi_fixedBytes (h : Heap) (fuel : ℕ) (n : Fin 32) (bs : List UInt8) :
    toAbi h (fuel + 1) (.fixedBytes n bs) = some (.fixedBytes n bs) := by
  simp [toAbi, scalarToAbi]

@[simp] theorem toAbi_strLit (h : Heap) (fuel : ℕ) (s : ByteArray) :
    toAbi h (fuel + 1) (.strLit s) = some (.bytes s) := by
  simp [toAbi, scalarToAbi]

theorem toAbi_memBytes {h : Heap} {id : ℕ} {s : Bool} {d : ByteArray} (fuel : ℕ)
    (hget : h.get? id = some (.bytes s d)) : toAbi h (fuel + 1) (.memRef id) = some (.bytes d) := by
  simp [toAbi, hget]

theorem encodePackedValue?_u256 (n : ℕ) (hn : n < 2 ^ 256) :
    ABI.encodePackedValue? (.elem (.int (.uint ⟨256, by decide⟩))) (.int n) = some (EVM.Word.toBytesBE (UInt256.ofNat n)) := by
  have hn' : n < EVM.twoPow 256 := hn
  simp [ABI.encodePackedValue?, ABI.encodeABIWord?, hn']
  rfl

theorem encodePackedValue?_address (a : EVM.Address) :
    ABI.encodePackedValue? (.elem .address) (.address a) = some ((EVM.Word.toBytesBE (UInt256.ofNat a.toNat)).drop 12) := by
  simp [ABI.encodePackedValue?]
  rfl

theorem encodePackedValue?_bytes32 (bs : List UInt8) (h : bs.length = 32) :
    ABI.encodePackedValue? (.elem (.bytes ⟨31, by decide⟩)) (.fixedBytes ⟨31, by decide⟩ bs) = some bs := by
  simp [ABI.encodePackedValue?, h]

@[simp] theorem encodePackedValue?_bytes (ba : ByteArray) : ABI.encodePackedValue? .bytes (.bytes ba) = some ba.toList := rfl
@[simp] theorem encodePackedValue?_string (ba : ByteArray) : ABI.encodePackedValue? .string (.bytes ba) = some ba.toList := rfl

theorem abiArgsAbi_of_mapM {env : TypeEnv} {m : Machine} {tys : List ABI.ABIType} {vs : List Value} {svs : List ABI.ABIValue}
    (hsvs : vs.mapM (toAbi m.heap fuelDefault) = some svs) : abiArgsAbi cfg env m tys vs = some (.ok (svs, m)) := by
  simp [abiArgsAbi, hsvs]

/-! ## Explicit conversions -/

theorem explicitConv_uint_widen (env : TypeEnv) (h : Heap) (w w' : ABI.BitWidth) (n : ℕ) (hle : w.val ≤ w'.val) :
    explicitConv env h (.uint w n) (.uint w') = some (.ok (.uint w' n, h)) := by
  simp [explicitConv, implicitConv, hle]

theorem explicitConv_uint_narrow (env : TypeEnv) (h : Heap) (w w' : ABI.BitWidth) (n : ℕ) (hlt : w'.val < w.val) :
    explicitConv env h (.uint w n) (.uint w') = some (.ok (.uint w' (n % 2 ^ w'.val), h)) := by
  simp [explicitConv, implicitConv, Nat.not_le.mpr hlt]

theorem explicitConv_uint160_address (env : TypeEnv) (h : Heap) (n : ℕ) (p : Bool) :
    explicitConv env h (.uint ⟨160, by decide⟩ n) (.address p) = some (.ok (.address (EVM.address n), h)) := by
  simp [explicitConv, implicitConv]

theorem explicitConv_address_uint160 (env : TypeEnv) (h : Heap) (a : EVM.Address) :
    explicitConv env h (.address a) (.uint ⟨160, by decide⟩) = some (.ok (.uint ⟨160, by decide⟩ a.toNat, h)) := by
  simp [explicitConv, implicitConv]

theorem explicitConv_address_address (env : TypeEnv) (h : Heap) (a : EVM.Address) (p : Bool) :
    explicitConv env h (.address a) (.address p) = some (.ok (.address a, h)) := by
  simp [explicitConv, implicitConv]

theorem explicitConv_address_contract (env : TypeEnv) (h : Heap) (a : EVM.Address) (q : Option Ident) (n : Ident)
    (hc : (env.contractKind? n).isSome = true) (he : (env.enum? q n).isNone = true) :
    explicitConv env h (.address a) (.user q n) = some (.ok (.contract n a, h)) := by
  simp [explicitConv, implicitConv, hc, he]

theorem explicitConv_contract_address (env : TypeEnv) (h : Heap) (c : Ident) (a : EVM.Address) (p : Bool) :
    explicitConv env h (.contract c a) (.address p) = some (.ok (.address a, h)) := by
  simp [explicitConv, implicitConv]

theorem explicitConv_u256_bytes32 (env : TypeEnv) (h : Heap) (n : ℕ) :
    explicitConv env h (u256Val n) (.fixedBytes ⟨31, by decide⟩) =
      some (.ok (.fixedBytes ⟨31, by decide⟩ (natToBytesBE n 32), h)) := by
  simp [explicitConv, implicitConv]

theorem explicitConv_bytes32_u256 (env : TypeEnv) (h : Heap) (bs : List UInt8) :
    explicitConv env h (.fixedBytes ⟨31, by decide⟩ bs) u256Ty = some (.ok (u256Val (bytesToNatBE bs), h)) := by
  simp [explicitConv, implicitConv]

theorem explicitConv_literal_address (env : TypeEnv) (h : Heap) (i : Int) (hd : Option Nat) (p : Bool)
    (h0 : 0 ≤ i) (hi : i < 2 ^ 160) :
    explicitConv env h (.literal i hd) (.address p) = some (.ok (.address (EVM.address i.toNat), h)) := by
  simp [explicitConv, implicitConv, h0]
  intro hbad
  omega

/-! ## Shifts, bitwise operators, exponentiation on `uint256` -/

/-- `Int.toNat` of a modular product of naturals (the shape `IntTy.wrap` leaves). -/
theorem toNat_natCast_mul_pow_emod (a s : ℕ) :
    ((a : ℤ) * 2 ^ s % (2 ^ 256 : ℤ)).toNat = a * 2 ^ s % 2 ^ 256 := by
  have h : ((a * 2 ^ s % 2 ^ 256 : ℕ) : ℤ) = (a : ℤ) * 2 ^ s % (2 ^ 256 : ℤ) := by push_cast; rfl
  rw [← h, Int.toNat_natCast]

theorem emod_toNat_of_lt (a : ℕ) (ha : a < 2 ^ 256) : ((a : ℤ) % (2 ^ 256 : ℤ)).toNat = a := by
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast ha), Int.toNat_natCast]

theorem binop_shl_u256 (c : Bool) (a s : ℕ) (hs : s < 256) :
    binop c .shl (u256Val a) (u256Val s) = some (.ok (u256Val (a * 2 ^ s % 2 ^ 256))) := by
  have key := toNat_natCast_mul_pow_emod a s
  simp [binop, adoptBytes, toBool, addrNat, natOperand, Value.int?, shl, IntTy.wrap, IntTy.width, IntTy.isSigned,
    mkInt, Nat.not_le.mpr hs]
  exact congrArg (fun x => some (Except.ok (u256Val x))) (by simpa using key)

theorem binop_shl_u256_lit (c : Bool) (a : ℕ) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 256) :
    binop c .shl (u256Val a) (.literal k hd) = some (.ok (u256Val (a * 2 ^ k.toNat % 2 ^ 256))) := by
  have key := toNat_natCast_mul_pow_emod a k.toNat
  simp [binop, adoptBytes, toBool, addrNat, natOperand, Value.int?, shl, IntTy.wrap, IntTy.width, IntTy.isSigned,
    mkInt, h0]
  rw [if_neg (by omega)]
  exact congrArg (fun x => some (Except.ok (u256Val x))) (by simpa using key)

theorem binop_shr_u256 (c : Bool) (a s : ℕ) (hs : s < 256) :
    binop c .shr (u256Val a) (u256Val s) = some (.ok (u256Val (a / 2 ^ s))) := by
  simp [binop, adoptBytes, toBool, addrNat, natOperand, Value.int?, shr, mkInt, IntTy.width, Nat.not_le.mpr hs]
  rw [← Int.natCast_shiftRight, Int.toNat_natCast, Nat.shiftRight_eq_div_pow]

theorem binop_shr_u256_lit (c : Bool) (a : ℕ) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 256) :
    binop c .shr (u256Val a) (.literal k hd) = some (.ok (u256Val (a / 2 ^ k.toNat))) := by
  simp [binop, adoptBytes, toBool, addrNat, natOperand, Value.int?, shr, mkInt, IntTy.width, h0]
  rw [if_neg (by omega), ← Int.natCast_shiftRight, Int.toNat_natCast, Nat.shiftRight_eq_div_pow]

theorem binop_bitAnd_u256 (c : Bool) (a b : ℕ) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    binop c .bitAnd (u256Val a) (u256Val b) = some (.ok (u256Val (a &&& b))) := by
  have h1 := emod_toNat_of_lt a ha
  have h2 := emod_toNat_of_lt b hb
  have h3 := emod_toNat_of_lt (a &&& b) (lt_of_le_of_lt (Nat.and_le_left) ha)
  norm_num at h1 h2 h3
  simp [binop, adoptBytes, toBool, addrNat, unifyInts_u256_u256, isCmp, bitAnd, IntTy.toWord, IntTy.wrap, IntTy.width,
    IntTy.isSigned, mkInt, h1, h2, h3]

theorem binop_bitOr_u256 (c : Bool) (a b : ℕ) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    binop c .bitOr (u256Val a) (u256Val b) = some (.ok (u256Val (a ||| b))) := by
  have h1 := emod_toNat_of_lt a ha
  have h2 := emod_toNat_of_lt b hb
  have h3 := emod_toNat_of_lt (a ||| b) (Nat.or_lt_two_pow ha hb)
  norm_num at h1 h2 h3
  simp [binop, adoptBytes, toBool, addrNat, unifyInts_u256_u256, isCmp, bitOr, IntTy.toWord, IntTy.wrap, IntTy.width,
    IntTy.isSigned, mkInt, h1, h2, h3]

theorem binop_bitXor_u256 (c : Bool) (a b : ℕ) (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    binop c .bitXor (u256Val a) (u256Val b) = some (.ok (u256Val (a ^^^ b))) := by
  have h1 := emod_toNat_of_lt a ha
  have h2 := emod_toNat_of_lt b hb
  have h3 := emod_toNat_of_lt (a ^^^ b) (Nat.xor_lt_two_pow ha hb)
  norm_num at h1 h2 h3
  simp [binop, adoptBytes, toBool, addrNat, unifyInts_u256_u256, isCmp, bitXor, IntTy.toWord, IntTy.wrap, IntTy.width,
    IntTy.isSigned, mkInt, h1, h2, h3]

theorem binop_bitAnd_u256_lit (c : Bool) (a : ℕ) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k) (hk : k < 2 ^ 256)
    (ha : a < 2 ^ 256) :
    binop c .bitAnd (u256Val a) (.literal k hd) = some (.ok (u256Val (a &&& k.toNat))) := by
  have h1 := emod_toNat_of_lt a ha
  have h2 : (k % (2 ^ 256 : ℤ)).toNat = k.toNat := by rw [Int.emod_eq_of_lt h0 hk]
  have h3 := emod_toNat_of_lt (a &&& k.toNat) (lt_of_le_of_lt (Nat.and_le_left) ha)
  norm_num at h1 h2 h3
  simp [binop, adoptBytes, toBool, addrNat, unifyInts_u256_lit a k hd h0 hk, isCmp, bitAnd, IntTy.toWord, IntTy.wrap,
    IntTy.width, IntTy.isSigned, mkInt, h1, h2, h3]

theorem unop_bitNot_u256 (c : Bool) (a : ℕ) (ha : a < 2 ^ 256) :
    unop c .bitNot (u256Val a) = some (.ok (u256Val (2 ^ 256 - 1 - a))) := by
  have h1 := emod_toNat_of_lt a ha
  have h3 := emod_toNat_of_lt (2 ^ 256 - 1 - a) (by omega)
  have h4 : ((2 ^ 256 - 1 : ℤ) - a) = ((2 ^ 256 - 1 - a : ℕ) : ℤ) := by omega
  norm_num at h1 h3 h4
  simp [unop, Value.int?, bitNot, IntTy.toWord, IntTy.wrap, IntTy.width, IntTy.isSigned, mkInt, h1, h4, h3]

/-- Checked `x ** b` on `uint256`, in range. -/
theorem exp_u256_ok (x : ℤ) (b : ℕ) (h0 : 0 ≤ x) (hb : b < 256) (hfit : x ^ b < 2 ^ 256) :
    exp u256IntTy true x b = .ok (x ^ b) := by
  unfold exp
  by_cases hx0 : x = 0
  · subst hx0
    cases b <;> simp
  by_cases hx1 : x = 1
  · subst hx1; simp
  have hm1 : x ≠ -1 := by omega
  simp only [hx0, hx1, hm1, if_false, IntTy.width]
  rw [if_neg (by simpa using hb)]
  exact settle_u256_ok _ (pow_nonneg h0 b) hfit

theorem exp_u256_overflow (x : ℤ) (b : ℕ) (h2 : 2 ≤ x) (hbig : 2 ^ 256 ≤ x ^ b) :
    exp u256IntTy true x b = .error .overflow := by
  unfold exp
  have hx0 : x ≠ 0 := by omega
  have hx1 : x ≠ 1 := by omega
  have hm1 : x ≠ -1 := by omega
  simp only [hx0, hx1, hm1, if_false, IntTy.width]
  split
  · rfl
  · exact settle_u256_overflow _ (by omega)

theorem binop_exp_u256 (a b : ℕ) (hb : b < 256) (hfit : a ^ b < 2 ^ 256) :
    binop true .exp (u256Val a) (u256Val b) = some (.ok (u256Val (a ^ b))) := by
  have hfit' : (a : ℤ) ^ b < 2 ^ 256 := by exact_mod_cast hfit
  simp [binop, adoptBytes, toBool, addrNat, natOperand, Value.int?, exp_u256_ok (a : ℤ) b (by omega) hb hfit', mkInt]
  exact congrArg (fun x => some (Except.ok (u256Val x))) (by rw [← Int.natCast_pow, Int.toNat_natCast])

theorem binop_exp_u256_overflow (a b : ℕ) (h2 : 2 ≤ a) (hbig : 2 ^ 256 ≤ a ^ b) :
    binop true .exp (u256Val a) (u256Val b) = some (.error .overflow) := by
  have hbig' : (2 : ℤ) ^ 256 ≤ (a : ℤ) ^ b := by exact_mod_cast hbig
  simp [binop, adoptBytes, toBool, addrNat, natOperand, Value.int?, exp_u256_overflow (a : ℤ) b (by omega) hbig',
    Op.panic, ExceptT.mk]

/-- `k ** b` with a number-literal base (`10 ** decimals`). -/
theorem binop_exp_lit_u256 (k : Int) (hd : Option Nat) (b : ℕ) (w : ABI.BitWidth) (h0 : 0 ≤ k) (hb : b < 256)
    (hfit : k ^ b < 2 ^ 256) :
    binop true .exp (.literal k hd) (.uint w b) = some (.ok (u256Val (k ^ b).toNat)) := by
  simp [binop, adoptBytes, toBool, addrNat, natOperand, literalBase, Int.not_lt.mpr h0]
  rw [show uint256Ty = u256IntTy from rfl, exp_u256_ok k b h0 hb hfit]
  rfl

theorem binop_exp_lit_lit (c : Bool) (x y : Int) (hx hy : Option Nat) (h0 : 0 ≤ y) :
    binop c .exp (.literal x hx) (.literal y hy) = some (.ok (.literal (x ^ y.toNat))) := by
  simp [binop, adoptBytes, toBool, addrNat, natOperand, h0]

/-! ## Comparisons with number literals, `Int.toNat` of casts -/

/-- Comparison of a `uint256` with a number literal: `cmpInt` on the integers. -/
theorem binop_cmp_u256_lit (c : Bool) (op : BinOp) (hop : isCmp op = true) (x : ℕ) (k : Int) (hd : Option Nat)
    (h0 : 0 ≤ k) (hk : k < 2 ^ 256) :
    binop c op (u256Val x) (.literal k hd) = Op.ofOpt (cmpInt op x k) := by
  cases op <;> simp [binop, adoptBytes, toBool, addrNat, unifyInts_u256_lit x k hd h0 hk, isCmp, cmpInt] at hop ⊢

theorem toNat_natCast_add (x k : ℕ) : ((x : ℤ) + k).toNat = x + k := by omega
theorem toNat_natCast_sub (x k : ℕ) (h : k ≤ x) : ((x : ℤ) - k).toNat = x - k := by omega
theorem toNat_natCast_mul (x k : ℕ) : ((x : ℤ) * k).toNat = x * k := by
  rw [← Int.natCast_mul, Int.toNat_natCast]
theorem toNat_natCast_pow (x k : ℕ) : ((x : ℤ) ^ k).toNat = x ^ k := by
  rw [← Int.natCast_pow, Int.toNat_natCast]

/-! ## Mapping keys of other value types, member dispatch, `delete` -/

@[simp] theorem storageIndex_mapping_uint (cfg : Config) (env : TypeEnv) (evm : EVM.State) (h : Heap)
    (er : Solm.EvaledStorageRef) (w : ABI.BitWidth) (v : Ty) (n : ℕ) :
    storageIndex cfg env evm h er (.mapping (.uint w) v) (.uint w n) = some (.ok (keyRef er (.int n), v)) := by
  simp [storageIndex, implicitConv, keyOf]

@[simp] theorem storageIndex_mapping_bytes32 (cfg : Config) (env : TypeEnv) (evm : EVM.State) (h : Heap)
    (er : Solm.EvaledStorageRef) (v : Ty) (bs : List UInt8) :
    storageIndex cfg env evm h er (.mapping (.fixedBytes ⟨31, by decide⟩) v) (.fixedBytes ⟨31, by decide⟩ bs) =
      some (.ok (keyRef er (.fixedBytes ⟨31, by decide⟩ bs), v)) := by
  simp [storageIndex, keyOf]

@[simp] theorem storageIndex_mapping_bool (cfg : Config) (env : TypeEnv) (evm : EVM.State) (h : Heap)
    (er : Solm.EvaledStorageRef) (v : Ty) (b : Bool) :
    storageIndex cfg env evm h er (.mapping .bool v) (.bool b) = some (.ok (keyRef er (.bool b), v)) := by
  simp [storageIndex, keyOf]

theorem storageIndex_mapping_u256_lit (cfg : Config) (env : TypeEnv) (evm : EVM.State) (h : Heap)
    (er : Solm.EvaledStorageRef) (v : Ty) (k : ℕ) (hd : Option Nat) (hk : k < 2 ^ 256) :
    storageIndex cfg env evm h er (.mapping u256Ty v) (.literal k hd) = some (.ok (keyRef er (.int k), v)) := by
  simp [storageIndex, implicitConv_literal_u256 env h k hd (Int.natCast_nonneg k) (by exact_mod_cast hk), keyOf]

theorem directMember_index (fc : FlatContract) (fr : Frame) (e i : Expr) : directMember fc fr (.index e i) = false := rfl
theorem directMember_member (fc : FlatContract) (fr : Frame) (e : Expr) (f : Ident) :
    directMember fc fr (.member e f) = false := rfl
theorem directMember_ident (fc : FlatContract) (fr : Frame) (x : Ident) (henv : isEnvObj x = false)
    (hx : (fr.get? x).isNone = false ∨ (fc.types.enum? none x).isSome = false) :
    directMember fc fr (.ident x) = false := by
  rcases hx with h | h <;> simp [directMember, henv, h]

theorem clearStorage_bool {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (fuel : ℕ) (hl : cfg.storage.layout er evm = some (boolOffset0Loc slot)) :
    clearStorage cfg env (fuel + 1) evm er .bool =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.lnot ⟨255⟩)))) := by
  have hw := writeScalar_bool_false hl
  rw [clearStorage]
  all_goals first
    | (simp only [storageTyOf, zeroValue]
       rw [hw]
       rfl)
    | (intros; simp_all)

theorem clearStorage_address {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (fuel : ℕ) (p : Bool) (hl : cfg.storage.layout er evm = some (addressOffset0Loc slot)) :
    clearStorage cfg env (fuel + 1) evm er (.address p) =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩))) := by
  have hw := writeScalar_address hl ⟨0⟩ (by decide)
  have hz : EVM.address 0 = AccountAddress.ofNat (⟨0⟩ : UInt256).toNat := by decide
  rw [clearStorage]
  all_goals first
    | (simp only [storageTyOf, zeroValue]
       rw [hz, hw]
       rfl)
    | (intros; simp_all)

theorem clearStorage_struct {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {q : Option Ident} {n : Ident} {s : StructInfo} (fuel : ℕ)
    (henum : (env.enum? q n).isSome = false) (hcon : (env.contractKind? n).isSome = false)
    (hs : env.struct? q n = some s) :
    clearStorage cfg env (fuel + 1) evm er (.user q n) =
      s.fields.foldlM (fun evm (fty, fname) => clearStorage cfg env fuel evm (fieldRef er fname) fty) evm := by
  rw [clearStorage]
  all_goals first
    | (simp [storageTyOf, zeroValue, henum, hcon, hs]
       try rfl)
    | (intros; simp_all)

/-! ## Number literals as right-hand sides, unchecked `+ 1` -/

theorem writeStorageDeep_literal_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {slot : UInt256} (hl : cfg.storage.layout er evm = some (uint256Loc slot)) (fuel : ℕ)
    (k : ℕ) (hd : Option Nat) (hk : k < 2 ^ 256) :
    writeStorageDeep cfg env (fuel + 1) evm h er u256Ty (.literal k hd) =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat k))) := by
  have hw := writeScalar_u256 hl (UInt256.ofNat k)
  rw [ulit_toNat' k hk] at hw
  rw [writeStorageDeep]
  · simp only [implicitConv_literal_u256 env h k hd (Int.natCast_nonneg k) (by exact_mod_cast hk), Int.toNat_natCast,
      Op.ofOpt, hw]
    rfl
  all_goals (intros; simp_all)

theorem assign_storage_u256_lit {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er m.evm = some (uint256Loc slot)) (k : ℕ) (hd : Option Nat)
    (hk : k < 2 ^ 256) :
    assign cfg env fr m (.storage er u256Ty) (.literal k hd) =
      some (.ok (fr, { m with evm := Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot (UInt256.ofNat k) })) := by
  simp [assign, fuelDefault, writeStorageDeep_literal_u256 hl 1023 k hd hk]

theorem assign_local_u256_lit {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {x : Ident} (l : Local)
    (hx : fr.get? x = some l) (hty : l.ty = u256Ty) (k : ℕ) (hd : Option Nat) (hk : k < 2 ^ 256) :
    assign cfg env fr m (.local x) (.literal k hd) = some (.ok (fr.setVal x (u256Val k), m)) := by
  simp [assign, hx, hty, coerce_literal_u256 cfg env m k hd l.loc (Int.natCast_nonneg k) (by exact_mod_cast hk)]

theorem binop_add_u256_lit1_unchecked (n : ℕ) :
    binop false .add (u256Val n) (.literal 1) = some (.ok (u256Val ((n + 1) % 2 ^ 256))) := by
  have key : ((n : ℤ) + 1) % (2 ^ 256 : ℤ) = (((n + 1) % 2 ^ 256 : ℕ) : ℤ) := by push_cast; rfl
  rw [binop_add_uint_of_unify false _ n _ (unifyInts_u256_lit n 1 none (by decide) (by decide)), add, settle_unchecked,
    liftArith_ok]
  simp only [mkInt, IntTy.wrap, IntTy.isSigned, IntTy.width, Bool.false_and, Bool.false_eq_true, if_false]
  rw [key, Int.toNat_natCast]

/-! ## Environment members and `bool` slots -/

theorem wordNat_eq (n : ℕ) (hn : n < UInt256.size) : wordNat n = u256Val n := by
  show Value.uint ⟨256, by decide⟩ (UInt256.ofNat n).toNat = _
  rw [ulit_toNat' n hn]

@[simp] theorem envMember_value (m : Machine) :
    envMember m "msg" "value" = some (u256Val m.evm.executionEnv.weiValue.toNat) := by
  show some (wordNat _) = _
  rw [wordNat_eq m.evm.executionEnv.weiValue.toNat (by exact m.evm.executionEnv.weiValue.val.isLt)]

@[simp] theorem envMember_timestamp (m : Machine) :
    envMember m "block" "timestamp" = some (wordNat m.evm.executionEnv.header.timestamp) := rfl
@[simp] theorem envMember_number (m : Machine) :
    envMember m "block" "number" = some (wordNat m.evm.executionEnv.header.number) := rfl
@[simp] theorem envMember_chainid (m : Machine) : envMember m "block" "chainid" = some (wordNat Ethereum.chainId) := rfl
@[simp] theorem envMember_origin (m : Machine) : envMember m "tx" "origin" = some (.address m.evm.executionEnv.sender) := rfl

theorem readScalar_bool {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (boolOffset0Loc slot)) :
    readScalar cfg env evm er .bool =
      some (.bool (!((UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0))) := by
  refine readScalar_of_loc hl ?_
  rw [storageLocLoad_bool_offset0]
  cases h : (UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0 <;>
    simp [ABI.wordToElem, scalarOfAbi, h]

theorem loadIfScalar_bool {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (boolOffset0Loc slot)) :
    loadIfScalar cfg env evm er .bool =
      some (.bool (!((UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0))) := by
  unfold loadIfScalar
  rw [if_pos (by rfl : isValueType env .bool = true)]
  exact readScalar_bool hl

/-! ## `int256` -/

abbrev s256Ty : Ty := .int ⟨256, by decide⟩
abbrev s256Val (i : Int) : Value := .sint ⟨256, by decide⟩ i
abbrev s256IntTy : IntTy := .sint ⟨256, by decide⟩

theorem settle_s256_ok (r : Int) (hlo : -2 ^ 255 ≤ r) (hhi : r < 2 ^ 255) : settle s256IntTy true r = .ok r := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]; omega

theorem settle_s256_overflow (r : Int) (h : ¬ (-2 ^ 255 ≤ r ∧ r < 2 ^ 255)) :
    settle s256IntTy true r = .error .overflow := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]; omega

theorem unifyInts_s256_s256 (a b : Int) :
    unifyInts (s256Val a) (s256Val b) = some (some s256IntTy, a, b) := by
  simp [unifyInts, Value.int?, commonIntType, implicitIntConv]

theorem unifyInts_s256_lit (a k : Int) (hd : Option Nat) (hlo : -2 ^ 255 ≤ k) (hhi : k < 2 ^ 255) :
    unifyInts (s256Val a) (.literal k hd) = some (some s256IntTy, a, k) := by
  simp [unifyInts, Value.int?, IntTy.inRange, IntTy.min, IntTy.max]; omega

theorem binop_add_sint_of_unify (c : Bool) (w : ABI.BitWidth) (i : Int) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.sint w i) b = some (some t, x, y)) :
    binop c .add (.sint w i) b = liftArith t (add t c x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases add t c x y <;> rfl

theorem binop_sub_sint_of_unify (c : Bool) (w : ABI.BitWidth) (i : Int) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.sint w i) b = some (some t, x, y)) :
    binop c .sub (.sint w i) b = liftArith t (sub t c x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases sub t c x y <;> rfl

theorem binop_mul_sint_of_unify (c : Bool) (w : ABI.BitWidth) (i : Int) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.sint w i) b = some (some t, x, y)) :
    binop c .mul (.sint w i) b = liftArith t (mul t c x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases mul t c x y <;> rfl

theorem binop_div_sint_of_unify (c : Bool) (w : ABI.BitWidth) (i : Int) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.sint w i) b = some (some t, x, y)) :
    binop c .div (.sint w i) b = liftArith t (div t c x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases div t c x y <;> rfl

theorem binop_mod_sint_of_unify (c : Bool) (w : ABI.BitWidth) (i : Int) (b : Value) {t : IntTy} {x y : Int}
    (hu : unifyInts (.sint w i) b = some (some t, x, y)) :
    binop c .mod (.sint w i) b = liftArith t (mod t x y) := by
  simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, Op.panic, ExceptT.mk]
  cases mod t x y <;> rfl

theorem binop_cmp_sint_of_unify (c : Bool) (op : BinOp) (hop : isCmp op = true) (w : ABI.BitWidth) (i : Int) (b : Value)
    {t : IntTy} {x y : Int} (hu : unifyInts (.sint w i) b = some (some t, x, y)) :
    binop c op (.sint w i) b = Op.ofOpt (cmpInt op x y) := by
  cases op <;> simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, cmpInt] at hop ⊢

theorem binop_add_s256 (a b : Int) (hlo : -2 ^ 255 ≤ a + b) (hhi : a + b < 2 ^ 255) :
    binop true .add (s256Val a) (s256Val b) = some (.ok (s256Val (a + b))) := by
  rw [binop_add_sint_of_unify true _ a _ (unifyInts_s256_s256 a b), add, settle_s256_ok _ hlo hhi, liftArith_ok]
  rfl

theorem binop_add_s256_overflow (a b : Int) (h : ¬ (-2 ^ 255 ≤ a + b ∧ a + b < 2 ^ 255)) :
    binop true .add (s256Val a) (s256Val b) = some (.error .overflow) := by
  rw [binop_add_sint_of_unify true _ a _ (unifyInts_s256_s256 a b), add, settle_s256_overflow _ h, liftArith_error]

theorem binop_sub_s256 (a b : Int) (hlo : -2 ^ 255 ≤ a - b) (hhi : a - b < 2 ^ 255) :
    binop true .sub (s256Val a) (s256Val b) = some (.ok (s256Val (a - b))) := by
  rw [binop_sub_sint_of_unify true _ a _ (unifyInts_s256_s256 a b), sub, settle_s256_ok _ hlo hhi, liftArith_ok]
  rfl

theorem binop_sub_s256_overflow (a b : Int) (h : ¬ (-2 ^ 255 ≤ a - b ∧ a - b < 2 ^ 255)) :
    binop true .sub (s256Val a) (s256Val b) = some (.error .overflow) := by
  rw [binop_sub_sint_of_unify true _ a _ (unifyInts_s256_s256 a b), sub, settle_s256_overflow _ h, liftArith_error]

theorem binop_mul_s256 (a b : Int) (hlo : -2 ^ 255 ≤ a * b) (hhi : a * b < 2 ^ 255) :
    binop true .mul (s256Val a) (s256Val b) = some (.ok (s256Val (a * b))) := by
  rw [binop_mul_sint_of_unify true _ a _ (unifyInts_s256_s256 a b), mul, settle_s256_ok _ hlo hhi, liftArith_ok]
  rfl

theorem binop_mul_s256_overflow (a b : Int) (h : ¬ (-2 ^ 255 ≤ a * b ∧ a * b < 2 ^ 255)) :
    binop true .mul (s256Val a) (s256Val b) = some (.error .overflow) := by
  rw [binop_mul_sint_of_unify true _ a _ (unifyInts_s256_s256 a b), mul, settle_s256_overflow _ h, liftArith_error]

/-- Truncating division; `type(int256).min / -1` is the overflow case (`settle_s256_overflow`). -/
theorem binop_div_s256 (a b : Int) (hb : b ≠ 0) (hlo : -2 ^ 255 ≤ Int.tdiv a b) (hhi : Int.tdiv a b < 2 ^ 255) :
    binop true .div (s256Val a) (s256Val b) = some (.ok (s256Val (Int.tdiv a b))) := by
  rw [binop_div_sint_of_unify true _ a _ (unifyInts_s256_s256 a b), div, if_neg hb, settle_s256_ok _ hlo hhi,
    liftArith_ok]
  rfl

theorem binop_div_s256_zero (c : Bool) (a : Int) :
    binop c .div (s256Val a) (s256Val 0) = some (.error .divByZero) := by
  rw [binop_div_sint_of_unify c _ a _ (unifyInts_s256_s256 a 0), div, if_pos rfl, liftArith_error]

theorem binop_mod_s256 (c : Bool) (a b : Int) (hb : b ≠ 0) :
    binop c .mod (s256Val a) (s256Val b) = some (.ok (s256Val (Int.tmod a b))) := by
  rw [binop_mod_sint_of_unify c _ a _ (unifyInts_s256_s256 a b), mod, if_neg hb, liftArith_ok]
  rfl

theorem binop_lt_s256 (c : Bool) (a b : Int) :
    binop c .lt (s256Val a) (s256Val b) = some (.ok (.bool (decide (a < b)))) := by
  rw [binop_cmp_sint_of_unify c .lt rfl _ a _ (unifyInts_s256_s256 a b)]; rfl
theorem binop_le_s256 (c : Bool) (a b : Int) :
    binop c .le (s256Val a) (s256Val b) = some (.ok (.bool (decide (a ≤ b)))) := by
  rw [binop_cmp_sint_of_unify c .le rfl _ a _ (unifyInts_s256_s256 a b)]; rfl
theorem binop_gt_s256 (c : Bool) (a b : Int) :
    binop c .gt (s256Val a) (s256Val b) = some (.ok (.bool (decide (a > b)))) := by
  rw [binop_cmp_sint_of_unify c .gt rfl _ a _ (unifyInts_s256_s256 a b)]; rfl
theorem binop_ge_s256 (c : Bool) (a b : Int) :
    binop c .ge (s256Val a) (s256Val b) = some (.ok (.bool (decide (a ≥ b)))) := by
  rw [binop_cmp_sint_of_unify c .ge rfl _ a _ (unifyInts_s256_s256 a b)]; rfl
theorem binop_eq_s256 (c : Bool) (a b : Int) :
    binop c .eq (s256Val a) (s256Val b) = some (.ok (.bool (decide (a = b)))) := by
  rw [binop_cmp_sint_of_unify c .eq rfl _ a _ (unifyInts_s256_s256 a b)]; rfl
theorem binop_ne_s256 (c : Bool) (a b : Int) :
    binop c .ne (s256Val a) (s256Val b) = some (.ok (.bool (decide (a ≠ b)))) := by
  rw [binop_cmp_sint_of_unify c .ne rfl _ a _ (unifyInts_s256_s256 a b)]; rfl

theorem binop_cmp_s256_lit (c : Bool) (op : BinOp) (hop : isCmp op = true) (a k : Int) (hd : Option Nat)
    (hlo : -2 ^ 255 ≤ k) (hhi : k < 2 ^ 255) :
    binop c op (s256Val a) (.literal k hd) = Op.ofOpt (cmpInt op a k) :=
  binop_cmp_sint_of_unify c op hop _ a _ (unifyInts_s256_lit a k hd hlo hhi)

theorem binop_add_s256_lit (a k : Int) (hd : Option Nat) (hlo : -2 ^ 255 ≤ k) (hhi : k < 2 ^ 255)
    (hlo' : -2 ^ 255 ≤ a + k) (hhi' : a + k < 2 ^ 255) :
    binop true .add (s256Val a) (.literal k hd) = some (.ok (s256Val (a + k))) := by
  rw [binop_add_sint_of_unify true _ a _ (unifyInts_s256_lit a k hd hlo hhi), add, settle_s256_ok _ hlo' hhi',
    liftArith_ok]
  rfl

theorem binop_sub_s256_lit (a k : Int) (hd : Option Nat) (hlo : -2 ^ 255 ≤ k) (hhi : k < 2 ^ 255)
    (hlo' : -2 ^ 255 ≤ a - k) (hhi' : a - k < 2 ^ 255) :
    binop true .sub (s256Val a) (.literal k hd) = some (.ok (s256Val (a - k))) := by
  rw [binop_sub_sint_of_unify true _ a _ (unifyInts_s256_lit a k hd hlo hhi), sub, settle_s256_ok _ hlo' hhi',
    liftArith_ok]
  rfl

theorem unop_neg_s256 (a : Int) (hlo : -2 ^ 255 ≤ -a) (hhi : -a < 2 ^ 255) :
    unop true .neg (s256Val a) = some (.ok (s256Val (-a))) := by
  simp only [unop, neg]
  rw [settle_s256_ok _ hlo hhi]
  rfl

theorem unop_neg_s256_overflow (a : Int) (h : ¬ (-2 ^ 255 ≤ -a ∧ -a < 2 ^ 255)) :
    unop true .neg (s256Val a) = some (.error .overflow) := by
  simp only [unop, neg]
  rw [settle_s256_overflow _ h]
  rfl

/-- `-k` on a number literal is exact. -/
theorem unop_neg_lit (c : Bool) (k : Int) (hd : Option Nat) :
    unop c .neg (.literal k hd) = some (.ok (.literal (-k))) := rfl

/-! ### Conversions between `uint256` and `int256` -/

theorem wrap_s256_of_lt (n : ℕ) (hn : n < 2 ^ 255) : IntTy.wrap s256IntTy n = n := by
  have h1 : (n : Int) % 2 ^ 256 = n := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [IntTy.wrap, IntTy.isSigned, IntTy.width, Bool.true_and, h1, decide_eq_true_eq]
  rw [if_neg (by omega)]

theorem wrap_s256_of_ge (n : ℕ) (hn : 2 ^ 255 ≤ n) (hlt : n < 2 ^ 256) : IntTy.wrap s256IntTy n = (n : Int) - 2 ^ 256 := by
  have h1 : (n : Int) % 2 ^ 256 = n := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [IntTy.wrap, IntTy.isSigned, IntTy.width, Bool.true_and, h1, decide_eq_true_eq]
  rw [if_pos (by omega)]

theorem toWord_u256_of_nonneg (i : Int) (h0 : 0 ≤ i) (hi : i < 2 ^ 256) : IntTy.toWord u256IntTy i = i.toNat := by
  simp only [IntTy.toWord, IntTy.width]
  rw [Int.emod_eq_of_lt h0 (by exact_mod_cast hi)]

theorem toWord_u256_of_neg (i : Int) (hlo : -2 ^ 256 ≤ i) (hi : i < 0) :
    IntTy.toWord u256IntTy i = (i + 2 ^ 256).toNat := by
  simp only [IntTy.toWord, IntTy.width]
  have : (i % (2 ^ 256 : ℕ) : Int) = i + 2 ^ 256 := by
    rw [show ((2 ^ 256 : ℕ) : Int) = 2 ^ 256 by norm_cast]
    omega
  rw [this]

/-- `int256(x)` for `x : uint256`: reinterpretation of the word. -/
theorem explicitConv_u256_s256 (env : TypeEnv) (h : Heap) (n : ℕ) :
    explicitConv env h (u256Val n) s256Ty = some (.ok (s256Val (IntTy.wrap s256IntTy n), h)) := by
  simp [explicitConv, implicitConv]

/-- `uint256(y)` for `y : int256`: reinterpretation of the word. -/
theorem explicitConv_s256_u256 (env : TypeEnv) (h : Heap) (i : Int) :
    explicitConv env h (s256Val i) u256Ty = some (.ok (u256Val (IntTy.toWord u256IntTy i), h)) := by
  simp [explicitConv, implicitConv]

theorem scalarOfAbi_s256 (env : TypeEnv) (i : Int) (hlo : -2 ^ 255 ≤ i) (hhi : i < 2 ^ 255) :
    scalarOfAbi env s256Ty (.int i) = some (s256Val i) := by
  simp [scalarOfAbi]; omega

/-! ### `int256` storage slots -/

theorem readScalar_s256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (int256Loc slot)) :
    readScalar cfg env evm er s256Ty =
      some (s256Val (s256OfWord (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) :=
  readScalar_of_loc hl (by
    rw [storageLocLoad_int256]
    exact scalarOfAbi_s256 env _ (s256OfWord_bounds _).1 (s256OfWord_bounds _).2)

theorem loadIfScalar_s256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (int256Loc slot)) :
    loadIfScalar cfg env evm er s256Ty =
      some (s256Val (s256OfWord (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold loadIfScalar
  rw [if_pos (by rfl : isValueType env s256Ty = true)]
  exact readScalar_s256 hl

theorem writeScalar_s256 {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (int256Loc slot)) (i : Int) :
    writeScalar cfg evm er (s256Val i) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt i)) :=
  writeScalar_of_loc hl rfl (storageLocStore_int256 evm slot i)

theorem writeStorageDeep_s256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er evm = some (int256Loc slot)) (fuel : Nat) (i : Int) :
    writeStorageDeep cfg env (fuel + 1) evm h er s256Ty (s256Val i) =
      some (.ok (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt i))) := by
  rw [writeStorageDeep]
  · simp only [implicitConv, le_refl, if_true, Op.ofOpt, writeScalar_s256 hl]
    rfl
  all_goals intros; simp_all

theorem assign_storage_s256 {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er m.evm = some (int256Loc slot)) (i : Int) :
    assign cfg env fr m (.storage er s256Ty) (s256Val i) =
      some (.ok (fr, { m with evm := Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot (EVM.wordOfInt i) })) := by
  simp [assign, fuelDefault, writeStorageDeep_s256 hl]

/-! ## `ecrecover` arguments, `catch` clause selection -/

theorem abiArgs_ecrecover (cfg : Config) (env : TypeEnv) (m : Machine) (hb rb sb : List UInt8) (n : ℕ) :
    abiArgs cfg env m ecrecoverParamTys
      [.fixedBytes ⟨31, by decide⟩ hb, .uint ⟨8, by decide⟩ n, .fixedBytes ⟨31, by decide⟩ rb, .fixedBytes ⟨31, by decide⟩ sb] =
      some (.ok ([.fixedBytes ⟨31, by decide⟩ hb, .int n, .fixedBytes ⟨31, by decide⟩ rb, .fixedBytes ⟨31, by decide⟩ sb], m)) := by
  simp [abiArgs, ecrecoverParamTys, coerce, implicitConv, fuelDefault]

theorem encodeABIValues_ecrecover (hb rb sb : List UInt8) (n : ℕ) (hh : hb.length = 32) (hr : rb.length = 32)
    (hs : sb.length = 32) (hn : n < 256) :
    ABI.encodeABIValues? ecrecoverAbiTys
      [.fixedBytes ⟨31, by decide⟩ hb, .int n, .fixedBytes ⟨31, by decide⟩ rb, .fixedBytes ⟨31, by decide⟩ sb] =
      some (hb ++ EVM.Word.toBytesBE (EVM.word n) ++ rb ++ sb) := by
  have hn' : n < EVM.twoPow 8 := hn
  simp [ecrecoverAbiTys, ABI.encodeABIValues?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.zeroBytes, hh, hr, hs, hn']

theorem selectCatch_generic_noParams (cfg : Config) (m : Machine) (body : List Stmt) (d : ByteArray) :
    selectCatch cfg m [.mk none [] body] d = some (.mk none [] body, [], m) := by
  cases errorStringArg? cfg d <;> cases panicArg? cfg d <;> simp [selectCatch, catchKind, catchParams]

/-! ## `address` and `bool` slots as values -/

theorem accountAddress_ofNat_toNat (a : EVM.Address) : AccountAddress.ofNat a.toNat = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem loadIfScalar_address {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (addressOffset0Loc slot)) :
    loadIfScalar cfg env evm er (.address false) =
      some (.address (AccountAddress.ofNat
        (UInt256.land (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask).toNat)) := by
  unfold loadIfScalar
  rw [if_pos (by rfl : isValueType env (.address false) = true)]
  exact readScalar_address hl

theorem writeScalar_address' {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.storage.layout er evm = some (addressOffset0Loc slot)) (a : EVM.Address) :
    writeScalar cfg evm er (.address a) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat a.toNat))) := by
  have ha : a.toNat < 2 ^ 160 := a.isLt
  have hlt : (UInt256.ofNat a.toNat).toNat = a.toNat := ulit_toNat' _ (by change a.toNat < 2 ^ 256; omega)
  have h := writeScalar_address hl (UInt256.ofNat a.toNat) (by rw [hlt]; exact ha)
  rw [hlt, accountAddress_ofNat_toNat] at h
  exact h

theorem exitScope_get?_of_none {fr fr' : Frame} {k : Ident} (h : fr.get? k = none) : (fr.exitScope fr').get? k = none := by
  rw [exitScope_get?]
  have h' : fr.locals[k]? = none := by simpa [Frame.get?, Std.HashMap.get?_eq_getElem?] using h
  simp [Std.HashMap.contains_eq_isSome_getElem?, h']

/-! ## `try`/`catch` facts -/

theorem decodeRets_single {cfg : Config} {env : TypeEnv} {m : Machine} {p : Param} {rtys : List ABI.ABIType}
    {out : ByteArray} {sv : ABI.ABIValue} {v : Value}
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some [sv])
    (hof : ofAbi env fuelDefault p.ty sv m.heap = some (v, m.heap)) :
    decodeRets cfg env m [p] rtys out = some ([v], m) := by
  simp [decodeRets, hdec, hof]

theorem tryRets_single {cfg : Config} {env : TypeEnv} {m : Machine} {p : Param} {rtys : List ABI.ABIType}
    {out : ByteArray} {sv : ABI.ABIValue} {v : Value}
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some [sv])
    (hof : ofAbi env fuelDefault p.ty sv m.heap = some (v, m.heap)) :
    tryRets cfg env m [p] rtys out = some ([v], m) := by
  simp [tryRets, decodeRets_single hdec hof]

theorem bindTryParams_single {cfg : Config} {env : TypeEnv} {fr fr' : Frame} {m m' : Machine} {p : Param} {x : Ident}
    {v : Value} (hname : p.name = some x)
    (hdecl : declare cfg env fr m p.ty (some (p.loc.getD .memory)) x (some v) = some (.ok (fr', m'))) :
    bindTryParams cfg env fr m [p] [v] = some (.ok (fr', m')) := by
  simp [bindTryParams, hname, hdecl]

theorem ofAbi_scalar_u256 (env : TypeEnv) (h : Heap) (n : ℕ) (hn : n < 2 ^ 256) :
    ofAbi env fuelDefault u256Ty (.int n) h = some (u256Val n, h) := by
  simp [ofAbi, fuelDefault, scalarOfAbi]; exact hn

theorem ofAbi_scalar_bool (env : TypeEnv) (h : Heap) (b : Bool) : ofAbi env fuelDefault .bool (.bool b) h = some (.bool b, h) := by
  simp [ofAbi, fuelDefault, scalarOfAbi]

theorem ofAbi_scalar_address (env : TypeEnv) (h : Heap) (a : EVM.Address) :
    ofAbi env fuelDefault (.address false) (.address a) h = some (.address a, h) := by
  simp [ofAbi, fuelDefault, scalarOfAbi]

/-- `catch Error(string memory reason) { … }` handles `Error(string)` data. -/
theorem selectCatch_error (cfg : Config) (m : Machine) {cs : List CatchClause} {d s : ByteArray} {c : CatchClause}
    (hErr : errorStringArg? cfg d = some s) (hfind : cs.find? (catchKind · == some "Error") = some c) :
    selectCatch cfg m cs d = some (c, [(allocBytes m true s).1], (allocBytes m true s).2) := by
  simp [selectCatch, hErr, hfind, allocBytes]

/-- `catch Panic(uint256 code) { … }` handles `Panic(uint256)` data. -/
theorem selectCatch_panic (cfg : Config) (m : Machine) {cs : List CatchClause} {d : ByteArray} {code : ℕ}
    {c : CatchClause} (hErr : errorStringArg? cfg d = none ∨ cs.find? (catchKind · == some "Error") = none)
    (hPanic : panicArg? cfg d = some code) (hfind : cs.find? (catchKind · == some "Panic") = some c) :
    selectCatch cfg m cs d = some (c, [u256Val code], m) := by
  rcases hErr with h | h
  · simp [selectCatch, h, hPanic, hfind, mkInt, uint256Ty]
  · cases errorStringArg? cfg d <;> simp [selectCatch, h, hPanic, hfind, mkInt, uint256Ty]

/-- `catch (bytes memory data) { … }` handles anything the typed clauses do not. -/
theorem selectCatch_generic_bytes (cfg : Config) (m : Machine) {cs : List CatchClause} {d : ByteArray} {c : CatchClause}
    (hErr : errorStringArg? cfg d = none ∨ cs.find? (catchKind · == some "Error") = none)
    (hPanic : panicArg? cfg d = none ∨ cs.find? (catchKind · == some "Panic") = none)
    (hfind : cs.find? (catchKind · == none) = some c) (hps : (catchParams c).isEmpty = false) :
    selectCatch cfg m cs d = some (c, [(allocBytes m false d).1], (allocBytes m false d).2) := by
  rcases hErr with h | h <;> rcases hPanic with h' | h' <;>
    cases hE : errorStringArg? cfg d <;> cases hP : panicArg? cfg d <;>
    simp [selectCatch, allocBytes, h, h', hE, hP, hfind, hps] <;> simp_all

/-! ## Call options -/

@[simp] theorem valueOpt_value (e : Expr) (rest : List CallOpt) : valueOpt (.value e :: rest) = some e := rfl
@[simp] theorem gasOpt_value (e : Expr) (rest : List CallOpt) : gasOpt (.value e :: rest) = gasOpt rest := rfl
@[simp] theorem saltOpt_value (e : Expr) (rest : List CallOpt) : saltOpt (.value e :: rest) = saltOpt rest := rfl
@[simp] theorem saltOpt_salt (e : Expr) (rest : List CallOpt) : saltOpt (.salt e :: rest) = some e := rfl
@[simp] theorem valueOpt_salt (e : Expr) (rest : List CallOpt) : valueOpt (.salt e :: rest) = valueOpt rest := rfl
@[simp] theorem gasOpt_salt (e : Expr) (rest : List CallOpt) : gasOpt (.salt e :: rest) = gasOpt rest := rfl
@[simp] theorem saltBytes_bytes32 (bs : List UInt8) : saltBytes (.fixedBytes ⟨31, by decide⟩ bs) = some ⟨bs.toArray⟩ := by
  simp [saltBytes]

/-! ## Memory arrays into storage, `delete` of arrays -/

theorem writeElems_eq (cfg : Config) (env : TypeEnv) (fuel : ℕ) (evm : EVM.State) (h : Heap) (er : Solm.EvaledStorageRef)
    (e : Ty) (elems : List Value) :
    writeStorageDeep.writeElems cfg env fuel evm h er e elems =
      (elems.zipIdx).foldlM (fun evm (v, i) => writeStorageDeep cfg env fuel evm h (elemRef er i) e v) evm := by
  rw [writeStorageDeep.writeElems]

/-- `arr = memArr` for a storage dynamic array: new length, the elements in order, the removed tail cleared. -/
theorem writeStorageDeep_dynArray {cfg : Config} {env : TypeEnv} {fuel : ℕ} {evm evm₁ : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {e ety : Ty} {id old : ℕ} {elems : List Value}
    (hget : h.get? id = some (.array ety elems)) (hold : dynArrayLength cfg evm er = some old)
    (hlen : writeDynArrayLength cfg evm er elems.length = some evm₁) :
    writeStorageDeep cfg env (fuel + 1) evm h er (.dynArray e) (.memRef id) = (do
      let evm₂ ← writeStorageDeep.writeElems cfg env fuel evm₁ h er e elems
      (List.range (old - elems.length)).foldlM
        (fun evm k => clearStorage cfg env fuel evm (elemRef er (elems.length + k)) e) evm₂) := by
  rw [writeStorageDeep.eq_def]
  simp [hget, hold, hlen]

/-- `arr = memArr` for a storage static array of the right length. -/
theorem writeStorageDeep_array {cfg : Config} {env : TypeEnv} {fuel : ℕ} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {e ety : Ty} {id n : ℕ} {elems : List Value}
    (hget : h.get? id = some (.array ety elems)) (hn : elems.length = n) :
    writeStorageDeep cfg env (fuel + 1) evm h er (.array e n) (.memRef id) =
      writeStorageDeep.writeElems cfg env fuel evm h er e elems := by
  rw [writeStorageDeep.eq_def]
  simp [hget, hn]

theorem clearRange_eq (cfg : Config) (env : TypeEnv) (fuel : ℕ) (evm : EVM.State) (er : Solm.EvaledStorageRef) (e : Ty)
    (lo hi : ℕ) :
    clearStorage.clearRange cfg env fuel evm er e lo hi =
      (List.range (hi - lo)).foldlM (fun evm k => clearStorage cfg env fuel evm (elemRef er (lo + k)) e) evm := by
  rw [clearStorage.clearRange]

/-- `delete arr` for a storage dynamic array: every element cleared, then the length. -/
theorem clearStorage_dynArray {cfg : Config} {env : TypeEnv} {fuel : ℕ} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {e : Ty} {n : ℕ} (hn : dynArrayLength cfg evm er = some n) :
    clearStorage cfg env (fuel + 1) evm er (.dynArray e) = (do
      let evm' ← clearStorage.clearRange cfg env fuel evm er e 0 n
      Op.ofOpt (writeDynArrayLength cfg evm' er 0)) := by
  rw [clearStorage]
  all_goals first
    | (simp [storageTyOf, zeroValue, hn]
       try rfl)
    | (intros; simp_all)

/-- `delete arr` for a storage static array. -/
theorem clearStorage_array {cfg : Config} {env : TypeEnv} {fuel : ℕ} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {e : Ty} {n : ℕ} :
    clearStorage cfg env (fuel + 1) evm er (.array e n) = clearStorage.clearRange cfg env fuel evm er e 0 n := by
  rw [clearStorage]
  all_goals first
    | (simp [storageTyOf, zeroValue]
       try rfl)
    | (intros; simp_all)

/-! ## `abi.decode` facts -/

theorem ofAbiList_nil (env : TypeEnv) (h : Heap) : ofAbiList env [] [] h = some ([], h) := by simp [ofAbiList]

/-- One step of `ofAbiList` (the fold with a generalised accumulator). -/
def ofAbiStep (env : TypeEnv) (acch : List Value × Heap) (tsv : Ty × ABI.ABIValue) : Option (List Value × Heap) := do
  let r ← ofAbi env fuelDefault tsv.1 tsv.2 acch.2
  pure (acch.1 ++ [r.1], r.2)

theorem ofAbiList_eq_foldlM (env : TypeEnv) (tys : List Ty) (svs : List ABI.ABIValue) (h : Heap)
    (hlen : tys.length = svs.length) :
    ofAbiList env tys svs h = (tys.zip svs).foldlM (ofAbiStep env) ([], h) := by
  simp only [ofAbiList, hlen, ne_eq, not_true_eq_false, if_false]
  rfl

/-- The fold behind `ofAbiList` only appends to its accumulator. -/
theorem ofAbi_fold_shift (env : TypeEnv) : ∀ (xs : List (Ty × ABI.ABIValue)) (acc : List Value) (h : Heap),
    xs.foldlM (ofAbiStep env) (acc, h) = (xs.foldlM (ofAbiStep env) ([], h)).map (fun r => (acc ++ r.1, r.2))
  | [], acc, h => by simp
  | (t, sv) :: xs, acc, h => by
    simp only [List.foldlM_cons, ofAbiStep]
    cases hr : ofAbi env fuelDefault t sv h with
    | none => simp
    | some r =>
      simp only [Opt.some_bind, Option.pure_def, List.nil_append]
      rw [ofAbi_fold_shift env xs (acc ++ [r.1]) r.2, ofAbi_fold_shift env xs [r.1] r.2, Option.map_map]
      congr 1
      funext p
      simp [List.append_assoc]

theorem ofAbiList_cons (env : TypeEnv) (t : Ty) (ts : List Ty) (sv : ABI.ABIValue) (svs : List ABI.ABIValue) (h h' h'' : Heap)
    (v : Value) (vs : List Value) (hlen : ts.length = svs.length)
    (hv : ofAbi env fuelDefault t sv h = some (v, h')) (hrest : ofAbiList env ts svs h' = some (vs, h'')) :
    ofAbiList env (t :: ts) (sv :: svs) h = some (v :: vs, h'') := by
  rw [ofAbiList_eq_foldlM env _ _ h (by simp [hlen]), List.zip_cons_cons, List.foldlM_cons]
  simp only [ofAbiStep, hv, Opt.some_bind, Option.pure_def, List.nil_append]
  rw [ofAbi_fold_shift env _ [v] h', ← ofAbiList_eq_foldlM env ts svs h' hlen, hrest]
  rfl

@[simp] theorem abiTypeOf_uint (env : TypeEnv) (w : ABI.BitWidth) : abiTypeOf env (.uint w) = some (.elem (.int (.uint w))) := rfl
@[simp] theorem abiTypeOf_address (env : TypeEnv) (p : Bool) : abiTypeOf env (.address p) = some (.elem .address) := rfl
@[simp] theorem abiTypeOf_bool (env : TypeEnv) : abiTypeOf env .bool = some (.elem .bool) := rfl
@[simp] theorem abiTypeOf_fixedBytes (env : TypeEnv) (n : Fin 32) : abiTypeOf env (.fixedBytes n) = some (.elem (.bytes n)) := rfl
@[simp] theorem abiTypeOf_bytes (env : TypeEnv) : abiTypeOf env .bytes = some .bytes := rfl
@[simp] theorem abiTypeOf_string (env : TypeEnv) : abiTypeOf env .string = some .string := rfl

/-! ## Packed signed fields -/

/-- A packed `int<8·size>` field at byte `offset`, read as a two's-complement value. -/
theorem readScalar_sint_offset {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {offset : Fin 32} {size : Fin 33} {w : ABI.BitWidth} {hbound : offset.val + size.val - 1 < 32}
    (hl : cfg.storage.layout er evm =
      some { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.sint w) })
    (hoff : 8 * offset.val < 256) :
    readScalar cfg env evm er (.int w) =
      some (.sint w (sextAt w.val (UInt256.land
        (UInt256.div (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (256 ^ offset.val)))
        (UInt256.ofNat (256 ^ size.val - 1))).toNat)) := by
  have hsize : 8 * size.val ≤ 256 := by have := size.isLt; omega
  refine readScalar_of_loc hl ?_
  rw [storageLocLoad_sint_offset evm slot offset size w hoff hsize]
  have hb := sextAt_bounds w.val (UInt256.land
    (UInt256.div (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (256 ^ offset.val)))
    (UInt256.ofNat (256 ^ size.val - 1))).toNat w.property.1
  simp [scalarOfAbi, hb.1, hb.2]

/-- A packed `int<8·size>` field written in place. -/
theorem writeScalar_sint_packed {cfg : Config} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    {offset : Fin 32} {size : Fin 33} {w : ABI.BitWidth} {hbound : offset.val + size.val - 1 < 32}
    (hl : cfg.storage.layout er evm =
      some { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.sint w) }) (i : Int) :
    writeScalar cfg evm er (.sint w i) =
      some (Storage.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (setPackedWordNat (Storage.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat
          offset.val size.val (EVM.wordOfInt i).toNat))) :=
  writeScalar_of_loc hl rfl (storageLocStore_int_packed evm slot offset size _ i)

end Solidity
