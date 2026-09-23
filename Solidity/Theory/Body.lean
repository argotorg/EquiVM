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

end Solidity
