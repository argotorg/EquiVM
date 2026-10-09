import Solidity.Semantics
import Reasoning.Storage
import Solidity.Theory.Backend

/-!
# Derivation helpers for function bodies

Small rewriting lemmas used when building `EvalExpr`/`ExecStmt`/`CallFn` derivations by hand:
frame lookups, scalar conversions, zero values, and full-word (`uint256`) storage reads and
writes through the storage backend (`Config.Leaf`).  `storageLocLoad`/`scalarOfAbi` are eliminated
by `rw`, never by definitional unfolding (their unfolding on a symbolic state does not terminate
quickly).
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

@[simp] theorem Frame.retVars_bind (fr : Frame) (x : Ident) (ty : Ty) (loc : Option DataLoc) (v : Value) :
    (fr.bind x ty loc v).retVars = fr.retVars := rfl

@[simp] theorem Frame.retVars_setVal (fr : Frame) (x : Ident) (v : Value) : (fr.setVal x v).retVars = fr.retVars := by
  unfold Frame.setVal; split <;> rfl

@[simp] theorem Frame.mem_bind (fr : Frame) (x y : Ident) (ty : Ty) (loc : Option DataLoc) (v : Value) :
    y ∈ (fr.bind x ty loc v).locals ↔ x = y ∨ y ∈ fr.locals := by
  simp [Frame.bind, Std.HashMap.mem_insert]

@[simp] theorem Frame.mem_setVal (fr : Frame) (x y : Ident) (v : Value) :
    y ∈ (fr.setVal x v).locals ↔ y ∈ fr.locals := by
  unfold Frame.setVal
  split
  · rename_i l h
    have hx : x ∈ fr.locals := by
      rw [Std.HashMap.mem_iff_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, h]; rfl
    simp only [Std.HashMap.mem_insert, beq_iff_eq]
    constructor
    · rintro (rfl | h') <;> assumption
    · exact Or.inr
  · rfl

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

/-! ## Storage through the backend

The semantics reads and writes storage through `cfg.storageBackend`.  `Config.Leaf cfg er loc`
(`Theory/Backend.lean`) says the backend treats `er` as the scalar at `loc`; a config built from a
layout table satisfies it at every leaf of the layout (`Config.leaf_of_table`).  The scalar lemmas
below are stated on it; dynamically-sized values take the backend's results (`length`, `push`,
`pop`, `clear`) as hypotheses. -/

theorem readScalar_of_leaf {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {e : ABI.ElemType} {loc : Solm.StorageLoc} {v : Value} (hst : storageTypeOf env ty = some (.elem e))
    (hl : cfg.Leaf er loc) (hv : scalarOfAbi env ty (Solm.storageLocLoad evm loc) = some v) :
    readScalar cfg env evm er ty = some v := by
  unfold readScalar
  rw [hst, Opt.some_bind, hl.read e evm]
  exact hv

theorem loadIfScalar_of_leaf {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {e : ABI.ElemType} {loc : Solm.StorageLoc} {v : Value} (hval : isValueType env ty = true)
    (hst : storageTypeOf env ty = some (.elem e)) (hl : cfg.Leaf er loc)
    (hv : scalarOfAbi env ty (Solm.storageLocLoad evm loc) = some v) : loadIfScalar cfg env evm er ty = some v := by
  unfold loadIfScalar
  rw [if_pos hval]
  exact readScalar_of_leaf hst hl hv

/-- A reference type is read as a storage reference. -/
theorem loadIfScalar_ref {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    (hnv : isValueType env ty = false) : loadIfScalar cfg env evm er ty = some (.storageRef er ty) := by
  unfold loadIfScalar
  rw [if_neg (by simp [hnv])]

theorem writeScalar_of_leaf {cfg : Config} {env : TypeEnv} {evm evm' : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {e : ABI.ElemType} {loc : Solm.StorageLoc} {v : Value} {sv : Solm.Value}
    (hst : storageTypeOf env ty = some (.elem e)) (hl : cfg.Leaf er loc)
    (hsv : scalarToAbi v = some sv) (hw : Solm.storageLocStore evm loc sv = some evm') :
    writeScalar cfg env evm er ty v = some evm' := by
  unfold writeScalar
  rw [hst, Opt.some_bind, hsv, Opt.some_bind, hl.write e sv evm evm' hw]

/-- A successful `writeScalar` is a successful backend write. -/
theorem writeScalar_write {cfg : Config} {env : TypeEnv} {evm evm' : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {st : Solm.StorageType} {v : Value} {sv : Solm.Value} (hst : storageTypeOf env ty = some st)
    (hsv : scalarToAbi v = some sv) (hw : writeScalar cfg env evm er ty v = some evm') :
    cfg.storageBackend.write er st sv evm = .ok evm' := by
  unfold writeScalar at hw
  rw [hst, Opt.some_bind, hsv, Opt.some_bind] at hw
  revert hw
  cases cfg.storageBackend.write er st sv evm <;> simp

theorem readLValue_storage_of {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {ty : Ty} {v : Value} (hload : loadIfScalar cfg env m.evm er ty = some v) :
    readLValue cfg env fr m (.storage er ty) = some (.ok v) := by
  simp [readLValue, hload]

theorem assign_storage_of {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {ty : Ty} {v : Value} {evm' : EVM.State}
    (hw : writeStorageDeep cfg env fuelDefault m.evm m.heap er ty v = some (.ok evm')) :
    assign cfg env fr m (.storage er ty) v = some (.ok (fr, { m with evm := evm' })) := by
  simp [assign, hw]

/-- Values `storageValueOf` converts with `implicitConv`: neither memory, calldata nor storage objects,
    nor string literals. -/
def Value.direct : Value → Prop
  | .memRef _ | .strLit _ | .raw .. | .storageRef .. | .cdRef .. => False
  | _ => True

theorem storageValueOf_direct {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h h' : Heap} {ty : Ty} {v v' : Value}
    {sv : Solm.Value} (fuel : Nat) (hd : v.direct) (hconv : implicitConv env h v ty = some (v', h'))
    (hsv : scalarToAbi v' = some sv) : storageValueOf cfg env (fuel + 1) evm h ty v = some (.ok sv) := by
  cases v <;> simp [Value.direct] at hd <;> simp [storageValueOf, toStorage, hconv, hsv]

/-- `writeStorageDeep` when the value's storage value is `sv`: a backend write of `sv`. -/
theorem writeStorageDeep_of_value {cfg : Config} {env : TypeEnv} {evm evm' : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {ty : Ty} {st : Solm.StorageType} {v : Value} {sv : Solm.Value} {fuel : Nat}
    (hst : storageTypeOf env ty = some st) (hv : storageValueOf cfg env fuel evm h ty v = some (.ok sv))
    (hw : cfg.storageBackend.write er st sv evm = .ok evm') :
    writeStorageDeep cfg env fuel evm h er ty v = some (.ok evm') := by
  simp only [writeStorageDeep, hst, hv, Op.bind_ok, hw, liftStorage, Op.pure_eq]

/-! ### Full-word `uint256` slots -/

/-- `readScalar` of a `uint256` slot: the stored word. -/
theorem readScalar_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (uint256Loc slot)) :
    readScalar cfg env evm er u256Ty =
      some (u256Val (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) :=
  readScalar_of_leaf (storageTypeOf_uint env _) hl (by rw [storageLocLoad_uint256, scalarOfAbi_u256])

theorem loadIfScalar_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (uint256Loc slot)) :
    loadIfScalar cfg env evm er u256Ty =
      some (u256Val (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  unfold loadIfScalar
  rw [if_pos (by rfl : isValueType env u256Ty = true)]
  exact readScalar_u256 hl

/-- `writeScalar` of a `uint256` slot: the stored word. -/
theorem writeScalar_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (uint256Loc slot)) (w : UInt256) :
    writeScalar cfg env evm er u256Ty (u256Val w.toNat) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot w) :=
  writeScalar_of_leaf (storageTypeOf_uint env _) hl rfl (storageLocStore_uint256 evm slot w)

/-- `writeStorageDeep` of a `uint256` value into a `uint256` slot. -/
theorem writeStorageDeep_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.Leaf er (uint256Loc slot)) (fuel : Nat) (w : UInt256) :
    writeStorageDeep cfg env (fuel + 1) evm h er u256Ty (u256Val w.toNat) =
      some (.ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot w)) :=
  writeStorageDeep_of_value (storageTypeOf_uint env _)
    (storageValueOf_direct fuel trivial (implicitConv_uint env h w.toNat) rfl)
    (hl.write _ _ _ _ (storageLocStore_uint256 evm slot w))

theorem writeStorageDeep_bool {cfg : Config} {env : TypeEnv} {evm evm' : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} (fuel : Nat) {b : Bool} (hw : writeScalar cfg env evm er .bool (.bool b) = some evm') :
    writeStorageDeep cfg env (fuel + 1) evm h er .bool (.bool b) = some (.ok evm') :=
  writeStorageDeep_of_value (storageTypeOf_bool env)
    (storageValueOf_direct fuel trivial (implicitConv_bool env h b) rfl)
    (writeScalar_write (storageTypeOf_bool env) rfl hw)

theorem writeStorageDeep_address {cfg : Config} {env : TypeEnv} {evm evm' : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} (fuel : Nat) {a : EVM.Address}
    (hw : writeScalar cfg env evm er (.address false) (.address a) = some evm') :
    writeStorageDeep cfg env (fuel + 1) evm h er (.address false) (.address a) = some (.ok evm') :=
  writeStorageDeep_of_value (storageTypeOf_address env false)
    (storageValueOf_direct fuel trivial (implicitConv_address env h a) rfl)
    (writeScalar_write (storageTypeOf_address env false) rfl hw)

/-! ### `bool` at offset 0 -/

theorem readScalar_bool_false {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.Leaf er (boolOffset0Loc slot))
    (hz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ = ⟨0⟩) :
    readScalar cfg env evm er .bool = some (.bool false) :=
  readScalar_of_leaf (storageTypeOf_bool env) hl (by rw [storageLocLoad_bool_offset0_false evm slot hz]; rfl)

theorem readScalar_bool_true {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.Leaf er (boolOffset0Loc slot))
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠ ⟨0⟩) :
    readScalar cfg env evm er .bool = some (.bool true) :=
  readScalar_of_leaf (storageTypeOf_bool env) hl (by rw [storageLocLoad_bool_offset0_true evm slot hnz]; rfl)

theorem writeScalar_bool_true {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (boolOffset0Loc slot)) :
    writeScalar cfg env evm er .bool (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.lnot ⟨255⟩)) ⟨1⟩)) :=
  writeScalar_of_leaf (storageTypeOf_bool env) hl rfl (storageLocStore_bool_true_offset0 evm slot)

theorem writeScalar_bool_false {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (boolOffset0Loc slot)) :
    writeScalar cfg env evm er .bool (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.lnot ⟨255⟩))) :=
  writeScalar_of_leaf (storageTypeOf_bool env) hl rfl (storageLocStore_bool_false_offset0 evm slot)

/-! ### `address` at offset 0 -/

theorem readScalar_address {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.Leaf er (addressOffset0Loc slot)) :
    readScalar cfg env evm er (.address false) =
      some (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask).toNat)) :=
  readScalar_of_leaf (storageTypeOf_address env false) hl (by rw [storageLocLoad_address_offset0]; rfl)

theorem writeScalar_address {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (addressOffset0Loc slot)) (addr : UInt256)
    (hcanon : addr.toNat < EVM.addressModulus) :
    writeScalar cfg env evm er (.address false) (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) :=
  writeScalar_of_leaf (storageTypeOf_address env false) hl rfl (storageLocStore_address_offset0 evm slot addr hcanon)

/-! ### `bytes32` -/

theorem readScalar_bytes32 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.Leaf er (bytes32Loc slot)) :
    readScalar cfg env evm er (.fixedBytes ⟨31, by decide⟩) =
      some (.fixedBytes ⟨31, by decide⟩
        (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) :=
  readScalar_of_leaf (storageTypeOf_fixedBytes env _) hl (by rw [storageLocLoad_bytes32]; rfl)

theorem writeScalar_bytes32 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot word : UInt256}
    (hl : cfg.Leaf er (bytes32Loc slot)) (bs : List UInt8)
    (hval : Solm.valueToWord (.fixedBytes ⟨31, by decide⟩ bs) = some word) :
    writeScalar cfg env evm er (.fixedBytes ⟨31, by decide⟩) (.fixedBytes ⟨31, by decide⟩ bs) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot word) :=
  writeScalar_of_leaf (storageTypeOf_fixedBytes env _) hl rfl (storageLocStore_bytes32 evm slot word _ hval)

/-! ## Arrays and structs -/

theorem storageLength_of_backend {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {st : Solm.StorageType} {n : ℕ} (hst : storageTypeOf env ty = some st)
    (hlen : cfg.storageBackend.length er st evm = .ok n) : storageLength cfg env evm er ty = some (.ok n) := by
  simp only [storageLength, hst, hlen, liftStorage, Op.pure_eq]

theorem dynArrayLength_of_backend {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {e : Ty}
    {st : Solm.StorageType} {n : ℕ} (hst : storageTypeOf env (.dynArray e) = some st)
    (hlen : cfg.storageBackend.length er st evm = .ok n) : dynArrayLength cfg env evm er e = some n := by
  simp only [dynArrayLength, storageLength_of_backend hst hlen]

/-- `arr.length` of a dynamic array whose length is known. -/
theorem storageLength_dynArray {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {e : Ty} {n : ℕ}
    (hlen : dynArrayLength cfg env evm er e = some n) : storageLength cfg env evm er (.dynArray e) = some (.ok n) := by
  unfold dynArrayLength at hlen
  split at hlen <;> simp_all

theorem storageLength_array {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {e : Ty}
    {st : Solm.StorageType} {n : ℕ} (hst : storageTypeOf env (.array e n) = some (.array st n))
    (hlen : cfg.storageBackend.length er (.array st n) evm = .ok n) :
    storageLength cfg env evm er (.array e n) = some (.ok n) :=
  storageLength_of_backend hst hlen

theorem storageIndex_dynArray_ok {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {e : Ty} {n i : ℕ} (hlen : storageLength cfg env evm er (.dynArray e) = some (.ok n))
    (hi : i < n) : storageIndex cfg env evm h er (.dynArray e) (u256Val i) = some (.ok (elemRef er i, e)) := by
  simp [storageIndex, natOperand, hlen, hi]

theorem storageIndex_dynArray_oob {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {e : Ty} {n i : ℕ} (hlen : storageLength cfg env evm er (.dynArray e) = some (.ok n))
    (hi : n ≤ i) : storageIndex cfg env evm h er (.dynArray e) (u256Val i) = some (.error .outOfBounds) := by
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

theorem readScalar_address_offset1 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {hbound : (1 : Fin 32).val + (20 : Fin 33).val - 1 < 32}
    (hl : cfg.Leaf er { slot := slot, offset := 1, size := 20, hbound := hbound, type := .address }) :
    readScalar cfg env evm er (.address false) =
      some (.address (AccountAddress.ofNat
        (UInt256.land (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨256⟩)
          solcAddrMask).toNat)) :=
  readScalar_of_leaf (storageTypeOf_address env false) hl (by rw [storageLocLoad_address_offset1]; rfl)

/-- `a.push(v)`: the backend's `push` of the value's storage value. -/
theorem storagePush_some {cfg : Config} {env : TypeEnv} {m : Machine} {er : Solm.EvaledStorageRef} {e : Ty}
    {st : Solm.StorageType} {v : Value} {sv : Solm.Value} {evm' : EVM.State}
    (hst : storageTypeOf env (.dynArray e) = some st)
    (hv : storageValueOf cfg env fuelDefault m.evm m.heap e v = some (.ok sv))
    (hpush : cfg.storageBackend.push er st (some sv) m.evm = .ok evm') :
    storagePush cfg env m er e (some v) = some (.ok { m with evm := evm' }) := by
  simp [storagePush, hst, hv, hpush, liftStorage]

/-- `a.push()`: the backend's valueless `push`. -/
theorem storagePush_none {cfg : Config} {env : TypeEnv} {m : Machine} {er : Solm.EvaledStorageRef} {e : Ty}
    {st : Solm.StorageType} {evm' : EVM.State} (hst : storageTypeOf env (.dynArray e) = some st)
    (hpush : cfg.storageBackend.push er st none m.evm = .ok evm') :
    storagePush cfg env m er e none = some (.ok { m with evm := evm' }) := by
  simp [storagePush, hst, hpush, liftStorage]

theorem storagePop_empty {cfg : Config} {env : TypeEnv} {m : Machine} {er : Solm.EvaledStorageRef} {e : Ty}
    (hlen : dynArrayLength cfg env m.evm er e = some 0) : storagePop cfg env m er e = some (.error .popEmpty) := by
  simp [storagePop, storageLength_dynArray hlen]
  rfl

theorem storagePop_succ {cfg : Config} {env : TypeEnv} {m : Machine} {er : Solm.EvaledStorageRef} {e : Ty}
    {st : Solm.StorageType} {n : ℕ} {evm' : EVM.State}
    (hlen : dynArrayLength cfg env m.evm er e = some (n + 1)) (hst : storageTypeOf env (.dynArray e) = some st)
    (hpop : cfg.storageBackend.pop er st m.evm = .ok evm') :
    storagePop cfg env m er e = some (.ok { m with evm := evm' }) := by
  simp [storagePop, storageLength_dynArray hlen, hst, hpop, liftStorage]

/-- `delete x` through the backend. -/
theorem clearStorage_of_backend {cfg : Config} {env : TypeEnv} {evm evm' : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {st : Solm.StorageType} (hst : storageTypeOf env ty = some st)
    (hclear : cfg.storageBackend.clear er st evm = .ok evm') : clearStorage cfg env evm er ty = some (.ok evm') := by
  simp only [clearStorage, hst, hclear, liftStorage, Op.pure_eq]

/-- `delete` is the backend's `clear`. -/
theorem clearStorage_eq {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {ty : Ty}
    {st : Solm.StorageType} (hst : storageTypeOf env ty = some st) :
    clearStorage cfg env evm er ty = liftStorage (cfg.storageBackend.clear er st evm) := by
  simp only [clearStorage, hst]

/-- `delete x` for a `uint256` slot. -/
theorem clearStorage_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (uint256Loc slot)) :
    clearStorage cfg env evm er u256Ty =
      some (.ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩)) := by
  have hst := storageLocStore_uint256_int evm slot 0
  rw [show EVM.wordOfInt 0 = (⟨0⟩ : UInt256) by decide] at hst
  exact clearStorage_of_backend (storageTypeOf_uint env _) (hl.clear _ _ _ hst)

/-! ## Calldata words: values without any -/

@[simp] theorem hasRaw_uint (h : Heap) (fuel : ℕ) (w : ABI.BitWidth) (n : ℕ) : hasRaw h (fuel + 1) (.uint w n) = false := by
  simp [hasRaw]
@[simp] theorem hasRaw_sint (h : Heap) (fuel : ℕ) (w : ABI.BitWidth) (i : Int) : hasRaw h (fuel + 1) (.sint w i) = false := by
  simp [hasRaw]
@[simp] theorem hasRaw_literal (h : Heap) (fuel : ℕ) (i : Int) (hd : Option ℕ) : hasRaw h (fuel + 1) (.literal i hd) = false := by
  simp [hasRaw]
@[simp] theorem hasRaw_bool (h : Heap) (fuel : ℕ) (b : Bool) : hasRaw h (fuel + 1) (.bool b) = false := by simp [hasRaw]
@[simp] theorem hasRaw_address (h : Heap) (fuel : ℕ) (a : EVM.Address) : hasRaw h (fuel + 1) (.address a) = false := by
  simp [hasRaw]
@[simp] theorem hasRaw_contract (h : Heap) (fuel : ℕ) (c : Ident) (a : EVM.Address) :
    hasRaw h (fuel + 1) (.contract c a) = false := by simp [hasRaw]
@[simp] theorem hasRaw_fixedBytes (h : Heap) (fuel : ℕ) (n : Fin 32) (bs : List UInt8) :
    hasRaw h (fuel + 1) (.fixedBytes n bs) = false := by simp [hasRaw]
@[simp] theorem hasRaw_strLit (h : Heap) (fuel : ℕ) (s : ByteArray) : hasRaw h (fuel + 1) (.strLit s) = false := by
  simp [hasRaw]
@[simp] theorem hasRaw_enum (h : Heap) (fuel : ℕ) (q : Option Ident) (n : Ident) (i : ℕ) :
    hasRaw h (fuel + 1) (.enum q n i) = false := by simp [hasRaw]
@[simp] theorem hasRaw_wrapped (h : Heap) (fuel : ℕ) (q : Option Ident) (n : Ident) (v : Value) :
    hasRaw h (fuel + 1) (.wrapped q n v) = false := by simp [hasRaw]
/-- A memory byte array holds no calldata word. -/
theorem hasRaw_memBytes {h : Heap} {id : ℕ} {s : Bool} {d : ByteArray} (fuel : ℕ) (hget : h.get? id = some (.bytes s d)) :
    hasRaw h (fuel + 1) (.memRef id) = false := by simp [hasRaw, hget]
theorem hasCdRaw_memBytes {h : Heap} {id : ℕ} {s : Bool} {d : ByteArray} (fuel : ℕ) (hget : h.get? id = some (.bytes s d)) :
    hasCdRaw h (fuel + 1) (.memRef id) = false := by simp [hasCdRaw, hget]

/-- Validation for an ABI encoding leaves a value without calldata words alone. -/
theorem validateDeep_of_noRaw {env : TypeEnv} {h : Heap} {fuel : ℕ} {v : Value} (hv : hasRaw h (fuel + 1) v = false) :
    validateDeep env (fuel + 1) h v = pure h := by
  cases v
  all_goals first
    | (simp [validateDeep]; done)
    | (simp [hasRaw] at hv; done)
    | (simp [validateDeep, hv]; done)

theorem foldlM_validateDeep_of_noRaw {env : TypeEnv} {h : Heap} {fuel : ℕ} {vs : List Value}
    (hvs : ∀ v ∈ vs, hasRaw h (fuel + 1) v = false) : vs.foldlM (validateDeep env (fuel + 1)) h = pure h := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.foldlM_cons, validateDeep_of_noRaw (hvs v (List.mem_cons_self ..)), pure_bind]
    exact ih fun x hx => hvs x (List.mem_cons_of_mem _ hx)

@[simp] theorem hasRaw_cdRef (h : Heap) (fuel : ℕ) (ty : Ty) (base len : ℕ) :
    hasRaw h (fuel + 1) (.cdRef ty base len) = true := by simp [hasRaw]

/-- An argument without calldata words is left alone by the encoding's preparation. -/
@[simp] theorem prepareArg_of_noRaw {env : TypeEnv} {cd : ByteArray} {h : Heap} {fuel : ℕ} {v : Value}
    (hv : hasRaw h (fuel + 1) v = false) : prepareArg env cd (fuel + 1) h v = pure (v, h) := by
  cases v
  all_goals first
    | (simp [hasRaw] at hv; done)
    | (simp only [prepareArg]; rw [validateDeep_of_noRaw hv]; rfl)

theorem prepareArgs_of_noRaw {env : TypeEnv} {cd : ByteArray} {h : Heap} {fuel : ℕ} {vs : List Value}
    (hvs : ∀ v ∈ vs, hasRaw h (fuel + 1) v = false) : prepareArgs env cd (fuel + 1) h vs = pure (vs, h) := by
  suffices ∀ acc, vs.foldlM (fun (p : List Value × Heap) v => do
      let (v', h') ← prepareArg env cd (fuel + 1) p.2 v
      pure (p.1 ++ [v'], h')) (acc, h) = pure (acc ++ vs, h) by
    simpa [prepareArgs] using this []
  induction vs with
  | nil => intro acc; simp
  | cons v vs ih =>
    intro acc
    rw [List.foldlM_cons]
    simp only [prepareArg_of_noRaw (hvs v (List.mem_cons_self ..)), pure_bind]
    rw [ih (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) (acc ++ [v])]
    simp

@[simp] theorem validateDeep_uint (env : TypeEnv) (h : Heap) (fuel : ℕ) (w : ABI.BitWidth) (n : ℕ) :
    validateDeep env (fuel + 1) h (.uint w n) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_sint (env : TypeEnv) (h : Heap) (fuel : ℕ) (w : ABI.BitWidth) (i : Int) :
    validateDeep env (fuel + 1) h (.sint w i) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_literal (env : TypeEnv) (h : Heap) (fuel : ℕ) (i : Int) (hd : Option ℕ) :
    validateDeep env (fuel + 1) h (.literal i hd) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_bool (env : TypeEnv) (h : Heap) (fuel : ℕ) (b : Bool) :
    validateDeep env (fuel + 1) h (.bool b) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_address (env : TypeEnv) (h : Heap) (fuel : ℕ) (a : EVM.Address) :
    validateDeep env (fuel + 1) h (.address a) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_contract (env : TypeEnv) (h : Heap) (fuel : ℕ) (c : Ident) (a : EVM.Address) :
    validateDeep env (fuel + 1) h (.contract c a) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_fixedBytes (env : TypeEnv) (h : Heap) (fuel : ℕ) (n : Fin 32) (bs : List UInt8) :
    validateDeep env (fuel + 1) h (.fixedBytes n bs) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_strLit (env : TypeEnv) (h : Heap) (fuel : ℕ) (s : ByteArray) :
    validateDeep env (fuel + 1) h (.strLit s) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_enum (env : TypeEnv) (h : Heap) (fuel : ℕ) (q : Option Ident) (n : Ident) (i : ℕ) :
    validateDeep env (fuel + 1) h (.enum q n i) = pure h := by simp [validateDeep]
@[simp] theorem validateDeep_wrapped (env : TypeEnv) (h : Heap) (fuel : ℕ) (q : Option Ident) (n : Ident) (v : Value) :
    validateDeep env (fuel + 1) h (.wrapped q n v) = pure h := by simp [validateDeep]

theorem abiArgs_u256 (cfg : Config) (env : TypeEnv) (m : Machine) (n : Nat) :
    abiArgs cfg env m [u256Ty] [u256Val n] = some (.ok ([.int n], m)) := by
  simp [abiArgs, prepareArgs, coerce, fuelDefault]

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

theorem memLength_array {h : Heap} {obj : ℕ} {e : Ty} {elems : List Value} {fx : Bool}
    (hget : h.get? obj = some (.array e elems fx)) : memLength h obj = some elems.length := by
  simp [memLength, hget]

theorem memIndex_array_ok {h : Heap} {obj : ℕ} {e : Ty} {elems : List Value} {fx : Bool} {i : ℕ}
    (hget : h.get? obj = some (.array e elems fx)) (hi : i < elems.length) :
    memIndex h obj (u256Val i) = some (.ok elems[i]) := by
  simp [memIndex, natOperand, hget, List.getElem?_eq_getElem hi]

theorem memIndex_array_oob {h : Heap} {obj : ℕ} {e : Ty} {elems : List Value} {fx : Bool} {i : ℕ}
    (hget : h.get? obj = some (.array e elems fx)) (hi : elems.length ≤ i) :
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

@[simp] theorem Frame.restore_nil (s : Store) : Frame.restore [] s = s := rfl

@[simp] theorem Frame.hidden_setVal (fr : Frame) (x : Ident) (v : Value) : (fr.setVal x v).hidden = fr.hidden := by
  unfold Frame.setVal; split <;> rfl

theorem Frame.hidden_bind (fr : Frame) (x : Ident) (ty : Ty) (loc : Option DataLoc) (v : Value) :
    (fr.bind x ty loc v).hidden =
      match fr.get? x with
      | some l => (x, l) :: fr.hidden
      | none => fr.hidden := rfl

/-- Declaring a fresh name hides nothing. -/
@[simp] theorem Frame.hidden_bind_of_none {fr : Frame} {x : Ident} (h : fr.get? x = none) (ty : Ty)
    (loc : Option DataLoc) (v : Value) : (fr.bind x ty loc v).hidden = fr.hidden := by
  rw [Frame.hidden_bind, h]

/-- Lookup after leaving a block, in general: hidden bindings come back first. -/
theorem exitScope_get?' (fr fr' : Frame) (k : Ident) :
    (fr.exitScope fr').get? k =
      if fr.locals.contains k then
        (Frame.restore (fr'.hidden.take (fr'.hidden.length - fr.hidden.length)) fr'.locals).get? k
      else none := by
  simp only [Frame.exitScope, Std.HashMap.get?_eq_getElem?, Frame.get?, Std.HashMap.getElem?_filter']
  cases (Frame.restore (fr'.hidden.take (fr'.hidden.length - fr.hidden.length)) fr'.locals)[k]? <;>
    simp [Option.filter]

/-- Lookup after leaving a block in which no declaration hid an outer binding. -/
@[simp] theorem exitScope_get? (fr fr' : Frame) (k : Ident) (h : fr'.hidden = fr.hidden) :
    (fr.exitScope fr').get? k = if fr.locals.contains k then fr'.get? k else none := by
  rw [exitScope_get?', h]
  simp [Frame.get?]

/-- Lookup after leaving a block in which one declaration hid the outer binding `l` of `x`. -/
theorem exitScope_get?_shadow {fr fr' : Frame} {x : Ident} {l : Local} (k : Ident)
    (h : fr'.hidden = (x, l) :: fr.hidden) :
    (fr.exitScope fr').get? k =
      if fr.locals.contains k then (if (x == k) = true then some l else fr'.get? k) else none := by
  rw [exitScope_get?', h]
  simp [Frame.restore, Frame.get?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem exitScope_hidden (fr fr' : Frame) :
    (fr.exitScope fr').hidden = fr'.hidden.drop (fr'.hidden.length - fr.hidden.length) := rfl

@[simp] theorem exitScope_hidden_of_eq {fr fr' : Frame} (h : fr'.hidden = fr.hidden) :
    (fr.exitScope fr').hidden = fr.hidden := by
  rw [exitScope_hidden, h]; simp

/-- Nothing hidden: `return` sees the frame as it is. -/
theorem Frame.unwind_of_hidden {fr : Frame} (h : fr.hidden = []) : fr.unwind = fr := by
  cases fr
  dsimp only at h
  subst h
  rfl

@[simp] theorem Frame.unwind_retVars (fr : Frame) : fr.unwind.retVars = fr.retVars := rfl
@[simp] theorem Frame.unwind_hidden (fr : Frame) : fr.unwind.hidden = [] := rfl

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
theorem ofAbi_dynArray_map {env : TypeEnv} {fuel : Nat} {e : Ty} {h : Heap} {svs : List Solm.Value}
    {g : Solm.Value → Value} (hsc : ∀ sv ∈ svs, ofAbi env fuel e sv h = some (g sv, h)) :
    ofAbi env (fuel + 1) (.dynArray e) (.array svs) h =
      some (.memRef (h.alloc (.array e (svs.map g) false)).2, (h.alloc (.array e (svs.map g) false)).1) := by
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
    {er : Solm.EvaledStorageRef} {slot : UInt256} (hl : cfg.Leaf er (uint256Loc slot)) :
    readLValue cfg env fr m (.storage er u256Ty) =
      some (.ok (u256Val (Solm.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner slot).toNat)) := by
  simp [readLValue, loadIfScalar_u256 hl]

theorem assign_storage_u256 {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine}
    {er : Solm.EvaledStorageRef} {slot : UInt256} (hl : cfg.Leaf er (uint256Loc slot))
    (w : UInt256) :
    assign cfg env fr m (.storage er u256Ty) (u256Val w.toNat) =
      some (.ok (fr, { m with evm := Solm.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot w })) := by
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
  simp [abiArgs, prepareArgs, coerce, fuelDefault]

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
    (hl : cfg.Leaf er { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.uint w) })
    (hw : w.val = 8 * size.val) (hoff : 8 * offset.val < 256) :
    readScalar cfg env evm er (.uint w) =
      some (.uint w (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (256 ^ offset.val)))
        (UInt256.ofNat (256 ^ size.val - 1))).toNat) := by
  have hsize : 8 * size.val ≤ 256 := by have := size.isLt; omega
  refine readScalar_of_leaf (storageTypeOf_uint env w) hl ?_
  rw [storageLocLoad_uint_offset evm slot offset size w hw hoff hsize]
  apply scalarOfAbi_uint_of_lt
  rw [hw, show (256 : ℕ) ^ size.val - 1 = 2 ^ (8 * size.val) - 1 by simp [Nat.pow_mul]]
  exact land_mask_toNat_lt _ _ hsize

/-- A packed `uintN` field at byte offset 0 of a slot. -/
theorem readScalar_uint_offset0 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {size : Fin 33} {w : ABI.BitWidth} {hbound : (0 : Fin 32).val + size.val - 1 < 32}
    (hl : cfg.Leaf er { slot := slot, offset := 0, size := size, hbound := hbound, type := .int (.uint w) })
    (hw : w.val = 8 * size.val) :
    readScalar cfg env evm er (.uint w) =
      some (.uint w (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat (2 ^ (8 * size.val) - 1))).toNat) := by
  have hsize : 8 * size.val ≤ 256 := by have := size.isLt; omega
  refine readScalar_of_leaf (storageTypeOf_uint env w) hl ?_
  rw [storageLocLoad_uint_offset0 evm slot size w hw hsize]
  apply scalarOfAbi_uint_of_lt
  rw [hw]
  exact land_mask_toNat_lt _ _ hsize

/-- A packed `uintN` field written in place (`N = 8 * size`); `setPackedWordNat` is the new slot word. -/
theorem writeScalar_uint_packed {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    {offset : Fin 32} {size : Fin 33} {w : ABI.BitWidth} {hbound : offset.val + size.val - 1 < 32}
    (hl : cfg.Leaf er { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.uint w) })
    (n : ℕ) (hn : n < 2 ^ 256) :
    writeScalar cfg env evm er (.uint w) (.uint w n) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (setPackedWordNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat
          offset.val size.val n))) :=
  writeScalar_of_leaf (storageTypeOf_uint env w) hl rfl (storageLocStore_uint_packed evm slot offset size w n hn)

/-! ## Memory structs written into storage -/

/-- One field of a memory struct copied to storage (`toStorage`'s per-field step). -/
def structFieldValue (env : TypeEnv) (h : Heap) (fuel : ℕ) (fields : List (Ident × Value)) :
    Ty × Ident → Op (Ident × Solm.Value)
  | (fty, fname) => do
    let some fv := (fields.find? (·.1 == fname)).map (·.2) | Op.stuck
    let sv ← toStorage env h fuel fty fv
    pure (fname, sv)

/-- `s = S(...)` for a memory struct: the declared fields are converted one by one. -/
theorem toStorage_struct {env : TypeEnv} {fuel : ℕ} {h : Heap} {q : Option Ident} {n : Ident} {id : ℕ} {sty : Ty}
    {fields : List (Ident × Value)} {sd : StructInfo} (hget : h.get? id = some (.struct sty fields))
    (hs : env.struct? q n = some sd) :
    toStorage env h (fuel + 1) (.user q n) (.memRef id) =
      (sd.fields.mapM (structFieldValue env h fuel fields) >>= fun fvs => pure (.struct sd.name fvs)) := by
  rw [toStorage.eq_def]
  simp only [hget, hs]
  rfl

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
    Solm.encodePackedValue? (.elem (.int (.uint ⟨256, by decide⟩))) (.int n) = some (EVM.Word.toBytesBE (UInt256.ofNat n)) := by
  have hn' : n < EVM.twoPow 256 := hn
  simp [Solm.encodePackedValue?, ABI.encodeABIWord?, hn']
  rfl

theorem encodePackedValue?_address (a : EVM.Address) :
    Solm.encodePackedValue? (.elem .address) (.address a) = some ((EVM.Word.toBytesBE (UInt256.ofNat a.toNat)).drop 12) := by
  simp [Solm.encodePackedValue?]
  rfl

theorem encodePackedValue?_bytes32 (bs : List UInt8) (h : bs.length = 32) :
    Solm.encodePackedValue? (.elem (.bytes ⟨31, by decide⟩)) (.fixedBytes ⟨31, by decide⟩ bs) = some bs := by
  simp [Solm.encodePackedValue?, h, Solm.fixedBytesSize]

@[simp] theorem encodePackedValue?_bytes (ba : ByteArray) : Solm.encodePackedValue? .bytes (.bytes ba) = some ba.toList := rfl
@[simp] theorem encodePackedValue?_string (ba : ByteArray) : Solm.encodePackedValue? .string (.bytes ba) = some ba.toList := rfl

theorem abiArgsAbi_of_mapM {env : TypeEnv} {m : Machine} {tys : List ABI.ABIType} {vs : List Value} {svs : List Solm.Value}
    (hsvs : vs.mapM (toAbi m.heap fuelDefault) = some svs) (hraw : ∀ v ∈ vs, hasRaw m.heap fuelDefault v = false) :
    abiArgsAbi cfg env m tys vs = some (.ok (svs, m)) := by
  have hf := prepareArgs_of_noRaw (env := env) (cd := m.evm.executionEnv.calldata) (fuel := 1023) hraw
  simp only [abiArgsAbi, fuelDefault] at hf hsvs ⊢
  rw [hf, pure_bind, hsvs]
  rfl

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
  have hi' : i < 1461501637330902918203684832716283019655932542976 := by omega
  by_cases h40 : hd = some 40 <;> simp [explicitConv, implicitConv, h0, h40, hi'] <;> rfl

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
theorem directMember_member (fc : FlatContract) (fr : Frame) (e : Expr) (f : Ident)
    (h : fnRefContract fc fr e = none) : directMember fc fr (.member e f) = false := by
  simp [directMember, h]
@[simp] theorem fnRefContract_index (fc : FlatContract) (fr : Frame) (e i : Expr) : fnRefContract fc fr (.index e i) = none := rfl
@[simp] theorem fnRefContract_member (fc : FlatContract) (fr : Frame) (e : Expr) (f : Ident) :
    fnRefContract fc fr (.member e f) = none := rfl
@[simp] theorem fnRefContract_call (fc : FlatContract) (fr : Frame) (c : Expr) (opts : List CallOpt) (args : Args) :
    fnRefContract fc fr (.call c opts args) = none := rfl
/-- A local that is not of contract type is no function reference receiver. -/
theorem fnRefContract_ident_local (fc : FlatContract) (fr : Frame) (x : Ident) (l : Local) (hl : fr.get? x = some l)
    (hty : contractTyName fc.types l.ty = none) : fnRefContract fc fr (.ident x) = none := by
  cases henv : isEnvObj x <;> simp [fnRefContract, henv, hl, hty]
theorem fnRefContract_ident_env (fc : FlatContract) (fr : Frame) (x : Ident) (h : isEnvObj x = true) :
    fnRefContract fc fr (.ident x) = none := by simp [fnRefContract, h]
/-- A state variable that is not of contract type. -/
theorem fnRefContract_ident_var (fc : FlatContract) (fr : Frame) (x : Ident) (v : FlatVar) (hl : fr.get? x = none)
    (hv : fc.varIn fr.here x = some v) (hty : contractTyName fc.types v.ty = none) :
    fnRefContract fc fr (.ident x) = none := by
  cases henv : isEnvObj x <;> simp [fnRefContract, henv, hl, hv, hty]
theorem fnRefContract_ident_noContract (fc : FlatContract) (fr : Frame) (x : Ident) (hl : fr.get? x = none)
    (hv : fc.varIn fr.here x = none) (h : fc.types.contractKind? x = none) :
    fnRefContract fc fr (.ident x) = none := by
  cases henv : isEnvObj x <;> simp [fnRefContract, henv, hl, hv, h]
/-- A variable of contract type `C`: `x.f` is a function of `C`. -/
theorem fnRefContract_ident_contractVar (fc : FlatContract) (fr : Frame) (x c : Ident) (l : Local)
    (henv : isEnvObj x = false) (hl : fr.get? x = some l) (hty : contractTyName fc.types l.ty = some c) :
    fnRefContract fc fr (.ident x) = some c := by simp [fnRefContract, henv, hl, hty]
@[simp] theorem contractTyName_uint (env : TypeEnv) (w : ABI.BitWidth) : contractTyName env (.uint w) = none := rfl
@[simp] theorem contractTyName_address (env : TypeEnv) (p : Bool) : contractTyName env (.address p) = none := rfl
@[simp] theorem contractTyName_qual (env : TypeEnv) (q n : Ident) : contractTyName env (.user (some q) n) = none := rfl
@[simp] theorem contractTyName_mapping (env : TypeEnv) (k v : Ty) : contractTyName env (.mapping k v) = none := rfl
@[simp] theorem contractTyName_dynArray (env : TypeEnv) (e : Ty) : contractTyName env (.dynArray e) = none := rfl
@[simp] theorem contractTyName_array (env : TypeEnv) (e : Ty) (n : ℕ) : contractTyName env (.array e n) = none := rfl
@[simp] theorem contractTyName_bytes (env : TypeEnv) : contractTyName env .bytes = none := rfl
@[simp] theorem contractTyName_string (env : TypeEnv) : contractTyName env .string = none := rfl
/-! ## Names of errors and events: `E` in the scope of the running code, or `Q.E` -/

@[simp] theorem eventsRef_ident (fc : FlatContract) (here ev : Ident) :
    eventsRef fc here (.ident ev) = fc.eventsNamedIn here ev := rfl
@[simp] theorem eventsRef_member (fc : FlatContract) (here q ev : Ident) :
    eventsRef fc here (.member (.ident q) ev) = fc.eventsOf q ev := rfl
@[simp] theorem errorRef_ident (fc : FlatContract) (here e : Ident) :
    errorRef fc here (.ident e) = fc.errorIn here e := rfl
@[simp] theorem errorRef_member (fc : FlatContract) (here q e : Ident) :
    errorRef fc here (.member (.ident q) e) = fc.errorOf q e := rfl

/-- A local is never a unit name in qualifier position. -/
theorem unitQual_local (fc : FlatContract) (fr : Frame) (x : Ident) (l : Local) (hl : fr.get? x = some l) :
    unitQual fc fr x = false := by simp [unitQual, hl]

/-- A variable of the running code is never a unit name in qualifier position. -/
theorem unitQual_var (fc : FlatContract) (fr : Frame) (x : Ident) (v : FlatVar) (hv : fc.varIn fr.here x = some v) :
    unitQual fc fr x = false := by simp [unitQual, hv]

/-- A name that is no contract-like unit. -/
theorem unitQual_noContract (fc : FlatContract) (fr : Frame) (x : Ident) (h : fc.types.contractKind? x = none) :
    unitQual fc fr x = false := by simp [unitQual, h]

/-- `x.f` evaluates `x` first when `x` is a local, or a name that is neither an enum nor a unit
    (`unitQual_var`, `unitQual_noContract`). -/
theorem directMember_ident (fc : FlatContract) (fr : Frame) (x : Ident) (henv : isEnvObj x = false)
    (hx : (fr.get? x).isNone = false ∨ ((fc.types.enumIn fr.here x).isSome = false ∧ unitQual fc fr x = false)) :
    directMember fc fr (.ident x) = false := by
  rcases hx with h | ⟨h, hu⟩
  · have hl : ∃ l, fr.get? x = some l := by
      cases hg : fr.get? x with
      | none => simp [hg] at h
      | some l => exact ⟨l, rfl⟩
    obtain ⟨l, hl⟩ := hl
    simp [directMember, henv, hl, unitQual_local fc fr x l hl]
  · simp [directMember, henv, h, hu]

theorem clearStorage_bool {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (boolOffset0Loc slot)) :
    clearStorage cfg env evm er .bool =
      some (.ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.lnot ⟨255⟩)))) :=
  clearStorage_of_backend (storageTypeOf_bool env)
    (hl.clear _ _ _ (by rw [storageLocStore_int_zero_eq_bool_false]; exact storageLocStore_bool_false_offset0 evm slot))

theorem clearStorage_address {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (p : Bool) (hl : cfg.Leaf er (addressOffset0Loc slot)) :
    clearStorage cfg env evm er (.address p) =
      some (.ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩))) :=
  clearStorage_of_backend (storageTypeOf_address env p)
    (hl.clear _ _ _ (by
      rw [storageLocStore_int_zero_eq_address_zero]
      exact storageLocStore_address_offset0 evm slot ⟨0⟩ (by decide)))

/-! ## Number literals as right-hand sides, unchecked `+ 1` -/

theorem writeStorageDeep_literal_u256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap}
    {er : Solm.EvaledStorageRef} {slot : UInt256} (hl : cfg.Leaf er (uint256Loc slot)) (fuel : ℕ)
    (k : ℕ) (hd : Option Nat) (hk : k < 2 ^ 256) :
    writeStorageDeep cfg env (fuel + 1) evm h er u256Ty (.literal k hd) =
      some (.ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat k))) := by
  have hconv := implicitConv_literal_u256 env h k hd (Int.natCast_nonneg k) (by exact_mod_cast hk)
  rw [Int.toNat_natCast] at hconv
  have hst := storageLocStore_uint256 evm slot (UInt256.ofNat k)
  rw [ulit_toNat' k hk] at hst
  exact writeStorageDeep_of_value (storageTypeOf_uint env _) (storageValueOf_direct fuel trivial hconv rfl)
    (hl.write _ _ _ _ hst)

theorem assign_storage_u256_lit {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.Leaf er (uint256Loc slot)) (k : ℕ) (hd : Option Nat)
    (hk : k < 2 ^ 256) :
    assign cfg env fr m (.storage er u256Ty) (.literal k hd) =
      some (.ok (fr, { m with evm := Solm.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot (UInt256.ofNat k) })) := by
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
    (hl : cfg.Leaf er (boolOffset0Loc slot)) :
    readScalar cfg env evm er .bool =
      some (.bool (!((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0))) := by
  refine readScalar_of_leaf (storageTypeOf_bool env) hl ?_
  rw [storageLocLoad_bool_offset0]
  cases h : (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0 <;>
    simp [Solm.wordToElem, scalarOfAbi, h]

theorem loadIfScalar_bool {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (boolOffset0Loc slot)) :
    loadIfScalar cfg env evm er .bool =
      some (.bool (!((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩).val == 0))) := by
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
    (hl : cfg.Leaf er (int256Loc slot)) :
    readScalar cfg env evm er s256Ty =
      some (s256Val (s256OfWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) :=
  readScalar_of_leaf (storageTypeOf_int env _) hl (by
    rw [storageLocLoad_int256]
    exact scalarOfAbi_s256 env _ (s256OfWord_bounds _).1 (s256OfWord_bounds _).2)

theorem loadIfScalar_s256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (int256Loc slot)) :
    loadIfScalar cfg env evm er s256Ty =
      some (s256Val (s256OfWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))) := by
  unfold loadIfScalar
  rw [if_pos (by rfl : isValueType env s256Ty = true)]
  exact readScalar_s256 hl

theorem writeScalar_s256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (int256Loc slot)) (i : Int) :
    writeScalar cfg env evm er s256Ty (s256Val i) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt i)) :=
  writeScalar_of_leaf (storageTypeOf_int env _) hl rfl (storageLocStore_int256 evm slot i)

theorem writeStorageDeep_s256 {cfg : Config} {env : TypeEnv} {evm : EVM.State} {h : Heap} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.Leaf er (int256Loc slot)) (fuel : Nat) (i : Int) :
    writeStorageDeep cfg env (fuel + 1) evm h er s256Ty (s256Val i) =
      some (.ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (EVM.wordOfInt i))) :=
  writeStorageDeep_of_value (storageTypeOf_int env _)
    (storageValueOf_direct fuel trivial
      (by simp [implicitConv] : implicitConv env h (s256Val i) s256Ty = some (s256Val i, h)) rfl)
    (hl.write _ _ _ _ (storageLocStore_int256 evm slot i))

theorem assign_storage_s256 {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.Leaf er (int256Loc slot)) (i : Int) :
    assign cfg env fr m (.storage er s256Ty) (s256Val i) =
      some (.ok (fr, { m with evm := Solm.EVM.storageStore m.evm m.evm.executionEnv.codeOwner slot (EVM.wordOfInt i) })) := by
  simp [assign, fuelDefault, writeStorageDeep_s256 hl]

/-! ## `ecrecover` arguments, `catch` clause selection -/

theorem abiArgs_ecrecover (cfg : Config) (env : TypeEnv) (m : Machine) (hb rb sb : List UInt8) (n : ℕ) :
    abiArgs cfg env m ecrecoverParamTys
      [.fixedBytes ⟨31, by decide⟩ hb, .uint ⟨8, by decide⟩ n, .fixedBytes ⟨31, by decide⟩ rb, .fixedBytes ⟨31, by decide⟩ sb] =
      some (.ok ([.fixedBytes ⟨31, by decide⟩ hb, .int n, .fixedBytes ⟨31, by decide⟩ rb, .fixedBytes ⟨31, by decide⟩ sb], m)) := by
  simp [abiArgs, prepareArgs, ecrecoverParamTys, coerce, implicitConv, fuelDefault]

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
    (hl : cfg.Leaf er (addressOffset0Loc slot)) :
    loadIfScalar cfg env evm er (.address false) =
      some (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask).toNat)) := by
  unfold loadIfScalar
  rw [if_pos (by rfl : isValueType env (.address false) = true)]
  exact readScalar_address hl

theorem writeScalar_address' {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    (hl : cfg.Leaf er (addressOffset0Loc slot)) (a : EVM.Address) :
    writeScalar cfg env evm er (.address false) (.address a) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat a.toNat))) := by
  have ha : a.toNat < 2 ^ 160 := a.isLt
  have hlt : (UInt256.ofNat a.toNat).toNat = a.toNat := ulit_toNat' _ (by change a.toNat < 2 ^ 256; omega)
  have h := writeScalar_address (env := env) (evm := evm) hl (UInt256.ofNat a.toNat) (by rw [hlt]; exact ha)
  rw [hlt, accountAddress_ofNat_toNat] at h
  exact h

theorem exitScope_get?_of_none {fr fr' : Frame} {k : Ident} (h : fr.get? k = none) : (fr.exitScope fr').get? k = none := by
  rw [exitScope_get?']
  have h' : fr.locals[k]? = none := by simpa [Frame.get?, Std.HashMap.get?_eq_getElem?] using h
  simp [Std.HashMap.contains_eq_isSome_getElem?, h']

/-! ## `try`/`catch` facts -/

theorem decodeRets_single {cfg : Config} {env : TypeEnv} {m : Machine} {p : Param} {rtys : List ABI.ABIType}
    {out : ByteArray} {sv : Solm.Value} {v : Value}
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some [sv])
    (hof : ofAbi env fuelDefault p.ty sv m.heap = some (v, m.heap)) :
    decodeRets cfg env m [p] rtys out = some ([v], m) := by
  simp [decodeRets, hdec, hof]

theorem tryRets_single {cfg : Config} {env : TypeEnv} {m : Machine} {p : Param} {rtys : List ABI.ABIType}
    {out : ByteArray} {sv : Solm.Value} {v : Value}
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

/-- A memory array is copied element by element. -/
theorem toStorage_dynArray {env : TypeEnv} {fuel : ℕ} {h : Heap} {e ety : Ty} {id : ℕ} {elems : List Value} {fx : Bool}
    (hget : h.get? id = some (.array ety elems fx)) :
    toStorage env h (fuel + 1) (.dynArray e) (.memRef id) = (Solm.Value.array ·) <$> elems.mapM (toStorage env h fuel e) := by
  rw [toStorage.eq_def]
  simp only [hget]

theorem toStorage_array {env : TypeEnv} {fuel : ℕ} {h : Heap} {e ety : Ty} {id n : ℕ} {elems : List Value} {fx : Bool}
    (hget : h.get? id = some (.array ety elems fx)) :
    toStorage env h (fuel + 1) (.array e n) (.memRef id) = (Solm.Value.array ·) <$> elems.mapM (toStorage env h fuel e) := by
  rw [toStorage.eq_def]
  simp only [hget]

/-- `writeStorageDeep` is a backend write of the value's storage value. -/
theorem writeStorageDeep_eq {cfg : Config} {env : TypeEnv} {fuel : ℕ} {evm : EVM.State} {h : Heap} {er : Solm.EvaledStorageRef}
    {ty : Ty} {v : Value} {st : Solm.StorageType} (hst : storageTypeOf env ty = some st) :
    writeStorageDeep cfg env fuel evm h er ty v =
      (storageValueOf cfg env fuel evm h ty v >>= fun sv => liftStorage (cfg.storageBackend.write er st sv evm)) := by
  simp only [writeStorageDeep, hst]

/-! ## `abi.decode` facts -/

theorem ofAbiList_nil (env : TypeEnv) (h : Heap) : ofAbiList env [] [] h = some ([], h) := by simp [ofAbiList]

/-- One step of `ofAbiList` (the fold with a generalised accumulator). -/
def ofAbiStep (env : TypeEnv) (acch : List Value × Heap) (tsv : Ty × Solm.Value) : Option (List Value × Heap) := do
  let r ← ofAbi env fuelDefault tsv.1 tsv.2 acch.2
  pure (acch.1 ++ [r.1], r.2)

theorem ofAbiList_eq_foldlM (env : TypeEnv) (tys : List Ty) (svs : List Solm.Value) (h : Heap)
    (hlen : tys.length = svs.length) :
    ofAbiList env tys svs h = (tys.zip svs).foldlM (ofAbiStep env) ([], h) := by
  simp only [ofAbiList, hlen, ne_eq, not_true_eq_false, if_false]
  rfl

/-- The fold behind `ofAbiList` only appends to its accumulator. -/
theorem ofAbi_fold_shift (env : TypeEnv) : ∀ (xs : List (Ty × Solm.Value)) (acc : List Value) (h : Heap),
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

theorem ofAbiList_cons (env : TypeEnv) (t : Ty) (ts : List Ty) (sv : Solm.Value) (svs : List Solm.Value) (h h' h'' : Heap)
    (v : Value) (vs : List Value) (hlen : ts.length = svs.length)
    (hv : ofAbi env fuelDefault t sv h = some (v, h')) (hrest : ofAbiList env ts svs h' = some (vs, h'')) :
    ofAbiList env (t :: ts) (sv :: svs) h = some (v :: vs, h'') := by
  rw [ofAbiList_eq_foldlM env _ _ h (by simp [hlen]), List.zip_cons_cons, List.foldlM_cons]
  simp only [ofAbiStep, hv, Opt.some_bind, Option.pure_def, List.nil_append]
  rw [ofAbi_fold_shift env _ [v] h', ← ofAbiList_eq_foldlM env ts svs h' hlen, hrest]
  rfl

/-! ## Canonical types

A type written in code is identified with its declaring unit (`TypeEnv.canonTy`); elementary types
are unchanged. -/

@[simp] theorem TypeEnv.canonTy_uint (env : TypeEnv) (here : Ident) (w : ABI.BitWidth) :
    env.canonTy here (.uint w) = .uint w := rfl
@[simp] theorem TypeEnv.canonTy_int (env : TypeEnv) (here : Ident) (w : ABI.BitWidth) :
    env.canonTy here (.int w) = .int w := rfl
@[simp] theorem TypeEnv.canonTy_bool (env : TypeEnv) (here : Ident) : env.canonTy here .bool = .bool := rfl
@[simp] theorem TypeEnv.canonTy_address (env : TypeEnv) (here : Ident) (p : Bool) :
    env.canonTy here (.address p) = .address p := rfl
@[simp] theorem TypeEnv.canonTy_fixedBytes (env : TypeEnv) (here : Ident) (n : Fin 32) :
    env.canonTy here (.fixedBytes n) = .fixedBytes n := rfl
@[simp] theorem TypeEnv.canonTy_bytes (env : TypeEnv) (here : Ident) : env.canonTy here .bytes = .bytes := rfl
@[simp] theorem TypeEnv.canonTy_string (env : TypeEnv) (here : Ident) : env.canonTy here .string = .string := rfl
@[simp] theorem TypeEnv.canonTy_dynArray (env : TypeEnv) (here : Ident) (e : Ty) :
    env.canonTy here (.dynArray e) = .dynArray (env.canonTy here e) := rfl
@[simp] theorem TypeEnv.canonTy_array (env : TypeEnv) (here : Ident) (e : Ty) (n : Nat) :
    env.canonTy here (.array e n) = .array (env.canonTy here e) n := rfl
@[simp] theorem TypeEnv.canonTy_mapping (env : TypeEnv) (here : Ident) (k v : Ty) :
    env.canonTy here (.mapping k v) = .mapping (env.canonTy here k) (env.canonTy here v) := rfl

/-- No struct or enum named `n` is in scope: `n` is a contract type (or unknown) and keeps its spelling. -/
theorem TypeEnv.canonTy_user_none {env : TypeEnv} {here n : Ident}
    (hs : env.structIn here n = none) (he : env.enumIn here n = none) (hv : env.valueTypeIn here n = none) :
    env.canonTy here (.user none n) = .user none n := by
  have ho : env.typeOwner (env.scope here) n = none := by
    simp only [TypeEnv.typeOwner, List.find?_eq_none]
    intro u hu
    have h1 := List.findSome?_eq_none_iff.mp hs u hu
    have h2 := List.findSome?_eq_none_iff.mp he u hu
    have h3 := List.findSome?_eq_none_iff.mp hv u hu
    simp [h1, h2, h3]
  simp [TypeEnv.canonTy, Ty.mapUser, ho]

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
    (hl : cfg.Leaf er { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.sint w) })
    (hoff : 8 * offset.val < 256) :
    readScalar cfg env evm er (.int w) =
      some (.sint w (sextAt w.val (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (256 ^ offset.val)))
        (UInt256.ofNat (256 ^ size.val - 1))).toNat)) := by
  have hsize : 8 * size.val ≤ 256 := by have := size.isLt; omega
  refine readScalar_of_leaf (storageTypeOf_int env w) hl ?_
  rw [storageLocLoad_sint_offset evm slot offset size w hoff hsize]
  have hb := sextAt_bounds w.val (UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (256 ^ offset.val)))
    (UInt256.ofNat (256 ^ size.val - 1))).toNat w.property.1
  simp [scalarOfAbi, hb.1, hb.2]

/-- A packed `int<8·size>` field written in place. -/
theorem writeScalar_sint_packed {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef} {slot : UInt256}
    {offset : Fin 32} {size : Fin 33} {w : ABI.BitWidth} {hbound : offset.val + size.val - 1 < 32}
    (hl : cfg.Leaf er { slot := slot, offset := offset, size := size, hbound := hbound, type := .int (.sint w) })
    (i : Int) :
    writeScalar cfg env evm er (.int w) (.sint w i) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (setPackedWordNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat
          offset.val size.val (EVM.wordOfInt i).toNat))) :=
  writeScalar_of_leaf (storageTypeOf_int env w) hl rfl (storageLocStore_int_packed evm slot offset size _ i)

/-! ## Declarations of value-type locals (the `declare` facts behind `varDecl*`) -/

theorem declare_u256 (cfg : Config) (env : TypeEnv) (fr : Frame) (m : Machine) (loc : Option DataLoc) (x : Ident) (n : ℕ) :
    declare cfg env fr m u256Ty loc x (some (u256Val n)) = some (.ok (fr.bind x u256Ty loc (u256Val n), m)) := by
  simp [declare, coerce]

theorem declare_bool (cfg : Config) (env : TypeEnv) (fr : Frame) (m : Machine) (loc : Option DataLoc) (x : Ident) (b : Bool) :
    declare cfg env fr m .bool loc x (some (.bool b)) = some (.ok (fr.bind x .bool loc (.bool b), m)) := by
  simp [declare, coerce]

theorem declare_address (cfg : Config) (env : TypeEnv) (fr : Frame) (m : Machine) (loc : Option DataLoc) (x : Ident)
    (a : EVM.Address) :
    declare cfg env fr m (.address false) loc x (some (.address a)) = some (.ok (fr.bind x (.address false) loc (.address a), m)) := by
  simp [declare, coerce]

theorem declare_bytes32 (cfg : Config) (env : TypeEnv) (fr : Frame) (m : Machine) (loc : Option DataLoc) (x : Ident)
    (bs : List UInt8) :
    declare cfg env fr m (.fixedBytes ⟨31, by decide⟩) loc x (some (.fixedBytes ⟨31, by decide⟩ bs)) =
      some (.ok (fr.bind x (.fixedBytes ⟨31, by decide⟩) loc (.fixedBytes ⟨31, by decide⟩ bs), m)) := by
  simp [declare, coerce]

/-- Assigning a `bool` into a return slot or local. -/
theorem assign_local_bool {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {x : Ident} (l : Local)
    (hx : fr.get? x = some l) (hty : l.ty = .bool) (b : Bool) :
    assign cfg env fr m (.local x) (.bool b) = some (.ok (fr.setVal x (.bool b), m)) := by
  simp [assign, coerce, hx, hty]

theorem assign_local_address {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {x : Ident} (l : Local)
    (hx : fr.get? x = some l) (hty : l.ty = .address false) (a : EVM.Address) :
    assign cfg env fr m (.local x) (.address a) = some (.ok (fr.setVal x (.address a), m)) := by
  simp [assign, coerce, hx, hty]

/-! ## Two decoded return values -/

theorem decodeRets_two {cfg : Config} {env : TypeEnv} {m : Machine} {p1 p2 : Param} {rtys : List ABI.ABIType}
    {out : ByteArray} {sv1 sv2 : Solm.Value} {v1 v2 : Value} {h1 h2 : Heap}
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some [sv1, sv2])
    (hof1 : ofAbi env fuelDefault p1.ty sv1 m.heap = some (v1, h1)) (hof2 : ofAbi env fuelDefault p2.ty sv2 h1 = some (v2, h2)) :
    decodeRets cfg env m [p1, p2] rtys out = some ([v1, v2], { m with heap := h2 }) := by
  simp [decodeRets, hdec, hof1, hof2]

theorem tryRets_two {cfg : Config} {env : TypeEnv} {m : Machine} {p1 p2 : Param} {rtys : List ABI.ABIType}
    {out : ByteArray} {sv1 sv2 : Solm.Value} {v1 v2 : Value} {h1 h2 : Heap}
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some [sv1, sv2])
    (hof1 : ofAbi env fuelDefault p1.ty sv1 m.heap = some (v1, h1)) (hof2 : ofAbi env fuelDefault p2.ty sv2 h1 = some (v2, h2)) :
    tryRets cfg env m [p1, p2] rtys out = some ([v1, v2], { m with heap := h2 }) := by
  simp [tryRets, decodeRets_two hdec hof1 hof2]

theorem bindTryParams_two {cfg : Config} {env : TypeEnv} {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {p1 p2 : Param}
    {x1 x2 : Ident} {v1 v2 : Value} (hn1 : p1.name = some x1) (hn2 : p2.name = some x2)
    (hd1 : declare cfg env fr m p1.ty (some (p1.loc.getD .memory)) x1 (some v1) = some (.ok (fr1, m1)))
    (hd2 : declare cfg env fr1 m1 p2.ty (some (p2.loc.getD .memory)) x2 (some v2) = some (.ok (fr2, m2))) :
    bindTryParams cfg env fr m [p1, p2] [v1, v2] = some (.ok (fr2, m2)) := by
  simp [bindTryParams, hn1, hn2, hd1, hd2]

/-! ## Integers of any width -/

theorem settle_uint_ok (w : ABI.BitWidth) (r : Int) (h0 : 0 ≤ r) (hr : r < (2 : Int) ^ w.val) :
    settle (.uint w) true r = .ok r := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]
  omega

theorem settle_uint_overflow_hi (w : ABI.BitWidth) (r : Int) (h : (2 : Int) ^ w.val ≤ r) :
    settle (.uint w) true r = .error .overflow := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]
  omega

theorem settle_uint_overflow_lo (w : ABI.BitWidth) (r : Int) (h : r < 0) :
    settle (.uint w) true r = .error .overflow := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]
  omega

theorem settle_sint_ok (w : ABI.BitWidth) (r : Int) (hlo : -(2 : Int) ^ (w.val - 1) ≤ r)
    (hhi : r < (2 : Int) ^ (w.val - 1)) : settle (.sint w) true r = .ok r := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]
  omega

theorem settle_sint_overflow (w : ABI.BitWidth) (r : Int)
    (h : ¬ (-(2 : Int) ^ (w.val - 1) ≤ r ∧ r < (2 : Int) ^ (w.val - 1))) :
    settle (.sint w) true r = .error .overflow := by
  simp [settle, IntTy.inRange, IntTy.min, IntTy.max]
  omega

theorem unifyInts_uint_uint (w : ABI.BitWidth) (a b : ℕ) :
    unifyInts (.uint w a) (.uint w b) = some (some (ABI.IntType.uint w), (a : Int), (b : Int)) := by
  simp [unifyInts, Value.int?, commonIntType, implicitIntConv]

/-- Mixed widths: the narrower operand is widened to the wider type. -/
theorem unifyInts_uint_widen (w w' : ABI.BitWidth) (a b : ℕ) (hle : w.val ≤ w'.val) :
    unifyInts (.uint w a) (.uint w' b) = some (some (ABI.IntType.uint w'), (a : Int), (b : Int)) := by
  simp [unifyInts, Value.int?, commonIntType, implicitIntConv, hle, -Subtype.coe_le_coe, -Subtype.coe_lt_coe]

theorem unifyInts_uint_widen' (w w' : ABI.BitWidth) (a b : ℕ) (hlt : w'.val < w.val) :
    unifyInts (.uint w a) (.uint w' b) = some (some (ABI.IntType.uint w), (a : Int), (b : Int)) := by
  simp [unifyInts, Value.int?, commonIntType, implicitIntConv, Nat.not_le.mpr hlt, Nat.le_of_lt hlt,
    -Subtype.coe_le_coe, -Subtype.coe_lt_coe]

theorem unifyInts_uint_lit (w : ABI.BitWidth) (n : ℕ) (k : Int) (hd : Option Nat) (h0 : 0 ≤ k)
    (hk : k < (2 : Int) ^ w.val) :
    unifyInts (.uint w n) (.literal k hd) = some (some (ABI.IntType.uint w), (n : Int), k) := by
  simp [unifyInts, Value.int?, IntTy.inRange, IntTy.min, IntTy.max]
  omega

theorem unifyInts_sint_sint (w : ABI.BitWidth) (a b : Int) :
    unifyInts (.sint w a) (.sint w b) = some (some (ABI.IntType.sint w), a, b) := by
  simp [unifyInts, Value.int?, commonIntType, implicitIntConv]

theorem binop_add_uint (w : ABI.BitWidth) (a b : ℕ) (hfit : a + b < 2 ^ w.val) :
    binop true .add (.uint w a) (.uint w b) = some (.ok (.uint w (a + b))) := by
  rw [binop_add_uint_of_unify true _ a _ (unifyInts_uint_uint w a b), add,
    settle_uint_ok w _ (by omega) (by exact_mod_cast hfit), liftArith_ok]
  simp [mkInt, toNat_natCast_add]

theorem binop_add_uint_overflow (w : ABI.BitWidth) (a b : ℕ) (hbig : 2 ^ w.val ≤ a + b) :
    binop true .add (.uint w a) (.uint w b) = some (.error .overflow) := by
  rw [binop_add_uint_of_unify true _ a _ (unifyInts_uint_uint w a b), add,
    settle_uint_overflow_hi w _ (by exact_mod_cast hbig), liftArith_error]

theorem binop_sub_uint (w : ABI.BitWidth) (a b : ℕ) (ha : a < 2 ^ w.val) (hle : b ≤ a) :
    binop true .sub (.uint w a) (.uint w b) = some (.ok (.uint w (a - b))) := by
  rw [binop_sub_uint_of_unify true _ a _ (unifyInts_uint_uint w a b), sub,
    settle_uint_ok w _ (by omega) (by rw [← Nat.cast_sub hle]; exact_mod_cast lt_of_le_of_lt (Nat.sub_le a b) ha),
    liftArith_ok]
  simp [mkInt, toNat_natCast_sub a b hle]

theorem binop_sub_uint_underflow (w : ABI.BitWidth) (a b : ℕ) (hlt : a < b) :
    binop true .sub (.uint w a) (.uint w b) = some (.error .overflow) := by
  rw [binop_sub_uint_of_unify true _ a _ (unifyInts_uint_uint w a b), sub,
    settle_uint_overflow_lo w _ (by omega), liftArith_error]

theorem binop_mul_uint (w : ABI.BitWidth) (a b : ℕ) (hfit : a * b < 2 ^ w.val) :
    binop true .mul (.uint w a) (.uint w b) = some (.ok (.uint w (a * b))) := by
  rw [binop_mul_uint_of_unify true _ a _ (unifyInts_uint_uint w a b), mul,
    settle_uint_ok w _ (by positivity) (by exact_mod_cast hfit), liftArith_ok]
  simp [mkInt, toNat_natCast_mul]

theorem binop_mul_uint_overflow (w : ABI.BitWidth) (a b : ℕ) (hbig : 2 ^ w.val ≤ a * b) :
    binop true .mul (.uint w a) (.uint w b) = some (.error .overflow) := by
  rw [binop_mul_uint_of_unify true _ a _ (unifyInts_uint_uint w a b), mul,
    settle_uint_overflow_hi w _ (by exact_mod_cast hbig), liftArith_error]

theorem binop_div_uint (c : Bool) (w : ABI.BitWidth) (a b : ℕ) (ha : a < 2 ^ w.val) (hb : b ≠ 0) :
    binop c .div (.uint w a) (.uint w b) = some (.ok (.uint w (a / b))) := by
  have hnn : (0 : Int) ≤ ((a / b : ℕ) : Int) := Int.natCast_nonneg _
  have hlt : ((a / b : ℕ) : Int) < (2 : Int) ^ w.val := by exact_mod_cast lt_of_le_of_lt (Nat.div_le_self a b) ha
  rw [binop_div_uint_of_unify c _ a _ (unifyInts_uint_uint w a b), div, if_neg (by exact_mod_cast hb),
    Int.tdiv_eq_ediv_of_nonneg (by omega), ← Int.natCast_ediv]
  cases c
  · rw [settle_unchecked, liftArith_ok]
    simp only [mkInt, IntTy.wrap, IntTy.isSigned, IntTy.width, Bool.false_and, Bool.false_eq_true, if_false]
    rw [Int.emod_eq_of_lt hnn (by exact_mod_cast hlt), Int.toNat_natCast]
  · rw [settle_uint_ok w _ hnn hlt, liftArith_ok]
    simp only [mkInt, Int.toNat_natCast]

theorem binop_mod_uint (c : Bool) (w : ABI.BitWidth) (a b : ℕ) (hb : b ≠ 0) :
    binop c .mod (.uint w a) (.uint w b) = some (.ok (.uint w (a % b))) := by
  rw [binop_mod_uint_of_unify c _ a _ (unifyInts_uint_uint w a b), mod, if_neg (by exact_mod_cast hb),
    Int.tmod_eq_emod_of_nonneg (by omega), ← Int.natCast_emod, liftArith_ok]
  simp only [mkInt, Int.toNat_natCast]

theorem binop_cmp_uint_of_unify (c : Bool) (op : BinOp) (hop : isCmp op = true) (w : ABI.BitWidth) (n : ℕ) (b : Value)
    {t : IntTy} {x y : Int} (hu : unifyInts (.uint w n) b = some (some t, x, y)) :
    binop c op (.uint w n) b = Op.ofOpt (cmpInt op x y) := by
  cases op <;> simp [binop, adoptBytes, toBool, addrNat, hu, isCmp, cmpInt] at hop ⊢

theorem binop_lt_uint (c : Bool) (w : ABI.BitWidth) (a b : ℕ) :
    binop c .lt (.uint w a) (.uint w b) = some (.ok (.bool (decide (a < b)))) := by
  rw [binop_cmp_uint_of_unify c .lt rfl w a _ (unifyInts_uint_uint w a b)]; simp [cmpInt]
theorem binop_le_uint (c : Bool) (w : ABI.BitWidth) (a b : ℕ) :
    binop c .le (.uint w a) (.uint w b) = some (.ok (.bool (decide (a ≤ b)))) := by
  rw [binop_cmp_uint_of_unify c .le rfl w a _ (unifyInts_uint_uint w a b)]; simp [cmpInt]
theorem binop_gt_uint (c : Bool) (w : ABI.BitWidth) (a b : ℕ) :
    binop c .gt (.uint w a) (.uint w b) = some (.ok (.bool (decide (b < a)))) := by
  rw [binop_cmp_uint_of_unify c .gt rfl w a _ (unifyInts_uint_uint w a b)]; simp [cmpInt]
theorem binop_ge_uint (c : Bool) (w : ABI.BitWidth) (a b : ℕ) :
    binop c .ge (.uint w a) (.uint w b) = some (.ok (.bool (decide (b ≤ a)))) := by
  rw [binop_cmp_uint_of_unify c .ge rfl w a _ (unifyInts_uint_uint w a b)]; simp [cmpInt]
theorem binop_eq_uint (c : Bool) (w : ABI.BitWidth) (a b : ℕ) :
    binop c .eq (.uint w a) (.uint w b) = some (.ok (.bool (decide (a = b)))) := by
  rw [binop_cmp_uint_of_unify c .eq rfl w a _ (unifyInts_uint_uint w a b)]; simp [cmpInt]
theorem binop_ne_uint (c : Bool) (w : ABI.BitWidth) (a b : ℕ) :
    binop c .ne (.uint w a) (.uint w b) = some (.ok (.bool (decide (a ≠ b)))) := by
  rw [binop_cmp_uint_of_unify c .ne rfl w a _ (unifyInts_uint_uint w a b)]; simp [cmpInt]

theorem binop_add_sint (w : ABI.BitWidth) (a b : Int) (hlo : -(2 : Int) ^ (w.val - 1) ≤ a + b)
    (hhi : a + b < (2 : Int) ^ (w.val - 1)) :
    binop true .add (.sint w a) (.sint w b) = some (.ok (.sint w (a + b))) := by
  rw [binop_add_sint_of_unify true _ a _ (unifyInts_sint_sint w a b), add, settle_sint_ok w _ hlo hhi, liftArith_ok]
  rfl

theorem binop_sub_sint (w : ABI.BitWidth) (a b : Int) (hlo : -(2 : Int) ^ (w.val - 1) ≤ a - b)
    (hhi : a - b < (2 : Int) ^ (w.val - 1)) :
    binop true .sub (.sint w a) (.sint w b) = some (.ok (.sint w (a - b))) := by
  rw [binop_sub_sint_of_unify true _ a _ (unifyInts_sint_sint w a b), sub, settle_sint_ok w _ hlo hhi, liftArith_ok]
  rfl

theorem binop_mul_sint (w : ABI.BitWidth) (a b : Int) (hlo : -(2 : Int) ^ (w.val - 1) ≤ a * b)
    (hhi : a * b < (2 : Int) ^ (w.val - 1)) :
    binop true .mul (.sint w a) (.sint w b) = some (.ok (.sint w (a * b))) := by
  rw [binop_mul_sint_of_unify true _ a _ (unifyInts_sint_sint w a b), mul, settle_sint_ok w _ hlo hhi, liftArith_ok]
  rfl

theorem binop_lt_sint (c : Bool) (w : ABI.BitWidth) (a b : Int) :
    binop c .lt (.sint w a) (.sint w b) = some (.ok (.bool (decide (a < b)))) := by
  rw [binop_cmp_sint_of_unify c .lt rfl w a _ (unifyInts_sint_sint w a b)]; rfl

/-- `uint8 n` and friends as a typed value. -/
abbrev uintVal (w : ABI.BitWidth) (n : ℕ) : Value := .uint w n

theorem scalarOfAbi_uint_lt (env : TypeEnv) (w : ABI.BitWidth) (n : ℕ) (hn : n < 2 ^ w.val) :
    scalarOfAbi env (.uint w) (.int n) = some (.uint w n) := by
  simp [scalarOfAbi]; exact_mod_cast hn

theorem assign_local_uint {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {x : Ident} (l : Local) (w : ABI.BitWidth)
    (hx : fr.get? x = some l) (hty : l.ty = .uint w) (n : ℕ) :
    assign cfg env fr m (.local x) (.uint w n) = some (.ok (fr.setVal x (.uint w n), m)) := by
  simp [assign, coerce, implicitConv, hx, hty]

/-! ## `try … returns (…)` for any number of returns -/

/-- The reconstruction fold of `decodeRets` is `ofAbiList` on the parameter types. -/
theorem decodeRets_eq_ofAbiList (cfg : Config) (env : TypeEnv) (m : Machine) (rets : List Param) (rtys : List ABI.ABIType)
    (out : ByteArray) (svs : List Solm.Value)
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some svs) (hlen : svs.length = rets.length) :
    decodeRets cfg env m rets rtys out =
      (ofAbiList env (rets.map (·.ty)) svs m.heap).map fun r => (r.1, { m with heap := r.2 }) := by
  rw [ofAbiList_eq_foldlM env _ _ _ (by simp [hlen])]
  simp only [decodeRets, hdec, Opt.some_bind, hlen, ne_eq, not_true_eq_false, if_false]
  have hzip : (rets.map (·.ty)).zip svs = (rets.zip svs).map fun p => (p.1.ty, p.2) := by
    rw [List.zip_map_left]; rfl
  rw [hzip, List.foldlM_map]
  simp [ofAbiStep, Option.map_eq_bind, Function.comp_def]

theorem decodeRets_of_ofAbiList {cfg : Config} {env : TypeEnv} {m : Machine} {rets : List Param} {rtys : List ABI.ABIType}
    {out : ByteArray} {svs : List Solm.Value} {vs : List Value} {h' : Heap}
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some svs) (hlen : svs.length = rets.length)
    (hof : ofAbiList env (rets.map (·.ty)) svs m.heap = some (vs, h')) :
    decodeRets cfg env m rets rtys out = some (vs, { m with heap := h' }) := by
  rw [decodeRets_eq_ofAbiList cfg env m rets rtys out svs hdec hlen, hof]; rfl

theorem tryRets_of_ofAbiList {cfg : Config} {env : TypeEnv} {m : Machine} {rets : List Param} {rtys : List ABI.ABIType}
    {out : ByteArray} {svs : List Solm.Value} {vs : List Value} {h' : Heap} (hne : rets ≠ [])
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some svs) (hlen : svs.length = rets.length)
    (hof : ofAbiList env (rets.map (·.ty)) svs m.heap = some (vs, h')) :
    tryRets cfg env m rets rtys out = some (vs, { m with heap := h' }) := by
  simp only [tryRets, List.isEmpty_eq_false_iff.mpr hne, if_false]
  exact decodeRets_of_ofAbiList hdec hlen hof

/-- `bindTryParams` one parameter at a time. -/
theorem bindTryParams_cons {cfg : Config} {env : TypeEnv} {fr fr1 fr' : Frame} {m m1 m' : Machine} {p : Param} {ps : List Param}
    {x : Ident} {v : Value} {vs : List Value} (hlen : ps.length = vs.length) (hname : p.name = some x)
    (hdecl : declare cfg env fr m p.ty (some (p.loc.getD .memory)) x (some v) = some (.ok (fr1, m1)))
    (hrest : bindTryParams cfg env fr1 m1 ps vs = some (.ok (fr', m'))) :
    bindTryParams cfg env fr m (p :: ps) (v :: vs) = some (.ok (fr', m')) := by
  have hloc : (p.loc <|> some DataLoc.memory) = some (p.loc.getD .memory) := by cases p.loc <;> rfl
  simp only [bindTryParams, List.length_cons, hlen, ne_eq, not_true_eq_false, if_false, List.zip_cons_cons,
    List.foldlM_cons] at hrest ⊢
  simp only [hname, hloc, hdecl, Opt.some_bind]
  simpa using hrest

/-! ## Named arguments, free functions, `C.f.selector`, `address.code` -/

@[simp] theorem callArgs_positional (paramss : List (List Param)) (es : List Expr) :
    callArgs paramss (.positional es) = some es := rfl

theorem callArgs_named (paramss : List (List Param)) (fs : List (Ident × Expr)) (ps : List Param)
    (h : paramss.filter (fun ps => ps.length == fs.length && ps.all fun p => fs.any (p.name == some ·.1)) = [ps]) :
    callArgs paramss (.named fs) = namedArgs (ps.map (·.name.getD "")) fs := by
  simp [callArgs, h]

/-- In code of a contract of the hierarchy, a name with implementations in the hierarchy. -/
theorem FlatContract.fnsNamedIn_vtable (fc : FlatContract) (here f : Ident) (c : FnKey × FnId) (cs : List (FnKey × FnId))
    (hh : fc.linearization.contains here = true) (h : fc.vtable.filter (·.1.name == f) = c :: cs) :
    fc.fnsNamedIn here f = c :: cs := by
  have hh' : here ∈ fc.linearization := by simpa using hh
  simp [FlatContract.fnsNamedIn, hh', h]

/-- In code of a contract of the hierarchy, a modifier is the hierarchy's most derived one. -/
theorem FlatContract.modifierIn_hier (fc : FlatContract) (here name : Ident)
    (hh : fc.linearization.contains here = true) : fc.modifierIn here name = fc.modifier? name := by
  have hh' : here ∈ fc.linearization := by simpa using hh
  simp [FlatContract.modifierIn, hh']

/-- In code of a contract of the hierarchy, a name the hierarchy does not define: the file's functions. -/
theorem FlatContract.fnsNamedIn_free (fc : FlatContract) (here f : Ident)
    (hh : fc.linearization.contains here = true) (h : fc.vtable.filter (·.1.name == f) = []) :
    fc.fnsNamedIn here f = fc.freeFns.filter (·.1.name == f) := by
  have hh' : here ∈ fc.linearization := by simpa using hh
  simp [FlatContract.fnsNamedIn, hh', h]

theorem fnRefContract_this (fc : FlatContract) (fr : Frame) : fnRefContract fc fr .this = some fc.name := rfl

theorem fnRefContract_ident (fc : FlatContract) (fr : Frame) (c : Ident) (hl : fr.get? c = none)
    (hv : fc.varIn fr.here c = none) (henv : isEnvObj c = false) (hk : (fc.types.contractKind? c).isSome) :
    fnRefContract fc fr (.ident c) = some c := by
  simp [fnRefContract, hl, hv, henv, hk]

@[simp] theorem selectorArg_bytes4 (env : TypeEnv) (h : Heap) (sb : List UInt8) :
    selectorArg env h (.fixedBytes ⟨3, by decide⟩ sb) = some sb := by
  simp [selectorArg, implicitConv]

theorem selectorMember_of_unique {fc : FlatContract} {fr : Frame} {recv : Expr} {f c : Ident} {s : String}
    (hc : fnRefContract fc fr recv = some c)
    (hs : ((fc.contractFnsNamed c f).filter fun d => d.visibility == some .external || d.visibility == some .pub).filterMap
        (fun d => sigStrOf fc.types f (d.params.map (·.ty))) = [s]) :
    selectorMember fc fr recv f = some (.fixedBytes ⟨3, by decide⟩ (selectorOf s).toList) := by
  simp [selectorMember, hc, hs]

theorem codeSize_eq (evm : EVM.State) (a : EVM.Address) : codeSize evm a = (codeOf evm a).size := rfl

theorem allocBytes_eq (m : Machine) (s : Bool) (d : ByteArray) :
    allocBytes m s d = (.memRef (m.heap.alloc (.bytes s d)).2, { m with heap := (m.heap.alloc (.bytes s d)).1 }) := rfl

theorem memLength_allocBytes (m : Machine) (s : Bool) (d : ByteArray) :
    memLength (allocBytes m s d).2.heap (m.heap.alloc (.bytes s d)).2 = some d.size := by
  simp [allocBytes, memLength]

/-! ## Overloaded events, slices, `bytesN` indexing, `bytesN(bytes)` -/

theorem eventArgs_positional (cands : List EventInfo) (es : List Expr) (h : cands ≠ []) :
    eventArgs cands (.positional es) = some es := by
  cases cands with
  | nil => exact absurd rfl h
  | cons c cs => rfl

/-- An event with a single declaration resolves to it when the arguments fit. -/
theorem resolveEvent_single {env : TypeEnv} {hp : Heap} {ei : EventInfo} {vs : List Value}
    (h : eventFits env hp ei vs = true) : resolveEvent env hp [ei] vs = some ei := by
  simp [resolveEvent, h]

theorem eventFits_addr_addr_u256 (env : TypeEnv) (hp : Heap) (ei : EventInfo) (a b : EVM.Address) (n : ℕ)
    {i1 i2 i3 : Bool} {n1 n2 n3 : Option Ident}
    (hparams : ei.decl.params = [{ ty := .address false, indexed := i1, name := n1 },
      { ty := .address false, indexed := i2, name := n2 }, { ty := u256Ty, indexed := i3, name := n3 }]) :
    eventFits env hp ei [.address a, .address b, u256Val n] = true := by
  simp [eventFits, eventArgFits, hparams, implicitConv]

theorem fixedBytesIndex_ok (bs : List UInt8) (iv : Value) (i : ℕ) (b : UInt8)
    (hi : natOperand iv = some i) (hb : bs[i]? = some b) :
    fixedBytesIndex bs iv = some (.ok (.fixedBytes ⟨0, by decide⟩ [b])) := by
  simp [fixedBytesIndex, hi, hb]

theorem fixedBytesIndex_oob (bs : List UInt8) (iv : Value) (i : ℕ)
    (hi : natOperand iv = some i) (hb : bs.length ≤ i) :
    fixedBytesIndex bs iv = some (.error .outOfBounds) := by
  simp [fixedBytesIndex, hi, List.getElem?_eq_none hb, Op.panic]
  rfl

/-- `d[lo:hi]` on a byte array within bounds. -/
theorem sliceObj_bytes (h : Heap) (obj : ℕ) (s : Bool) (d : ByteArray) (lo hi : Option ℕ)
    (hobj : h.get? obj = some (.bytes s d)) (hab : lo.getD 0 ≤ hi.getD d.size) (hb : hi.getD d.size ≤ d.size) :
    sliceObj h obj lo hi = some (.ok (.memRef (h.alloc (.bytes s (d.extract (lo.getD 0) (hi.getD d.size)))).2,
      (h.alloc (.bytes s (d.extract (lo.getD 0) (hi.getD d.size)))).1)) := by
  simp [sliceObj, hobj, hab, hb]

/-- `d[lo:hi]` on a byte array with bad bounds: empty revert data. -/
theorem sliceObj_bytes_bounds (h : Heap) (obj : ℕ) (s : Bool) (d : ByteArray) (lo hi : Option ℕ)
    (hobj : h.get? obj = some (.bytes s d)) (hbad : ¬ (lo.getD 0 ≤ hi.getD d.size ∧ hi.getD d.size ≤ d.size)) :
    sliceObj h obj lo hi = some (.error ByteArray.empty) := by
  simp only [sliceObj, hobj]
  rw [if_neg hbad]

/-- `bytesN(b)` on a byte array: the first `N` bytes, zero-padded on the right. -/
theorem explicitConv_bytes_fixedBytes (env : TypeEnv) (h : Heap) (id : ℕ) (d : ByteArray) (k : Fin 32)
    (hobj : h.get? id = some (.bytes false d)) :
    explicitConv env h (.memRef id) (.fixedBytes k) =
      some (.ok (.fixedBytes k (d.toList.take (k.val + 1) ++
        List.replicate (k.val + 1 - (d.toList.take (k.val + 1)).length) 0), h)) := by
  simp [explicitConv, hobj]

/-- An address literal (40 hex digits) converts implicitly to `address`. -/
theorem implicitConv_addrLit (env : TypeEnv) (h : Heap) (i : ℕ) (pay : Bool) (hi : i < 2 ^ 160) :
    implicitConv env h (.literal i (some 40)) (.address pay) = some (.address (EVM.address i), h) := by
  have hi' : i < 1461501637330902918203684832716283019655932542976 := by omega
  simp [implicitConv, hi']

/-! ## The value of an assignment expression -/

theorem assignedValue_local {env : TypeEnv} {fr : Frame} {m : Machine} {x : Ident} {l : Local} {v v' : Value}
    {h' : Heap} (hx : fr.get? x = some l) (hval : isValueType env l.ty = true)
    (hc : implicitConv env m.heap v l.ty = some (v', h')) : assignedValue env fr m (.local x) v = v' := by
  simp [assignedValue, lvalueTy, hx, hval, hc]

theorem assignedValue_storage {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef} {ty : Ty}
    {v v' : Value} {h' : Heap} (hval : isValueType env ty = true)
    (hc : implicitConv env m.heap v ty = some (v', h')) : assignedValue env fr m (.storage er ty) v = v' := by
  simp [assignedValue, lvalueTy, hval, hc]

theorem assignedValue_storage_u256 (env : TypeEnv) (fr : Frame) (m : Machine) (er : Solm.EvaledStorageRef) (n : ℕ) :
    assignedValue env fr m (.storage er u256Ty) (u256Val n) = u256Val n :=
  assignedValue_storage rfl (implicitConv_uint env m.heap n)

theorem assignedValue_storage_u256_lit (env : TypeEnv) (fr : Frame) (m : Machine) (er : Solm.EvaledStorageRef)
    (k : ℕ) (hd : Option Nat) (hk : k < 2 ^ 256) :
    assignedValue env fr m (.storage er u256Ty) (.literal k hd) = u256Val k := by
  have h := implicitConv_literal_u256 env m.heap k hd (Int.natCast_nonneg k) (by exact_mod_cast hk)
  rw [Int.toNat_natCast] at h
  exact assignedValue_storage rfl h

theorem assignedValue_storage_s256 (env : TypeEnv) (fr : Frame) (m : Machine) (er : Solm.EvaledStorageRef) (i : Int) :
    assignedValue env fr m (.storage er s256Ty) (s256Val i) = s256Val i :=
  assignedValue_storage (v' := s256Val i) (h' := m.heap) rfl (by simp [implicitConv])

theorem assignedValue_storage_address (env : TypeEnv) (fr : Frame) (m : Machine) (er : Solm.EvaledStorageRef)
    (a : EVM.Address) : assignedValue env fr m (.storage er (.address false)) (.address a) = .address a :=
  assignedValue_storage rfl (implicitConv_address env m.heap a)

/-! ## Builtins and conversions (fixture `Builtins`) -/

theorem explicitConv_address_bytes20 (env : TypeEnv) (h : Heap) (a : EVM.Address) :
    explicitConv env h (.address a) (.fixedBytes ⟨19, by decide⟩) =
      some (.ok (.fixedBytes ⟨19, by decide⟩ (natToBytesBE a.toNat 20), h)) := by
  simp [explicitConv, implicitConv]

theorem explicitConv_bytes20_address (env : TypeEnv) (h : Heap) (bs : List UInt8) (p : Bool) :
    explicitConv env h (.fixedBytes ⟨19, by decide⟩ bs) (.address p) =
      some (.ok (.address (EVM.address (bytesToNatBE bs)), h)) := by
  simp [explicitConv, implicitConv]

@[simp] theorem natValue_u256 (n : ℕ) : natValue (u256Val n) = some n := rfl

@[simp] theorem hashAddr_sha256 : hashAddr "sha256" = some 2 := by decide
@[simp] theorem hashAddr_ripemd160 : hashAddr "ripemd160" = some 3 := by decide

@[simp] theorem concatKind_bytes : concatKind .bytes = some false := rfl
@[simp] theorem concatKind_string : concatKind .string = some true := rfl

/-- The bytes of a memory `bytes` / `string` argument. -/
theorem bytesOf_memBytes {cfg : Config} {m : Machine} {id : ℕ} {s : Bool} {d : ByteArray}
    (hget : m.heap.get? id = some (.bytes s d)) : bytesOf cfg m (.memRef id) = some (.ok d) := by
  simp [bytesOf, hget]

@[simp] theorem bytesOf_strLit (cfg : Config) (m : Machine) (s : ByteArray) :
    bytesOf cfg m (.strLit s) = some (.ok s) := rfl

/-- `name`, `creationCode` and `runtimeCode` are not among the value members of `type(T)`. -/
theorem typeMember_name (fc : FlatContract) (here : Ident) (ty : Ty) : typeMember fc here ty "name" = none := by
  unfold typeMember; split <;> simp_all

theorem typeMember_creationCode (fc : FlatContract) (here : Ident) (ty : Ty) :
    typeMember fc here ty "creationCode" = none := by
  unfold typeMember; split <;> simp_all

theorem typeMember_runtimeCode (fc : FlatContract) (here : Ident) (ty : Ty) :
    typeMember fc here ty "runtimeCode" = none := by
  unfold typeMember; split <;> simp_all

/-! ## User-defined value types (fixture `Udvt`) -/

@[simp] theorem Value.ty?_wrapped (q : Option Ident) (n : Ident) (v : Value) :
    (Value.wrapped q n v).ty? = some (.user q n) := rfl

@[simp] theorem scalarToAbi_wrapped (q : Option Ident) (n : Ident) (v : Value) :
    scalarToAbi (.wrapped q n v) = scalarToAbi v := by
  simp [scalarToAbi]

@[simp] theorem keyOf_wrapped (q : Option Ident) (n : Ident) (v : Value) : keyOf (.wrapped q n v) = keyOf v := by
  simp [keyOf]

/-- A value type converts to itself. -/
theorem implicitConv_wrapped (env : TypeEnv) (h : Heap) (q : Option Ident) (n : Ident) (v : Value) :
    implicitConv env h (.wrapped q n v) (.user q n) = some (.wrapped q n v, h) := by
  simp [implicitConv]

/-- `T.wrap(v)`: `v` converted to the underlying type, tagged with `T`. -/
theorem wrapValue_of_conv {env : TypeEnv} {h h' : Heap} {t : ValueTypeInfo} {v u : Value}
    (hc : implicitConv env h v t.underlying = some (u, h')) (he : u.isElem = true) :
    wrapValue env h t v = some (.wrapped t.qual t.name u) := by
  simp [wrapValue, hc, he]

@[simp] theorem unwrapValue_wrapped (t : ValueTypeInfo) (u : Value) :
    unwrapValue t (.wrapped t.qual t.name u) = some u := by
  simp [unwrapValue]

/-- On an elementary type the scalar reconstruction is `elemOfAbi`. -/
theorem scalarOfAbi_elem (env : TypeEnv) {ty : Ty} (h : (elemTypeOf ty).isSome = true) (sv : Solm.Value) :
    scalarOfAbi env ty sv = elemOfAbi ty sv := by
  cases ty <;> first | (simp [elemTypeOf] at h; done) | (cases sv <;> simp [scalarOfAbi, elemOfAbi])

/-- A value type is rebuilt from the ABI/storage value of its underlying type. -/
theorem scalarOfAbi_valueType {env : TypeEnv} {q : Option Ident} {n : Ident} {t : ValueTypeInfo} {sv : Solm.Value}
    {u : Value} (he : env.enum? q n = none) (ht : env.valueType? q n = some t)
    (hu : elemOfAbi t.underlying sv = some u) : scalarOfAbi env (.user q n) sv = some (.wrapped q n u) := by
  cases sv <;> simp [scalarOfAbi, wrappedOfAbi, he, ht, hu]

/-- The zero value of a value type: the zero of its underlying type, tagged. -/
theorem zeroValue_valueType {env : TypeEnv} {q : Option Ident} {n : Ident} {t : ValueTypeInfo} {z : Value}
    (he : env.enum? q n = none) (ht : env.valueType? q n = some t) (hz : zeroElem t.underlying = some z) :
    zeroValue env (.user q n) = some (.wrapped q n z) := by
  simp [zeroValue, he, ht, hz]

/-- A value type is stored as its underlying type. -/
theorem leafElemType_valueType {env : TypeEnv} {q : Option Ident} {n : Ident} {t : ValueTypeInfo}
    (he : env.enum? q n = none) (ht : env.valueType? q n = some t) :
    leafElemType env (.user q n) = elemTypeOf t.underlying := by
  simp [leafElemType, he, ht]

/-- A value type is ABI-encoded as its underlying type. -/
theorem abiTypeOf_valueType {env : TypeEnv} {q : Option Ident} {n : Ident} {t : ValueTypeInfo}
    (hs : env.struct? q n = none) (he : env.enum? q n = none) (ht : env.valueType? q n = some t) :
    abiTypeOf env (.user q n) = (elemTypeOf t.underlying).map .elem := by
  simp [abiTypeOf, abiTypeOfFuel, hs, he, ht]

theorem storageTypeOf_of_leafElemType {env : TypeEnv} {ty : Ty} {e : ABI.ElemType} (h : leafElemType env ty = some e) :
    storageTypeOf env ty = some (.elem e) := by
  simp only [storageTypeOf, storageTypeOfFuel, h]

theorem leafElemType_of_elemTypeOf {env : TypeEnv} {ty : Ty} {e : ABI.ElemType} (h : elemTypeOf ty = some e) :
    leafElemType env ty = some e := by
  cases ty <;> simp_all [elemTypeOf, leafElemType]

/-- A stored value type by location: the underlying value, tagged. -/
theorem readScalar_valueType_of_leaf {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {q : Option Ident} {n : Ident} {t : ValueTypeInfo} {loc : Solm.StorageLoc} {u : Value} {e : ABI.ElemType}
    (hst : storageTypeOf env (.user q n) = some (.elem e)) (hl : cfg.Leaf er loc)
    (he : env.enum? q n = none) (ht : env.valueType? q n = some t)
    (hu : elemOfAbi t.underlying (Solm.storageLocLoad evm loc) = some u) :
    readScalar cfg env evm er (.user q n) = some (.wrapped q n u) :=
  readScalar_of_leaf hst hl (scalarOfAbi_valueType he ht hu)

/-- A stored value type reads as its underlying type does, tagged (so the `readScalar_*` lemmas of
    the underlying type apply). -/
theorem readScalar_valueType {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {q : Option Ident} {n : Ident} {t : ValueTypeInfo} {u : Value}
    (he : env.enum? q n = none) (ht : env.valueType? q n = some t) (hel : (elemTypeOf t.underlying).isSome = true)
    (hu : readScalar cfg env evm er t.underlying = some u) :
    readScalar cfg env evm er (.user q n) = some (.wrapped q n u) := by
  obtain ⟨e, he'⟩ := Option.isSome_iff_exists.mp hel
  have h1 : storageTypeOf env (.user q n) = some (.elem e) :=
    storageTypeOf_of_leafElemType (by rw [leafElemType_valueType he ht, he'])
  have h2 : storageTypeOf env t.underlying = some (.elem e) :=
    storageTypeOf_of_leafElemType (leafElemType_of_elemTypeOf he')
  unfold readScalar at hu ⊢
  rw [h1, Opt.some_bind]
  rw [h2, Opt.some_bind] at hu
  revert hu
  cases cfg.storageBackend.read er (.elem e) evm with
  | ok sv =>
    intro hu
    change scalarOfAbi env t.underlying sv = some u at hu
    rw [scalarOfAbi_elem env hel] at hu
    exact scalarOfAbi_valueType he ht hu
  | revert => simp
  | error _ => simp

theorem loadIfScalar_valueType {cfg : Config} {env : TypeEnv} {evm : EVM.State} {er : Solm.EvaledStorageRef}
    {q : Option Ident} {n : Ident} {t : ValueTypeInfo} {u : Value}
    (he : env.enum? q n = none) (ht : env.valueType? q n = some t) (hel : (elemTypeOf t.underlying).isSome = true)
    (hu : readScalar cfg env evm er t.underlying = some u) :
    loadIfScalar cfg env evm er (.user q n) = some (.wrapped q n u) := by
  have hv : isValueType env (.user q n) = true := by simp [isValueType, leafElemType_valueType he ht, hel]
  unfold loadIfScalar
  rw [if_pos hv]
  exact readScalar_valueType he ht hel hu

/-- A value type is written as its underlying value. -/
@[simp] theorem writeScalar_wrapped (cfg : Config) (env : TypeEnv) (evm : EVM.State) (er : Solm.EvaledStorageRef) (ty : Ty)
    (q : Option Ident) (n : Ident) (u : Value) :
    writeScalar cfg env evm er ty (.wrapped q n u) = writeScalar cfg env evm er ty u := by
  simp [writeScalar, scalarToAbi]

/-- A value type named in the scope of the running code (`T.wrap`, `T.unwrap`). -/
theorem valueTypeRecv_ident {fc : FlatContract} {fr : Frame} {x : Ident} {t : ValueTypeInfo}
    (hx : fr.get? x = none) (henv : isEnvObj x = false) (hv : fc.varIn fr.here x = none) (hlib : fc.library? x = none)
    (hlin : fc.linearization.contains x = false) (hk : fc.types.contractKind? x = none)
    (ht : fc.types.valueTypeIn fr.here x = some t) : valueTypeRecv fc fr (.ident x) = some t := by
  have hlin' : x ∉ fc.linearization := by simpa using hlin
  simp [valueTypeRecv, hx, henv, hv, hlib, hlin', hk, ht]

/-- `Q.T` for a value type `T` of the unit `Q`. -/
theorem valueTypeRecv_qual {fc : FlatContract} {fr : Frame} {q x : Ident} {t : ValueTypeInfo}
    (hq : unitQual fc fr q = true) (ht : fc.types.valueTypeOf q x = some t) :
    valueTypeRecv fc fr (.member (.ident q) x) = some t := by
  simp [valueTypeRecv, hq, ht]

/-- A local in receiver position names no value type. -/
theorem valueTypeRecv_local {fc : FlatContract} {fr : Frame} {x : Ident} {l : Local} (hx : fr.get? x = some l) :
    valueTypeRecv fc fr (.ident x) = none := by
  simp [valueTypeRecv, hx]

/-- A state variable in receiver position names no value type. -/
theorem valueTypeRecv_var {fc : FlatContract} {fr : Frame} {x : Ident} {v : FlatVar} (hv : fc.varIn fr.here x = some v) :
    valueTypeRecv fc fr (.ident x) = none := by
  simp [valueTypeRecv, hv]

end Solidity
