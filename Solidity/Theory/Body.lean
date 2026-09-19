import Solidity.Semantics
import EVMReasoning.Storage

/-!
# Derivation helpers for function bodies

Small rewriting lemmas used when building `EvalExpr`/`ExecStmt`/`CallFn` derivations by hand:
frame lookups, scalar conversions, zero values, and full-word (`uint256`) storage reads and
writes through a layout.  `storageLocLoad`/`scalarOfSolm` are eliminated by `rw`, never by
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
  simp [toAbi, scalarToSolm]

@[simp] theorem toAbi_bool (h : Heap) (fuel : Nat) (b : Bool) :
    toAbi h (fuel + 1) (.bool b) = some (.bool b) := by
  simp [toAbi, scalarToSolm]

@[simp] theorem toAbi_address (h : Heap) (fuel : Nat) (a : EVM.Address) :
    toAbi h (fuel + 1) (.address a) = some (.address a) := by
  simp [toAbi, scalarToSolm]

theorem scalarOfSolm_u256 (env : TypeEnv) (w : UInt256) :
    scalarOfSolm env u256Ty (.int (Int.ofNat w.toNat)) = some (u256Val w.toNat) := by
  have h : w.toNat < 2 ^ 256 := w.val.isLt
  simp [scalarOfSolm]
  omega

theorem scalarOfSolm_u256_nat (env : TypeEnv) (n : Nat) (hn : n < UInt256.size) :
    scalarOfSolm env u256Ty (.int (Int.ofNat n)) = some (u256Val n) := by
  simp [scalarOfSolm]
  exact hn

@[simp] theorem scalarOfSolm_address (env : TypeEnv) (a : EVM.Address) :
    scalarOfSolm env (.address false) (.address a) = some (.address a) := by
  simp [scalarOfSolm]

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
  rw [h, Opt.some_bind, storageLocLoad_uint256, scalarOfSolm_u256]

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
  show (some (Solm.Value.int (Int.ofNat w.toNat)) >>= _) = _
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
  simp [binop, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, cmpInt]

theorem binop_sub_u256_ok (a b : Nat) (ha : a < 2 ^ 256) (h : b ≤ a) :
    binop true .sub (u256Val a) (u256Val b) = some (.ok (u256Val (a - b))) := by
  have ht : ((a : Int) - b).toNat = a - b := by omega
  simp [binop, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, sub, settle,
    IntTy.inRange, IntTy.min, IntTy.max, mkInt]
  rw [if_pos (by omega)]
  simp [ht]

theorem binop_sub_u256_underflow (a b : Nat) (h : a < b) :
    binop true .sub (u256Val a) (u256Val b) = some (.error .overflow) := by
  simp [binop, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, sub, settle,
    IntTy.inRange, IntTy.min, IntTy.max]
  rw [if_neg (by omega)]
  rfl

theorem binop_add_u256_ok (a b : Nat) (h : a + b < 2 ^ 256) :
    binop true .add (u256Val a) (u256Val b) = some (.ok (u256Val (a + b))) := by
  have ht : ((a : Int) + b).toNat = a + b := by omega
  simp [binop, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, add, settle,
    IntTy.inRange, IntTy.min, IntTy.max, mkInt]
  rw [if_pos (by omega)]
  simp [ht]

theorem binop_add_u256_overflow (a b : Nat) (h : 2 ^ 256 ≤ a + b) :
    binop true .add (u256Val a) (u256Val b) = some (.error .overflow) := by
  simp [binop, toBool, addrNat, unifyInts, Value.int?, commonIntType, implicitIntConv, isCmp, add, settle,
    IntTy.inRange, IntTy.min, IntTy.max]
  rw [if_neg (by omega)]
  rfl

/-! ## Events -/

theorem abiArgs_addr_addr_u256 (cfg : Config) (env : TypeEnv) (m : Machine) (a b : EVM.Address) (n : Nat) :
    abiArgs cfg env m [.address false, .address false, u256Ty] [.address a, .address b, u256Val n] =
      some (.ok ([.address a, .address b, .int n], m)) := by
  simp [abiArgs, coerce, fuelDefault]

/-- `Panic` payloads. -/
theorem Panic.data_overflow : Panic.data .overflow = panicData 0x11 := rfl

end Solidity
