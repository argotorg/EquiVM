import Solidity.Theory.Trace

/-!
# Derivation builders for function bodies

One lemma per statement shape a modifier-free body is made of: `require` with a string message,
compound `+=`/`-=` on a `uint256` storage slot (checked, with the `Panic(0x11)` cases), reads and
lvalues of `mapping(address => uint256)` state variables (one and two levels), `emit` of an
`(address indexed, address indexed, uint256)` event, `return` of a scalar, and the packaging of a
body run into `CallFn`.  Each builder takes the sub-derivations of its operands and the storage
layout of the slot it touches, and states the resulting frame and machine explicitly.
-/

namespace Solidity

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Trace

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

/-- The frame a modifier-free body runs in. -/
def bodyFrame (fr : Frame) (b : Block) : Frame := { fr with chain := [], body := b }

/-! ## Calls -/

/-- A function without modifiers whose body finishes (`return` or fall-through). -/
theorem CallFn.plain {fr fr0 fr2 : Frame} {m m0 m2 : Machine} {fn : FnDef} {args : List Value} {body : Block}
    {r : ExecResult} {rets : List Value}
    (henter : enterFn cfg fc.types fn.declaredIn fn.decl args m = some (.ok (fr0, m0)))
    (hbody : fn.decl.body = some body) (hmods : fn.decl.modifiers = [])
    (hrun : ExecBlock cfg o fc (bodyFrame fr0 body) m0 body r)
    (hfin : finished r = some (fr2, m2)) (hrets : retVals fr2 = some rets) :
    CallFn cfg o fc fr m fn args (.ok rets m2) := by
  refine CallFn.ok henter hbody ?_ hfin hrets
  rw [hmods]
  exact ExecChain.body hrun

/-- A function without modifiers whose body reverts. -/
theorem CallFn.plainRevert {fr fr0 : Frame} {m m0 : Machine} {fn : FnDef} {args : List Value} {body : Block}
    {d : ByteArray}
    (henter : enterFn cfg fc.types fn.declaredIn fn.decl args m = some (.ok (fr0, m0)))
    (hbody : fn.decl.body = some body) (hmods : fn.decl.modifiers = [])
    (hrun : ExecBlock cfg o fc (bodyFrame fr0 body) m0 body (.reverted d)) :
    CallFn cfg o fc fr m fn args (.reverted d) := by
  refine CallFn.reverted henter hbody ?_
  rw [hmods]
  exact ExecChain.body hrun

/-! ## Expressions -/

theorem EvalExpr.msgSender {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.member (.ident "msg") "sender") (.ok (.address m.evm.executionEnv.source) fr m) :=
  EvalExpr.envMember rfl (envMember_sender m)

theorem EvalExpr.boolLit {fr : Frame} {m : Machine} (b : Bool) :
    EvalExpr cfg o fc fr m (.lit (.bool b)) (.ok (.bool b) fr m) :=
  EvalExpr.lit rfl

theorem EvalLValue.not_tuple {fr : Frame} {m : Machine} {e : Expr} {r : Res LValue}
    (h : EvalLValue cfg o fc fr m e r) : isTupleExpr e = false := by
  cases h <;> rfl

/-- `x[k]` for a state variable `x : mapping(address => uint256)`, read. -/
theorem EvalExpr.mappingAddrU256 {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {k : Expr}
    {a : EVM.Address} {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.address false) u256Ty)
    (hk : EvalExpr cfg o fc fr m k (.ok (.address a) fr m))
    (hl : cfg.storage.layout (keyRef ⟨v.key, []⟩ (.address a)) m.evm = some (uint256Loc slot)) :
    EvalExpr cfg o fc fr m (.index (.ident x) k) (.ok (u256Val (loadU256 m slot).toNat) fr m) := by
  have hload : loadIfScalar cfg fc.types m.evm ⟨v.key, []⟩ v.ty =
      some (.storageRef ⟨v.key, []⟩ (.mapping (.address false) u256Ty)) := by
    rw [hty]; exact loadIfScalar_mapping ..
  exact EvalExpr.indexStorage (EvalExpr.stateVar hx hv hmut hload) hk (storageIndex_mapping_address ..)
    (loadIfScalar_u256 hl)

/-- `x[k]` for a state variable `x : mapping(address => uint256)`, as an lvalue. -/
theorem EvalLValue.mappingAddr {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {k : Expr}
    {a : EVM.Address}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.address false) u256Ty)
    (hk : EvalExpr cfg o fc fr m k (.ok (.address a) fr m)) :
    EvalLValue cfg o fc fr m (.index (.ident x) k) (.ok (.storage (keyRef ⟨v.key, []⟩ (.address a)) u256Ty) fr m) := by
  have hload : loadIfScalar cfg fc.types m.evm ⟨v.key, []⟩ v.ty =
      some (.storageRef ⟨v.key, []⟩ (.mapping (.address false) u256Ty)) := by
    rw [hty]; exact loadIfScalar_mapping ..
  exact EvalLValue.indexStorage (EvalExpr.stateVar hx hv hmut hload) hk (storageIndex_mapping_address ..)

/-- `x[k1][k2]` for a state variable `x : mapping(address => mapping(address => uint256))`, read. -/
theorem EvalExpr.mapping2AddrU256 {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {k1 k2 : Expr}
    {a b : EVM.Address} {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.address false) (.mapping (.address false) u256Ty))
    (hk1 : EvalExpr cfg o fc fr m k1 (.ok (.address a) fr m))
    (hk2 : EvalExpr cfg o fc fr m k2 (.ok (.address b) fr m))
    (hl : cfg.storage.layout (keyRef (keyRef ⟨v.key, []⟩ (.address a)) (.address b)) m.evm =
      some (uint256Loc slot)) :
    EvalExpr cfg o fc fr m (.index (.index (.ident x) k1) k2) (.ok (u256Val (loadU256 m slot).toNat) fr m) := by
  have hload : loadIfScalar cfg fc.types m.evm ⟨v.key, []⟩ v.ty =
      some (.storageRef ⟨v.key, []⟩ (.mapping (.address false) (.mapping (.address false) u256Ty))) := by
    rw [hty]; exact loadIfScalar_mapping ..
  have hinner : EvalExpr cfg o fc fr m (.index (.ident x) k1)
      (.ok (.storageRef (keyRef ⟨v.key, []⟩ (.address a)) (.mapping (.address false) u256Ty)) fr m) :=
    EvalExpr.indexStorage (EvalExpr.stateVar hx hv hmut hload) hk1 (storageIndex_mapping_address ..)
      (loadIfScalar_mapping ..)
  exact EvalExpr.indexStorage hinner hk2 (storageIndex_mapping_address ..) (loadIfScalar_u256 hl)

/-- `x[k1][k2]` for a state variable `x : mapping(address => mapping(address => uint256))`, as an lvalue. -/
theorem EvalLValue.mapping2Addr {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {k1 k2 : Expr}
    {a b : EVM.Address}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.address false) (.mapping (.address false) u256Ty))
    (hk1 : EvalExpr cfg o fc fr m k1 (.ok (.address a) fr m))
    (hk2 : EvalExpr cfg o fc fr m k2 (.ok (.address b) fr m)) :
    EvalLValue cfg o fc fr m (.index (.index (.ident x) k1) k2)
      (.ok (.storage (keyRef (keyRef ⟨v.key, []⟩ (.address a)) (.address b)) u256Ty) fr m) := by
  have hload : loadIfScalar cfg fc.types m.evm ⟨v.key, []⟩ v.ty =
      some (.storageRef ⟨v.key, []⟩ (.mapping (.address false) (.mapping (.address false) u256Ty))) := by
    rw [hty]; exact loadIfScalar_mapping ..
  have hinner : EvalExpr cfg o fc fr m (.index (.ident x) k1)
      (.ok (.storageRef (keyRef ⟨v.key, []⟩ (.address a)) (.mapping (.address false) u256Ty)) fr m) :=
    EvalExpr.indexStorage (EvalExpr.stateVar hx hv hmut hload) hk1 (storageIndex_mapping_address ..)
      (loadIfScalar_mapping ..)
  exact EvalLValue.indexStorage hinner hk2 (storageIndex_mapping_address ..)

/-! ## Statements -/

theorem ExecStmt.requireTrue {fr fr1 : Frame} {m m1 : Machine} {c : Expr} {rest : List Expr}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1)) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident "require") [] (.positional (c :: rest)))) (.normal fr1 m1) :=
  ExecStmt.exprStmt (EvalExpr.requireTrue hc)

theorem ExecStmt.requireRevert {fr fr1 : Frame} {m m1 : Machine} {c : Expr}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool false) fr1 m1)) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident "require") [] (.positional [c]))) (.reverted ByteArray.empty) :=
  ExecStmt.exprStmtRevert (EvalExpr.requireFalse hc)

/-- `require(c, "msg")` with `c` false: `Error("msg")`. -/
theorem ExecStmt.requireMsgRevert {fr fr1 : Frame} {m m1 : Machine} {c : Expr} {s : String}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool false) fr1 m1)) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident "require") [] (.positional [c, .lit (.str s)])))
      (.reverted (errorStringData s.toUTF8)) :=
  ExecStmt.exprStmtRevert (EvalExpr.requireMsg rfl hc (EvalExpr.lit rfl) rfl)

/-- `lhs -= rhs` on a `uint256` storage slot, no underflow. -/
theorem ExecStmt.subAssignU256 {fr : Frame} {m : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot b : UInt256}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val b.toNat) fr m))
    (hlv : EvalLValue cfg o fc fr m lhs (.ok (.storage er u256Ty) fr m))
    (hl : cfg.storage.layout er m.evm = some (uint256Loc slot))
    (hunch : fr.unchecked = false) (hle : b.toNat ≤ (loadU256 m slot).toNat) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .sub lhs rhs))
      (.normal fr (storeU256 m slot (UInt256.ofNat ((loadU256 m slot).toNat - b.toNat)))) := by
  have hb : (loadU256 m slot).toNat < UInt256.size := (loadU256 m slot).val.isLt
  have hassign := assign_storage_u256 (env := fc.types) (fr := fr) hl
    (UInt256.ofNat ((loadU256 m slot).toNat - b.toNat))
  rw [ulit_toNat' _ (by omega)] at hassign
  refine ExecStmt.exprStmt (EvalExpr.assignCompound (cur := u256Val (loadU256 m slot).toNat)
    (r := u256Val ((loadU256 m slot).toNat - b.toNat)) hlv.not_tuple (by decide) hrhs hlv
    (readLValue_storage_u256 hl) ?_ hassign)
  rw [hunch]
  exact binop_sub_u256_ok _ _ hb hle

/-- `lhs -= rhs` on a `uint256` storage slot, underflow: `Panic(0x11)`. -/
theorem ExecStmt.subAssignU256Underflow {fr : Frame} {m : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot b : UInt256}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val b.toNat) fr m))
    (hlv : EvalLValue cfg o fc fr m lhs (.ok (.storage er u256Ty) fr m))
    (hl : cfg.storage.layout er m.evm = some (uint256Loc slot))
    (hunch : fr.unchecked = false) (hlt : (loadU256 m slot).toNat < b.toNat) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .sub lhs rhs)) (.reverted (panicData 0x11)) := by
  refine ExecStmt.exprStmtRevert (EvalExpr.assignCompoundPanic (cur := u256Val (loadU256 m slot).toNat)
    (p := .overflow) hlv.not_tuple (by decide) hrhs hlv (readLValue_storage_u256 hl) ?_)
  rw [hunch]
  exact binop_sub_u256_underflow _ _ hlt

/-- `lhs += rhs` on a `uint256` storage slot, no overflow. -/
theorem ExecStmt.addAssignU256 {fr : Frame} {m : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot b : UInt256}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val b.toNat) fr m))
    (hlv : EvalLValue cfg o fc fr m lhs (.ok (.storage er u256Ty) fr m))
    (hl : cfg.storage.layout er m.evm = some (uint256Loc slot))
    (hunch : fr.unchecked = false) (hfit : (loadU256 m slot).toNat + b.toNat < UInt256.size) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .add lhs rhs))
      (.normal fr (storeU256 m slot (UInt256.ofNat ((loadU256 m slot).toNat + b.toNat)))) := by
  have hassign := assign_storage_u256 (env := fc.types) (fr := fr) hl
    (UInt256.ofNat ((loadU256 m slot).toNat + b.toNat))
  rw [ulit_toNat' _ hfit] at hassign
  refine ExecStmt.exprStmt (EvalExpr.assignCompound (cur := u256Val (loadU256 m slot).toNat)
    (r := u256Val ((loadU256 m slot).toNat + b.toNat)) hlv.not_tuple (by decide) hrhs hlv
    (readLValue_storage_u256 hl) ?_ hassign)
  rw [hunch]
  exact binop_add_u256_ok _ _ hfit

/-- `lhs += rhs` on a `uint256` storage slot, overflow: `Panic(0x11)`. -/
theorem ExecStmt.addAssignU256Overflow {fr : Frame} {m : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot b : UInt256}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val b.toNat) fr m))
    (hlv : EvalLValue cfg o fc fr m lhs (.ok (.storage er u256Ty) fr m))
    (hl : cfg.storage.layout er m.evm = some (uint256Loc slot))
    (hunch : fr.unchecked = false) (hover : UInt256.size ≤ (loadU256 m slot).toNat + b.toNat) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .add lhs rhs)) (.reverted (panicData 0x11)) := by
  refine ExecStmt.exprStmtRevert (EvalExpr.assignCompoundPanic (cur := u256Val (loadU256 m slot).toNat)
    (p := .overflow) hlv.not_tuple (by decide) hrhs hlv (readLValue_storage_u256 hl) ?_)
  rw [hunch]
  exact binop_add_u256_overflow _ _ hover

/-- `emit E(a, b, n)` for `event E(address indexed, address indexed, uint256)`. -/
theorem ExecStmt.emitAddrAddrU256 {fr fr1 : Frame} {m m1 : Machine} {ev : Ident} {ei : EventInfo} {es : List Expr}
    {a b : EVM.Address} {n : UInt256} {n1 n2 n3 : Option Ident}
    (hev : fc.event? ev = some ei)
    (hparams : ei.decl.params = [{ ty := .address false, indexed := true, name := n1 },
      { ty := .address false, indexed := true, name := n2 }, { ty := u256Ty, indexed := false, name := n3 }])
    (htys : ei.sig.paramTypes = [.elem .address, .elem .address, .elem (.int (.uint ⟨256, by decide⟩))])
    (hanon : ei.decl.anonymous = false)
    (hargs : EvalExprs cfg o fc fr m es (.ok [.address a, .address b, u256Val n.toNat] fr1 m1)) :
    ExecStmt cfg o fc fr m (.emit (.ident ev) (.positional es))
      (.normal fr1 (m1.pushLog
        { address := m1.this
          topics := #[hashWord ei.sigStr.toUTF8, UInt256.ofNat a.toNat, UInt256.ofNat b.toNat]
          data := UInt256.toByteArray n })) := by
  have habi : abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) [.address a, .address b, u256Val n.toNat] =
      some (.ok ([.address a, .address b, .int n.toNat], m1)) := by
    rw [hparams]; exact abiArgs_addr_addr_u256 ..
  have hle := mkLogEntry_addr_addr_u256 m1.this ei a b n.toNat hparams htys hanon n.val.isLt
  rw [u256_ofNat_toNat] at hle
  exact ExecStmt.emit hev rfl hargs habi hle

/-- `return e` for a `bool` return slot `r` (its current binding `l` is given explicitly). -/
theorem ExecStmt.returnBool {fr fr1 : Frame} {m m1 : Machine} {r : Ident} {e : Expr} {b : Bool} (l : Local)
    (hret : fr.retVars = [r]) (he : EvalExpr cfg o fc fr m e (.ok (.bool b) fr1 m1))
    (hr : fr1.get? r = some l) (hty : l.ty = .bool) :
    ExecStmt cfg o fc fr m (.return (some e)) (.returned (fr1.setVal r (.bool b)) m1) := by
  refine ExecStmt.returnSingle hret he ?_
  simp [assign, coerce, hr, hty]
  try rfl

/-- `return e` for a `uint256` return slot. -/
theorem ExecStmt.returnU256 {fr fr1 : Frame} {m m1 : Machine} {r : Ident} {e : Expr} {n : ℕ} (l : Local)
    (hret : fr.retVars = [r]) (he : EvalExpr cfg o fc fr m e (.ok (u256Val n) fr1 m1))
    (hr : fr1.get? r = some l) (hty : l.ty = u256Ty) :
    ExecStmt cfg o fc fr m (.return (some e)) (.returned (fr1.setVal r (u256Val n)) m1) := by
  refine ExecStmt.returnSingle hret he ?_
  simp [assign, coerce, hr, hty]
  try rfl

/-- `return e` for an `address` return slot. -/
theorem ExecStmt.returnAddress {fr fr1 : Frame} {m m1 : Machine} {r : Ident} {e : Expr} {a : EVM.Address} (l : Local)
    (hret : fr.retVars = [r]) (he : EvalExpr cfg o fc fr m e (.ok (.address a) fr1 m1))
    (hr : fr1.get? r = some l) (hty : l.ty = .address false) :
    ExecStmt cfg o fc fr m (.return (some e)) (.returned (fr1.setVal r (.address a)) m1) := by
  refine ExecStmt.returnSingle hret he ?_
  simp [assign, coerce, hr, hty]
  try rfl

/-! ## Internal calls -/

@[simp] theorem retValue_single (v : Value) : retValue [v] = v := rfl
@[simp] theorem retValue_nil : retValue [] = .unit := rfl

/-- A call of a same-contract function with positional arguments that returns. -/
theorem EvalExpr.internalCallPlain {fr fr1 : Frame} {m m1 m2 : Machine} {f : Ident} {es : List Expr}
    {vs : List Value} {fn : FnDef} {rets : List Value}
    (hf : isBuiltinFn f = false) (hx : fr.get? f = none) (hne : fc.fnsNamed f ≠ [])
    (hargs : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (hres : resolveOverload fc.types m1.heap fc (fc.fnsNamed f) vs = some fn)
    (hcall : CallFn cfg o fc fr1 m1 fn vs (.ok rets m2)) :
    EvalExpr cfg o fc fr m (.call (.ident f) [] (.positional es)) (.ok (retValue rets) fr1 m2) :=
  EvalExpr.internalCall hf hx hne rfl hargs hres hcall

theorem EvalExpr.internalCallPlainRevert {fr fr1 : Frame} {m m1 : Machine} {f : Ident} {es : List Expr}
    {vs : List Value} {fn : FnDef} {d : ByteArray}
    (hf : isBuiltinFn f = false) (hx : fr.get? f = none) (hne : fc.fnsNamed f ≠ [])
    (hargs : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (hres : resolveOverload fc.types m1.heap fc (fc.fnsNamed f) vs = some fn)
    (hcall : CallFn cfg o fc fr1 m1 fn vs (.reverted d)) :
    EvalExpr cfg o fc fr m (.call (.ident f) [] (.positional es)) (.reverted d) :=
  EvalExpr.internalCallRevert hf hx hne rfl hargs hres hcall

theorem ExecStmt.internalCallStmt {fr fr1 : Frame} {m m1 m2 : Machine} {f : Ident} {es : List Expr}
    {vs : List Value} {fn : FnDef} {rets : List Value}
    (hf : isBuiltinFn f = false) (hx : fr.get? f = none) (hne : fc.fnsNamed f ≠ [])
    (hargs : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (hres : resolveOverload fc.types m1.heap fc (fc.fnsNamed f) vs = some fn)
    (hcall : CallFn cfg o fc fr1 m1 fn vs (.ok rets m2)) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident f) [] (.positional es))) (.normal fr1 m2) :=
  ExecStmt.exprStmt (EvalExpr.internalCallPlain hf hx hne hargs hres hcall)

/-! ## Local variables and plain assignment -/

theorem ExecStmt.varDeclU256 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {e : Expr} {n : ℕ} {loc : Option DataLoc}
    (he : EvalExpr cfg o fc fr m e (.ok (u256Val n) fr1 m1)) :
    ExecStmt cfg o fc fr m (.varDecl u256Ty loc x (some e)) (.normal (fr1.bind x u256Ty loc (u256Val n)) m1) := by
  refine ExecStmt.varDecl he ?_
  simp [declare, coerce]
  try rfl

theorem ExecStmt.varDeclBool {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {e : Expr} {b : Bool} {loc : Option DataLoc}
    (he : EvalExpr cfg o fc fr m e (.ok (.bool b) fr1 m1)) :
    ExecStmt cfg o fc fr m (.varDecl .bool loc x (some e)) (.normal (fr1.bind x .bool loc (.bool b)) m1) := by
  refine ExecStmt.varDecl he ?_
  simp [declare, coerce]
  try rfl

theorem ExecStmt.varDeclAddress {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {e : Expr} {a : EVM.Address}
    {loc : Option DataLoc}
    (he : EvalExpr cfg o fc fr m e (.ok (.address a) fr1 m1)) :
    ExecStmt cfg o fc fr m (.varDecl (.address false) loc x (some e))
      (.normal (fr1.bind x (.address false) loc (.address a)) m1) := by
  refine ExecStmt.varDecl he ?_
  simp [declare, coerce]
  try rfl

/-- `uint256 x;` -/
theorem ExecStmt.varDeclNoneU256 {fr : Frame} {m : Machine} {x : Ident} {loc : Option DataLoc}
    (hloc : (loc == some DataLoc.storage) = false) :
    ExecStmt cfg o fc fr m (.varDecl u256Ty loc x none) (.normal (fr.bind x u256Ty loc (u256Val 0)) m) := by
  refine ExecStmt.varDeclNone ?_
  simp [declare, hloc, fuelDefault]
  try rfl

/-- `x = rhs` for a `uint256` local `x` (its current binding `l` is given explicitly). -/
theorem EvalExpr.assignLocalU256 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {rhs : Expr} {n : ℕ} (l : Local)
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val n) fr1 m1))
    (hx : fr1.get? x = some l) (hty : l.ty = u256Ty) :
    EvalExpr cfg o fc fr m (.assign .assign (.ident x) rhs) (.ok (u256Val n) (fr1.setVal x (u256Val n)) m1) := by
  refine EvalExpr.assignPlain rfl hrhs (EvalLValue.local hx) ?_
  simp [assign, coerce, hx, hty]
  try rfl

theorem ExecStmt.assignLocalU256 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {rhs : Expr} {n : ℕ} (l : Local)
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val n) fr1 m1))
    (hx : fr1.get? x = some l) (hty : l.ty = u256Ty) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.ident x) rhs)) (.normal (fr1.setVal x (u256Val n)) m1) :=
  ExecStmt.exprStmt (EvalExpr.assignLocalU256 l hrhs hx hty)

/-- `lhs = rhs` into a `uint256` storage slot. -/
theorem EvalExpr.assignStorageU256 {fr fr1 : Frame} {m m1 : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot w : UInt256}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val w.toNat) fr1 m1))
    (hlv : EvalLValue cfg o fc fr1 m1 lhs (.ok (.storage er u256Ty) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (uint256Loc slot)) :
    EvalExpr cfg o fc fr m (.assign .assign lhs rhs) (.ok (u256Val w.toNat) fr1 (storeU256 m1 slot w)) :=
  EvalExpr.assignPlain hlv.not_tuple hrhs hlv (assign_storage_u256 hl w)

theorem ExecStmt.assignStorageU256 {fr fr1 : Frame} {m m1 : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot w : UInt256}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val w.toNat) fr1 m1))
    (hlv : EvalLValue cfg o fc fr1 m1 lhs (.ok (.storage er u256Ty) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (uint256Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign lhs rhs)) (.normal fr1 (storeU256 m1 slot w)) :=
  ExecStmt.exprStmt (EvalExpr.assignStorageU256 hrhs hlv hl)

/-! ## Operators on `uint256`, `bool` and `address`

The right operand is evaluated first (legacy solc order), then the left one. -/

theorem EvalExpr.geU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .ge a b) (.ok (.bool (decide (y ≤ x))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_ge_u256 ..)

theorem EvalExpr.gtU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .gt a b) (.ok (.bool (decide (y < x))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_gt_u256 ..)

theorem EvalExpr.leU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .le a b) (.ok (.bool (decide (x ≤ y))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_le_u256 ..)

theorem EvalExpr.ltU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .lt a b) (.ok (.bool (decide (x < y))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_lt_u256 ..)

theorem EvalExpr.eqU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .eq a b) (.ok (.bool (decide (x = y))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_eq_u256 ..)

theorem EvalExpr.neU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .ne a b) (.ok (.bool (!decide (x = y))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_ne_u256 ..)

theorem EvalExpr.eqAddress {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : EVM.Address}
    (hb : EvalExpr cfg o fc fr m b (.ok (.address y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.address x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .eq a b) (.ok (.bool (decide (x.toNat = y.toNat))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_eq_address ..)

theorem EvalExpr.neAddress {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : EVM.Address}
    (hb : EvalExpr cfg o fc fr m b (.ok (.address y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.address x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .ne a b) (.ok (.bool (decide (x.toNat ≠ y.toNat))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_ne_address ..)

theorem EvalExpr.notBool {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {b : Bool}
    (he : EvalExpr cfg o fc fr m e (.ok (.bool b) fr1 m1)) :
    EvalExpr cfg o fc fr m (.unary .not e) (.ok (.bool (!b)) fr1 m1) :=
  EvalExpr.unary he (unop_not ..) (by decide) (by decide)

theorem EvalExpr.addU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hfit : x + y < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .add a b) (.ok (u256Val (x + y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_add_u256_ok _ _ hfit)

theorem EvalExpr.addU256Overflow {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hover : 2 ^ 256 ≤ x + y) :
    EvalExpr cfg o fc fr m (.binary .add a b) (.reverted (panicData 0x11)) :=
  EvalExpr.binaryPanic (p := .overflow) (by decide) (by decide) hb ha
    (by rw [hunch]; exact binop_add_u256_overflow _ _ hover)

theorem EvalExpr.subU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hx : x < 2 ^ 256) (hle : y ≤ x) :
    EvalExpr cfg o fc fr m (.binary .sub a b) (.ok (u256Val (x - y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_sub_u256_ok _ _ hx hle)

theorem EvalExpr.subU256Underflow {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hlt : x < y) :
    EvalExpr cfg o fc fr m (.binary .sub a b) (.reverted (panicData 0x11)) :=
  EvalExpr.binaryPanic (p := .overflow) (by decide) (by decide) hb ha
    (by rw [hunch]; exact binop_sub_u256_underflow _ _ hlt)

theorem EvalExpr.mulU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hfit : x * y < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .mul a b) (.ok (u256Val (x * y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_mul_u256_ok _ _ hfit)

theorem EvalExpr.mulU256Overflow {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hover : 2 ^ 256 ≤ x * y) :
    EvalExpr cfg o fc fr m (.binary .mul a b) (.reverted (panicData 0x11)) :=
  EvalExpr.binaryPanic (p := .overflow) (by decide) (by decide) hb ha
    (by rw [hunch]; exact binop_mul_u256_overflow _ _ hover)

theorem EvalExpr.divU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hx : x < 2 ^ 256) (hy : y ≠ 0) :
    EvalExpr cfg o fc fr m (.binary .div a b) (.ok (u256Val (x / y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_div_u256 _ _ _ hx hy)

theorem EvalExpr.divU256Zero {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val 0) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .div a b) (.reverted (panicData 0x12)) :=
  EvalExpr.binaryPanic (p := .divByZero) (by decide) (by decide) hb ha (binop_div_u256_zero ..)

theorem EvalExpr.modU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) (hy : y ≠ 0) :
    EvalExpr cfg o fc fr m (.binary .mod a b) (.ok (u256Val (x % y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_mod_u256 _ _ _ hy)

theorem EvalExpr.modU256Zero {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val 0) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .mod a b) (.reverted (panicData 0x12)) :=
  EvalExpr.binaryPanic (p := .divByZero) (by decide) (by decide) hb ha (binop_mod_u256_zero ..)

theorem EvalExpr.addU256Unchecked {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) (hunch : fr2.unchecked = true) :
    EvalExpr cfg o fc fr m (.binary .add a b) (.ok (u256Val ((x + y) % 2 ^ 256)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_add_u256_unchecked ..)

theorem EvalExpr.mulU256Unchecked {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) (hunch : fr2.unchecked = true) :
    EvalExpr cfg o fc fr m (.binary .mul a b) (.ok (u256Val ((x * y) % 2 ^ 256)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_mul_u256_unchecked ..)

theorem EvalExpr.subU256Unchecked {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1))
    (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2)) (hunch : fr2.unchecked = true) :
    EvalExpr cfg o fc fr m (.binary .sub a b) (.ok (u256Val ((((x : Int) - y) % 2 ^ 256).toNat)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_sub_u256_unchecked ..)

/-! ## External calls -/

/-- `recv.f(args)` on a contract-typed receiver, no call options, call made and return values decoded. -/
theorem EvalExpr.externalCallPlain {fr fr1 fr4 : Frame} {m m1 m4 m5 m6 m7 : Machine} {recv : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {rets : List Value}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.contract c a) fr1 m1))
    (hargs : EvalExprs cfg o fc fr1 m1 es (.ok vs fr4 m4))
    (hres : resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d)
    (hsig : externalSig fc.types d = some (sigStr, ptys, rtys))
    (habi : abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs = some (.ok (svs, m5)))
    (henc : ABI.encodeABIValues? ptys svs = some bs)
    (hcode : d.returns = [] → codeSize m4.evm a ≠ 0)
    (hcall : callViaEVM o m5 a 0 (selectorOf sigStr ++ bs.toByteArray)
      (m5.evm.executionEnv.perm && d.mutability != .view && d.mutability != .pure) (calleeGas o m5 none 0)
      (true, m6, out))
    (hdec : decodeRets cfg fc.types m6 d.returns rtys out = some (rets, m7)) :
    EvalExpr cfg o fc fr m (.call (.member recv f) [] (.positional es)) (.ok (retValue rets) fr4 m7) :=
  EvalExpr.externalCall hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall hdec

/-- `recv.f(args)`, call made and the callee reverted: the revert data is bubbled up. -/
theorem EvalExpr.externalCallPlainFailed {fr fr1 fr4 : Frame} {m m1 m4 m5 m6 : Machine} {recv : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.contract c a) fr1 m1))
    (hargs : EvalExprs cfg o fc fr1 m1 es (.ok vs fr4 m4))
    (hres : resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d)
    (hsig : externalSig fc.types d = some (sigStr, ptys, rtys))
    (habi : abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs = some (.ok (svs, m5)))
    (henc : ABI.encodeABIValues? ptys svs = some bs)
    (hcode : d.returns = [] → codeSize m4.evm a ≠ 0)
    (hcall : callViaEVM o m5 a 0 (selectorOf sigStr ++ bs.toByteArray)
      (m5.evm.executionEnv.perm && d.mutability != .view && d.mutability != .pure) (calleeGas o m5 none 0)
      (false, m6, out)) :
    EvalExpr cfg o fc fr m (.call (.member recv f) [] (.positional es)) (.reverted out) :=
  EvalExpr.externalCallFailed hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall

/-! ## Loops

A loop is run by a variant `v` on an abstract state `a` carrying the frame and machine: `P 0 a`
means the condition is about to fail, `P (v + 1) a` that one more iteration runs.  Conditions and
post-expressions here leave the frame and machine unchanged. -/

theorem ExecLoop.variant {α : Type} (P : ℕ → α → Prop) (fr : α → Frame) (m : α → Machine)
    {c : Expr} {post : Option Expr} {body : Stmt}
    (hfalse : ∀ a, P 0 a → EvalExpr cfg o fc (fr a) (m a) c (.ok (.bool false) (fr a) (m a)))
    (hstep : ∀ v a, P (v + 1) a →
      EvalExpr cfg o fc (fr a) (m a) c (.ok (.bool true) (fr a) (m a)) ∧
      ∃ a1 a', ExecStmt cfg o fc (fr a) (m a) body (.normal (fr a1) (m a1)) ∧
        ExecPost cfg o fc (fr a1) (m a1) post (.ok () (fr a') (m a')) ∧ P v a') :
    ∀ v a, P v a → ∃ a', P 0 a' ∧ ExecLoop cfg o fc (fr a) (m a) (some c) post body (.normal (fr a') (m a')) := by
  intro v
  induction v with
  | zero => intro a h; exact ⟨a, h, ExecLoop.condFalse (hfalse a h)⟩
  | succ v ih =>
    intro a h
    obtain ⟨hc, a1, a', hbody, hpost, hP⟩ := hstep v a h
    obtain ⟨a'', hP'', hloop⟩ := ih a' hP
    exact ⟨a'', hP'', ExecLoop.iterate (EvalCond.some hc) hbody hpost hloop⟩

/-- The loop rule coupled with the EVM trace: the body step also advances the cursor, the
    exit also reaches the exit cursor (as `Run.whileLoop`). -/
theorem coupledLoop {α : Type} {code : ByteArray} {s0 : EVM.State}
    (P : ℕ → α → Prop) (fr : α → Frame) (m : α → Machine) (cur exitCur : α → Reasoning.Trace.Cursor)
    {c : Expr} {post : Option Expr} {body : Stmt}
    (hexit : ∀ a, P 0 a →
      EvalExpr cfg o fc (fr a) (m a) c (.ok (.bool false) (fr a) (m a)) ∧
      ∀ k C, Run code s0 (cur a) k C → ∃ k' C', Run code s0 (exitCur a) k' C')
    (hstep : ∀ v a, P (v + 1) a → ∀ k C, Run code s0 (cur a) k C →
      EvalExpr cfg o fc (fr a) (m a) c (.ok (.bool true) (fr a) (m a)) ∧
      ∃ a1 a', ExecStmt cfg o fc (fr a) (m a) body (.normal (fr a1) (m a1)) ∧
        ExecPost cfg o fc (fr a1) (m a1) post (.ok () (fr a') (m a')) ∧ P v a' ∧
        ∃ k' C', Run code s0 (cur a') k' C') :
    ∀ v a, P v a → ∀ k C, Run code s0 (cur a) k C →
      ∃ a', P 0 a' ∧ ExecLoop cfg o fc (fr a) (m a) (some c) post body (.normal (fr a') (m a')) ∧
        ∃ k' C', Run code s0 (exitCur a') k' C' := by
  intro v
  induction v with
  | zero =>
    intro a h k C hrun
    obtain ⟨hc, hex⟩ := hexit a h
    exact ⟨a, h, ExecLoop.condFalse hc, hex k C hrun⟩
  | succ v ih =>
    intro a h k C hrun
    obtain ⟨hc, a1, a', hbody, hpost, hP, k', C', hrun'⟩ := hstep v a h k C hrun
    obtain ⟨a'', hP'', hloop, hex⟩ := ih a' hP k' C' hrun'
    exact ⟨a'', hP'', ExecLoop.iterate (EvalCond.some hc) hbody hpost hloop, hex⟩

/-! ## Constructors -/

/-- A `uint256` state variable's inline initialiser. -/
theorem ExecInits.storageU256 {fr fr1 : Frame} {m m1 : Machine} {v : FlatVar} {rest : List FlatVar} {e : Expr}
    {w slot : UInt256} {r : Res Unit}
    (hmut : v.mutability = .mutable) (hinit : v.init = some e) (hty : v.ty = u256Ty)
    (he : EvalExpr cfg o fc fr m e (.ok (u256Val w.toNat) fr1 m1))
    (hl : cfg.storage.layout ⟨v.key, []⟩ m1.evm = some (uint256Loc slot))
    (hrest : ExecInits cfg o fc fr1 (storeU256 m1 slot w) rest r) :
    ExecInits cfg o fc fr m (v :: rest) r :=
  ExecInits.storage hmut hinit he (by rw [hty]; exact assign_storage_u256 hl w) hrest

/-- A constructor-chain step whose constructor has no modifiers. -/
theorem ExecCtorChain.runPlain {frP fr2 fr4 : Frame} {topArgs vs : List Value} {imms : Store} {m m1 m2 m4 : Machine}
    {step : CtorStep} {rest : List CtorStep} {fid : FnId} {fn : FnDef} {body : Block} {res : ExecResult}
    {r : CtorResult} {frA : Frame}
    (hfid : step.fn = some fid) (hfn : fc.fns[fid]? = some fn)
    (hargs : CtorArgs cfg o fc frP topArgs m step (.ok vs frA m1))
    (henter : enterFn cfg fc.types fn.declaredIn fn.decl vs m1 imms = some (.ok (fr2, m2)))
    (hbody : fn.decl.body = some body) (hmods : fn.decl.modifiers = [])
    (hrun : ExecBlock cfg o fc (bodyFrame fr2 body) m2 body res) (hfin : finished res = some (fr4, m4))
    (hrest : ExecCtorChain cfg o fc frP topArgs (immStore fr4) m4 rest r) :
    ExecCtorChain cfg o fc frP topArgs imms m (step :: rest) r := by
  refine ExecCtorChain.run hfid hfn hargs henter hbody ?_ hfin hrest
  rw [hmods]
  exact ExecChain.body hrun

/-- The single top-level constructor step: the decoded arguments, no base constructors. -/
theorem ExecCtorChain.topPlain {frP fr2 fr4 : Frame} {topArgs : List Value} {imms : Store} {m m2 m4 : Machine}
    {step : CtorStep} {fid : FnId} {fn : FnDef} {body : Block} {res : ExecResult}
    (hstep : step.contract = fc.name) (hfid : step.fn = some fid) (hfn : fc.fns[fid]? = some fn)
    (henter : enterFn cfg fc.types fn.declaredIn fn.decl topArgs m imms = some (.ok (fr2, m2)))
    (hbody : fn.decl.body = some body) (hmods : fn.decl.modifiers = [])
    (hrun : ExecBlock cfg o fc (bodyFrame fr2 body) m2 body res) (hfin : finished res = some (fr4, m4)) :
    ExecCtorChain cfg o fc frP topArgs imms m [step] (.ok m4 (immStore fr4)) :=
  ExecCtorChain.runPlain hfid hfn (CtorArgs.top hstep) henter hbody hmods hrun hfin ExecCtorChain.nil

/-! ## Modifiers

`m(args) { …; _; … }` runs its body in a fresh scope over the function scope (`pushScope`); `_;`
runs the rest of the chain and the function body in the function scope and resumes the modifier
scope; leaving the body pops the scope (`popScope`). -/

@[simp] theorem pushScope_chain (here : Ident) (fr : Frame) (rest : List ModifierInvocation) (body : Block) :
    (pushScope here fr rest body).chain = rest := rfl
@[simp] theorem pushScope_body (here : Ident) (fr : Frame) (rest : List ModifierInvocation) (body : Block) :
    (pushScope here fr rest body).body = body := rfl
@[simp] theorem pushScope_here (here : Ident) (fr : Frame) (rest : List ModifierInvocation) (body : Block) :
    (pushScope here fr rest body).here = here := rfl
@[simp] theorem pushScope_unchecked (here : Ident) (fr : Frame) (rest : List ModifierInvocation) (body : Block) :
    (pushScope here fr rest body).unchecked = fr.unchecked := rfl
@[simp] theorem pushScope_get? (here : Ident) (fr : Frame) (rest : List ModifierInvocation) (body : Block) (x : Ident) :
    (pushScope here fr rest body).get? x = none := by
  simp [Frame.get?, pushScope, Std.HashMap.get?_eq_getElem?]
@[simp] theorem popFrame_pushScope (here : Ident) (fr : Frame) (rest : List ModifierInvocation) (body : Block) :
    popFrame (pushScope here fr rest body) = { fr with chain := rest, body := body } := rfl
@[simp] theorem popFrame_resumeScope_pushScope (here : Ident) (fr fr' : Frame) (rest : List ModifierInvocation)
    (body : Block) :
    popFrame (resumeScope (pushScope here fr rest body) fr') = { fr' with chain := rest, body := body } := rfl
@[simp] theorem resumeScope_get? (fr fr' : Frame) (x : Ident) : (resumeScope fr fr').get? x = fr.get? x := rfl
@[simp] theorem resumeScope_chain (fr fr' : Frame) : (resumeScope fr fr').chain = fr.chain := rfl
@[simp] theorem resumeScope_body (fr fr' : Frame) : (resumeScope fr fr').body = fr.body := rfl
@[simp] theorem resumeScope_unchecked (fr fr' : Frame) : (resumeScope fr fr').unchecked = fr'.unchecked := rfl

theorem bindModParams_nil (fr : Frame) (m : Machine) : bindModParams cfg fc.types fr m [] [] = some (.ok (fr, m)) := rfl

/-- A modifier invoked without arguments. -/
theorem ExecChain.modifierNoArgs {fr : Frame} {m : Machine} {mi : ModifierInvocation} {rest : List ModifierInvocation}
    {body : Block} {md : ModDef} {mb : Block} {r : ExecResult}
    (hmod : fc.modifier? mi.name = some md) (hparams : md.decl.params = []) (hargs : mi.args = none)
    (hbody : md.decl.body = some mb)
    (hrun : ExecBlock cfg o fc (pushScope md.declaredIn fr rest body) m mb r) :
    ExecChain cfg o fc fr m (mi :: rest) body (popScope r) := by
  refine ExecChain.modifier (vs := []) (fr1 := fr) (m1 := m) hmod ?_ EvalExprs.nil ?_ hbody hrun
  · rw [hparams, hargs]; rfl
  · rw [hparams]; rfl

/-- A modifier with positional arguments (bound by `hbind`). -/
theorem ExecChain.modifierPlain {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {mi : ModifierInvocation}
    {rest : List ModifierInvocation} {body : Block} {md : ModDef} {mb : Block} {r : ExecResult} {es : List Expr}
    {vs : List Value}
    (hmod : fc.modifier? mi.name = some md) (hargs : mi.args = some (.positional es))
    (hes : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (hbind : bindModParams cfg fc.types (pushScope md.declaredIn fr1 rest body) m1 md.decl.params vs =
      some (.ok (fr2, m2)))
    (hbody : md.decl.body = some mb) (hrun : ExecBlock cfg o fc fr2 m2 mb r) :
    ExecChain cfg o fc fr m (mi :: rest) body (popScope r) := by
  refine ExecChain.modifier hmod ?_ hes hbind hbody hrun
  rw [hargs]; rfl

/-- `_;` when the rest of the chain and the body finish (normally or by `return`). -/
theorem ExecStmt.placeholderNormal {fr fr' : Frame} {m m' : Machine}
    (hrest : ExecChain cfg o fc (popFrame fr) m fr.chain fr.body (.normal fr' m')) :
    ExecStmt cfg o fc fr m .placeholder (.normal (resumeScope fr fr') m') :=
  ExecStmt.placeholder hrest rfl

theorem ExecStmt.placeholderReturned {fr fr' : Frame} {m m' : Machine}
    (hrest : ExecChain cfg o fc (popFrame fr) m fr.chain fr.body (.returned fr' m')) :
    ExecStmt cfg o fc fr m .placeholder (.normal (resumeScope fr fr') m') :=
  ExecStmt.placeholder hrest rfl

theorem ExecStmt.placeholderRevert {fr : Frame} {m : Machine} {d : ByteArray}
    (hrest : ExecChain cfg o fc (popFrame fr) m fr.chain fr.body (.reverted d)) :
    ExecStmt cfg o fc fr m .placeholder (.reverted d) :=
  ExecStmt.placeholder hrest rfl

@[simp] theorem popScope_normal (fr : Frame) (m : Machine) : popScope (.normal fr m) = .normal (popFrame fr) m := rfl
@[simp] theorem popScope_returned (fr : Frame) (m : Machine) :
    popScope (.returned fr m) = .returned (popFrame fr) m := rfl
@[simp] theorem popScope_reverted (d : ByteArray) : popScope (.reverted d) = .reverted d := rfl

/-! ## Value transfers and low-level calls -/

/-- `payable(a).transfer(amount)`, call made. -/
theorem EvalExpr.transferPlain {fr fr1 fr2 : Frame} {m m1 m2 m3 : Machine} {recv amt : Expr} {a : EVM.Address}
    {value : ℕ} {out : ByteArray}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.address a) fr1 m1))
    (hamt : EvalExpr cfg o fc fr1 m1 amt (.ok (u256Val value) fr2 m2))
    (hcall : callViaEVM o m2 (EVM.address a.toNat) value ByteArray.empty m2.evm.executionEnv.perm
      (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value) (true, m3, out)) :
    EvalExpr cfg o fc fr m (.call (.member recv "transfer") [] (.positional [amt])) (.ok .unit fr2 m3) :=
  EvalExpr.transfer hdirect hrecv rfl rfl hamt rfl hcall

/-- `payable(a).transfer(amount)`, callee failed: the revert data is bubbled up. -/
theorem EvalExpr.transferPlainFailed {fr fr1 fr2 : Frame} {m m1 m2 m3 : Machine} {recv amt : Expr} {a : EVM.Address}
    {value : ℕ} {out : ByteArray}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.address a) fr1 m1))
    (hamt : EvalExpr cfg o fc fr1 m1 amt (.ok (u256Val value) fr2 m2))
    (hcall : callViaEVM o m2 (EVM.address a.toNat) value ByteArray.empty m2.evm.executionEnv.perm
      (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value) (false, m3, out)) :
    EvalExpr cfg o fc fr m (.call (.member recv "transfer") [] (.positional [amt])) (.reverted out) :=
  EvalExpr.transferFailed hdirect hrecv rfl rfl hamt rfl hcall

/-- `payable(a).send(amount)`. -/
theorem EvalExpr.sendPlain {fr fr1 fr2 : Frame} {m m1 m2 m3 : Machine} {recv amt : Expr} {a : EVM.Address}
    {value : ℕ} {z : Bool} {out : ByteArray}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.address a) fr1 m1))
    (hamt : EvalExpr cfg o fc fr1 m1 amt (.ok (u256Val value) fr2 m2))
    (hcall : callViaEVM o m2 (EVM.address a.toNat) value ByteArray.empty m2.evm.executionEnv.perm
      (calleeGas o m2 (some (if value = 0 then 2300 else 0)) value) (z, m3, out)) :
    EvalExpr cfg o fc fr m (.call (.member recv "send") [] (.positional [amt])) (.ok (.bool z) fr2 m3) :=
  EvalExpr.send hdirect hrecv rfl rfl hamt rfl hcall

/-- `a.call{value: v}("")`: the `(success, data)` pair, the returned bytes allocated in memory. -/
theorem EvalExpr.lowLevelCallValue {fr fr1 fr2 : Frame} {m m1 m2 m5 : Machine} {recv v : Expr} {a : EVM.Address}
    {value : ℕ} {z : Bool} {out : ByteArray}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.address a) fr1 m1))
    (hv : EvalExpr cfg o fc fr1 m1 v (.ok (u256Val value) fr2 m2))
    (hcall : callViaEVM o m2 (EVM.address a.toNat) value ByteArray.empty m2.evm.executionEnv.perm
      (calleeGas o m2 none value) (z, m5, out)) :
    EvalExpr cfg o fc fr m (.call (.member recv "call") [.value v] (.positional [.lit (.str "")]))
      (.ok (.tuple [.bool z, (allocBytes m5 false out).1]) fr2 (allocBytes m5 false out).2) := by
  refine EvalExpr.lowLevelCall (data := ByteArray.empty) (Or.inl rfl) hdirect hrecv rfl rfl (EvalValueOpt.some hv rfl)
    EvalGasOpt.none (EvalExpr.lit rfl) ?_ ?_ rfl
  · show some "".toUTF8 = some ByteArray.empty
    rw [toUTF8_empty]
  · simpa using hcall

/-- `(bool x, ) = rhs;` -/
theorem ExecStmt.tupleDeclBoolSkip {fr fr1 : Frame} {m m1 : Machine} {rhs : Expr} {x : Ident} {z : Bool} {ov : Value}
    {loc : Option DataLoc}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [.bool z, ov]) fr1 m1)) :
    ExecStmt cfg o fc fr m (.tupleDecl [some { ty := .bool, loc := loc, name := some x }, none] rhs)
      (.normal (fr1.bind x .bool loc (.bool z)) m1) := by
  refine ExecStmt.tupleDecl hrhs (DeclareTuple.cons (fr1 := fr1.bind x .bool loc (.bool z)) (m1 := m1) rfl ?_
    (DeclareTuple.skip DeclareTuple.nil))
  simp [declare, coerce]
  try rfl

/-! ## Custom errors -/

/-- `revert E();` -/
theorem ExecStmt.revertErrorNoArgs {fr : Frame} {m : Machine} {err : Ident} {ei : ErrorInfo}
    (hei : fc.error? err = some ei) (hparams : ei.decl.params = []) (htys : ei.sig.paramTypes = []) :
    ExecStmt cfg o fc fr m (.revert (.ident err) (.positional [])) (.reverted (selectorOf ei.sigStr)) := by
  refine ExecStmt.revertError (es := []) (vs := []) (svs := []) (fr1 := fr) (m1 := m) (m2 := m) hei ?_ EvalExprs.nil
    ?_ ?_
  · rw [hparams]; rfl
  · rw [hparams]; rfl
  · rw [htys]; exact customErrorData_nil _

/-- `revert E(n);` for `error E(uint256)`. -/
theorem ExecStmt.revertErrorU256 {fr fr1 : Frame} {m m1 : Machine} {err : Ident} {ei : ErrorInfo} {e : Expr} {n : ℕ}
    {l1 : Option DataLoc} {n1 : Option Ident}
    (hei : fc.error? err = some ei) (hparams : ei.decl.params = [{ ty := u256Ty, loc := l1, name := n1 }])
    (htys : ei.sig.paramTypes = [.elem (.int (.uint ⟨256, by decide⟩))])
    (he : EvalExpr cfg o fc fr m e (.ok (u256Val n) fr1 m1)) (hn : n < 2 ^ 256) :
    ExecStmt cfg o fc fr m (.revert (.ident err) (.positional [e]))
      (.reverted (selectorOf ei.sigStr ++ UInt256.toByteArray (UInt256.ofNat n))) := by
  refine ExecStmt.revertError (es := [e]) (vs := [u256Val n]) (svs := [.int n]) (fr1 := fr1) (m1 := m1) (m2 := m1) hei ?_
    (EvalExprs.cons he EvalExprs.nil) ?_ ?_
  · rw [hparams]; rfl
  · rw [hparams]; exact abiArgs_u256 ..
  · rw [htys]; exact customErrorData_u256 _ n hn

/-! ## Immutables -/

theorem EvalExpr.immutableLocal {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {l : Local}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .immutable)
    (hloc : fr.get? (immName v.name) = some l) :
    EvalExpr cfg o fc fr m (.ident x) (.ok l.val fr m) :=
  EvalExpr.immutableVar hx hv hmut (by simp [immutableValue, hloc])

theorem EvalExpr.immutableCfg {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {nm : Ident} {val : Value}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .immutable)
    (hnone : fr.get? (immName v.name) = none) (hfind : cfg.immutables.find? (·.1 == v.name) = some (nm, val)) :
    EvalExpr cfg o fc fr m (.ident x) (.ok val fr m) :=
  EvalExpr.immutableVar hx hv hmut (by simp [immutableValue, hnone, hfind])

/-! ## Memory objects -/

theorem EvalExpr.memFieldPlain {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {f : Ident} {obj : ℕ} {v : Value}
    (hdirect : directMember fc fr e = false) (hf : f ≠ "length")
    (he : EvalExpr cfg o fc fr m e (.ok (.memRef obj) fr1 m1)) (hget : memField m1.heap obj f = some v) :
    EvalExpr cfg o fc fr m (.member e f) (.ok v fr1 m1) :=
  EvalExpr.memberMemField hdirect hf he hget

theorem EvalExpr.memLengthPlain {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {obj n : ℕ}
    (hdirect : directMember fc fr e = false)
    (he : EvalExpr cfg o fc fr m e (.ok (.memRef obj) fr1 m1)) (hlen : memLength m1.heap obj = some n) :
    EvalExpr cfg o fc fr m (.member e "length") (.ok (wordNat n) fr1 m1) :=
  EvalExpr.memberMemLength hdirect he hlen

theorem wordNat_eq (n : ℕ) (hn : n < UInt256.size) : wordNat n = u256Val n := by
  show Value.uint ⟨256, by decide⟩ (UInt256.ofNat n).toNat = _
  rw [ulit_toNat' n hn]

end Solidity
