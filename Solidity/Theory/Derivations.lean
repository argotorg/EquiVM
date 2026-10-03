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
    (hev : fc.eventsNamed ev = [ei])
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
  exact ExecStmt.emit (by rw [hev]; rfl) hargs
    (by rw [hev]; exact resolveEvent_single (eventFits_addr_addr_u256 _ _ ei a b n.toNat hparams)) habi hle

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

/-! ## Increments and `for` loops -/

theorem EvalExpr.postIncLocalU256 {fr : Frame} {m : Machine} {x : Ident} {n : ℕ} (l : Local)
    (hx : fr.get? x = some l) (hty : l.ty = u256Ty) (hval : l.val = u256Val n) (hunch : fr.unchecked = false)
    (hfit : n + 1 < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.unary .postInc (.ident x)) (.ok (u256Val n) (fr.setVal x (u256Val (n + 1))) m) := by
  have h := EvalExpr.incDec (cfg := cfg) (o := o) (fc := fc) (op := .postInc) (cur := u256Val n)
    (nv := u256Val (n + 1)) rfl (EvalLValue.local (m := m) hx) (by rw [readLValue_local hx, hval])
    (by rw [hunch]; exact binop_add_u256_lit1 n hfit) (assign_local_u256 l hx hty (n + 1))
  simpa [isPrefix] using h

theorem EvalExpr.preIncLocalU256 {fr : Frame} {m : Machine} {x : Ident} {n : ℕ} (l : Local)
    (hx : fr.get? x = some l) (hty : l.ty = u256Ty) (hval : l.val = u256Val n) (hunch : fr.unchecked = false)
    (hfit : n + 1 < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.unary .preInc (.ident x)) (.ok (u256Val (n + 1)) (fr.setVal x (u256Val (n + 1))) m) := by
  have h := EvalExpr.incDec (cfg := cfg) (o := o) (fc := fc) (op := .preInc) (cur := u256Val n)
    (nv := u256Val (n + 1)) rfl (EvalLValue.local (m := m) hx) (by rw [readLValue_local hx, hval])
    (by rw [hunch]; exact binop_add_u256_lit1 n hfit) (assign_local_u256 l hx hty (n + 1))
  simpa [isPrefix] using h

theorem EvalExpr.postDecLocalU256 {fr : Frame} {m : Machine} {x : Ident} {n : ℕ} (l : Local)
    (hx : fr.get? x = some l) (hty : l.ty = u256Ty) (hval : l.val = u256Val n) (hunch : fr.unchecked = false)
    (hpos : 0 < n) (hn : n < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.unary .postDec (.ident x)) (.ok (u256Val n) (fr.setVal x (u256Val (n - 1))) m) := by
  have h := EvalExpr.incDec (cfg := cfg) (o := o) (fc := fc) (op := .postDec) (cur := u256Val n)
    (nv := u256Val (n - 1)) rfl (EvalLValue.local (m := m) hx) (by rw [readLValue_local hx, hval])
    (by rw [hunch]; exact binop_sub_u256_lit1 n hpos hn) (assign_local_u256 l hx hty (n - 1))
  simpa [isPrefix] using h

/-- The `i++` of a `for` loop. -/
theorem ExecPost.postIncLocalU256 {fr : Frame} {m : Machine} {x : Ident} {n : ℕ} (l : Local)
    (hx : fr.get? x = Option.some l) (hty : l.ty = u256Ty) (hval : l.val = u256Val n) (hunch : fr.unchecked = false)
    (hfit : n + 1 < 2 ^ 256) :
    ExecPost cfg o fc fr m (Option.some (.unary .postInc (.ident x))) (.ok () (fr.setVal x (u256Val (n + 1))) m) :=
  ExecPost.some (EvalExpr.postIncLocalU256 l hx hty hval hunch hfit)

/-- `for (init; c; post) body` that runs to completion: the loop variable's scope is left. -/
theorem ExecStmt.forFinished {fr fr1 fr' : Frame} {m m1 m' : Machine} {init : Stmt} {c post : Option Expr}
    {body : Stmt}
    (hinit : ExecStmt cfg o fc fr m init (.normal fr1 m1))
    (hloop : ExecLoop cfg o fc fr1 m1 c post body (.normal fr' m')) :
    ExecStmt cfg o fc fr m (.for (some init) c post body) (.normal (fr.exitScope fr') m') :=
  ExecStmt.forInit hinit hloop

/-! ## Struct literals, storage arrays of structs, memory arrays -/

/-- `S({f₁: e₁, …})` or `S(e₁, …)`. -/
theorem EvalExpr.structLitPlain {fr fr1 : Frame} {m m1 m2 : Machine} {s : Ident} {sd : StructInfo} {args : Args}
    {es : List Expr} {vs : List Value} {v : Value}
    (hbuiltin : isBuiltinFn s = false) (hx : fr.get? s = none) (hfns : fc.fnsNamed s = [])
    (hsd : fc.types.struct? none s = some sd)
    (hargs : argExprs (sd.fields.map fun f => some f.2) args = some es)
    (hes : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (hobj : structObj cfg fc.types m1 sd vs = some (.ok (v, m2))) :
    EvalExpr cfg o fc fr m (.call (.ident s) [] args) (.ok v fr1 m2) :=
  EvalExpr.structLit hbuiltin hx hfns hsd hargs hes hobj

/-- A state variable of reference type, as a storage reference. -/
theorem EvalExpr.stateRef {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hnv : isValueType fc.types v.ty = false) :
    EvalExpr cfg o fc fr m (.ident x) (.ok (.storageRef ⟨v.key, []⟩ v.ty) fr m) :=
  EvalExpr.stateVar hx hv hmut (loadIfScalar_ref hnv)

/-- `a.push(x)` on a storage array. -/
theorem EvalExpr.pushValue {fr fr1 fr2 : Frame} {m m1 m2 m3 : Machine} {recv x : Expr} {er : Solm.EvaledStorageRef}
    {e : Ty} {v : Value}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1))
    (hx : EvalExpr cfg o fc fr1 m1 x (.ok v fr2 m2))
    (hpush : storagePush cfg fc.types m2 er e (some v) = some (.ok m3)) :
    EvalExpr cfg o fc fr m (.call (.member recv "push") [] (.positional [x])) (.ok .unit fr2 m3) :=
  EvalExpr.push1 hdirect hrecv hx hpush

theorem ExecStmt.pushValue {fr fr1 fr2 : Frame} {m m1 m2 m3 : Machine} {recv x : Expr} {er : Solm.EvaledStorageRef}
    {e : Ty} {v : Value}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1))
    (hx : EvalExpr cfg o fc fr1 m1 x (.ok v fr2 m2))
    (hpush : storagePush cfg fc.types m2 er e (some v) = some (.ok m3)) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.member recv "push") [] (.positional [x]))) (.normal fr2 m3) :=
  ExecStmt.exprStmt (EvalExpr.pushValue hdirect hrecv hx hpush)

/-- `a[i]` on a memory array. -/
theorem EvalExpr.indexMemPlain {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {e i : Expr} {obj k : ℕ} {ety : Ty}
    {elems : List Value}
    (he : EvalExpr cfg o fc fr m e (.ok (.memRef obj) fr1 m1))
    (hi : EvalExpr cfg o fc fr1 m1 i (.ok (u256Val k) fr2 m2))
    (hget : m2.heap.get? obj = some (.array ety elems)) (hk : k < elems.length) (hraw : isRaw elems[k] = false) :
    EvalExpr cfg o fc fr m (.index e i) (.ok elems[k] fr2 m2) :=
  EvalExpr.indexMem he hi (memIndex_array_ok hget hk) hraw

/-! ## `abi.encode*` and `keccak256` -/

/-- `abi.encodePacked(es)`: the packed bytes land in a fresh memory `bytes` object. -/
theorem EvalExpr.abiEncodePackedPlain {fr fr1 : Frame} {m m1 : Machine} {es : List Expr} {vs : List Value}
    {tys : List ABI.ABIType} {svs : List ABI.ABIValue} {parts : List (List UInt8)}
    (hes : EvalExprs cfg o fc fr m es (.ok vs fr1 m1)) (htys : vs.mapM (abiTyOfValue fc.types m1.heap) = some tys)
    (hsvs : vs.mapM (toAbi m1.heap fuelDefault) = some svs)
    (hparts : (tys.zip svs).mapM (fun (t, sv) => ABI.encodePackedValue? t sv) = some parts) :
    EvalExpr cfg o fc fr m (.call (.member (.ident "abi") "encodePacked") [] (.positional es))
      (.ok (allocBytes m1 false parts.flatten.toByteArray).1 fr1 (allocBytes m1 false parts.flatten.toByteArray).2) :=
  EvalExpr.abiEncodePacked hes htys (abiArgsAbi_of_mapM hsvs) hparts rfl

/-- `abi.encode(es)`. -/
theorem EvalExpr.abiEncodePlain {fr fr1 : Frame} {m m1 : Machine} {es : List Expr} {vs : List Value}
    {tys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8}
    (hes : EvalExprs cfg o fc fr m es (.ok vs fr1 m1)) (htys : vs.mapM (abiTyOfValue fc.types m1.heap) = some tys)
    (hsvs : vs.mapM (toAbi m1.heap fuelDefault) = some svs) (henc : ABI.encodeABIValues? tys svs = some bs) :
    EvalExpr cfg o fc fr m (.call (.member (.ident "abi") "encode") [] (.positional es))
      (.ok (allocBytes m1 false bs.toByteArray).1 fr1 (allocBytes m1 false bs.toByteArray).2) :=
  EvalExpr.abiEncode hes htys (abiArgsAbi_of_mapM hsvs) henc rfl

/-- `abi.encodeWithSelector(sel, es)`. -/
theorem EvalExpr.abiEncodeWithSelectorPlain {fr fr1 : Frame} {m m1 : Machine} {sel : Expr} {es : List Expr}
    {sb : List UInt8} {vs : List Value} {tys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8}
    (hes : EvalExprs cfg o fc fr m (sel :: es) (.ok (.fixedBytes ⟨3, by decide⟩ sb :: vs) fr1 m1))
    (htys : vs.mapM (abiTyOfValue fc.types m1.heap) = some tys)
    (hsvs : vs.mapM (toAbi m1.heap fuelDefault) = some svs) (henc : ABI.encodeABIValues? tys svs = some bs) :
    EvalExpr cfg o fc fr m (.call (.member (.ident "abi") "encodeWithSelector") [] (.positional (sel :: es)))
      (.ok (allocBytes m1 false (ByteArray.mk sb.toArray ++ bs.toByteArray)).1 fr1
        (allocBytes m1 false (ByteArray.mk sb.toArray ++ bs.toByteArray)).2) :=
  EvalExpr.abiEncodeWithSelector hes rfl htys (abiArgsAbi_of_mapM hsvs) henc rfl

/-- `keccak256(b)` of a memory `bytes`/`string` object. -/
theorem EvalExpr.keccakMemBytes {fr fr1 : Frame} {m m1 : Machine} {b : Expr} {id : ℕ} {s : Bool} {d : ByteArray}
    (hb : EvalExpr cfg o fc fr m b (.ok (.memRef id) fr1 m1)) (hget : m1.heap.get? id = some (.bytes s d)) :
    EvalExpr cfg o fc fr m (.call (.ident "keccak256") [] (.positional [b]))
      (.ok (.fixedBytes ⟨31, by decide⟩ (ffi.KEC d).toList) fr1 m1) :=
  EvalExpr.keccak hb (by simp [bytesArg, hget])

/-- `keccak256(abi.encodePacked(es))`. -/
theorem EvalExpr.keccakPacked {fr fr1 : Frame} {m m1 : Machine} {es : List Expr} {vs : List Value}
    {tys : List ABI.ABIType} {svs : List ABI.ABIValue} {parts : List (List UInt8)}
    (hes : EvalExprs cfg o fc fr m es (.ok vs fr1 m1)) (htys : vs.mapM (abiTyOfValue fc.types m1.heap) = some tys)
    (hsvs : vs.mapM (toAbi m1.heap fuelDefault) = some svs)
    (hparts : (tys.zip svs).mapM (fun (t, sv) => ABI.encodePackedValue? t sv) = some parts) :
    EvalExpr cfg o fc fr m
      (.call (.ident "keccak256") [] (.positional [.call (.member (.ident "abi") "encodePacked") [] (.positional es)]))
      (.ok (.fixedBytes ⟨31, by decide⟩ (ffi.KEC parts.flatten.toByteArray).toList) fr1
        (allocBytes m1 false parts.flatten.toByteArray).2) :=
  EvalExpr.keccakMemBytes (s := false) (d := parts.flatten.toByteArray)
    (EvalExpr.abiEncodePackedPlain hes htys hsvs hparts) (Heap.get?_alloc_self _ _)

/-- `keccak256(abi.encode(es))`. -/
theorem EvalExpr.keccakEncode {fr fr1 : Frame} {m m1 : Machine} {es : List Expr} {vs : List Value}
    {tys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8}
    (hes : EvalExprs cfg o fc fr m es (.ok vs fr1 m1)) (htys : vs.mapM (abiTyOfValue fc.types m1.heap) = some tys)
    (hsvs : vs.mapM (toAbi m1.heap fuelDefault) = some svs) (henc : ABI.encodeABIValues? tys svs = some bs) :
    EvalExpr cfg o fc fr m
      (.call (.ident "keccak256") [] (.positional [.call (.member (.ident "abi") "encode") [] (.positional es)]))
      (.ok (.fixedBytes ⟨31, by decide⟩ (ffi.KEC bs.toByteArray).toList) fr1 (allocBytes m1 false bs.toByteArray).2) :=
  EvalExpr.keccakMemBytes (s := false) (d := bs.toByteArray) (EvalExpr.abiEncodePlain hes htys hsvs henc)
    (Heap.get?_alloc_self _ _)

theorem EvalExprs.two {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {e1 e2 : Expr} {v1 v2 : Value}
    (h1 : EvalExpr cfg o fc fr m e1 (.ok v1 fr1 m1)) (h2 : EvalExpr cfg o fc fr1 m1 e2 (.ok v2 fr2 m2)) :
    EvalExprs cfg o fc fr m [e1, e2] (.ok [v1, v2] fr2 m2) :=
  EvalExprs.cons h1 (EvalExprs.cons h2 EvalExprs.nil)

theorem EvalExprs.three {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {e1 e2 e3 : Expr} {v1 v2 v3 : Value}
    (h1 : EvalExpr cfg o fc fr m e1 (.ok v1 fr1 m1)) (h2 : EvalExpr cfg o fc fr1 m1 e2 (.ok v2 fr2 m2))
    (h3 : EvalExpr cfg o fc fr2 m2 e3 (.ok v3 fr3 m3)) :
    EvalExprs cfg o fc fr m [e1, e2, e3] (.ok [v1, v2, v3] fr3 m3) :=
  EvalExprs.cons h1 (EvalExprs.cons h2 (EvalExprs.cons h3 EvalExprs.nil))

/-! ## Conversions and `type(T)` members -/

/-- `T(a)` whose conversion leaves the heap unchanged. -/
theorem EvalExpr.convertPlain {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {ty : Ty} {v v' : Value}
    (ha : EvalExpr cfg o fc fr m a (.ok v fr1 m1)) (hc : explicitConv fc.types m1.heap v ty = some (.ok (v', m1.heap))) :
    EvalExpr cfg o fc fr m (.call (.typeExpr ty) [] (.positional [a])) (.ok v' fr1 m1) :=
  EvalExpr.convert ha hc

theorem EvalExpr.typeMaxU256 {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.member (.call (.ident "type") [] (.positional [.typeExpr u256Ty])) "max")
      (.ok (u256Val (2 ^ 256 - 1)) fr m) :=
  EvalExpr.typeMember rfl

theorem EvalExpr.typeMaxUint {fr : Frame} {m : Machine} (w : ABI.BitWidth) :
    EvalExpr cfg o fc fr m (.member (.call (.ident "type") [] (.positional [.typeExpr (.uint w)])) "max")
      (.ok (.uint w (2 ^ w.val - 1)) fr m) :=
  EvalExpr.typeMember rfl

/-! ## Blocks, `unchecked`, loops -/

theorem ExecStmt.blockNormal {fr fr' : Frame} {m m' : Machine} {ss : List Stmt}
    (hb : ExecBlock cfg o fc fr m ss (.normal fr' m')) :
    ExecStmt cfg o fc fr m (.block ss) (.normal (fr.exitScope fr') m') :=
  ExecStmt.block hb

theorem ExecStmt.blockRevert {fr : Frame} {m : Machine} {ss : List Stmt} {d : ByteArray}
    (hb : ExecBlock cfg o fc fr m ss (.reverted d)) : ExecStmt cfg o fc fr m (.block ss) (.reverted d) :=
  ExecStmt.block hb

theorem ExecStmt.uncheckedNormal {fr fr' : Frame} {m m' : Machine} {ss : List Stmt}
    (hb : ExecBlock cfg o fc { fr with unchecked := true } m ss (.normal fr' m')) :
    ExecStmt cfg o fc fr m (.unchecked ss) (.normal (fr.exitScope { fr' with unchecked := fr.unchecked }) m') :=
  ExecStmt.unchecked hb

theorem ExecStmt.uncheckedRevert {fr : Frame} {m : Machine} {ss : List Stmt} {d : ByteArray}
    (hb : ExecBlock cfg o fc { fr with unchecked := true } m ss (.reverted d)) :
    ExecStmt cfg o fc fr m (.unchecked ss) (.reverted d) :=
  ExecStmt.unchecked hb

theorem ExecBlock.one {fr fr1 : Frame} {m m1 : Machine} {s : Stmt}
    (h : ExecStmt cfg o fc fr m s (.normal fr1 m1)) : ExecBlock cfg o fc fr m [s] (.normal fr1 m1) :=
  ExecBlock.cons h ExecBlock.nil

theorem ExecBlock.oneRevert {fr : Frame} {m : Machine} {s : Stmt} {d : ByteArray}
    (h : ExecStmt cfg o fc fr m s (.reverted d)) : ExecBlock cfg o fc fr m [s] (.reverted d) :=
  ExecBlock.consRevert h

theorem ExecLoop.step {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {c : Expr} {post : Option Expr} {body : Stmt}
    {r : ExecResult} (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1))
    (hb : ExecStmt cfg o fc fr1 m1 body (.normal fr2 m2)) (hp : ExecPost cfg o fc fr2 m2 post (.ok () fr3 m3))
    (hrest : ExecLoop cfg o fc fr3 m3 (some c) post body r) : ExecLoop cfg o fc fr m (some c) post body r :=
  ExecLoop.iterate (EvalCond.some hc) hb hp hrest

theorem ExecLoop.stepWhile {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {c : Expr} {body : Stmt} {r : ExecResult}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1)) (hb : ExecStmt cfg o fc fr1 m1 body (.normal fr2 m2))
    (hrest : ExecLoop cfg o fc fr2 m2 (some c) none body r) : ExecLoop cfg o fc fr m (some c) none body r :=
  ExecLoop.iterate (EvalCond.some hc) hb ExecPost.none hrest

theorem ExecLoop.exit {fr fr1 : Frame} {m m1 : Machine} {c : Expr} {post : Option Expr} {body : Stmt}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool false) fr1 m1)) :
    ExecLoop cfg o fc fr m (some c) post body (.normal fr1 m1) :=
  ExecLoop.condFalse hc

theorem ExecLoop.breakStep {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {c : Expr} {post : Option Expr} {body : Stmt}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1)) (hb : ExecStmt cfg o fc fr1 m1 body (.break fr2 m2)) :
    ExecLoop cfg o fc fr m (some c) post body (.normal fr2 m2) :=
  ExecLoop.breakOut (EvalCond.some hc) hb

theorem ExecLoop.returnStep {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {c : Expr} {post : Option Expr} {body : Stmt}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1)) (hb : ExecStmt cfg o fc fr1 m1 body (.returned fr2 m2)) :
    ExecLoop cfg o fc fr m (some c) post body (.returned fr2 m2) :=
  ExecLoop.returnOut (EvalCond.some hc) hb

theorem ExecLoop.revertStep {fr fr1 : Frame} {m m1 : Machine} {c : Expr} {post : Option Expr} {body : Stmt}
    {d : ByteArray} (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1))
    (hb : ExecStmt cfg o fc fr1 m1 body (.reverted d)) : ExecLoop cfg o fc fr m (some c) post body (.reverted d) :=
  ExecLoop.bodyRevert (EvalCond.some hc) hb

theorem ExecStmt.whileNormal {fr fr' : Frame} {m m' : Machine} {c : Expr} {body : Stmt}
    (h : ExecLoop cfg o fc fr m (some c) none body (.normal fr' m')) :
    ExecStmt cfg o fc fr m (.while c body) (.normal fr' m') :=
  ExecStmt.while h

theorem ExecStmt.iteTrue {fr fr1 : Frame} {m m1 : Machine} {c : Expr} {t : Stmt} {e : Option Stmt} {r : ExecResult}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1)) (ht : ExecStmt cfg o fc fr1 m1 t r) :
    ExecStmt cfg o fc fr m (.ite c t e) r :=
  ExecStmt.iteT hc ht

theorem ExecStmt.iteFalseNone {fr fr1 : Frame} {m m1 : Machine} {c : Expr} {t : Stmt}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool false) fr1 m1)) :
    ExecStmt cfg o fc fr m (.ite c t none) (.normal fr1 m1) :=
  ExecStmt.iteFNone hc

theorem ExecStmt.iteFalse {fr fr1 : Frame} {m m1 : Machine} {c : Expr} {t s : Stmt} {r : ExecResult}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool false) fr1 m1)) (hs : ExecStmt cfg o fc fr1 m1 s r) :
    ExecStmt cfg o fc fr m (.ite c t (some s)) r :=
  ExecStmt.iteF hc hs

theorem EvalExpr.andTrue {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {y : Bool}
    (ha : EvalExpr cfg o fc fr m a (.ok (.bool true) fr1 m1)) (hb : EvalExpr cfg o fc fr1 m1 b (.ok (.bool y) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .and a b) (.ok (.bool y) fr2 m2) :=
  EvalExpr.andFull ha hb

theorem EvalExpr.andFalse {fr fr1 : Frame} {m m1 : Machine} {a b : Expr}
    (ha : EvalExpr cfg o fc fr m a (.ok (.bool false) fr1 m1)) :
    EvalExpr cfg o fc fr m (.binary .and a b) (.ok (.bool false) fr1 m1) :=
  EvalExpr.andShort ha

theorem EvalExpr.orFalse {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {y : Bool}
    (ha : EvalExpr cfg o fc fr m a (.ok (.bool false) fr1 m1)) (hb : EvalExpr cfg o fc fr1 m1 b (.ok (.bool y) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .or a b) (.ok (.bool y) fr2 m2) :=
  EvalExpr.orFull ha hb

theorem EvalExpr.orTrue {fr fr1 : Frame} {m m1 : Machine} {a b : Expr}
    (ha : EvalExpr cfg o fc fr m a (.ok (.bool true) fr1 m1)) :
    EvalExpr cfg o fc fr m (.binary .or a b) (.ok (.bool true) fr1 m1) :=
  EvalExpr.orShort ha

theorem EvalExpr.condTrue {fr fr1 : Frame} {m m1 : Machine} {c t e : Expr} {r : Res Value}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1)) (ht : EvalExpr cfg o fc fr1 m1 t r) :
    EvalExpr cfg o fc fr m (.cond c t e) r :=
  EvalExpr.condT hc ht

theorem EvalExpr.condFalse {fr fr1 : Frame} {m m1 : Machine} {c t e : Expr} {r : Res Value}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool false) fr1 m1)) (he : EvalExpr cfg o fc fr1 m1 e r) :
    EvalExpr cfg o fc fr m (.cond c t e) r :=
  EvalExpr.condF hc he

/-! ## Number literals as operands, shifts, bitwise operators, exponentiation -/

/-- A number literal without unit. -/
theorem EvalExpr.numLit {fr : Frame} {m : Machine} (k : ℕ) (hd : Option Nat) :
    EvalExpr cfg o fc fr m (.lit (.number k none hd)) (.ok (.literal k hd) fr m) :=
  EvalExpr.lit (by simp [literalValue, unitMul])

/-! ### `uint256 op literal` -/

theorem EvalExpr.addU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hunch : fr1.unchecked = false)
    (hk : k < 2 ^ 256) (hfit : x + k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .add a (.lit (.number k none hd))) (.ok (u256Val (x + k)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [hunch, Bool.not_false, binop_add_u256_lit x k hd (Int.natCast_nonneg k) (by exact_mod_cast hk) (by exact_mod_cast hfit),
      toNat_natCast_add])

theorem EvalExpr.addU256LitOverflow {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hunch : fr1.unchecked = false)
    (hk : k < 2 ^ 256) (hbig : 2 ^ 256 ≤ x + k) :
    EvalExpr cfg o fc fr m (.binary .add a (.lit (.number k none hd))) (.reverted (panicData 0x11)) :=
  EvalExpr.binaryPanic (p := .overflow) (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [hunch]
        exact binop_add_u256_lit_overflow x k hd (Int.natCast_nonneg k) (by exact_mod_cast hk) (by exact_mod_cast hbig))

theorem EvalExpr.subU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hunch : fr1.unchecked = false)
    (hx : x < 2 ^ 256) (hle : k ≤ x) :
    EvalExpr cfg o fc fr m (.binary .sub a (.lit (.number k none hd))) (.ok (u256Val (x - k)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [hunch, Bool.not_false, binop_sub_u256_lit x k hd (Int.natCast_nonneg k) (by exact_mod_cast (lt_of_le_of_lt hle hx)) hx
      (by exact_mod_cast hle), toNat_natCast_sub x k hle])

theorem EvalExpr.subU256LitUnderflow {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hunch : fr1.unchecked = false)
    (hk : k < 2 ^ 256) (hlt : x < k) :
    EvalExpr cfg o fc fr m (.binary .sub a (.lit (.number k none hd))) (.reverted (panicData 0x11)) :=
  EvalExpr.binaryPanic (p := .overflow) (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [hunch]
        exact binop_sub_u256_lit_underflow x k hd (Int.natCast_nonneg k) (by exact_mod_cast hk) (by exact_mod_cast hlt))

theorem EvalExpr.mulU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hunch : fr1.unchecked = false)
    (hk : k < 2 ^ 256) (hfit : x * k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .mul a (.lit (.number k none hd))) (.ok (u256Val (x * k)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [hunch, Bool.not_false, binop_mul_u256_lit x k hd (Int.natCast_nonneg k) (by exact_mod_cast hk) (by exact_mod_cast hfit),
      toNat_natCast_mul])

theorem EvalExpr.divU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (h0 : 0 < k) (hk : k < 2 ^ 256) (hx : x < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .div a (.lit (.number k none hd))) (.ok (u256Val (x / k)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [binop_div_u256_lit _ x k hd (by exact_mod_cast h0) (by exact_mod_cast hk) hx, Int.toNat_natCast])

theorem EvalExpr.modU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (h0 : 0 < k) (hk : k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .mod a (.lit (.number k none hd))) (.ok (u256Val (x % k)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [binop_mod_u256_lit _ x k hd (by exact_mod_cast h0) (by exact_mod_cast hk), Int.toNat_natCast])

theorem EvalExpr.cmpU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} {op : BinOp} {v : Value}
    (hop : isCmp op = true) (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 2 ^ 256)
    (hv : cmpInt op x k = some v) :
    EvalExpr cfg o fc fr m (.binary op a (.lit (.number k none hd))) (.ok v fr1 m1) :=
  EvalExpr.binary (by rintro rfl; simp [isCmp] at hop) (by rintro rfl; simp [isCmp] at hop) (EvalExpr.numLit k hd) ha
    (by rw [binop_cmp_u256_lit _ op hop x k hd (Int.natCast_nonneg k) (by exact_mod_cast hk), hv]; rfl)

theorem EvalExpr.ltU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .lt a (.lit (.number k none hd))) (.ok (.bool (decide (x < k))) fr1 m1) :=
  EvalExpr.cmpU256Lit rfl k hd ha hk (by simp [cmpInt])

theorem EvalExpr.leU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .le a (.lit (.number k none hd))) (.ok (.bool (decide (x ≤ k))) fr1 m1) :=
  EvalExpr.cmpU256Lit rfl k hd ha hk (by simp [cmpInt])

theorem EvalExpr.gtU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .gt a (.lit (.number k none hd))) (.ok (.bool (decide (x > k))) fr1 m1) :=
  EvalExpr.cmpU256Lit rfl k hd ha hk (by simp [cmpInt])

theorem EvalExpr.geU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .ge a (.lit (.number k none hd))) (.ok (.bool (decide (x ≥ k))) fr1 m1) :=
  EvalExpr.cmpU256Lit rfl k hd ha hk (by simp [cmpInt])

theorem EvalExpr.eqU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .eq a (.lit (.number k none hd))) (.ok (.bool (decide (x = k))) fr1 m1) :=
  EvalExpr.cmpU256Lit rfl k hd ha hk (by simp [cmpInt])

theorem EvalExpr.neU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .ne a (.lit (.number k none hd))) (.ok (.bool (decide (x ≠ k))) fr1 m1) :=
  EvalExpr.cmpU256Lit rfl k hd ha hk (by simp [cmpInt])

/-! ### Shifts, bitwise operators, exponentiation -/

theorem EvalExpr.shlU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x s : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val s) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hs : s < 256) :
    EvalExpr cfg o fc fr m (.binary .shl a b) (.ok (u256Val (x * 2 ^ s % 2 ^ 256)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_shl_u256 _ x s hs)

theorem EvalExpr.shlU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 256) :
    EvalExpr cfg o fc fr m (.binary .shl a (.lit (.number k none hd))) (.ok (u256Val (x * 2 ^ k % 2 ^ 256)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [binop_shl_u256_lit _ x k hd (Int.natCast_nonneg k) (by exact_mod_cast hk), Int.toNat_natCast])

theorem EvalExpr.shrU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x s : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val s) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hs : s < 256) :
    EvalExpr cfg o fc fr m (.binary .shr a b) (.ok (u256Val (x / 2 ^ s)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_shr_u256 _ x s hs)

theorem EvalExpr.shrU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 256) :
    EvalExpr cfg o fc fr m (.binary .shr a (.lit (.number k none hd))) (.ok (u256Val (x / 2 ^ k)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [binop_shr_u256_lit _ x k hd (Int.natCast_nonneg k) (by exact_mod_cast hk), Int.toNat_natCast])

theorem EvalExpr.bitAndU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .bitAnd a b) (.ok (u256Val (x &&& y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_bitAnd_u256 _ x y hx hy)

theorem EvalExpr.bitAndU256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : ℕ} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val x) fr1 m1)) (hk : k < 2 ^ 256) (hx : x < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .bitAnd a (.lit (.number k none hd))) (.ok (u256Val (x &&& k)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [binop_bitAnd_u256_lit _ x k hd (Int.natCast_nonneg k) (by exact_mod_cast hk) hx, Int.toNat_natCast])

theorem EvalExpr.bitOrU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .bitOr a b) (.ok (u256Val (x ||| y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_bitOr_u256 _ x y hx hy)

theorem EvalExpr.bitXorU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .bitXor a b) (.ok (u256Val (x ^^^ y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_bitXor_u256 _ x y hx hy)

theorem EvalExpr.bitNotU256 {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {x : ℕ}
    (he : EvalExpr cfg o fc fr m e (.ok (u256Val x) fr1 m1)) (hx : x < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.unary .bitNot e) (.ok (u256Val (2 ^ 256 - 1 - x)) fr1 m1) :=
  EvalExpr.unary he (unop_bitNot_u256 _ x hx) (by decide) (by decide)

theorem EvalExpr.expU256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hy : y < 256) (hfit : x ^ y < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .exp a b) (.ok (u256Val (x ^ y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_exp_u256 x y hy hfit)

theorem EvalExpr.expU256Overflow {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (u256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (u256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (h2 : 2 ≤ x) (hbig : 2 ^ 256 ≤ x ^ y) :
    EvalExpr cfg o fc fr m (.binary .exp a b) (.reverted (panicData 0x11)) :=
  EvalExpr.binaryPanic (p := .overflow) (by decide) (by decide) hb ha
    (by rw [hunch]; exact binop_exp_u256_overflow x y h2 hbig)

/-- `k ** b` with a number-literal base and a typed exponent (`10 ** decimals`). -/
theorem EvalExpr.expLitUint {fr fr1 : Frame} {m m1 : Machine} {b : Expr} {w : ABI.BitWidth} {y : ℕ} (k : ℕ)
    (hd : Option Nat) (hb : EvalExpr cfg o fc fr m b (.ok (.uint w y) fr1 m1)) (hunch : fr1.unchecked = false)
    (hy : y < 256) (hfit : k ^ y < 2 ^ 256) :
    EvalExpr cfg o fc fr m (.binary .exp (.lit (.number k none hd)) b) (.ok (u256Val (k ^ y)) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) hb (EvalExpr.numLit k hd)
    (by rw [hunch, Bool.not_false, binop_exp_lit_u256 k hd y w (Int.natCast_nonneg k) hy (by exact_mod_cast hfit), toNat_natCast_pow])

/-- `k ** j` on two number literals is exact. -/
theorem EvalExpr.expLitLit {fr : Frame} {m : Machine} (x y : ℕ) (hx hy : Option Nat) :
    EvalExpr cfg o fc fr m (.binary .exp (.lit (.number x none hx)) (.lit (.number y none hy)))
      (.ok (.literal ((x : Int) ^ y)) fr m) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit y hy) (EvalExpr.numLit x hx)
    (by rw [binop_exp_lit_lit _ x y hx hy (Int.natCast_nonneg y), Int.toNat_natCast])

/-! ## Mappings with other key types, storage struct fields, `delete` -/

/-- `x[k]` for a state variable `x : mapping(K => V)` with a value-type `V`: generic in the key and
    the loaded value. -/
theorem EvalExpr.mappingIndexScalar {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {k : Expr} {kv val : Value}
    {kt vt : Ty} {er' : Solm.EvaledStorageRef}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable) (hty : v.ty = .mapping kt vt)
    (hk : EvalExpr cfg o fc fr m k (.ok kv fr1 m1))
    (hidx : storageIndex cfg fc.types m1.evm m1.heap ⟨v.key, []⟩ (.mapping kt vt) kv = some (.ok (er', vt)))
    (hload : loadIfScalar cfg fc.types m1.evm er' vt = some val) :
    EvalExpr cfg o fc fr m (.index (.ident x) k) (.ok val fr1 m1) := by
  have hload0 : loadIfScalar cfg fc.types m.evm ⟨v.key, []⟩ v.ty =
      some (.storageRef ⟨v.key, []⟩ (.mapping kt vt)) := by
    rw [hty]; exact loadIfScalar_mapping ..
  exact EvalExpr.indexStorage (EvalExpr.stateVar hx hv hmut hload0) hk hidx hload

theorem EvalLValue.mappingIndex {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {k : Expr} {kv : Value}
    {kt vt : Ty} {er' : Solm.EvaledStorageRef}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable) (hty : v.ty = .mapping kt vt)
    (hk : EvalExpr cfg o fc fr m k (.ok kv fr1 m1))
    (hidx : storageIndex cfg fc.types m1.evm m1.heap ⟨v.key, []⟩ (.mapping kt vt) kv = some (.ok (er', vt))) :
    EvalLValue cfg o fc fr m (.index (.ident x) k) (.ok (.storage er' vt) fr1 m1) := by
  have hload0 : loadIfScalar cfg fc.types m.evm ⟨v.key, []⟩ v.ty =
      some (.storageRef ⟨v.key, []⟩ (.mapping kt vt)) := by
    rw [hty]; exact loadIfScalar_mapping ..
  exact EvalLValue.indexStorage (EvalExpr.stateVar hx hv hmut hload0) hk hidx

theorem EvalExpr.mappingU256U256 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {k : Expr} {n : ℕ}
    {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping u256Ty u256Ty) (hk : EvalExpr cfg o fc fr m k (.ok (u256Val n) fr1 m1))
    (hl : cfg.storage.layout (keyRef ⟨v.key, []⟩ (.int n)) m1.evm = some (uint256Loc slot)) :
    EvalExpr cfg o fc fr m (.index (.ident x) k) (.ok (u256Val (loadU256 m1 slot).toNat) fr1 m1) :=
  EvalExpr.mappingIndexScalar hx hv hmut hty hk (storageIndex_mapping_uint ..) (loadIfScalar_u256 hl)

theorem EvalLValue.mappingU256 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {k : Expr} {n : ℕ} {vt : Ty}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping u256Ty vt) (hk : EvalExpr cfg o fc fr m k (.ok (u256Val n) fr1 m1)) :
    EvalLValue cfg o fc fr m (.index (.ident x) k) (.ok (.storage (keyRef ⟨v.key, []⟩ (.int n)) vt) fr1 m1) :=
  EvalLValue.mappingIndex hx hv hmut hty hk (storageIndex_mapping_uint ..)

theorem EvalExpr.mappingBytes32U256 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {k : Expr}
    {bs : List UInt8} {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.fixedBytes ⟨31, by decide⟩) u256Ty)
    (hk : EvalExpr cfg o fc fr m k (.ok (.fixedBytes ⟨31, by decide⟩ bs) fr1 m1))
    (hl : cfg.storage.layout (keyRef ⟨v.key, []⟩ (.fixedBytes ⟨31, by decide⟩ bs)) m1.evm = some (uint256Loc slot)) :
    EvalExpr cfg o fc fr m (.index (.ident x) k) (.ok (u256Val (loadU256 m1 slot).toNat) fr1 m1) :=
  EvalExpr.mappingIndexScalar hx hv hmut hty hk (storageIndex_mapping_bytes32 ..) (loadIfScalar_u256 hl)

theorem EvalLValue.mappingBytes32 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {k : Expr}
    {bs : List UInt8} {vt : Ty}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.fixedBytes ⟨31, by decide⟩) vt)
    (hk : EvalExpr cfg o fc fr m k (.ok (.fixedBytes ⟨31, by decide⟩ bs) fr1 m1)) :
    EvalLValue cfg o fc fr m (.index (.ident x) k)
      (.ok (.storage (keyRef ⟨v.key, []⟩ (.fixedBytes ⟨31, by decide⟩ bs)) vt) fr1 m1) :=
  EvalLValue.mappingIndex hx hv hmut hty hk (storageIndex_mapping_bytes32 ..)

/-- `x[k]` for `x : mapping(address => S)` with a struct `S`: a storage reference to the struct. -/
theorem EvalExpr.mappingAddrStruct {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {k : Expr}
    {a : EVM.Address} {q : Option Ident} {n : Ident}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.address false) (.user q n)) (hk : EvalExpr cfg o fc fr m k (.ok (.address a) fr1 m1))
    (hnv : isValueType fc.types (.user q n) = false) :
    EvalExpr cfg o fc fr m (.index (.ident x) k)
      (.ok (.storageRef (keyRef ⟨v.key, []⟩ (.address a)) (.user q n)) fr1 m1) :=
  EvalExpr.mappingIndexScalar hx hv hmut hty hk (storageIndex_mapping_address ..) (loadIfScalar_ref hnv)

/-- Any storage reference indexed again (`x[k1][k2]`, `arr[i].f[k]`): generic step. -/
theorem EvalExpr.indexStorageScalar {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {e i : Expr} {er er' : Solm.EvaledStorageRef}
    {ty ty' : Ty} {iv val : Value}
    (he : EvalExpr cfg o fc fr m e (.ok (.storageRef er ty) fr1 m1)) (hi : EvalExpr cfg o fc fr1 m1 i (.ok iv fr2 m2))
    (hidx : storageIndex cfg fc.types m2.evm m2.heap er ty iv = some (.ok (er', ty')))
    (hload : loadIfScalar cfg fc.types m2.evm er' ty' = some val) :
    EvalExpr cfg o fc fr m (.index e i) (.ok val fr2 m2) :=
  EvalExpr.indexStorage he hi hidx hload

/-! ## Struct fields in storage -/

/-- `e.f` for a storage struct reference `e`. -/
theorem EvalExpr.storageFieldRead {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {f f' : Ident} {er : Solm.EvaledStorageRef}
    {q : Option Ident} {n : Ident} {s : StructInfo} {fty : Ty} {val : Value}
    (hdm : directMember fc fr e = false) (hf : f ≠ "length")
    (he : EvalExpr cfg o fc fr m e (.ok (.storageRef er (.user q n)) fr1 m1))
    (hs : fc.types.struct? q n = some s) (hfind : s.fields.find? (·.2 == f) = some (fty, f'))
    (hload : loadIfScalar cfg fc.types m1.evm (fieldRef er f) fty = some val) :
    EvalExpr cfg o fc fr m (.member e f) (.ok val fr1 m1) :=
  EvalExpr.memberField hdm hf he (storageField_of hs hfind) hload

theorem EvalExpr.storageFieldU256 {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {f f' : Ident} {er : Solm.EvaledStorageRef}
    {q : Option Ident} {n : Ident} {s : StructInfo} {slot : UInt256}
    (hdm : directMember fc fr e = false) (hf : f ≠ "length")
    (he : EvalExpr cfg o fc fr m e (.ok (.storageRef er (.user q n)) fr1 m1))
    (hs : fc.types.struct? q n = some s) (hfind : s.fields.find? (·.2 == f) = some (u256Ty, f'))
    (hl : cfg.storage.layout (fieldRef er f) m1.evm = some (uint256Loc slot)) :
    EvalExpr cfg o fc fr m (.member e f) (.ok (u256Val (loadU256 m1 slot).toNat) fr1 m1) :=
  EvalExpr.storageFieldRead hdm hf he hs hfind (loadIfScalar_u256 hl)

/-- `e.f` as an lvalue. -/
theorem EvalLValue.storageField {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {f f' : Ident} {er : Solm.EvaledStorageRef}
    {q : Option Ident} {n : Ident} {s : StructInfo} {fty : Ty}
    (he : EvalExpr cfg o fc fr m e (.ok (.storageRef er (.user q n)) fr1 m1))
    (hs : fc.types.struct? q n = some s) (hfind : s.fields.find? (·.2 == f) = some (fty, f')) :
    EvalLValue cfg o fc fr m (.member e f) (.ok (.storage (fieldRef er f) fty) fr1 m1) :=
  EvalLValue.memberStorage he (storageField_of hs hfind)

theorem ExecStmt.deleteStorageU256 {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hlv : EvalLValue cfg o fc fr m e (.ok (.storage er u256Ty) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (uint256Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.unary .delete e)) (.normal fr1 (storeU256 m1 slot ⟨0⟩)) :=
  ExecStmt.exprStmt (EvalExpr.deleteStorage hlv (clearStorage_u256 1023 hl))

theorem ExecStmt.deleteStorageAddress {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {p : Bool} (hlv : EvalLValue cfg o fc fr m e (.ok (.storage er (.address p)) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (addressOffset0Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.unary .delete e))
      (.normal fr1 (storeU256 m1 slot (setAddressOffset0Word (loadU256 m1 slot) ⟨0⟩))) :=
  ExecStmt.exprStmt (EvalExpr.deleteStorage hlv (clearStorage_address 1023 p hl))

theorem ExecStmt.deleteStorageBool {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hlv : EvalLValue cfg o fc fr m e (.ok (.storage er .bool) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (boolOffset0Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.unary .delete e))
      (.normal fr1 (storeU256 m1 slot (UInt256.land (loadU256 m1 slot) (UInt256.lnot ⟨255⟩)))) :=
  ExecStmt.exprStmt (EvalExpr.deleteStorage hlv (clearStorage_bool 1023 hl))

/-! ## Literal right-hand sides, unchecked increments, `emit` of value-type events -/

/-- `x = k` into a `uint256` storage slot, `k` a number literal. -/
theorem EvalExpr.assignStorageU256Lit {fr fr1 : Frame} {m m1 : Machine} {lhs : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (k : ℕ) (hd : Option Nat) (hk : k < 2 ^ 256)
    (hlv : EvalLValue cfg o fc fr m lhs (.ok (.storage er u256Ty) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (uint256Loc slot)) :
    EvalExpr cfg o fc fr m (.assign .assign lhs (.lit (.number k none hd)))
      (.ok (.literal k hd) fr1 (storeU256 m1 slot (UInt256.ofNat k))) :=
  EvalExpr.assignPlain hlv.not_tuple (EvalExpr.numLit k hd) hlv (assign_storage_u256_lit hl k hd hk)

theorem ExecStmt.assignStorageU256Lit {fr fr1 : Frame} {m m1 : Machine} {lhs : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (k : ℕ) (hd : Option Nat) (hk : k < 2 ^ 256)
    (hlv : EvalLValue cfg o fc fr m lhs (.ok (.storage er u256Ty) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (uint256Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign lhs (.lit (.number k none hd))))
      (.normal fr1 (storeU256 m1 slot (UInt256.ofNat k))) :=
  ExecStmt.exprStmt (EvalExpr.assignStorageU256Lit k hd hk hlv hl)

/-- `x = k` for a `uint256` local `x`, `k` a number literal. -/
theorem ExecStmt.assignLocalU256Lit {fr : Frame} {m : Machine} {x : Ident} (l : Local) (k : ℕ) (hd : Option Nat)
    (hx : fr.get? x = some l) (hty : l.ty = u256Ty) (hk : k < 2 ^ 256) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.ident x) (.lit (.number k none hd))))
      (.normal (fr.setVal x (u256Val k)) m) :=
  ExecStmt.exprStmt (EvalExpr.assignPlain rfl (EvalExpr.numLit k hd) (EvalLValue.local (m := m) hx)
    (assign_local_u256_lit l hx hty k hd hk))

/-- `uint256 x = k;` -/
theorem ExecStmt.varDeclU256Lit {fr : Frame} {m : Machine} {x : Ident} {loc : Option DataLoc} (k : ℕ) (hd : Option Nat)
    (hk : k < 2 ^ 256) :
    ExecStmt cfg o fc fr m (.varDecl u256Ty loc x (some (.lit (.number k none hd))))
      (.normal (fr.bind x u256Ty loc (u256Val k)) m) := by
  refine ExecStmt.varDecl (EvalExpr.numLit k hd) ?_
  simp [declare, coerce_literal_u256 cfg fc.types m k hd loc (Int.natCast_nonneg k) (by exact_mod_cast hk)]

theorem EvalExpr.postIncLocalU256Unchecked {fr : Frame} {m : Machine} {x : Ident} {n : ℕ} (l : Local)
    (hx : fr.get? x = some l) (hty : l.ty = u256Ty) (hval : l.val = u256Val n) (hunch : fr.unchecked = true) :
    EvalExpr cfg o fc fr m (.unary .postInc (.ident x)) (.ok (u256Val n) (fr.setVal x (u256Val ((n + 1) % 2 ^ 256))) m) := by
  have h := EvalExpr.incDec (cfg := cfg) (o := o) (fc := fc) (op := .postInc) (cur := u256Val n)
    (nv := u256Val ((n + 1) % 2 ^ 256)) rfl (EvalLValue.local (m := m) hx) (by rw [readLValue_local hx, hval])
    (by rw [hunch]; exact binop_add_u256_lit1_unchecked n) (assign_local_u256 l hx hty _)
  simpa [isPrefix] using h

theorem ExecPost.postIncLocalU256Unchecked {fr : Frame} {m : Machine} {x : Ident} {n : ℕ} (l : Local)
    (hx : fr.get? x = Option.some l) (hty : l.ty = u256Ty) (hval : l.val = u256Val n) (hunch : fr.unchecked = true) :
    ExecPost cfg o fc fr m (Option.some (.unary .postInc (.ident x)))
      (.ok () (fr.setVal x (u256Val ((n + 1) % 2 ^ 256))) m) :=
  ExecPost.some (EvalExpr.postIncLocalU256Unchecked l hx hty hval hunch)

/-- `emit E(args)` for an event whose parameters are all value types (see `mkLogEntry_static`). -/
theorem ExecStmt.emitStatic {fr fr1 : Frame} {m m1 : Machine} {ev : Ident} {ei : EventInfo} {es : List Expr}
    (xs : List LogArg) (hev : fc.eventsNamed ev = [ei]) (hparams : ei.decl.params = xs.map LogArg.param)
    (htys : ei.sig.paramTypes = xs.map (·.val.abiTy)) (hanon : ei.decl.anonymous = false) (hwf : ∀ x ∈ xs, x.val.wf)
    (hargs : EvalExprs cfg o fc fr m es (.ok (xs.map (·.val.solValue)) fr1 m1)) :
    ExecStmt cfg o fc fr m (.emit (.ident ev) (.positional es))
      (.normal fr1 (m1.pushLog
        { address := m1.this
          topics := (hashWord ei.sigStr.toUTF8 :: (xs.filter (·.indexed)).map (·.val.word)).toArray
          data := ((xs.filter (!·.indexed)).flatMap (·.val.bytes)).toByteArray })) := by
  have habi : abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) (xs.map (·.val.solValue)) =
      some (.ok (xs.map (·.val.value), m1)) := by
    rw [hparams, List.map_map]
    exact abiArgs_static ..
  exact ExecStmt.emit (by rw [hev]; rfl) hargs
    (by rw [hev]; exact resolveEvent_single (eventFits_static _ _ ei xs hparams)) habi
    (mkLogEntry_static m1.this ei xs hparams htys hanon hwf)

/-! ## Environment reads, `assert`, `revert("msg")`, tuples, multiple returns, `bool` mappings -/

theorem EvalExpr.msgValue {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.member (.ident "msg") "value") (.ok (u256Val m.evm.executionEnv.weiValue.toNat) fr m) :=
  EvalExpr.envMember rfl (envMember_value m)

theorem EvalExpr.blockTimestamp {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.member (.ident "block") "timestamp") (.ok (wordNat m.evm.executionEnv.header.timestamp) fr m) :=
  EvalExpr.envMember rfl rfl

theorem EvalExpr.blockNumber {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.member (.ident "block") "number") (.ok (wordNat m.evm.executionEnv.header.number) fr m) :=
  EvalExpr.envMember rfl rfl

theorem EvalExpr.chainId {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.member (.ident "block") "chainid") (.ok (wordNat Ethereum.chainId) fr m) :=
  EvalExpr.envMember rfl rfl

theorem EvalExpr.txOrigin {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.member (.ident "tx") "origin") (.ok (.address m.evm.executionEnv.sender) fr m) :=
  EvalExpr.envMember rfl rfl

/-- `address(this)`. -/
theorem EvalExpr.thisAddress {fr : Frame} {m : Machine} (p : Bool) :
    EvalExpr cfg o fc fr m (.call (.typeExpr (.address p)) [] (.positional [.this])) (.ok (.address m.this) fr m) :=
  EvalExpr.convertPlain EvalExpr.thisRef (explicitConv_contract_address _ _ _ _ _)

/-! ## `assert`, `revert("msg")`, `require(c, CustomError())` -/

theorem ExecStmt.assertTrue {fr fr1 : Frame} {m m1 : Machine} {c : Expr}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1)) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident "assert") [] (.positional [c]))) (.normal fr1 m1) :=
  ExecStmt.exprStmt (EvalExpr.assertTrue hc)

theorem ExecStmt.assertFalse {fr fr1 : Frame} {m m1 : Machine} {c : Expr}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool false) fr1 m1)) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident "assert") [] (.positional [c]))) (.reverted (panicData 0x01)) :=
  ExecStmt.exprStmtRevert (EvalExpr.assertFalse hc)

theorem ExecStmt.revertMsg {fr : Frame} {m : Machine} (s : String) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident "revert") [] (.positional [.lit (.str s)])))
      (.reverted (errorStringData s.toUTF8)) :=
  ExecStmt.exprStmtRevert (EvalExpr.revertMsg (EvalExpr.lit rfl) rfl)

/-! ## Tuples and multiple return values -/

theorem EvalExpr.tupleTwo {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {e1 e2 : Expr} {v1 v2 : Value}
    (h1 : EvalExpr cfg o fc fr m e1 (.ok v1 fr1 m1)) (h2 : EvalExpr cfg o fc fr1 m1 e2 (.ok v2 fr2 m2)) :
    EvalExpr cfg o fc fr m (.tuple [some e1, some e2]) (.ok (.tuple [v1, v2]) fr2 m2) :=
  EvalExpr.tuple rfl (EvalExprs.two h1 h2)

/-- `return (e1, e2)` into two `uint256` return slots. -/
theorem ExecStmt.returnTwoU256 {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {r1 r2 : Ident} {n1 n2 : ℕ} (l1 l2 : Local)
    (hret : fr.retVars = [r1, r2]) (he : EvalExpr cfg o fc fr m e (.ok (.tuple [u256Val n1, u256Val n2]) fr1 m1))
    (hr1 : fr1.get? r1 = some l1) (ht1 : l1.ty = u256Ty)
    (hr2 : (fr1.setVal r1 (u256Val n1)).get? r2 = some l2) (ht2 : l2.ty = u256Ty) :
    ExecStmt cfg o fc fr m (.return (some e))
      (.returned ((fr1.setVal r1 (u256Val n1)).setVal r2 (u256Val n2)) m1) := by
  refine ExecStmt.returnMulti (by simp [hret]) he ?_
  rw [hret]
  exact AssignTuple.cons (EvalLValue.local (m := m1) hr1) (assign_local_u256 l1 hr1 ht1 n1)
    (AssignTuple.cons (EvalLValue.local (m := m1) hr2) (assign_local_u256 l2 hr2 ht2 n2) AssignTuple.nil)

/-- `x[k]` for `x : mapping(address => bool)`. -/
theorem EvalExpr.mappingAddrBool {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {k : Expr} {a : EVM.Address}
    {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.address false) .bool) (hk : EvalExpr cfg o fc fr m k (.ok (.address a) fr1 m1))
    (hl : cfg.storage.layout (keyRef ⟨v.key, []⟩ (.address a)) m1.evm = some (boolOffset0Loc slot)) :
    EvalExpr cfg o fc fr m (.index (.ident x) k)
      (.ok (.bool (!((UInt256.land (loadU256 m1 slot) ⟨255⟩).val == 0))) fr1 m1) :=
  EvalExpr.mappingIndexScalar hx hv hmut hty hk (storageIndex_mapping_address ..) (loadIfScalar_bool hl)

/-! ## `int256` -/

/-! ### Builders -/

theorem EvalExpr.addS256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : Int}
    (hb : EvalExpr cfg o fc fr m b (.ok (s256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (s256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hlo : -2 ^ 255 ≤ x + y) (hhi : x + y < 2 ^ 255) :
    EvalExpr cfg o fc fr m (.binary .add a b) (.ok (s256Val (x + y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_add_s256 x y hlo hhi)

theorem EvalExpr.addS256Overflow {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : Int}
    (hb : EvalExpr cfg o fc fr m b (.ok (s256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (s256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (h : ¬ (-2 ^ 255 ≤ x + y ∧ x + y < 2 ^ 255)) :
    EvalExpr cfg o fc fr m (.binary .add a b) (.reverted (panicData 0x11)) :=
  EvalExpr.binaryPanic (p := .overflow) (by decide) (by decide) hb ha
    (by rw [hunch]; exact binop_add_s256_overflow x y h)

theorem EvalExpr.subS256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : Int}
    (hb : EvalExpr cfg o fc fr m b (.ok (s256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (s256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hlo : -2 ^ 255 ≤ x - y) (hhi : x - y < 2 ^ 255) :
    EvalExpr cfg o fc fr m (.binary .sub a b) (.ok (s256Val (x - y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_sub_s256 x y hlo hhi)

theorem EvalExpr.mulS256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : Int}
    (hb : EvalExpr cfg o fc fr m b (.ok (s256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (s256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hlo : -2 ^ 255 ≤ x * y) (hhi : x * y < 2 ^ 255) :
    EvalExpr cfg o fc fr m (.binary .mul a b) (.ok (s256Val (x * y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_mul_s256 x y hlo hhi)

theorem EvalExpr.divS256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : Int}
    (hb : EvalExpr cfg o fc fr m b (.ok (s256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (s256Val x) fr2 m2))
    (hunch : fr2.unchecked = false) (hy : y ≠ 0) (hlo : -2 ^ 255 ≤ Int.tdiv x y) (hhi : Int.tdiv x y < 2 ^ 255) :
    EvalExpr cfg o fc fr m (.binary .div a b) (.ok (s256Val (Int.tdiv x y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_div_s256 x y hy hlo hhi)

theorem EvalExpr.ltS256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : Int}
    (hb : EvalExpr cfg o fc fr m b (.ok (s256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (s256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .lt a b) (.ok (.bool (decide (x < y))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_lt_s256 _ x y)

theorem EvalExpr.geS256 {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {x y : Int}
    (hb : EvalExpr cfg o fc fr m b (.ok (s256Val y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (s256Val x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .ge a b) (.ok (.bool (decide (x ≥ y))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_ge_s256 _ x y)

theorem EvalExpr.geS256Lit {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {x : Int} (k : ℕ) (hd : Option Nat)
    (ha : EvalExpr cfg o fc fr m a (.ok (s256Val x) fr1 m1)) (hk : k < 2 ^ 255) :
    EvalExpr cfg o fc fr m (.binary .ge a (.lit (.number k none hd))) (.ok (.bool (decide (x ≥ k))) fr1 m1) :=
  EvalExpr.binary (by decide) (by decide) (EvalExpr.numLit k hd) ha
    (by rw [binop_cmp_s256_lit _ .ge rfl x k hd (by omega) (by exact_mod_cast hk)]; rfl)

theorem EvalExpr.negS256 {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {x : Int}
    (he : EvalExpr cfg o fc fr m e (.ok (s256Val x) fr1 m1)) (hunch : fr1.unchecked = false)
    (hlo : -2 ^ 255 ≤ -x) (hhi : -x < 2 ^ 255) :
    EvalExpr cfg o fc fr m (.unary .neg e) (.ok (s256Val (-x)) fr1 m1) :=
  EvalExpr.unary he (by rw [hunch]; exact unop_neg_s256 x hlo hhi) (by decide) (by decide)

/-- `-k` on a number literal. -/
theorem EvalExpr.negLit {fr : Frame} {m : Machine} (k : ℕ) (hd : Option Nat) :
    EvalExpr cfg o fc fr m (.unary .neg (.lit (.number k none hd))) (.ok (.literal (-(k : Int))) fr m) :=
  EvalExpr.unary (EvalExpr.numLit k hd) (unop_neg_lit _ k hd) (by decide) (by decide)

/-- `int256(x)`. -/
theorem EvalExpr.convertU256S256 {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {n : ℕ}
    (ha : EvalExpr cfg o fc fr m a (.ok (u256Val n) fr1 m1)) :
    EvalExpr cfg o fc fr m (.call (.typeExpr s256Ty) [] (.positional [a])) (.ok (s256Val (IntTy.wrap s256IntTy n)) fr1 m1) :=
  EvalExpr.convertPlain ha (explicitConv_u256_s256 _ _ n)

/-- `uint256(y)`. -/
theorem EvalExpr.convertS256U256 {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {i : Int}
    (ha : EvalExpr cfg o fc fr m a (.ok (s256Val i) fr1 m1)) :
    EvalExpr cfg o fc fr m (.call (.typeExpr u256Ty) [] (.positional [a])) (.ok (u256Val (IntTy.toWord u256IntTy i)) fr1 m1) :=
  EvalExpr.convertPlain ha (explicitConv_s256_u256 _ _ i)

/-- A state variable `x : int256`. -/
theorem EvalExpr.stateS256 {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable) (hty : v.ty = s256Ty)
    (hl : cfg.storage.layout ⟨v.key, []⟩ m.evm = some (int256Loc slot)) :
    EvalExpr cfg o fc fr m (.ident x) (.ok (s256Val (s256OfWord (loadU256 m slot))) fr m) :=
  EvalExpr.stateVar hx hv hmut (by rw [hty]; exact loadIfScalar_s256 hl)

theorem EvalExpr.assignStorageS256 {fr fr1 : Frame} {m m1 : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {i : Int}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (s256Val i) fr1 m1))
    (hlv : EvalLValue cfg o fc fr1 m1 lhs (.ok (.storage er s256Ty) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (int256Loc slot)) :
    EvalExpr cfg o fc fr m (.assign .assign lhs rhs) (.ok (s256Val i) fr1 (storeU256 m1 slot (EVM.wordOfInt i))) :=
  EvalExpr.assignPlain hlv.not_tuple hrhs hlv (assign_storage_s256 hl i)

theorem ExecStmt.assignStorageS256 {fr fr1 : Frame} {m m1 : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {i : Int}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (s256Val i) fr1 m1))
    (hlv : EvalLValue cfg o fc fr1 m1 lhs (.ok (.storage er s256Ty) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (int256Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign lhs rhs)) (.normal fr1 (storeU256 m1 slot (EVM.wordOfInt i))) :=
  ExecStmt.exprStmt (EvalExpr.assignStorageS256 hrhs hlv hl)

theorem ExecStmt.varDeclS256 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {e : Expr} {i : Int} {loc : Option DataLoc}
    (he : EvalExpr cfg o fc fr m e (.ok (s256Val i) fr1 m1)) :
    ExecStmt cfg o fc fr m (.varDecl s256Ty loc x (some e)) (.normal (fr1.bind x s256Ty loc (s256Val i)) m1) := by
  refine ExecStmt.varDecl he ?_
  simp [declare, coerce, implicitConv]
  try rfl

/-! ## `ecrecover`, `try`/`catch`, `new` -/

/-- `ecrecover(h, v, r, s)` with the precompile call made (its `Θ` result is `hcall`). -/
theorem EvalExpr.ecrecoverPlain {fr fr1 : Frame} {m m1 m3 : Machine} {eh ev er es : Expr} {hb rb sb : List UInt8} {n : ℕ}
    {out : ByteArray}
    (hargs : EvalExprs cfg o fc fr m [eh, ev, er, es]
      (.ok [.fixedBytes ⟨31, by decide⟩ hb, .uint ⟨8, by decide⟩ n, .fixedBytes ⟨31, by decide⟩ rb,
        .fixedBytes ⟨31, by decide⟩ sb] fr1 m1))
    (hh : hb.length = 32) (hr : rb.length = 32) (hs : sb.length = 32) (hn : n < 256)
    (hcall : callViaEVM o m1 (EVM.address 1) 0 (hb ++ EVM.Word.toBytesBE (EVM.word n) ++ rb ++ sb).toByteArray false
      (calleeGas o m1 none 0) (true, m3, out)) :
    EvalExpr cfg o fc fr m (.call (.ident "ecrecover") [] (.positional [eh, ev, er, es])) (.ok (ecrecoverResult out) fr1 m3) :=
  EvalExpr.ecrecover hargs (abiArgs_ecrecover ..) (encodeABIValues_ecrecover hb rb sb n hh hr hs hn) hcall

theorem bindTryParams_nil (fr : Frame) (m : Machine) : bindTryParams cfg fc.types fr m [] [] = some (.ok (fr, m)) := by
  simp [bindTryParams]

/-- The tried call succeeds; no `returns` clause, no call options. -/
theorem ExecStmt.tryCallOkNoRets {fr fr1 fr4 : Frame} {m m1 m4 m5 m6 : Machine} {recv : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {body : List Stmt}
    {cs : List CatchClause} {r : ExecResult}
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
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out ≠ none)
    (hbody : ExecBlock cfg o fc fr4 m6 body r) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.member recv f) [] (.positional es)) [] body cs) (exitBlock fr r) := by
  have hrets : tryRets cfg fc.types m6 [] rtys out = some ([], m6) := by
    simp only [tryRets, List.isEmpty_nil, if_true]
    cases h : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out
    · exact absurd h hdec
    · rfl
  exact ExecStmt.tryCallOk hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall
    hrets (bindTryParams_nil _ _) hbody

/-- The tried call reverts and a parameterless generic `catch { … }` handles it. -/
theorem ExecStmt.tryCallCaughtGeneric {fr fr1 fr4 : Frame} {m m1 m4 m5 m6 : Machine} {recv : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {ps : List Param}
    {body cbody : List Stmt} {r : ExecResult}
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
      (false, m6, out))
    (hcatch : ExecBlock cfg o fc fr4 m6 cbody r) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.member recv f) [] (.positional es)) ps body [.mk none [] cbody])
      (exitBlock fr r) :=
  ExecStmt.tryCallCaught hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall
    (selectCatch_generic_noParams cfg m6 cbody out) (bindTryParams_nil _ _) hcatch

/-! ## `new C(args)` -/

theorem EvalExpr.newContractPlain {fr fr3 : Frame} {m m3 m4 m5 : Machine} {ty : Ty} {es : List Expr} {c : Ident}
    {tys : List Ty} {vs : List Value} {svs : List ABI.ABIValue} {a : EVM.Address} {out : EVM.Bytes}
    (hnew : newContract? fc ty = some (c, tys)) (hargs : EvalExprs cfg o fc fr m es (.ok vs fr3 m3))
    (habi : abiArgs cfg fc.types m3 tys vs = some (.ok (svs, m4)))
    (hcreate : newViaEVM cfg o m4 c 0 svs none (a, m5, true, out)) :
    EvalExpr cfg o fc fr m (.call (.new ty) [] (.positional es)) (.ok (.contract c a) fr3 m5) :=
  EvalExpr.newContract hnew EvalValueOpt.none EvalSaltOpt.none rfl hargs habi hcreate

theorem EvalExpr.newContractPlainFailed {fr fr3 : Frame} {m m3 m4 m5 : Machine} {ty : Ty} {es : List Expr} {c : Ident}
    {tys : List Ty} {vs : List Value} {svs : List ABI.ABIValue} {a : EVM.Address} {out : EVM.Bytes}
    (hnew : newContract? fc ty = some (c, tys)) (hargs : EvalExprs cfg o fc fr m es (.ok vs fr3 m3))
    (habi : abiArgs cfg fc.types m3 tys vs = some (.ok (svs, m4)))
    (hcreate : newViaEVM cfg o m4 c 0 svs none (a, m5, false, out)) :
    EvalExpr cfg o fc fr m (.call (.new ty) [] (.positional es)) (.reverted out) :=
  EvalExpr.newContractFailed hnew EvalValueOpt.none EvalSaltOpt.none rfl hargs habi hcreate

/-! ## State variables of value types, `address`/`bool` slot assignments -/

theorem assign_storage_address {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er m.evm = some (addressOffset0Loc slot)) (a : EVM.Address) :
    assign cfg env fr m (.storage er (.address false)) (.address a) =
      some (.ok (fr, storeU256 m slot (setAddressOffset0Word (loadU256 m slot) (UInt256.ofNat a.toNat)))) := by
  simp [assign, fuelDefault, writeStorageDeep_address 1023 (writeScalar_address' hl a)]

theorem assign_storage_bool_true {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er m.evm = some (boolOffset0Loc slot)) :
    assign cfg env fr m (.storage er .bool) (.bool true) =
      some (.ok (fr, storeU256 m slot (UInt256.lor (UInt256.land (loadU256 m slot) (UInt256.lnot ⟨255⟩)) ⟨1⟩))) := by
  simp [assign, fuelDefault, writeStorageDeep_bool 1023 (writeScalar_bool_true hl)]

theorem assign_storage_bool_false {cfg : Config} {env : TypeEnv} {fr : Frame} {m : Machine} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hl : cfg.storage.layout er m.evm = some (boolOffset0Loc slot)) :
    assign cfg env fr m (.storage er .bool) (.bool false) =
      some (.ok (fr, storeU256 m slot (UInt256.land (loadU256 m slot) (UInt256.lnot ⟨255⟩)))) := by
  simp [assign, fuelDefault, writeStorageDeep_bool 1023 (writeScalar_bool_false hl)]

/-! ### Builders -/

theorem EvalExpr.stateU256 {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable) (hty : v.ty = u256Ty)
    (hl : cfg.storage.layout ⟨v.key, []⟩ m.evm = some (uint256Loc slot)) :
    EvalExpr cfg o fc fr m (.ident x) (.ok (u256Val (loadU256 m slot).toNat) fr m) :=
  EvalExpr.stateVar hx hv hmut (by rw [hty]; exact loadIfScalar_u256 hl)

theorem EvalExpr.stateAddress {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable) (hty : v.ty = .address false)
    (hl : cfg.storage.layout ⟨v.key, []⟩ m.evm = some (addressOffset0Loc slot)) :
    EvalExpr cfg o fc fr m (.ident x)
      (.ok (.address (AccountAddress.ofNat (UInt256.land (loadU256 m slot) solcAddrMask).toNat)) fr m) :=
  EvalExpr.stateVar hx hv hmut (by rw [hty]; exact loadIfScalar_address hl)

theorem EvalExpr.stateBool {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {slot : UInt256}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable) (hty : v.ty = .bool)
    (hl : cfg.storage.layout ⟨v.key, []⟩ m.evm = some (boolOffset0Loc slot)) :
    EvalExpr cfg o fc fr m (.ident x) (.ok (.bool (!((UInt256.land (loadU256 m slot) ⟨255⟩).val == 0))) fr m) :=
  EvalExpr.stateVar hx hv hmut (by rw [hty]; exact loadIfScalar_bool hl)

/-- A mutable state variable of type `ty` as an lvalue. -/
theorem EvalLValue.stateVarTy {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {ty : Ty}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .mutable) (hty : v.ty = ty) :
    EvalLValue cfg o fc fr m (.ident x) (.ok (.storage ⟨v.key, []⟩ ty) fr m) :=
  hty ▸ EvalLValue.stateVar hx hv hmut

theorem EvalExpr.assignStorageAddress {fr fr1 : Frame} {m m1 : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {a : EVM.Address}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.address a) fr1 m1))
    (hlv : EvalLValue cfg o fc fr1 m1 lhs (.ok (.storage er (.address false)) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (addressOffset0Loc slot)) :
    EvalExpr cfg o fc fr m (.assign .assign lhs rhs)
      (.ok (.address a) fr1 (storeU256 m1 slot (setAddressOffset0Word (loadU256 m1 slot) (UInt256.ofNat a.toNat)))) :=
  EvalExpr.assignPlain hlv.not_tuple hrhs hlv (assign_storage_address hl a)

theorem ExecStmt.assignStorageAddress {fr fr1 : Frame} {m m1 : Machine} {lhs rhs : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} {a : EVM.Address}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.address a) fr1 m1))
    (hlv : EvalLValue cfg o fc fr1 m1 lhs (.ok (.storage er (.address false)) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (addressOffset0Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign lhs rhs))
      (.normal fr1 (storeU256 m1 slot (setAddressOffset0Word (loadU256 m1 slot) (UInt256.ofNat a.toNat)))) :=
  ExecStmt.exprStmt (EvalExpr.assignStorageAddress hrhs hlv hl)

theorem ExecStmt.assignStorageBoolTrue {fr fr1 : Frame} {m m1 : Machine} {lhs : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hlv : EvalLValue cfg o fc fr m lhs (.ok (.storage er .bool) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (boolOffset0Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign lhs (.lit (.bool true))))
      (.normal fr1 (storeU256 m1 slot (UInt256.lor (UInt256.land (loadU256 m1 slot) (UInt256.lnot ⟨255⟩)) ⟨1⟩))) :=
  ExecStmt.exprStmt (EvalExpr.assignPlain hlv.not_tuple (EvalExpr.boolLit true) hlv (assign_storage_bool_true hl))

theorem ExecStmt.assignStorageBoolFalse {fr fr1 : Frame} {m m1 : Machine} {lhs : Expr} {er : Solm.EvaledStorageRef}
    {slot : UInt256} (hlv : EvalLValue cfg o fc fr m lhs (.ok (.storage er .bool) fr1 m1))
    (hl : cfg.storage.layout er m1.evm = some (boolOffset0Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign lhs (.lit (.bool false))))
      (.normal fr1 (storeU256 m1 slot (UInt256.land (loadU256 m1 slot) (UInt256.lnot ⟨255⟩)))) :=
  ExecStmt.exprStmt (EvalExpr.assignPlain hlv.not_tuple (EvalExpr.boolLit false) hlv (assign_storage_bool_false hl))

/-! ## Environment reads through a rewritten machine -/

/-- `msg.sender` with the source spelled as the caller likes (e.g. through a chain of stores). -/
theorem EvalExpr.msgSenderEq {fr : Frame} {m : Machine} {a : EVM.Address} (h : m.evm.executionEnv.source = a) :
    EvalExpr cfg o fc fr m (.member (.ident "msg") "sender") (.ok (.address a) fr m) :=
  h ▸ EvalExpr.msgSender

theorem EvalExpr.msgValueEq {fr : Frame} {m : Machine} {n : ℕ} (h : m.evm.executionEnv.weiValue.toNat = n) :
    EvalExpr cfg o fc fr m (.member (.ident "msg") "value") (.ok (u256Val n) fr m) :=
  h ▸ EvalExpr.msgValue

theorem EvalExpr.blockTimestampEq {fr : Frame} {m : Machine} {n : ℕ}
    (h : (EVM.Word.ofNat m.evm.executionEnv.header.timestamp).toNat = n) :
    EvalExpr cfg o fc fr m (.member (.ident "block") "timestamp") (.ok (u256Val n) fr m) :=
  h ▸ EvalExpr.blockTimestamp

/-! ## `try`/`catch` with returns and typed clauses, call options, `abi.decode` -/

/-- `try recv.f(args) returns (T x) { … }`, the call succeeding with one value-type return. -/
theorem ExecStmt.tryCallOkOneRet {fr fr1 fr4 fr5 : Frame} {m m1 m4 m5 m6 m8 : Machine} {recv : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {body : List Stmt}
    {cs : List CatchClause} {r : ExecResult} {p : Param} {x : Ident} {sv : ABI.ABIValue} {v : Value}
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
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some [sv])
    (hof : ofAbi fc.types fuelDefault p.ty sv m6.heap = some (v, m6.heap))
    (hname : p.name = some x)
    (hdecl : declare cfg fc.types fr4 m6 p.ty (some (p.loc.getD .memory)) x (some v) = some (.ok (fr5, m8)))
    (hbody : ExecBlock cfg o fc fr5 m8 body r) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.member recv f) [] (.positional es)) [p] body cs) (exitBlock fr r) :=
  ExecStmt.tryCallOk hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall
    (tryRets_single hdec hof) (bindTryParams_single hname hdecl) hbody

/-- The tried call reverts and a typed or parameterised clause is selected (`hsel`). -/
theorem ExecStmt.tryCallCaughtSelected {fr fr1 fr4 fr5 : Frame} {m m1 m4 m5 m6 m7 m8 : Machine} {recv : Expr}
    {f : Ident} {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {ps : List Param}
    {body : List Stmt} {cs : List CatchClause} {cc : CatchClause} {cvs : List Value} {r : ExecResult}
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
      (false, m6, out))
    (hsel : selectCatch cfg m6 cs out = some (cc, cvs, m7))
    (hbind : bindTryParams cfg fc.types fr4 m7 (catchParams cc) cvs = some (.ok (fr5, m8)))
    (hcatch : ExecBlock cfg o fc fr5 m8 (catchBody cc) r) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.member recv f) [] (.positional es)) ps body cs) (exitBlock fr r) :=
  ExecStmt.tryCallCaught hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall
    hsel hbind hcatch

theorem EvalValueOpt.u256 {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {n : ℕ}
    (he : EvalExpr cfg o fc fr m e (.ok (u256Val n) fr1 m1)) : EvalValueOpt cfg o fc fr m (Option.some e) (.ok n fr1 m1) :=
  EvalValueOpt.some he rfl

theorem EvalSaltOpt.bytes32 {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {bs : List UInt8}
    (he : EvalExpr cfg o fc fr m e (.ok (.fixedBytes ⟨31, by decide⟩ bs) fr1 m1)) :
    EvalSaltOpt cfg o fc fr m (Option.some e) (.ok (Option.some ⟨bs.toArray⟩) fr1 m1) :=
  EvalSaltOpt.some he (saltBytes_bytes32 bs)

/-- `new C{value: v}(args)`. -/
theorem EvalExpr.newContractValue {fr fr1 fr3 : Frame} {m m1 m3 m4 m5 : Machine} {ty : Ty} {ve : Expr} {es : List Expr}
    {c : Ident} {tys : List Ty} {n : ℕ} {vs : List Value} {svs : List ABI.ABIValue} {a : EVM.Address} {out : EVM.Bytes}
    (hnew : newContract? fc ty = some (c, tys)) (hv : EvalExpr cfg o fc fr m ve (.ok (u256Val n) fr1 m1))
    (hargs : EvalExprs cfg o fc fr1 m1 es (.ok vs fr3 m3)) (habi : abiArgs cfg fc.types m3 tys vs = some (.ok (svs, m4)))
    (hcreate : newViaEVM cfg o m4 c n svs none (a, m5, true, out)) :
    EvalExpr cfg o fc fr m (.call (.new ty) [.value ve] (.positional es)) (.ok (.contract c a) fr3 m5) :=
  EvalExpr.newContract hnew (EvalValueOpt.u256 hv) EvalSaltOpt.none rfl hargs habi hcreate

/-- `new C{salt: s}(args)`. -/
theorem EvalExpr.newContractSalt {fr fr2 fr3 : Frame} {m m2 m3 m4 m5 : Machine} {ty : Ty} {se : Expr} {es : List Expr}
    {c : Ident} {tys : List Ty} {bs : List UInt8} {vs : List Value} {svs : List ABI.ABIValue} {a : EVM.Address}
    {out : EVM.Bytes}
    (hnew : newContract? fc ty = some (c, tys)) (hs : EvalExpr cfg o fc fr m se (.ok (.fixedBytes ⟨31, by decide⟩ bs) fr2 m2))
    (hargs : EvalExprs cfg o fc fr2 m2 es (.ok vs fr3 m3)) (habi : abiArgs cfg fc.types m3 tys vs = some (.ok (svs, m4)))
    (hcreate : newViaEVM cfg o m4 c 0 svs (some ⟨bs.toArray⟩) (a, m5, true, out)) :
    EvalExpr cfg o fc fr m (.call (.new ty) [.salt se] (.positional es)) (.ok (.contract c a) fr3 m5) :=
  EvalExpr.newContract hnew EvalValueOpt.none (EvalSaltOpt.bytes32 hs) rfl hargs habi hcreate

/-- `recv.f{value: v}(args)`, call made and returned. -/
theorem EvalExpr.externalCallValue {fr fr1 fr2 fr4 : Frame} {m m1 m2 m4 m5 m6 m7 : Machine} {recv ve : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {n : ℕ} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {rets : List Value}
    (hdirect : memberCallDirect fc fr recv = false)
    (hrecv : EvalExpr cfg o fc fr m recv (.ok (.contract c a) fr1 m1))
    (hv : EvalExpr cfg o fc fr1 m1 ve (.ok (u256Val n) fr2 m2))
    (hargs : EvalExprs cfg o fc fr2 m2 es (.ok vs fr4 m4))
    (hres : resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d)
    (hsig : externalSig fc.types d = some (sigStr, ptys, rtys))
    (habi : abiArgs cfg fc.types m4 (d.params.map (·.ty)) vs = some (.ok (svs, m5)))
    (henc : ABI.encodeABIValues? ptys svs = some bs)
    (hcode : d.returns = [] → codeSize m4.evm a ≠ 0)
    (hcall : callViaEVM o m5 a n (selectorOf sigStr ++ bs.toByteArray)
      (m5.evm.executionEnv.perm && d.mutability != .view && d.mutability != .pure) (calleeGas o m5 none n)
      (true, m6, out))
    (hdec : decodeRets cfg fc.types m6 d.returns rtys out = some (rets, m7)) :
    EvalExpr cfg o fc fr m (.call (.member recv f) [.value ve] (.positional es)) (.ok (retValue rets) fr4 m7) :=
  EvalExpr.externalCall hdirect hrecv (EvalValueOpt.u256 hv) EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall
    hdec

/-- `abi.decode(data, (T₁, …))` of a memory `bytes` object. -/
theorem EvalExpr.abiDecodeMemBytes {fr fr1 : Frame} {m m1 : Machine} {d tyArg : Expr} {id : ℕ} {s : Bool} {bs : ByteArray}
    {tys : List Ty} {atys : List ABI.ABIType} {svs : List ABI.ABIValue} {vs : List Value} {h' : Heap}
    (hd : EvalExpr cfg o fc fr m d (.ok (.memRef id) fr1 m1)) (hget : m1.heap.get? id = some (.bytes s bs))
    (htys : typeArgs tyArg = some tys) (hatys : tys.mapM (abiTypeOf fc.types) = some atys)
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode atys bs = some svs)
    (hof : ofAbiList fc.types tys svs m1.heap = some (vs, h')) :
    EvalExpr cfg o fc fr m (.call (.member (.ident "abi") "decode") [] (.positional [d, tyArg]))
      (.ok (retValue vs) fr1 { m1 with heap := h' }) :=
  EvalExpr.abiDecode hd (by simp [bytesArg, hget]) htys hatys hdec hof

/-! ## Tuple declarations `(T₁ x₁, …) = rhs` -/

/-- `(T₁ x₁, T₂ x₂) = rhs`, each binder declared with the given `declare` facts. -/
theorem ExecStmt.tupleDeclTwo {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {rhs : Expr} {p1 p2 : Param} {x1 x2 : Ident}
    {v1 v2 : Value}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [v1, v2]) fr1 m1))
    (hn1 : p1.name = some x1) (hd1 : declare cfg fc.types fr1 m1 p1.ty p1.loc x1 (some v1) = some (.ok (fr2, m2)))
    (hn2 : p2.name = some x2) (hd2 : declare cfg fc.types fr2 m2 p2.ty p2.loc x2 (some v2) = some (.ok (fr3, m3))) :
    ExecStmt cfg o fc fr m (.tupleDecl [some p1, some p2] rhs) (.normal fr3 m3) :=
  ExecStmt.tupleDecl hrhs (DeclareTuple.cons hn1 hd1 (DeclareTuple.cons hn2 hd2 DeclareTuple.nil))

/-- `(T₁ x₁, , T₃ x₃) = rhs`: the middle component is dropped. -/
theorem ExecStmt.tupleDeclSkipMiddle {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {rhs : Expr} {p1 p3 : Param}
    {x1 x3 : Ident} {v1 v2 v3 : Value}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [v1, v2, v3]) fr1 m1))
    (hn1 : p1.name = some x1) (hd1 : declare cfg fc.types fr1 m1 p1.ty p1.loc x1 (some v1) = some (.ok (fr2, m2)))
    (hn3 : p3.name = some x3) (hd3 : declare cfg fc.types fr2 m2 p3.ty p3.loc x3 (some v3) = some (.ok (fr3, m3))) :
    ExecStmt cfg o fc fr m (.tupleDecl [some p1, none, some p3] rhs) (.normal fr3 m3) :=
  ExecStmt.tupleDecl hrhs (DeclareTuple.cons hn1 hd1 (DeclareTuple.skip (DeclareTuple.cons hn3 hd3 DeclareTuple.nil)))

/-- `(T₁ x₁, T₂ x₂, T₃ x₃) = rhs`. -/
theorem ExecStmt.tupleDeclThree {fr fr1 fr2 fr3 fr4 : Frame} {m m1 m2 m3 m4 : Machine} {rhs : Expr} {p1 p2 p3 : Param}
    {x1 x2 x3 : Ident} {v1 v2 v3 : Value}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [v1, v2, v3]) fr1 m1))
    (hn1 : p1.name = some x1) (hd1 : declare cfg fc.types fr1 m1 p1.ty p1.loc x1 (some v1) = some (.ok (fr2, m2)))
    (hn2 : p2.name = some x2) (hd2 : declare cfg fc.types fr2 m2 p2.ty p2.loc x2 (some v2) = some (.ok (fr3, m3)))
    (hn3 : p3.name = some x3) (hd3 : declare cfg fc.types fr3 m3 p3.ty p3.loc x3 (some v3) = some (.ok (fr4, m4))) :
    ExecStmt cfg o fc fr m (.tupleDecl [some p1, some p2, some p3] rhs) (.normal fr4 m4) :=
  ExecStmt.tupleDecl hrhs
    (DeclareTuple.cons hn1 hd1 (DeclareTuple.cons hn2 hd2 (DeclareTuple.cons hn3 hd3 DeclareTuple.nil)))

/-- `(uint256 a, uint256 b) = rhs` (memory binders). -/
theorem ExecStmt.tupleDeclTwoU256 {fr fr1 : Frame} {m m1 : Machine} {rhs : Expr} {x1 x2 : Ident} {n1 n2 : ℕ}
    {l1 l2 : Option DataLoc}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [u256Val n1, u256Val n2]) fr1 m1)) :
    ExecStmt cfg o fc fr m (.tupleDecl [some { ty := u256Ty, loc := l1, name := some x1 },
      some { ty := u256Ty, loc := l2, name := some x2 }] rhs)
      (.normal ((fr1.bind x1 u256Ty l1 (u256Val n1)).bind x2 u256Ty l2 (u256Val n2)) m1) :=
  ExecStmt.tupleDeclTwo hrhs rfl (declare_u256 ..) rfl (declare_u256 ..)

/-! ## Tuple assignments `(a, …) = rhs` -/

/-- `(a₁, a₂) = rhs`. -/
theorem EvalExpr.assignTupleTwo {fr fr1 fr2 fr3 fr4 fr5 : Frame} {m m1 m2 m3 m4 m5 : Machine} {l1 l2 rhs : Expr}
    {lv1 lv2 : LValue} {v1 v2 : Value}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [v1, v2]) fr1 m1))
    (hl1 : EvalLValue cfg o fc fr1 m1 l1 (.ok lv1 fr2 m2)) (ha1 : assign cfg fc.types fr2 m2 lv1 v1 = some (.ok (fr3, m3)))
    (hl2 : EvalLValue cfg o fc fr3 m3 l2 (.ok lv2 fr4 m4)) (ha2 : assign cfg fc.types fr4 m4 lv2 v2 = some (.ok (fr5, m5))) :
    EvalExpr cfg o fc fr m (.assign .assign (.tuple [some l1, some l2]) rhs) (.ok (.tuple [v1, v2]) fr5 m5) :=
  EvalExpr.assignTuple hrhs (AssignTuple.cons hl1 ha1 (AssignTuple.cons hl2 ha2 AssignTuple.nil))

theorem ExecStmt.assignTupleTwo {fr fr1 fr2 fr3 fr4 fr5 : Frame} {m m1 m2 m3 m4 m5 : Machine} {l1 l2 rhs : Expr}
    {lv1 lv2 : LValue} {v1 v2 : Value}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [v1, v2]) fr1 m1))
    (hl1 : EvalLValue cfg o fc fr1 m1 l1 (.ok lv1 fr2 m2)) (ha1 : assign cfg fc.types fr2 m2 lv1 v1 = some (.ok (fr3, m3)))
    (hl2 : EvalLValue cfg o fc fr3 m3 l2 (.ok lv2 fr4 m4)) (ha2 : assign cfg fc.types fr4 m4 lv2 v2 = some (.ok (fr5, m5))) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.tuple [some l1, some l2]) rhs)) (.normal fr5 m5) :=
  ExecStmt.exprStmt (EvalExpr.assignTupleTwo hrhs hl1 ha1 hl2 ha2)

/-- `(a, ) = rhs`: only the first component is assigned. -/
theorem ExecStmt.assignTupleFirst {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {l1 rhs : Expr} {lv1 : LValue}
    {v1 v2 : Value}
    (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [v1, v2]) fr1 m1))
    (hl1 : EvalLValue cfg o fc fr1 m1 l1 (.ok lv1 fr2 m2)) (ha1 : assign cfg fc.types fr2 m2 lv1 v1 = some (.ok (fr3, m3))) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.tuple [some l1, none]) rhs)) (.normal fr3 m3) :=
  ExecStmt.exprStmt (EvalExpr.assignTuple hrhs (AssignTuple.cons hl1 ha1 (AssignTuple.skip AssignTuple.nil)))

/-- `(a, b) = (b, a)`-style swaps and other two-local assignments of `uint256`s. -/
theorem ExecStmt.assignTupleTwoLocalsU256 {fr fr1 : Frame} {m m1 : Machine} {rhs : Expr} {x1 x2 : Ident} {n1 n2 : ℕ}
    (l1 l2 : Local) (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.tuple [u256Val n1, u256Val n2]) fr1 m1))
    (hx1 : fr1.get? x1 = some l1) (ht1 : l1.ty = u256Ty)
    (hx2 : (fr1.setVal x1 (u256Val n1)).get? x2 = some l2) (ht2 : l2.ty = u256Ty) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.tuple [some (.ident x1), some (.ident x2)]) rhs))
      (.normal ((fr1.setVal x1 (u256Val n1)).setVal x2 (u256Val n2)) m1) :=
  ExecStmt.assignTupleTwo hrhs (EvalLValue.local (m := m1) hx1) (assign_local_u256 l1 hx1 ht1 n1)
    (EvalLValue.local (m := m1) hx2) (assign_local_u256 l2 hx2 ht2 n2)

/-! ## Multiple return values -/

/-- `return (e₁, e₂)` into two return slots with the given `assign` facts. -/
theorem ExecStmt.returnTwo {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {e : Expr} {r1 r2 : Ident} {v1 v2 : Value}
    (hret : fr.retVars = [r1, r2]) (he : EvalExpr cfg o fc fr m e (.ok (.tuple [v1, v2]) fr1 m1))
    (ha1 : assign cfg fc.types fr1 m1 (.local r1) v1 = some (.ok (fr2, m2)))
    (ha2 : assign cfg fc.types fr2 m2 (.local r2) v2 = some (.ok (fr3, m3))) (l1 l2 : Local)
    (hr1 : fr1.get? r1 = some l1) (hr2 : fr2.get? r2 = some l2) :
    ExecStmt cfg o fc fr m (.return (some e)) (.returned fr3 m3) := by
  refine ExecStmt.returnMulti (by simp [hret]) he ?_
  rw [hret]
  exact AssignTuple.cons (EvalLValue.local (m := m1) hr1) ha1
    (AssignTuple.cons (EvalLValue.local (m := m2) hr2) ha2 AssignTuple.nil)

/-- `return (e₁, e₂, e₃)` into three return slots. -/
theorem ExecStmt.returnThree {fr fr1 fr2 fr3 fr4 : Frame} {m m1 m2 m3 m4 : Machine} {e : Expr} {r1 r2 r3 : Ident}
    {v1 v2 v3 : Value}
    (hret : fr.retVars = [r1, r2, r3]) (he : EvalExpr cfg o fc fr m e (.ok (.tuple [v1, v2, v3]) fr1 m1))
    (ha1 : assign cfg fc.types fr1 m1 (.local r1) v1 = some (.ok (fr2, m2)))
    (ha2 : assign cfg fc.types fr2 m2 (.local r2) v2 = some (.ok (fr3, m3)))
    (ha3 : assign cfg fc.types fr3 m3 (.local r3) v3 = some (.ok (fr4, m4))) (l1 l2 l3 : Local)
    (hr1 : fr1.get? r1 = some l1) (hr2 : fr2.get? r2 = some l2) (hr3 : fr3.get? r3 = some l3) :
    ExecStmt cfg o fc fr m (.return (some e)) (.returned fr4 m4) := by
  refine ExecStmt.returnMulti (by simp [hret]) he ?_
  rw [hret]
  exact AssignTuple.cons (EvalLValue.local (m := m1) hr1) ha1
    (AssignTuple.cons (EvalLValue.local (m := m2) hr2) ha2
      (AssignTuple.cons (EvalLValue.local (m := m3) hr3) ha3 AssignTuple.nil))

theorem EvalExpr.tupleThree {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {e1 e2 e3 : Expr} {v1 v2 v3 : Value}
    (h1 : EvalExpr cfg o fc fr m e1 (.ok v1 fr1 m1)) (h2 : EvalExpr cfg o fc fr1 m1 e2 (.ok v2 fr2 m2))
    (h3 : EvalExpr cfg o fc fr2 m2 e3 (.ok v3 fr3 m3)) :
    EvalExpr cfg o fc fr m (.tuple [some e1, some e2, some e3]) (.ok (.tuple [v1, v2, v3]) fr3 m3) :=
  EvalExpr.tuple rfl (EvalExprs.three h1 h2 h3)

/-! ## `try` with two returns -/

/-- `try recv.f(args) returns (T₁ x₁, T₂ x₂) { … }`, the call succeeding with two value-type returns. -/
theorem ExecStmt.tryCallOkTwoRets {fr fr1 fr4 fr5 fr6 : Frame} {m m1 m4 m5 m6 m7 m8 : Machine} {recv : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {body : List Stmt}
    {cs : List CatchClause} {r : ExecResult} {p1 p2 : Param} {x1 x2 : Ident} {sv1 sv2 : ABI.ABIValue} {v1 v2 : Value}
    {h1 h2 : Heap}
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
    (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some [sv1, sv2])
    (hof1 : ofAbi fc.types fuelDefault p1.ty sv1 m6.heap = some (v1, h1))
    (hof2 : ofAbi fc.types fuelDefault p2.ty sv2 h1 = some (v2, h2))
    (hn1 : p1.name = some x1) (hn2 : p2.name = some x2)
    (hd1 : declare cfg fc.types fr4 { m6 with heap := h2 } p1.ty (some (p1.loc.getD .memory)) x1 (some v1) =
      some (.ok (fr5, m7)))
    (hd2 : declare cfg fc.types fr5 m7 p2.ty (some (p2.loc.getD .memory)) x2 (some v2) = some (.ok (fr6, m8)))
    (hbody : ExecBlock cfg o fc fr6 m8 body r) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.member recv f) [] (.positional es)) [p1, p2] body cs) (exitBlock fr r) :=
  ExecStmt.tryCallOk hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall
    (tryRets_two hdec hof1 hof2) (bindTryParams_two hn1 hn2 hd1 hd2) hbody

/-! ## Builtins -/

theorem EvalExpr.addmodU256 {fr fr1 : Frame} {m m1 : Machine} {x y k : Expr} {a b c : ℕ}
    (hargs : EvalExprs cfg o fc fr m [x, y, k] (.ok [u256Val a, u256Val b, u256Val c] fr1 m1)) (hc : c ≠ 0) :
    EvalExpr cfg o fc fr m (.call (.ident "addmod") [] (.positional [x, y, k])) (.ok (wordNat ((a + b) % c)) fr1 m1) :=
  EvalExpr.addmod hargs rfl rfl rfl hc

theorem EvalExpr.mulmodU256 {fr fr1 : Frame} {m m1 : Machine} {x y k : Expr} {a b c : ℕ}
    (hargs : EvalExprs cfg o fc fr m [x, y, k] (.ok [u256Val a, u256Val b, u256Val c] fr1 m1)) (hc : c ≠ 0) :
    EvalExpr cfg o fc fr m (.call (.ident "mulmod") [] (.positional [x, y, k])) (.ok (wordNat ((a * b) % c)) fr1 m1) :=
  EvalExpr.mulmod hargs rfl rfl rfl hc

/-- `gasleft()`: the oracle's value at the current tick. -/
theorem EvalExpr.gasleftVal {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.call (.ident "gasleft") [] (.positional []))
      (.ok (u256Val (o.gasleft m.tick).toNat) fr { m with tick := m.tick + 1 }) :=
  EvalExpr.gasleft

/-- `msg.data`: a fresh memory `bytes` holding the calldata. -/
theorem EvalExpr.msgDataVal {fr : Frame} {m : Machine} :
    EvalExpr cfg o fc fr m (.member (.ident "msg") "data")
      (.ok (allocBytes m false m.evm.executionEnv.calldata).1 fr (allocBytes m false m.evm.executionEnv.calldata).2) :=
  EvalExpr.msgData rfl

/-- `a.balance` for an `address` expression. -/
theorem EvalExpr.addressBalance {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {a : EVM.Address}
    (hdm : directMember fc fr e = false) (he : EvalExpr cfg o fc fr m e (.ok (.address a) fr1 m1)) :
    EvalExpr cfg o fc fr m (.member e "balance") (.ok (wordNat (balanceOf m1.evm a)) fr1 m1) := by
  have h := EvalExpr.memberBalance (cfg := cfg) (o := o) (fc := fc) hdm he (a := a.toNat) rfl
  rwa [address_toNat] at h

/-- `b.length` for a `bytesN` value. -/
theorem EvalExpr.bytesNLength {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {n : Fin 32} {bs : List UInt8}
    (hdm : directMember fc fr e = false) (he : EvalExpr cfg o fc fr m e (.ok (.fixedBytes n bs) fr1 m1)) :
    EvalExpr cfg o fc fr m (.member e "length") (.ok (wordNat (n.val + 1)) fr1 m1) :=
  EvalExpr.memberBytesLength hdm he

/-- `arr.length` for a storage dynamic array. -/
theorem EvalExpr.storageArrayLength {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {er : Solm.EvaledStorageRef} {ety : Ty}
    {n : ℕ} (hdm : directMember fc fr e = false)
    (he : EvalExpr cfg o fc fr m e (.ok (.storageRef er (.dynArray ety)) fr1 m1))
    (hlen : dynArrayLength cfg m1.evm er = some n) :
    EvalExpr cfg o fc fr m (.member e "length") (.ok (wordNat n) fr1 m1) :=
  EvalExpr.memberStorageLength hdm he (storageLength_dynArray hlen)

/-- An enum constant `E.member`. -/
theorem EvalExpr.enumConst {fr : Frame} {m : Machine} {t f : Ident} {e : EnumInfo} {i : ℕ}
    (henv : isEnvObj t = false) (hx : fr.get? t = none) (he : fc.types.enum? none t = some e)
    (hi : indexOf e.members f = some i) :
    EvalExpr cfg o fc fr m (.member (.ident t) f) (.ok (.enum t i) fr m) :=
  EvalExpr.enumMember henv hx he hi

/-- A `constant` state variable: its initializer is evaluated in place. -/
theorem EvalExpr.constVarVal {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {e : Expr} {r : Res Value}
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hconst : v.mutability = .constant) (hinit : v.init = some e)
    (he : EvalExpr cfg o fc fr m e r) : EvalExpr cfg o fc fr m (.ident x) r :=
  EvalExpr.constVar hx hv hconst hinit he

/-- `IFoo(addr)`: an address cast to a contract type by name. -/
theorem EvalExpr.contractCast {fr fr1 : Frame} {m m1 : Machine} {c : Ident} {a : Expr} {addr : EVM.Address}
    (hbuiltin : isBuiltinFn c = false) (hx : fr.get? c = none) (hvar : fc.var? c = none) (hfns : fc.fnsNamed c = [])
    (hstruct : fc.types.struct? none c = none) (hkind : (fc.types.contractKind? c).isSome = true)
    (henum : (fc.types.enum? none c).isNone = true)
    (ha : EvalExpr cfg o fc fr m a (.ok (.address addr) fr1 m1)) :
    EvalExpr cfg o fc fr m (.call (.ident c) [] (.positional [a])) (.ok (.contract c addr) fr1 m1) :=
  EvalExpr.convertUser hbuiltin hx hvar hfns hstruct (Or.inl hkind)
    (EvalExpr.convertPlain ha (explicitConv_address_contract _ _ addr none c hkind henum))

theorem EvalExpr.arrayLitPlain {fr fr1 : Frame} {m m1 m2 : Machine} {es : List Expr} {vs : List Value} {v : Value}
    (hes : EvalExprs cfg o fc fr m es (.ok vs fr1 m1)) (hobj : arrayLitObj fc.types m1 vs = some (.ok (v, m2))) :
    EvalExpr cfg o fc fr m (.arrayLit es) (.ok v fr1 m2) :=
  EvalExpr.arrayLit hes hobj

/-- `new T[](n)`. -/
theorem EvalExpr.newArrayPlain {fr fr1 : Frame} {m m1 : Machine} {ty : Ty} {n : Expr} {len : ℕ} {v : Value} {h' : Heap}
    (hnew : newContract? fc ty = none) (hn : EvalExpr cfg o fc fr m n (.ok (u256Val len) fr1 m1))
    (hnv : isValueType fc.types ty = false) (hz : zeroObj fc.types fuelDefault ty len m1.heap = some (v, h')) :
    EvalExpr cfg o fc fr m (.call (.new ty) [] (.positional [n])) (.ok v fr1 { m1 with heap := h' }) :=
  EvalExpr.newArray hnew hn rfl hnv hz

/-! ## Storage arrays: `push()` and `pop()` -/

/-- `arr.push()`: a zero element appended, the length incremented. -/
theorem EvalExpr.pushEmpty {fr fr1 : Frame} {m m1 : Machine} {recv : Expr} {er : Solm.EvaledStorageRef} {e : Ty} {n : ℕ}
    {slot : UInt256} (hdm : memberCallDirect fc fr recv = false)
    (he : EvalExpr cfg o fc fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1))
    (hlen : dynArrayLength cfg m1.evm er = some n) (hl : cfg.storage.layout (lengthRef er) m1.evm = some (uint256Loc slot))
    (hn : n + 1 < UInt256.size) :
    EvalExpr cfg o fc fr m (.call (.member recv "push") [] (.positional []))
      (.ok .unit fr1 (storeU256 m1 slot (UInt256.ofNat (n + 1)))) :=
  EvalExpr.push0 hdm he (storagePush_none hlen hl hn)

/-- `arr.pop()` on a non-empty array: the last element cleared, the length decremented. -/
theorem EvalExpr.popLast {fr fr1 : Frame} {m m1 : Machine} {recv : Expr} {er : Solm.EvaledStorageRef} {e : Ty} {n : ℕ}
    {slot : UInt256} {evm₁ : EVM.State} (hdm : memberCallDirect fc fr recv = false)
    (he : EvalExpr cfg o fc fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1))
    (hlen : dynArrayLength cfg m1.evm er = some (n + 1))
    (hclear : clearStorage cfg fc.types fuelDefault m1.evm (elemRef er n) e = some (.ok evm₁))
    (hl : cfg.storage.layout (lengthRef er) evm₁ = some (uint256Loc slot)) (hn : n < UInt256.size) :
    EvalExpr cfg o fc fr m (.call (.member recv "pop") [] (.positional []))
      (.ok .unit fr1 { m1 with evm := Storage.EVM.storageStore evm₁ evm₁.executionEnv.codeOwner slot (UInt256.ofNat n) }) :=
  EvalExpr.pop hdm he (storagePop_succ hlen hclear hl hn)

/-- `arr.pop()` on an empty array: `Panic(0x31)`. -/
theorem EvalExpr.popEmptyPanic {fr fr1 : Frame} {m m1 : Machine} {recv : Expr} {er : Solm.EvaledStorageRef} {e : Ty}
    (hdm : memberCallDirect fc fr recv = false)
    (he : EvalExpr cfg o fc fr m recv (.ok (.storageRef er (.dynArray e)) fr1 m1))
    (hlen : dynArrayLength cfg m1.evm er = some 0) :
    EvalExpr cfg o fc fr m (.call (.member recv "pop") [] (.positional [])) (.reverted (panicData 0x31)) := by
  have h := EvalExpr.popPanic (cfg := cfg) (o := o) (fc := fc) hdm he (storagePop_empty hlen)
  exact h

/-! ## `require(c, Err())`, `revert()`, `return;` -/

theorem ExecStmt.requireCustomNoArgs {fr fr1 : Frame} {m m1 : Machine} {c : Expr} {err : Ident} {ei : ErrorInfo}
    (hc : EvalExpr cfg o fc fr m c (.ok (.bool false) fr1 m1)) (hei : fc.error? err = some ei)
    (hparams : ei.decl.params = []) (htys : ei.sig.paramTypes = []) :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident "require") [] (.positional [c, .call (.ident err) [] (.positional [])])))
      (.reverted (selectorOf ei.sigStr)) := by
  refine ExecStmt.exprStmtRevert (EvalExpr.requireCustom (es := []) (vs := []) (svs := []) (fr2 := fr1) (m2 := m1)
    (m3 := m1) hc hei ?_ EvalExprs.nil ?_ ?_)
  · rw [hparams]; rfl
  · rw [hparams]; rfl
  · rw [htys]; exact customErrorData_nil _

theorem ExecStmt.revertEmptyStmt {fr : Frame} {m : Machine} :
    ExecStmt cfg o fc fr m (.exprStmt (.call (.ident "revert") [] (.positional []))) (.reverted ByteArray.empty) :=
  ExecStmt.exprStmtRevert EvalExpr.revertEmpty

theorem ExecStmt.returnNoneStmt {fr : Frame} {m : Machine} : ExecStmt cfg o fc fr m (.return none) (.returned fr m) :=
  ExecStmt.returnNone

/-! ## Loops: `do … while`, `continue`, `for` without initializer -/

theorem ExecStmt.doWhileNormal {fr fr1 fr' : Frame} {m m1 m' : Machine} {body : Stmt} {c : Expr}
    (hbody : ExecStmt cfg o fc fr m body (.normal fr1 m1))
    (hloop : ExecLoop cfg o fc fr1 m1 (some c) none body (.normal fr' m')) :
    ExecStmt cfg o fc fr m (.doWhile body c) (.normal fr' m') :=
  ExecStmt.doWhile hbody hloop

theorem ExecStmt.continueStmt {fr : Frame} {m : Machine} : ExecStmt cfg o fc fr m .continue (.continue fr m) :=
  ExecStmt.continue

theorem ExecStmt.forNoInitNormal {fr fr' : Frame} {m m' : Machine} {c post : Option Expr} {body : Stmt}
    (hloop : ExecLoop cfg o fc fr m c post body (.normal fr' m')) :
    ExecStmt cfg o fc fr m (.for none c post body) (.normal fr' m') :=
  ExecStmt.forNoInit hloop

/-- A loop iteration whose body ends in `continue`. -/
theorem ExecLoop.stepContinue {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {c : Expr} {post : Option Expr} {body : Stmt}
    {r : ExecResult} (hc : EvalExpr cfg o fc fr m c (.ok (.bool true) fr1 m1))
    (hb : ExecStmt cfg o fc fr1 m1 body (.continue fr2 m2)) (hp : ExecPost cfg o fc fr2 m2 post (.ok () fr3 m3))
    (hrest : ExecLoop cfg o fc fr3 m3 (some c) post body r) : ExecLoop cfg o fc fr m (some c) post body r :=
  ExecLoop.iterateContinue (EvalCond.some hc) hb hp hrest

/-! ## Calls through `super`, a base, a library, `using for`, `delegatecall` -/

theorem EvalExpr.superCallPlain {fr fr1 : Frame} {m m1 m2 : Machine} {f : Ident} {es : List Expr} {vs rets : List Value}
    {fn : FnDef} (hargs : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (hres : resolveOverload fc.types m1.heap fc (superCands fc fr.here f) vs = some fn)
    (hcall : CallFn cfg o fc fr1 m1 fn vs (.ok rets m2)) :
    EvalExpr cfg o fc fr m (.call (.member .super f) [] (.positional es)) (.ok (retValue rets) fr1 m2) :=
  EvalExpr.superCall rfl hargs hres hcall

theorem EvalExpr.baseCallPlain {fr fr1 : Frame} {m m1 m2 : Machine} {b f : Ident} {es : List Expr} {vs rets : List Value}
    {fn : FnDef} (henv : isEnvObj b = false) (hx : fr.get? b = none) (hlib : fc.library? b = none)
    (hlin : fc.linearization.contains b = true) (hargs : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (hres : resolveOverload fc.types m1.heap fc (baseCands fc b f) vs = some fn)
    (hcall : CallFn cfg o fc fr1 m1 fn vs (.ok rets m2)) :
    EvalExpr cfg o fc fr m (.call (.member (.ident b) f) [] (.positional es)) (.ok (retValue rets) fr1 m2) :=
  EvalExpr.baseCall henv hx hlib hlin rfl hargs hres hcall

theorem EvalExpr.libraryCallPlain {fr fr1 : Frame} {m m1 m2 : Machine} {l f : Ident} {lib : ContractDecl} {es : List Expr}
    {vs rets : List Value} {d : FnDecl} (henv : isEnvObj l = false) (hx : fr.get? l = none)
    (hlib : fc.library? l = some lib) (hargs : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (hres : resolveDecl fc.types m1.heap (lib.functions.filter (·.name == f)) vs = some d)
    (hcall : CallFn cfg o fc fr1 m1 ⟨0, l, d⟩ vs (.ok rets m2)) :
    EvalExpr cfg o fc fr m (.call (.member (.ident l) f) [] (.positional es)) (.ok (retValue rets) fr1 m2) :=
  EvalExpr.libraryCall henv hx hlib rfl hargs hres hcall

theorem EvalExpr.usingForCallPlain {fr fr1 fr2 : Frame} {m m1 m2 m3 : Machine} {recv : Expr} {f : Ident} {rv : Value}
    {lib : ContractDecl} {es : List Expr} {vs rets : List Value} {d : FnDecl}
    (hdm : memberCallDirect fc fr recv = false) (hrecv : EvalExpr cfg o fc fr m recv (.ok rv fr1 m1))
    (hspecial : specialMemberCall rv f = false) (hlib : usingLibrary fc fr.here (receiverTy m1.heap rv) = [lib])
    (hargs : EvalExprs cfg o fc fr1 m1 es (.ok vs fr2 m2))
    (hres : resolveDecl fc.types m2.heap (lib.functions.filter (·.name == f)) (rv :: vs) = some d)
    (hcall : CallFn cfg o fc fr2 m2 ⟨0, lib.name, d⟩ (rv :: vs) (.ok rets m3)) :
    EvalExpr cfg o fc fr m (.call (.member recv f) [] (.positional es)) (.ok (retValue rets) fr2 m3) :=
  EvalExpr.usingForCall hdm hrecv hspecial hlib rfl hargs hres hcall

/-- `a.delegatecall(data)` with `data` a memory `bytes`: the EVM result is `hcall`. -/
theorem EvalExpr.delegateCallPlain {fr fr1 fr3 : Frame} {m m1 m3 m4 : Machine} {recv dataE : Expr} {a : EVM.Address}
    {id : ℕ} {s : Bool} {data out : ByteArray} {z : Bool}
    (hdm : memberCallDirect fc fr recv = false) (hrecv : EvalExpr cfg o fc fr m recv (.ok (.address a) fr1 m1))
    (hdata : EvalExpr cfg o fc fr1 m1 dataE (.ok (.memRef id) fr3 m3)) (hget : m3.heap.get? id = some (.bytes s data))
    (hcall : delegateCallViaEVM o m3 (EVM.address a.toNat) data (calleeGas o m3 none 0) (z, m4, out)) :
    EvalExpr cfg o fc fr m (.call (.member recv "delegatecall") [] (.positional [dataE]))
      (.ok (.tuple [.bool z, (allocBytes m4 false out).1]) fr3 (allocBytes m4 false out).2) :=
  EvalExpr.delegateCall hdm hrecv rfl rfl EvalGasOpt.none hdata (by simp [bytesArg, hget]) hcall rfl

/-- `recv.f(args)` on an address without code and no return values: empty revert (solc's extcodesize check). -/
theorem EvalExpr.externalCallNoCodePlain {fr fr1 fr4 : Frame} {m m1 m4 : Machine} {recv : Expr} {f c : Ident}
    {a : EVM.Address} {es : List Expr} {vs : List Value} {d : FnDecl}
    (hdm : memberCallDirect fc fr recv = false) (hrecv : EvalExpr cfg o fc fr m recv (.ok (.contract c a) fr1 m1))
    (hargs : EvalExprs cfg o fc fr1 m1 es (.ok vs fr4 m4))
    (hres : resolveDecl fc.types m4.heap (fc.contractFnsNamed c f) vs = some d) (hret : d.returns = [])
    (hcode : codeSize m4.evm a = 0) :
    EvalExpr cfg o fc fr m (.call (.member recv f) [] (.positional es)) (.reverted ByteArray.empty) :=
  EvalExpr.externalCallNoCode hdm hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hret hcode

/-! ## `try new C(args)` and uncaught reverts -/

theorem ExecStmt.tryNewOkNoRets {fr fr3 : Frame} {m m3 m4 m5 : Machine} {ty : Ty} {es : List Expr} {c : Ident}
    {tys : List Ty} {vs : List Value} {svs : List ABI.ABIValue} {a : EVM.Address} {out : EVM.Bytes} {body : List Stmt}
    {cs : List CatchClause} {r : ExecResult}
    (hnew : newContract? fc ty = some (c, tys)) (hargs : EvalExprs cfg o fc fr m es (.ok vs fr3 m3))
    (habi : abiArgs cfg fc.types m3 tys vs = some (.ok (svs, m4)))
    (hcreate : newViaEVM cfg o m4 c 0 svs none (a, m5, true, out)) (hbody : ExecBlock cfg o fc fr3 m5 body r) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.new ty) [] (.positional es)) [] body cs) (exitBlock fr r) :=
  ExecStmt.tryNewOk hnew EvalValueOpt.none EvalSaltOpt.none rfl hargs habi hcreate (bindTryParams_nil _ _) hbody

theorem ExecStmt.tryNewCaughtGeneric {fr fr3 : Frame} {m m3 m4 m5 : Machine} {ty : Ty} {es : List Expr} {c : Ident}
    {tys : List Ty} {vs : List Value} {svs : List ABI.ABIValue} {a : EVM.Address} {out : EVM.Bytes} {ps : List Param}
    {body cbody : List Stmt} {r : ExecResult}
    (hnew : newContract? fc ty = some (c, tys)) (hargs : EvalExprs cfg o fc fr m es (.ok vs fr3 m3))
    (habi : abiArgs cfg fc.types m3 tys vs = some (.ok (svs, m4)))
    (hcreate : newViaEVM cfg o m4 c 0 svs none (a, m5, false, out)) (hcatch : ExecBlock cfg o fc fr3 m5 cbody r) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.new ty) [] (.positional es)) ps body [.mk none [] cbody]) (exitBlock fr r) :=
  ExecStmt.tryNewCaught hnew EvalValueOpt.none EvalSaltOpt.none rfl hargs habi hcreate
    (selectCatch_generic_noParams cfg m5 cbody out) (bindTryParams_nil _ _) hcatch

/-- The tried call reverts and no clause matches: the revert bubbles up. -/
theorem ExecStmt.tryCallUncaughtPlain {fr fr1 fr4 : Frame} {m m1 m4 m5 m6 : Machine} {recv : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {ps : List Param}
    {body : List Stmt} {cs : List CatchClause}
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
      (false, m6, out))
    (hsel : selectCatch cfg m6 cs out = none) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.member recv f) [] (.positional es)) ps body cs) (.reverted out) :=
  ExecStmt.tryCallUncaught hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall hsel

/-! ## `abi.encodeWithSignature`, `delete` of a local -/

theorem EvalExpr.abiEncodeWithSignaturePlain {fr fr1 : Frame} {m m1 : Machine} {sig : String} {es : List Expr}
    {vs : List Value} {tys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8}
    (hes : EvalExprs cfg o fc fr m (.lit (.str sig) :: es) (.ok (.strLit sig.toUTF8 :: vs) fr1 m1))
    (htys : vs.mapM (abiTyOfValue fc.types m1.heap) = some tys)
    (hsvs : vs.mapM (toAbi m1.heap fuelDefault) = some svs) (henc : ABI.encodeABIValues? tys svs = some bs) :
    EvalExpr cfg o fc fr m (.call (.member (.ident "abi") "encodeWithSignature") [] (.positional (.lit (.str sig) :: es)))
      (.ok (allocBytes m1 false ((ffi.KEC sig.toUTF8).extract 0 4 ++ bs.toByteArray)).1 fr1
        (allocBytes m1 false ((ffi.KEC sig.toUTF8).extract 0 4 ++ bs.toByteArray)).2) :=
  EvalExpr.abiEncodeWithSignature hes rfl htys (abiArgsAbi_of_mapM hsvs) henc rfl

/-- `delete x` for a `uint256` local. -/
theorem ExecStmt.deleteLocalU256 {fr : Frame} {m : Machine} {x : Ident} (l : Local) (hx : fr.get? x = some l)
    (hty : l.ty = u256Ty) :
    ExecStmt cfg o fc fr m (.exprStmt (.unary .delete (.ident x))) (.normal (fr.setVal x (u256Val 0)) m) :=
  ExecStmt.exprStmt (EvalExpr.deleteLocal (EvalLValue.local (m := m) hx) hx (by rw [hty]; simp [fuelDefault]))

/-! ## Integers of any width: builders -/

/-! ### Builders -/

theorem EvalExpr.addUint {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {w : ABI.BitWidth} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (.uint w y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.uint w x) fr2 m2))
    (hunch : fr2.unchecked = false) (hfit : x + y < 2 ^ w.val) :
    EvalExpr cfg o fc fr m (.binary .add a b) (.ok (.uint w (x + y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_add_uint w x y hfit)

theorem EvalExpr.addUintOverflow {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {w : ABI.BitWidth} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (.uint w y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.uint w x) fr2 m2))
    (hunch : fr2.unchecked = false) (hbig : 2 ^ w.val ≤ x + y) :
    EvalExpr cfg o fc fr m (.binary .add a b) (.reverted (panicData 0x11)) :=
  EvalExpr.binaryPanic (p := .overflow) (by decide) (by decide) hb ha
    (by rw [hunch]; exact binop_add_uint_overflow w x y hbig)

theorem EvalExpr.subUint {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {w : ABI.BitWidth} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (.uint w y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.uint w x) fr2 m2))
    (hunch : fr2.unchecked = false) (hx : x < 2 ^ w.val) (hle : y ≤ x) :
    EvalExpr cfg o fc fr m (.binary .sub a b) (.ok (.uint w (x - y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_sub_uint w x y hx hle)

theorem EvalExpr.mulUint {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {w : ABI.BitWidth} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (.uint w y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.uint w x) fr2 m2))
    (hunch : fr2.unchecked = false) (hfit : x * y < 2 ^ w.val) :
    EvalExpr cfg o fc fr m (.binary .mul a b) (.ok (.uint w (x * y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_mul_uint w x y hfit)

theorem EvalExpr.divUint {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {w : ABI.BitWidth} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (.uint w y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.uint w x) fr2 m2))
    (hx : x < 2 ^ w.val) (hy : y ≠ 0) :
    EvalExpr cfg o fc fr m (.binary .div a b) (.ok (.uint w (x / y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_div_uint _ w x y hx hy)

theorem EvalExpr.ltUint {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {w : ABI.BitWidth} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (.uint w y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.uint w x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .lt a b) (.ok (.bool (decide (x < y))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_lt_uint _ w x y)

theorem EvalExpr.eqUint {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {w : ABI.BitWidth} {x y : ℕ}
    (hb : EvalExpr cfg o fc fr m b (.ok (.uint w y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.uint w x) fr2 m2)) :
    EvalExpr cfg o fc fr m (.binary .eq a b) (.ok (.bool (decide (x = y))) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (binop_eq_uint _ w x y)

theorem EvalExpr.addSint {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {a b : Expr} {w : ABI.BitWidth} {x y : Int}
    (hb : EvalExpr cfg o fc fr m b (.ok (.sint w y) fr1 m1)) (ha : EvalExpr cfg o fc fr1 m1 a (.ok (.sint w x) fr2 m2))
    (hunch : fr2.unchecked = false) (hlo : -(2 : Int) ^ (w.val - 1) ≤ x + y) (hhi : x + y < (2 : Int) ^ (w.val - 1)) :
    EvalExpr cfg o fc fr m (.binary .add a b) (.ok (.sint w (x + y)) fr2 m2) :=
  EvalExpr.binary (by decide) (by decide) hb ha (by rw [hunch]; exact binop_add_sint w x y hlo hhi)

/-- `uintN(x)` narrowing a `uint256`: the low `N` bits. -/
theorem EvalExpr.convertNarrow {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {w w' : ABI.BitWidth} {n : ℕ}
    (ha : EvalExpr cfg o fc fr m a (.ok (.uint w n) fr1 m1)) (hlt : w'.val < w.val) :
    EvalExpr cfg o fc fr m (.call (.typeExpr (.uint w')) [] (.positional [a])) (.ok (.uint w' (n % 2 ^ w'.val)) fr1 m1) :=
  EvalExpr.convertPlain ha (explicitConv_uint_narrow _ _ w w' n hlt)

/-- `uint256(x)` widening a `uintN`. -/
theorem EvalExpr.convertWiden {fr fr1 : Frame} {m m1 : Machine} {a : Expr} {w w' : ABI.BitWidth} {n : ℕ}
    (ha : EvalExpr cfg o fc fr m a (.ok (.uint w n) fr1 m1)) (hle : w.val ≤ w'.val) :
    EvalExpr cfg o fc fr m (.call (.typeExpr (.uint w')) [] (.positional [a])) (.ok (.uint w' n) fr1 m1) :=
  EvalExpr.convertPlain ha (explicitConv_uint_widen _ _ w w' n hle)

/-! ## Immutables in constructors -/

/-- `x = e;` for an immutable `x` inside the constructor: the `imm_x` local is updated. -/
theorem ExecStmt.assignImmutableU256 {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {rhs : Expr} {n : ℕ}
    (l : Local) (hrhs : EvalExpr cfg o fc fr m rhs (.ok (u256Val n) fr1 m1))
    (hx : fr1.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .immutable)
    (hl : fr1.get? (immName x) = some l) (hty : l.ty = u256Ty) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.ident x) rhs))
      (.normal (fr1.setVal (immName x) (u256Val n)) m1) :=
  ExecStmt.exprStmt (EvalExpr.assignPlain rfl hrhs (EvalLValue.immutableVar (m := m1) hx hv hmut)
    (assign_local_u256 l hl hty n))

theorem ExecStmt.assignImmutableAddress {fr fr1 : Frame} {m m1 : Machine} {x : Ident} {v : FlatVar} {rhs : Expr}
    {a : EVM.Address} (l : Local) (hrhs : EvalExpr cfg o fc fr m rhs (.ok (.address a) fr1 m1))
    (hx : fr1.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .immutable)
    (hl : fr1.get? (immName x) = some l) (hty : l.ty = .address false) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.ident x) rhs))
      (.normal (fr1.setVal (immName x) (.address a)) m1) :=
  ExecStmt.exprStmt (EvalExpr.assignPlain rfl hrhs (EvalLValue.immutableVar (m := m1) hx hv hmut)
    (by simp [assign, coerce, hl, hty]))

/-- Reading an immutable inside the constructor after it was set. -/
theorem EvalExpr.immutableLocalVal {fr : Frame} {m : Machine} {x : Ident} {v : FlatVar} {val : Value} (l : Local)
    (hx : fr.get? x = none) (hv : fc.var? x = some v) (hmut : v.mutability = .immutable)
    (hl : fr.get? (immName v.name) = some l) (hval : l.val = val) :
    EvalExpr cfg o fc fr m (.ident x) (.ok val fr m) :=
  EvalExpr.immutableVar hx hv hmut (by simp [immutableValue, hl, hval])

/-- `try recv.f(args) returns (ps) { … }`: the call succeeds, the returns are reconstructed (`hof`) and bound (`hbind`). -/
theorem ExecStmt.tryCallOkRets {fr fr1 fr4 fr5 : Frame} {m m1 m4 m5 m6 m8 : Machine} {recv : Expr} {f : Ident}
    {es : List Expr} {c : Ident} {a : EVM.Address} {vs : List Value} {d : FnDecl} {sigStr : String}
    {ptys rtys : List ABI.ABIType} {svs : List ABI.ABIValue} {bs : List UInt8} {out : ByteArray} {body : List Stmt}
    {cs : List CatchClause} {r : ExecResult} {ps : List Param} {rsvs : List ABI.ABIValue} {rets : List Value} {h' : Heap}
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
    (hne : ps ≠ []) (hdec : ABI.decodeReturnValuesWithMode? cfg.abiDecodeMode rtys out = some rsvs)
    (hlen : rsvs.length = ps.length) (hof : ofAbiList fc.types (ps.map (·.ty)) rsvs m6.heap = some (rets, h'))
    (hbind : bindTryParams cfg fc.types fr4 { m6 with heap := h' } ps rets = some (.ok (fr5, m8)))
    (hbody : ExecBlock cfg o fc fr5 m8 body r) :
    ExecStmt cfg o fc fr m (.tryCatch (.call (.member recv f) [] (.positional es)) ps body cs) (exitBlock fr r) :=
  ExecStmt.tryCallOk hdirect hrecv EvalValueOpt.none EvalGasOpt.none rfl hargs hres hsig habi henc hcode hcall
    (tryRets_of_ofAbiList hne hdec hlen hof) hbind hbody

/-- `C.f.selector` / `this.f.selector`. -/
theorem EvalExpr.selectorVal {fr : Frame} {m : Machine} {recv : Expr} {g : Ident} {v : Value}
    (h : selectorMember fc fr recv g = some v) :
    EvalExpr cfg o fc fr m (.member (.member recv g) "selector") (.ok v fr m) :=
  EvalExpr.memberSelector h

/-- `a.code.length` on an address: `codeSize`, with the code bytes allocated in memory. -/
theorem EvalExpr.codeLength {fr fr1 : Frame} {m m1 : Machine} {e : Expr} {v : Value} {a : ℕ}
    (hdm : directMember fc fr e = false) (hnf : fnRefContract fc fr e = none)
    (he : EvalExpr cfg o fc fr m e (.ok v fr1 m1)) (ha : addrNat v = some a) :
    EvalExpr cfg o fc fr m (.member (.member e "code") "length")
      (.ok (wordNat (codeSize m1.evm (EVM.address a))) fr1
        { m1 with heap := (m1.heap.alloc (.bytes false (codeOf m1.evm (EVM.address a)))).1 }) :=
  EvalExpr.memberMemLength (directMember_member fc fr e "code" hnf)
    (EvalExpr.memberCode hdm he ha (allocBytes_eq m1 false _)) (memLength_allocBytes m1 false _)

/-- `emit ev(args)` for an event with a single declaration. -/
theorem ExecStmt.emitSingle {fr fr1 : Frame} {m m1 m2 : Machine} {ev : Ident} {ei : EventInfo} {es : List Expr}
    {vs : List Value} {svs : List ABI.ABIValue} {le : Ethereum.LogEntry}
    (hev : fc.eventsNamed ev = [ei]) (hfit : eventFits fc.types m1.heap ei vs = true)
    (hargs : EvalExprs cfg o fc fr m es (.ok vs fr1 m1))
    (habi : abiArgs cfg fc.types m1 (ei.decl.params.map (·.ty)) vs = some (.ok (svs, m2)))
    (hle : mkLogEntry m2.this ei svs = some le) :
    ExecStmt cfg o fc fr m (.emit (.ident ev) (.positional es)) (.normal fr1 (m2.pushLog le)) :=
  ExecStmt.emit (by rw [hev]; rfl) hargs (by rw [hev]; exact resolveEvent_single hfit) habi hle

/-- `x[i]` on a `bytesN` value. -/
theorem EvalExpr.indexFixedBytesNat {fr fr1 fr2 : Frame} {m m1 m2 : Machine} {e i : Expr} {n : Fin 32}
    {bs : List UInt8} {iv : Value} {k : ℕ} {b : UInt8}
    (he : EvalExpr cfg o fc fr m e (.ok (.fixedBytes n bs) fr1 m1)) (hi : EvalExpr cfg o fc fr1 m1 i (.ok iv fr2 m2))
    (hk : natOperand iv = some k) (hb : bs[k]? = some b) :
    EvalExpr cfg o fc fr m (.index e i) (.ok (.fixedBytes ⟨0, by decide⟩ [b]) fr2 m2) :=
  EvalExpr.indexFixedBytes he hi (fixedBytesIndex_ok bs iv k b hk hb)

/-- `d[lo:hi]` on a byte array, both bounds given and in range. -/
theorem EvalExpr.sliceBytes {fr fr1 fr2 fr3 : Frame} {m m1 m2 m3 : Machine} {e lo hi : Expr} {obj a b : ℕ}
    {s : Bool} {d : ByteArray} {lv hv : Value}
    (he : EvalExpr cfg o fc fr m e (.ok (.memRef obj) fr1 m1))
    (hlo : EvalExpr cfg o fc fr1 m1 lo (.ok lv fr2 m2)) (hla : natValue lv = some a)
    (hhi : EvalExpr cfg o fc fr2 m2 hi (.ok hv fr3 m3)) (hhb : natValue hv = some b)
    (hobj : m3.heap.get? obj = some (.bytes s d)) (hab : a ≤ b) (hbd : b ≤ d.size) :
    EvalExpr cfg o fc fr m (.slice e (some lo) (some hi))
      (.ok (.memRef (m3.heap.alloc (.bytes s (d.extract a b))).2) fr3
        { m3 with heap := (m3.heap.alloc (.bytes s (d.extract a b))).1 }) :=
  EvalExpr.slice he (EvalGasOpt.some hlo hla) (EvalGasOpt.some hhi hhb)
    (sliceObj_bytes m3.heap obj s d (some a) (some b) hobj hab hbd)

end Solidity
