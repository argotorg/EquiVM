import Solidity.Theory.Derivations

/-!
# Usage examples of the derivation builders

Compiled with the library so they cannot rot.  Each example derives one statement or a whole body
with the builders alone; the contract facts (variables, layout, events) are hypotheses.  Referenced
from `GUIDE.md`.
-/

namespace Solidity.Usage

open Ethereum Reasoning.Theory

variable (cfg : Config) (o : Oracle) (fc : FlatContract)

/-- `y = x * 2 + 1;` on `uint256` locals. -/
example (fr : Frame) (m : Machine) (lx ly : Local) (n : ℕ)
    (hx : fr.get? "x" = some lx) (hlx : lx.ty = u256Ty) (hval : lx.val = u256Val n)
    (hy : fr.get? "y" = some ly) (hly : ly.ty = u256Ty) (hunch : fr.unchecked = false) (hfit : n * 2 + 1 < 2 ^ 256) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.ident "y")
      (.binary .add (.binary .mul (.ident "x") (.lit (.number 2 none none))) (.lit (.number 1 none none)))))
      (.normal (fr.setVal "y" (u256Val (n * 2 + 1))) m) :=
  ExecStmt.assignLocalU256 ly
    (EvalExpr.addU256Lit 1 none (EvalExpr.mulU256Lit 2 none (hval ▸ EvalExpr.local (m := m) hx) hunch (by decide) (by omega))
      hunch (by decide) hfit)
    hy hly

/-- `keccak256(abi.encodePacked(a, b))` on two `address` locals. -/
example (fr : Frame) (m : Machine) (a b : EVM.Address)
    (ha : fr.get? "a" = some { ty := .address false, loc := none, val := .address a })
    (hb : fr.get? "b" = some { ty := .address false, loc := none, val := .address b }) :
    EvalExpr cfg o fc fr m
      (.call (.ident "keccak256") [] (.positional
        [.call (.member (.ident "abi") "encodePacked") [] (.positional [.ident "a", .ident "b"])]))
      (.ok (.fixedBytes ⟨31, by decide⟩
        (ffi.KEC ([(EVM.Word.toBytesBE (UInt256.ofNat a.toNat)).drop 12,
          (EVM.Word.toBytesBE (UInt256.ofNat b.toNat)).drop 12].flatten.toByteArray)).toList)
        fr (allocBytes m false ([(EVM.Word.toBytesBE (UInt256.ofNat a.toNat)).drop 12,
          (EVM.Word.toBytesBE (UInt256.ofNat b.toNat)).drop 12].flatten.toByteArray)).2) :=
  EvalExpr.keccakPacked (tys := [.elem .address, .elem .address]) (svs := [.address a, .address b])
    (EvalExprs.two (EvalExpr.localVal _ _ ha) (EvalExpr.localVal _ _ hb)) (by simp) (by simp [fuelDefault])
    (by simp [encodePackedValue?_address])

/-- `roles[h] = true;` for `roles : mapping(bytes32 => bool)` and a `bytes32` local `h`. -/
example (fr : Frame) (m : Machine) (v : FlatVar) (bs : List UInt8) (slot : UInt256)
    (hroles : fr.get? "roles" = none) (hv : fc.var? "roles" = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .mapping (.fixedBytes ⟨31, by decide⟩) .bool)
    (hh : fr.get? "h" = some { ty := .fixedBytes ⟨31, by decide⟩, loc := none, val := .fixedBytes ⟨31, by decide⟩ bs })
    (hl : cfg.storage.layout (keyRef ⟨v.key, []⟩ (.fixedBytes ⟨31, by decide⟩ bs)) m.evm = some (boolOffset0Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.assign .assign (.index (.ident "roles") (.ident "h")) (.lit (.bool true))))
      (.normal fr (storeU256 m slot (UInt256.lor (UInt256.land (loadU256 m slot) (UInt256.lnot ⟨255⟩)) ⟨1⟩))) :=
  ExecStmt.exprStmt (EvalExpr.assignPlain rfl (EvalExpr.boolLit true)
    (EvalLValue.mappingBytes32 hroles hv hmut hty (EvalExpr.localVal _ _ hh))
    (assign_storage_of (writeStorageDeep_bool 1023 (writeScalar_bool_true hl))))

/-- `if (x & 0xff == 0) revert Foo();` -/
example (fr : Frame) (m : Machine) (lx : Local) (n : ℕ) (ei : ErrorInfo)
    (hx : fr.get? "x" = some lx) (hval : lx.val = u256Val n) (hn : n < 2 ^ 256) (h0 : n &&& 255 = 0)
    (hei : fc.error? "Foo" = some ei) (hparams : ei.decl.params = []) (htys : ei.sig.paramTypes = []) :
    ExecStmt cfg o fc fr m
      (.ite (.binary .eq (.binary .bitAnd (.ident "x") (.lit (.number 255 none none))) (.lit (.number 0 none none)))
        (.revert (.ident "Foo") (.positional [])) none)
      (.reverted (selectorOf ei.sigStr)) := by
  have hc := EvalExpr.eqU256Lit (cfg := cfg) (o := o) (fc := fc) 0 none
    (EvalExpr.bitAndU256Lit 255 none (hval ▸ EvalExpr.local (m := m) hx) (by decide) hn) (by decide)
  rw [decide_eq_true h0] at hc
  exact ExecStmt.iteTrue hc (ExecStmt.revertErrorNoArgs hei hparams htys)

/-- `unchecked { i++; }` -/
example (fr : Frame) (m : Machine) (l : Local) (n : ℕ)
    (hi : fr.get? "i" = some l) (hl : l.ty = u256Ty) (hval : l.val = u256Val n) :
    let fr' := Frame.setVal { fr with unchecked := true } "i" (u256Val ((n + 1) % 2 ^ 256))
    ExecStmt cfg o fc fr m (.unchecked [.exprStmt (.unary .postInc (.ident "i"))])
      (.normal (fr.exitScope { fr' with unchecked := fr.unchecked }) m) :=
  ExecStmt.uncheckedNormal (ExecBlock.one (ExecStmt.exprStmt
    (EvalExpr.postIncLocalU256Unchecked l hi hl hval rfl)))

/-- `delete owner;` for `owner : address`. -/
example (fr : Frame) (m : Machine) (v : FlatVar) (slot : UInt256)
    (hx : fr.get? "owner" = none) (hv : fc.var? "owner" = some v) (hmut : v.mutability = .mutable)
    (hty : v.ty = .address false) (hl : cfg.storage.layout ⟨v.key, []⟩ m.evm = some (addressOffset0Loc slot)) :
    ExecStmt cfg o fc fr m (.exprStmt (.unary .delete (.ident "owner")))
      (.normal fr (storeU256 m slot (setAddressOffset0Word (loadU256 m slot) ⟨0⟩))) :=
  ExecStmt.deleteStorageAddress (hty ▸ EvalLValue.stateVar hx hv hmut) hl

/-- `emit Sync(r0, r1);` with two plain `uint256` arguments. -/
example (fr fr1 : Frame) (m m1 : Machine) (ei : EventInfo) (e0 e1 : Expr) (r0 r1 : ℕ)
    (hr0 : r0 < 2 ^ 256) (hr1 : r1 < 2 ^ 256)
    (hev : fc.eventsNamed "Sync" = [ei])
    (hparams : ei.decl.params = [{ ty := u256Ty, indexed := false, name := some "reserve0" },
      { ty := u256Ty, indexed := false, name := some "reserve1" }])
    (htys : ei.sig.paramTypes = [.elem (.int (.uint ⟨256, by decide⟩)), .elem (.int (.uint ⟨256, by decide⟩))])
    (hanon : ei.decl.anonymous = false)
    (h0 : EvalExpr cfg o fc fr m e0 (.ok (u256Val r0) fr m)) (h1 : EvalExpr cfg o fc fr m e1 (.ok (u256Val r1) fr1 m1)) :
    ExecStmt cfg o fc fr m (.emit (.ident "Sync") (.positional [e0, e1]))
      (.normal fr1 (m1.pushLog
        { address := m1.this
          topics := #[hashWord ei.sigStr.toUTF8]
          data := (EVM.Word.toBytesBE (UInt256.ofNat r0) ++ EVM.Word.toBytesBE (UInt256.ofNat r1)).toByteArray })) := by
  have h := ExecStmt.emitStatic [⟨.u256 r0, false, some "reserve0"⟩, ⟨.u256 r1, false, some "reserve1"⟩] hev hparams htys
    hanon (by simp <;> omega) (EvalExprs.two h0 h1)
  simpa [LogVal.word, LogVal.bytes] using h

/-! ## A whole body: SimpleAuction `bid()`, success path with a previous bid to refund

```
if (block.timestamp > auctionEndTime) revert AuctionAlreadyEnded();
if (msg.value <= highestBid) revert BidNotHighEnough(highestBid);
if (highestBid != 0) { pendingReturns[highestBidder] += highestBid; }
highestBidder = msg.sender;
highestBid = msg.value;
emit HighestBidIncreased(msg.sender, msg.value);
```
The final machine is existential: `constructor` then a chain of `refine ExecBlock.cons … ?_`. -/

def bidStmts : List Stmt :=
  [ .ite (.binary .gt (.member (.ident "block") "timestamp") (.ident "auctionEndTime"))
      (.revert (.ident "AuctionAlreadyEnded") (.positional [])) none,
    .ite (.binary .le (.member (.ident "msg") "value") (.ident "highestBid"))
      (.revert (.ident "BidNotHighEnough") (.positional [.ident "highestBid"])) none,
    .ite (.binary .ne (.ident "highestBid") (.lit (.number 0 none none)))
      (.block [.exprStmt (.assign .add (.index (.ident "pendingReturns") (.ident "highestBidder")) (.ident "highestBid"))])
      none,
    .exprStmt (.assign .assign (.ident "highestBidder") (.member (.ident "msg") "sender")),
    .exprStmt (.assign .assign (.ident "highestBid") (.member (.ident "msg") "value")),
    .emit (.ident "HighestBidIncreased") (.positional [.member (.ident "msg") "sender", .member (.ident "msg") "value"]) ]

example (fr : Frame) (m : Machine)
    (vEnd vBidder vBid vPend : FlatVar) (ei : EventInfo)
    (slotEnd slotBidder slotBid : UInt256) (pendSlot : EVM.Address → UInt256)
    (hfrEnd : fr.get? "auctionEndTime" = none) (hvEnd : fc.var? "auctionEndTime" = some vEnd)
    (hmEnd : vEnd.mutability = .mutable) (htEnd : vEnd.ty = u256Ty)
    (hfrBidder : fr.get? "highestBidder" = none) (hvBidder : fc.var? "highestBidder" = some vBidder)
    (hmBidder : vBidder.mutability = .mutable) (htBidder : vBidder.ty = .address false)
    (hfrBid : fr.get? "highestBid" = none) (hvBid : fc.var? "highestBid" = some vBid)
    (hmBid : vBid.mutability = .mutable) (htBid : vBid.ty = u256Ty)
    (hfrPend : fr.get? "pendingReturns" = none) (hvPend : fc.var? "pendingReturns" = some vPend)
    (hmPend : vPend.mutability = .mutable) (htPend : vPend.ty = .mapping (.address false) u256Ty)
    (hev : fc.eventsNamed "HighestBidIncreased" = [ei])
    (hparams : ei.decl.params = [{ ty := .address false, indexed := false, name := some "bidder" },
      { ty := u256Ty, indexed := false, name := some "amount" }])
    (htys : ei.sig.paramTypes = [.elem .address, .elem (.int (.uint ⟨256, by decide⟩))])
    (hanon : ei.decl.anonymous = false)
    (hlEnd : ∀ evm, cfg.storage.layout ⟨vEnd.key, []⟩ evm = some (uint256Loc slotEnd))
    (hlBidder : ∀ evm, cfg.storage.layout ⟨vBidder.key, []⟩ evm = some (addressOffset0Loc slotBidder))
    (hlBid : ∀ evm, cfg.storage.layout ⟨vBid.key, []⟩ evm = some (uint256Loc slotBid))
    (hlPend : ∀ a evm, cfg.storage.layout (keyRef ⟨vPend.key, []⟩ (.address a)) evm = some (uint256Loc (pendSlot a)))
    (hunch : fr.unchecked = false)
    (hts : (EVM.Word.ofNat m.evm.executionEnv.header.timestamp).toNat ≤ (loadU256 m slotEnd).toNat)
    (hval : (loadU256 m slotBid).toNat < m.evm.executionEnv.weiValue.toNat)
    (hne : (loadU256 m slotBid).toNat ≠ 0)
    (hfit : (loadU256 m (pendSlot (AccountAddress.ofNat (UInt256.land (loadU256 m slotBidder) solcAddrMask).toNat))).toNat
      + (loadU256 m slotBid).toNat < UInt256.size) :
    ∃ m', ExecBlock cfg o fc fr m bidStmts (.normal (fr.exitScope fr) m') := by
  constructor
  have h1 : EvalExpr cfg o fc fr m (.binary .gt (.member (.ident "block") "timestamp") (.ident "auctionEndTime"))
      (.ok (.bool false) fr m) := by
    have h := EvalExpr.gtU256 (cfg := cfg) (o := o) (fc := fc)
      (EvalExpr.stateU256 hfrEnd hvEnd hmEnd htEnd (hlEnd m.evm)) EvalExpr.blockTimestamp
    rwa [decide_eq_false (Nat.not_lt.mpr hts)] at h
  refine ExecBlock.cons (ExecStmt.iteFalseNone h1) ?_
  have h2 : EvalExpr cfg o fc fr m (.binary .le (.member (.ident "msg") "value") (.ident "highestBid"))
      (.ok (.bool false) fr m) := by
    have h := EvalExpr.leU256 (cfg := cfg) (o := o) (fc := fc)
      (EvalExpr.stateU256 hfrBid hvBid hmBid htBid (hlBid m.evm)) EvalExpr.msgValue
    rwa [decide_eq_false (Nat.not_le.mpr hval)] at h
  refine ExecBlock.cons (ExecStmt.iteFalseNone h2) ?_
  have h3 : EvalExpr cfg o fc fr m (.binary .ne (.ident "highestBid") (.lit (.number 0 none none)))
      (.ok (.bool true) fr m) := by
    have h := EvalExpr.neU256Lit (cfg := cfg) (o := o) (fc := fc) 0 none
      (EvalExpr.stateU256 hfrBid hvBid hmBid htBid (hlBid m.evm)) (by decide)
    rwa [decide_eq_true hne] at h
  have hrefund := ExecStmt.addAssignU256 (cfg := cfg) (o := o) (fc := fc) (m := m) (b := loadU256 m slotBid)
    (EvalExpr.stateU256 hfrBid hvBid hmBid htBid (hlBid m.evm))
    (EvalLValue.mappingAddr hfrPend hvPend hmPend htPend
      (EvalExpr.stateAddress hfrBidder hvBidder hmBidder htBidder (hlBidder m.evm)))
    (hlPend _ m.evm) hunch hfit
  refine ExecBlock.cons (ExecStmt.iteTrue h3 (ExecStmt.blockNormal (ExecBlock.one hrefund))) ?_
  have hfrBidder' := exitScope_get?_of_none (fr' := fr) hfrBidder
  have hfrBid' := exitScope_get?_of_none (fr' := fr) hfrBid
  refine ExecBlock.cons (ExecStmt.assignStorageAddress EvalExpr.msgSender
    (EvalLValue.stateVarTy hfrBidder' hvBidder hmBidder htBidder) (hlBidder _)) ?_
  refine ExecBlock.cons (ExecStmt.assignStorageU256 EvalExpr.msgValue
    (EvalLValue.stateVarTy hfrBid' hvBid hmBid htBid) (hlBid _)) ?_
  refine ExecBlock.cons (ExecStmt.emitStatic
    [⟨.addr m.evm.executionEnv.source, false, some "bidder"⟩,
     ⟨.u256 m.evm.executionEnv.weiValue.toNat, false, some "amount"⟩] hev (by rw [hparams]; rfl) htys hanon
    (by simp; exact m.evm.executionEnv.weiValue.val.isLt)
    (EvalExprs.two (EvalExpr.msgSenderEq (by simp)) (EvalExpr.msgValueEq (by simp)))) ?_
  exact ExecBlock.nil

/-! ## Scopes

A function-entry frame with a parameter `a` and a return variable `r`.  A block-local is gone after
the block, an assignment made inside stays, a shadowed binding comes back, and the return values are
read after the body's own locals are dropped. -/

def entryFrame : Frame :=
  (({ here := "C", locals := ∅, retVars := ["r"] } : Frame).bind "a" u256Ty (some .memory) (u256Val 7)).bind
    "r" u256Ty (some .memory) (u256Val 0)

example : entryFrame.hidden = [] := by simp [entryFrame]

example : (entryFrame.exitScope ((entryFrame.bind "t" u256Ty none (u256Val 1)).setVal "r" (u256Val 5))).get? "t" =
    none := by
  simp [entryFrame]

example : ((entryFrame.exitScope ((entryFrame.bind "t" u256Ty none (u256Val 1)).setVal "r" (u256Val 5))).get?
    "r").map (·.val) = some (u256Val 5) := by
  simp [entryFrame]

/-- `{ uint256 a = 99; }`: the parameter `a` is visible again after the block. -/
example : ((entryFrame.exitScope (entryFrame.bind "a" u256Ty none (u256Val 99))).get? "a").map (·.val) =
    some (u256Val 7) := by
  rw [exitScope_get?_shadow (x := "a") (l := { ty := u256Ty, loc := some .memory, val := u256Val 7 }) "a"
    (by simp [entryFrame, Frame.hidden_bind])]
  simp [entryFrame]

example : retVals (entryFrame.exitScope (entryFrame.setVal "r" (u256Val 5))) = some [u256Val 5] :=
  retVals_exitScope (by simp) (by simp [entryFrame]) (by simp [retVals, entryFrame])

end Solidity.Usage
