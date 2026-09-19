import Solidity.Examples.ERC20.Common

/-!
# ERC20 — `transfer(address,uint256)` refines its Solidity body (core relation)

Success, the `require` failure (`Error("ERC20: insufficient balance")`) and the checked-add
overflow (`Panic(0x11)`), each coupled with the pinned EVM trace.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace ERC20.SolidityProof

/-! ## Arguments -/

theorem erc20Args_transfer_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hcanon : (transferToWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnTransfer.decl I.calldata =
      some [transferToValue I, transferValueValue I] := by
  rw [decodeArgs_unfold _ _ sigTransfer sigOf_transfer]
  have h := decodeCalldata_addr_uint256_ok (cd := I.calldata) (x := "to") (y := "value") hsz68 hbig hcanon
  simp only [fnTransfer, List.zipIdx, List.map, paramName, Option.getD, sigTransfer]
  rw [h]
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, transferToValue, transferValueValue,
    transferToWord, transferValueWord, calldataWord, -getElem?_pos, -getElem?_neg]
  exact ⟨rfl, rfl⟩

theorem erc20Args_transfer_none_short {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 68) :
    decodeArgs erc20Cfg erc20Flat.types fnTransfer.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigTransfer sigOf_transfer]
  simp only [fnTransfer, List.zipIdx, List.map, paramName, Option.getD, sigTransfer]
  rw [decodeCalldata_addr_uint256_none_short (cd := I.calldata) (x := "to") (y := "value") hsz4 hshort]
  rfl

theorem erc20Args_transfer_none_noncanon {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hnc : ¬ (transferToWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnTransfer.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigTransfer sigOf_transfer]
  simp only [fnTransfer, List.zipIdx, List.map, paramName, Option.getD, sigTransfer]
  rw [decodeCalldata_addr_uint256_none_noncanon (cd := I.calldata) (x := "to") (y := "value") hsz68 hbig hnc]
  rfl

theorem erc20Args_transfer_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeArgs erc20Cfg erc20Flat.types fnTransfer.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigTransfer sigOf_transfer]
  simp only [fnTransfer, List.zipIdx, List.map, paramName, Option.getD, sigTransfer]
  rw [decodeCalldata_addr_uint256_none_huge (cd := I.calldata) (x := "to") (y := "value") hbig]
  rfl

/-! ## The spec derivations -/

def trFrame (a : EVM.Address) (w : UInt256) : Frame :=
  ((({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "to" addrTy (some .memory)
    (.address a)).bind "value" u256 (some .memory) (u256Val w.toNat)).bind "#ret0" .bool (some .memory) (.bool false)

def trCond : Expr := .binary .ge (.index (.ident "balanceOf") msgSender) (.ident "value")
def trMsg : Expr := .lit (.str "ERC20: insufficient balance")

def trStmts : Block :=
  [ .exprStmt (.call (.ident "require") [] (.positional [trCond, trMsg])),
    .exprStmt (.assign .sub (.index (.ident "balanceOf") msgSender) (.ident "value")),
    .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
    .emit (.ident "Transfer") (.positional [msgSender, .ident "to", .ident "value"]),
    .return (some (.lit (.bool true))) ]

theorem trEnter (m : Machine) (a : EVM.Address) (w : UInt256) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnTransfer.decl [.address a, u256Val w.toNat] m =
      some (.ok (trFrame a w, m)) := by
  simp [enterFn, declare, coerce, fnTransfer, trFrame, fuelDefault]
  try rfl

abbrev trFr (a : EVM.Address) (w : UInt256) : Frame := bodyFrame (trFrame a w) trStmts

/-- The sender's balance word. -/
abbrev senderBal (m : Machine) : UInt256 :=
  Storage.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner (erc20BalanceOfSlot (.address m.evm.executionEnv.source))

/-- The machine after `balanceOf[msg.sender] -= value` (the sender's balance word is `bal`). -/
def trDebited (m : Machine) (w : UInt256) : Machine :=
  { m with evm := (Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner
      (erc20BalanceOfSlot (.address m.evm.executionEnv.source)) (UInt256.ofNat ((senderBal m).toNat - w.toNat))) }

/-- The recipient's balance word after the debit. -/
abbrev toBal (m : Machine) (a : EVM.Address) (w : UInt256) : UInt256 :=
  Storage.EVM.storageLoad (trDebited m w).evm (trDebited m w).evm.executionEnv.codeOwner (erc20BalanceOfSlot (.address a))

/-- The machine after both stores. -/
def trCredited (m : Machine) (a : EVM.Address) (w : UInt256) : Machine :=
  { trDebited m w with evm := (Storage.EVM.storageStore (trDebited m w).evm (trDebited m w).evm.executionEnv.codeOwner
      (erc20BalanceOfSlot (.address a)) (UInt256.ofNat ((toBal m a w).toNat + w.toNat))) }

/-- `balanceOf[msg.sender]` as a value. -/
theorem evalBalanceOfSender (o : Oracle) (fr : Frame) (m : Machine) (hb : fr.get? "balanceOf" = none) :
    EvalExpr erc20Cfg o erc20Flat fr m (.index (.ident "balanceOf") msgSender) (.ok (u256Val (senderBal m).toNat) fr m) :=
  EvalExpr.indexStorage (EvalExpr.stateVar hb erc20Flat_var_balanceOf rfl (loadIfScalar_mapping ..))
    (EvalExpr.envMember rfl (envMember_sender m)) (storageIndex_mapping_address ..)
    (loadIfScalar_u256 (env := erc20Flat.types) (erc20Layout_balanceOf m.evm.executionEnv.source m.evm))

/-- `balanceOf[msg.sender]` as an lvalue. -/
theorem lvalBalanceOfSender (o : Oracle) (fr : Frame) (m : Machine) (hb : fr.get? "balanceOf" = none) :
    EvalLValue erc20Cfg o erc20Flat fr m (.index (.ident "balanceOf") msgSender)
      (.ok (.storage ⟨"balanceOf", [.mindex (.address m.evm.executionEnv.source)]⟩ u256) fr m) :=
  EvalLValue.indexStorage (EvalExpr.stateVar hb erc20Flat_var_balanceOf rfl (loadIfScalar_mapping ..))
    (EvalExpr.envMember rfl (envMember_sender m)) (storageIndex_mapping_address ..)

/-- `balanceOf[k]` as an lvalue, for a local address `k`. -/
theorem lvalBalanceOfLocal (o : Oracle) (fr : Frame) (m : Machine) (x : Ident) (a : EVM.Address)
    (hx : fr.get? x = some { ty := addrTy, loc := some .memory, val := .address a })
    (hb : fr.get? "balanceOf" = none) :
    EvalLValue erc20Cfg o erc20Flat fr m (.index (.ident "balanceOf") (.ident x))
      (.ok (.storage ⟨"balanceOf", [.mindex (.address a)]⟩ u256) fr m) :=
  EvalLValue.indexStorage (EvalExpr.stateVar hb erc20Flat_var_balanceOf rfl (loadIfScalar_mapping ..))
    (EvalExpr.local hx) (storageIndex_mapping_address ..)

/-- The `require` condition evaluates to `value ≤ balanceOf[msg.sender]`. -/
theorem trEvalCond (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) :
    EvalExpr erc20Cfg o erc20Flat (trFr a w) m trCond
      (.ok (.bool (decide (w.toNat ≤ (senderBal m).toNat))) (trFr a w) m) :=
  EvalExpr.binary (by decide) (by decide) (evalBalanceOfSender o _ m (by frame_simp [trFr, bodyFrame, trFrame]))
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [trFr, bodyFrame, trFrame])) (binop_ge_u256 ..)

/-- `require` fails: `Error("ERC20: insufficient balance")`. -/
theorem trBodyInsufficient (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (hlt : (senderBal m).toNat < w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (trFr a w) m trStmts
      (.reverted (errorStringData "ERC20: insufficient balance".toUTF8)) := by
  have hc := trEvalCond o m a w
  rw [decide_eq_false (by omega)] at hc
  exact ExecBlock.consRevert (ExecStmt.exprStmtRevert (EvalExpr.requireMsg rfl hc (EvalExpr.lit rfl) rfl))

/-- The debit assignment `balanceOf[msg.sender] -= value`. -/
theorem trDebit (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) (henough : w.toNat ≤ (senderBal m).toNat) :
    ExecStmt erc20Cfg o erc20Flat (trFr a w) m (.exprStmt (.assign .sub (.index (.ident "balanceOf") msgSender) (.ident "value")))
      (.normal (trFr a w) (trDebited m w)) := by
  have hassign := assign_storage_u256 (env := erc20Flat.types) (fr := trFr a w)
    (erc20Layout_balanceOf m.evm.executionEnv.source m.evm) (UInt256.ofNat ((senderBal m).toNat - w.toNat))
  have hb : (senderBal m).toNat < UInt256.size := (senderBal m).val.isLt
  rw [ulit_toNat' _ (by omega)] at hassign
  refine ExecStmt.exprStmt (EvalExpr.assignCompound (cur := u256Val (senderBal m).toNat) (r := u256Val ((senderBal m).toNat - w.toNat))
    rfl (by decide) (EvalExpr.localVal u256 (some .memory) (by frame_simp [trFr, bodyFrame, trFrame]))
    (lvalBalanceOfSender o _ m (by frame_simp [trFr, bodyFrame, trFrame]))
    (readLValue_storage_u256 (erc20Layout_balanceOf m.evm.executionEnv.source m.evm))
    (binop_sub_u256_ok _ _ (senderBal m).val.isLt henough) hassign)

/-- The credit assignment `balanceOf[to] += value` (no overflow). -/
theorem trCredit (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (hfit : (toBal m a w).toNat + w.toNat < UInt256.size) :
    ExecStmt erc20Cfg o erc20Flat (trFr a w) (trDebited m w)
      (.exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")))
      (.normal (trFr a w) (trCredited m a w)) := by
  have hassign := assign_storage_u256 (env := erc20Flat.types) (fr := trFr a w)
    (erc20Layout_balanceOf a (trDebited m w).evm) (UInt256.ofNat ((toBal m a w).toNat + w.toNat))
  rw [ulit_toNat' _ hfit] at hassign
  refine ExecStmt.exprStmt (EvalExpr.assignCompound (cur := u256Val (toBal m a w).toNat)
    (r := u256Val ((toBal m a w).toNat + w.toNat))
    rfl (by decide) (EvalExpr.localVal u256 (some .memory) (by frame_simp [trFr, bodyFrame, trFrame]))
    (lvalBalanceOfLocal o _ _ "to" a (by frame_simp [trFr, bodyFrame, trFrame]) (by frame_simp [trFr, bodyFrame, trFrame]))
    (readLValue_storage_u256 (erc20Layout_balanceOf a (trDebited m w).evm))
    (binop_add_u256_ok _ _ hfit) hassign)

/-- The credit assignment overflows: `Panic(0x11)`. -/
theorem trCreditOverflow (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (hover : UInt256.size ≤ (toBal m a w).toNat + w.toNat) :
    ExecStmt erc20Cfg o erc20Flat (trFr a w) (trDebited m w)
      (.exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")))
      (.reverted (panicData 0x11)) :=
  ExecStmt.exprStmtRevert (EvalExpr.assignCompoundPanic (cur := u256Val (toBal m a w).toNat) (p := .overflow)
    rfl (by decide) (EvalExpr.localVal u256 (some .memory) (by frame_simp [trFr, bodyFrame, trFrame]))
    (lvalBalanceOfLocal o _ _ "to" a (by frame_simp [trFr, bodyFrame, trFrame]) (by frame_simp [trFr, bodyFrame, trFrame]))
    (readLValue_storage_u256 (erc20Layout_balanceOf a (trDebited m w).evm))
    (binop_add_u256_overflow _ _ hover))

theorem trBodyOk (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (henough : w.toNat ≤ (senderBal m).toNat) (hfit : (toBal m a w).toNat + w.toNat < UInt256.size) :
    ∃ le, ExecBlock erc20Cfg o erc20Flat (trFr a w) m trStmts
      (.returned ((trFr a w).setVal "#ret0" (.bool true)) ((trCredited m a w).pushLog le)) := by
  obtain ⟨le, hle⟩ := mkLogEntry_evTransfer (trCredited m a w).this m.evm.executionEnv.source a w
  have hc := trEvalCond o m a w
  rw [decide_eq_true henough] at hc
  refine ⟨le, ExecBlock.cons (fr1 := trFr a w) (m1 := m) (ExecStmt.exprStmt (EvalExpr.requireTrue hc))
    (ExecBlock.cons (fr1 := trFr a w) (m1 := trDebited m w) (trDebit o m a w henough)
      (ExecBlock.cons (fr1 := trFr a w) (m1 := trCredited m a w) (trCredit o m a w hfit)
        (ExecBlock.cons (fr1 := trFr a w) (m1 := (trCredited m a w).pushLog le) ?_ (ExecBlock.consReturn ?_))))⟩
  · refine ExecStmt.emit (vs := [.address m.evm.executionEnv.source, .address a, u256Val w.toNat])
      (fr1 := trFr a w) (m1 := trCredited m a w) erc20Flat_event_Transfer rfl ?_ (abiArgs_addr_addr_u256 ..) ?_
    · refine EvalExprs.cons (EvalExpr.envMember rfl ?_) (EvalExprs.cons (EvalExpr.localVal addrTy (some .memory) ?_)
        (EvalExprs.cons (EvalExpr.localVal u256 (some .memory) ?_) EvalExprs.nil))
      · rw [envMember_sender]; simp [trCredited, trDebited, storageStore_executionEnv]
      · frame_simp [trFr, bodyFrame, trFrame]
      · frame_simp [trFr, bodyFrame, trFrame]
    · exact hle
  · refine ExecStmt.returnSingle (r := "#ret0") (v := .bool true) (fr1 := trFr a w)
      (m1 := (trCredited m a w).pushLog le) rfl (EvalExpr.lit rfl) ?_
    frame_simp [assign, coerce, trFr, bodyFrame, trFrame]
    try rfl

theorem trBodyOverflow (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (henough : w.toNat ≤ (senderBal m).toNat) (hover : UInt256.size ≤ (toBal m a w).toNat + w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (trFr a w) m trStmts (.reverted (panicData 0x11)) := by
  have hc := trEvalCond o m a w
  rw [decide_eq_true henough] at hc
  exact ExecBlock.cons (fr1 := trFr a w) (m1 := m) (ExecStmt.exprStmt (EvalExpr.requireTrue hc))
    (ExecBlock.cons (fr1 := trFr a w) (m1 := trDebited m w) (trDebit o m a w henough)
      (ExecBlock.consRevert (trCreditOverflow o m a w hover)))

/-! ## The calls -/

theorem trCallOk (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256)
    (henough : w.toNat ≤ (senderBal m).toNat) (hfit : (toBal m a w).toNat + w.toNat < UInt256.size) :
    ∃ le, CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTransfer [.address a, u256Val w.toNat]
      (.ok [.bool true] ((trCredited m a w).pushLog le)) := by
  obtain ⟨le, hb⟩ := trBodyOk o m a w henough hfit
  refine ⟨le, CallFn.ok (trEnter m a w) EvalMods.nil rfl (ExecChain.body hb) rfl ?_⟩
  frame_simp [retVals, trFr, bodyFrame, trFrame]

theorem trCallRevert (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) (d : ByteArray)
    (hb : ExecBlock erc20Cfg o erc20Flat (trFr a w) m trStmts (.reverted d)) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTransfer [.address a, u256Val w.toNat] (.reverted d) :=
  CallFn.reverted (trEnter m a w) EvalMods.nil rfl (ExecChain.body hb)

/-! ## The dispatch-level spec runs -/

abbrev trM (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) : Machine :=
  initMachine cA gh bl σ σ₀ g A I
abbrev trTo (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (transferToWord I).toNat

theorem erc20TransferSpecOk (o : Oracle) {cA gh bl σ σ₀ g A I}
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤ (senderBal (trM cA gh bl σ σ₀ g A I)).toNat)
    (hfit : (toBal (trM cA gh bl σ σ₀ g A I) (trTo I) (transferValueWord I)).toNat + (transferValueWord I).toNat <
      UInt256.size) :
    ∃ le, solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I
      (.returned ((trCredited (trM cA gh bl σ σ₀ g A I) (trTo I) (transferValueWord I)).pushLog le) [.bool true])
      (.abi [.elem .bool]) := by
  obtain ⟨le, hc⟩ := trCallOk o (trM cA gh bl σ σ₀ g A I) (trTo I) (transferValueWord I) henough hfit
  exact ⟨le, solidityExec.call (erc20Dispatch_transfer hsel) erc20Flat_fns1 (Or.inr hwv) rfl
    (erc20Args_transfer_ok hsz68 hbig hcanon) (by simp [ofAbiList, fnTransfer, fuelDefault]) hc
    (by simp [fuelDefault])⟩

theorem erc20TransferSpecRevert (o : Oracle) {cA gh bl σ σ₀ g A I} {d : ByteArray}
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferToWord I).toNat < EVM.addressModulus)
    (hb : ExecBlock erc20Cfg o erc20Flat (trFr (trTo I) (transferValueWord I)) (trM cA gh bl σ σ₀ g A I) trStmts
      (.reverted d)) :
    solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I (.reverted d) (.abi [.elem .bool]) :=
  solidityExec.callReverted (erc20Dispatch_transfer hsel) erc20Flat_fns1 (Or.inr hwv) rfl
    (erc20Args_transfer_ok hsz68 hbig hcanon) (by simp [ofAbiList, fnTransfer, fuelDefault])
    (trCallRevert o _ _ _ d hb)

theorem erc20TransferRejects {I : ExecutionEnv}
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hdec : decodeArgs erc20Cfg erc20Flat.types fnTransfer.decl I.calldata = none)
    {cA gh bl σ_evm σ_spec σ₀ A} {g : UInt256} (hcode : I.code = erc20Bytecode)
    (h : RDrev erc20Bytecode (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have := RDrev.specDecodingFailedCore (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode h
    (erc20Dispatch_transfer hsel) erc20Flat_fns1 (Or.inr hwv) hdec
  simpa [Sat256.ofUInt256, Sat256.toUInt256] using this

/-! ## The coupled result -/

theorem erc20TransferCore {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨274⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hsz4 := erc20TransferSelector_size hsel
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_spec σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hFromBalance : transferFromBalanceWord evmE = transferFromBalanceWord evmS := by
    unfold transferFromBalanceWord transferSenderSlot
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (erc20BalanceOfSlot (.address evmS.executionEnv.source))
  have hDebit : transferDebitWord evmE I = transferDebitWord evmS I := by
    simp [transferDebitWord, hFromBalance]
  have hσDebit : EVMStateEquiv (transferAfterDebitState evmE I) (transferAfterDebitState evmS I) := by
    unfold transferAfterDebitState transferSenderSlot
    rw [hσ.executionEnv, hDebit]
    exact hσ.storageStore_codeOwner (erc20BalanceOfSlot (.address evmS.executionEnv.source)) rfl
  have hToBalance : transferToBalanceWord evmE I = transferToBalanceWord evmS I := by
    unfold transferToBalanceWord
    exact hσDebit.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferToSlot I)
  have hNewToNat : transferNewToNat evmE I = transferNewToNat evmS I := by
    simp [transferNewToNat, hToBalance]
  have hNewToWord : transferNewToWord evmE I = transferNewToWord evmS I := by
    simp [transferNewToWord, hNewToNat]
  have hσPost : EVMStateEquiv (transferPostState evmE I) (transferPostState evmS I) := by
    unfold transferPostState
    rw [hσ.executionEnv, hNewToWord]
    exact hσDebit.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferToSlot I) rfl
  -- the spec machines are the Sol⁻ post-states over `σ_spec`
  have hmS : (trM cA gh bl σ_spec σ₀ g A I).evm = evmS := rfl
  have hSender : senderBal (trM cA gh bl σ_spec σ₀ g A I) = transferFromBalanceWord evmS := rfl
  have hDebited : (trDebited (trM cA gh bl σ_spec σ₀ g A I) (transferValueWord I)).evm =
      transferAfterDebitState evmS I := rfl
  have hToBal : toBal (trM cA gh bl σ_spec σ₀ g A I) (trTo I) (transferValueWord I) = transferToBalanceWord evmS I := by
    show Storage.EVM.storageLoad (transferAfterDebitState evmS I) (transferAfterDebitState evmS I).executionEnv.codeOwner
      (transferToSlot I) = _
    rw [transferAfterDebitState, storageStore_executionEnv]
    rfl
  have hCredited : (trCredited (trM cA gh bl σ_spec σ₀ g A I) (trTo I) (transferValueWord I)).evm =
      transferPostState evmS I := by
    show Storage.EVM.storageStore (transferAfterDebitState evmS I) (transferAfterDebitState evmS I).executionEnv.codeOwner
      (transferToSlot I) (UInt256.ofNat ((toBal (trM cA gh bl σ_spec σ₀ g A I) (trTo I) (transferValueWord I)).toNat +
        (transferValueWord I).toNat)) = _
    rw [hToBal, transferAfterDebitState, storageStore_executionEnv]
    rfl
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonTo : (transferToWord I).toNat < EVM.addressModulus
      · by_cases henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evmE).toNat
        · have henoughS : (transferValueWord I).toNat ≤ (senderBal (trM cA gh bl σ_spec σ₀ g A I)).toNat := by
            rw [hSender, ← hFromBalance]; exact henough
          by_cases hfit : transferNewToNat evmE I < UInt256.size
          · have hfitS : (toBal (trM cA gh bl σ_spec σ₀ g A I) (trTo I) (transferValueWord I)).toNat +
                (transferValueWord I).toNat < UInt256.size := by
              rw [hToBal, ← hToBalance]; exact hfit
            have hX := erc20X_transfer (g := Sat256.ofUInt256 g) hsz68 hsize hbig hperm hcanonTo henough hfit hreach
            obtain ⟨le, hspec⟩ := erc20TransferSpecOk (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀)
              (g := g) (A := A) noOracle hsel hwv hsz68 hbig hcanonTo henoughS hfitS
            have h := RDret.specExecutionCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
              (by
                rw [pushLog_evm_createdAccounts, hCredited, ← hσPost.createdAccounts]
                simp [evmE, initState, transferPostState, transferAfterDebitState, storageStore_createdAccounts])
              (by
                rw [pushLog_evm_accountMap, hCredited]
                refine Refinement.accountMapEquiv.trans (Refinement.accountMapEquiv.of_eq ?_) hσPost.accountMap
                simp [evmE, initState, transferPostState, transferAfterDebitState, transferSenderSlot,
                  transferSenderSlotI, storageStore_accountMap, storageStore_executionEnv])
              (.abi boolTrueReturnEncoding)
            simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
          · have hover : UInt256.size ≤ transferNewToNat evmE I := by omega
            have hoverS : UInt256.size ≤ (toBal (trM cA gh bl σ_spec σ₀ g A I) (trTo I) (transferValueWord I)).toNat +
                (transferValueWord I).toNat := by
              rw [hToBal, ← hToBalance]; exact hover
            have hX := erc20TransferX_overflow (g := Sat256.ofUInt256 g) hsz68 hsize hbig hperm hcanonTo henough hover
              hreach
            have hspec := erc20TransferSpecRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀) (g := g)
              (A := A) noOracle hsel hwv hsz68 hbig hcanonTo (trBodyOverflow noOracle _ _ _ henoughS hoverS)
            have h := RDrev.specRevertCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
            simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
        · have hlt : (transferFromBalanceWord evmE).toNat < (transferValueWord I).toNat := by omega
          have hltS : (senderBal (trM cA gh bl σ_spec σ₀ g A I)).toNat < (transferValueWord I).toNat := by
            rw [hSender, ← hFromBalance]; exact hlt
          have hX := erc20TransferX_insufficient (g := Sat256.ofUInt256 g) hsz68 hsize hbig hcanonTo hlt hreach
          have hspec := erc20TransferSpecRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀) (g := g)
            (A := A) noOracle hsel hwv hsz68 hbig hcanonTo (trBodyInsufficient noOracle _ _ _ hltS)
          have h := RDrev.specRevertCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
          simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
      · have hnc : UInt256.eq (transferToWord I) (UInt256.land (transferToWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanonTo (erc20Word_canonical_of_clean he))
        exact erc20TransferRejects hsel hwv (erc20Args_transfer_none_noncanon hsz68 hbig hcanonTo) hcode
          (erc20TransferX_noncanon_to (g := Sat256.ofUInt256 g) hsz68 hsize hbig hnc hreach)
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact erc20TransferRejects hsel hwv (erc20Args_transfer_none_huge hbigge) hcode
        (erc20TransferX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
  · have hshort : I.calldata.size < 68 := by omega
    exact erc20TransferRejects hsel hwv (erc20Args_transfer_none_short hsz4 hshort) hcode
      (erc20TransferX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)

end ERC20.SolidityProof
