import Solidity.Examples.ERC20.BalanceOf
import Solidity.Examples.ERC20.Transfer

/-!
# ERC20 — `transferFrom(address,address,uint256)` refines its Solidity body (core relation)

Success, the two `require` failures, the balance-debit underflow and the credit overflow
(both `Panic(0x11)`), each coupled with the pinned EVM trace.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace ERC20.SolidityProof

/-! ## Arguments -/

set_option maxHeartbeats 2000000 in
theorem erc20Args_transferFrom_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl I.calldata =
      some [.address (AccountAddress.ofNat (transferFromFromWord I).toNat),
        .address (AccountAddress.ofNat (transferFromToWord I).toNat),
        .int (Int.ofNat (transferFromValueWord I).toNat)] := by
  rw [decodeArgs_unfold _ _ sigTransferFrom sigOf_transferFrom]
  exact decodeCalldataValues_address_address_uint256_ok hsz100 hbig hcanonFrom hcanonTo

theorem erc20Args_transferFrom_none_short {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 100) :
    decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigTransferFrom sigOf_transferFrom]
  exact decodeCalldataValues_address_address_uint256_none_short hsz4 hshort

theorem erc20Args_transferFrom_none_noncanon0 {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hnc : ¬ (transferFromFromWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigTransferFrom sigOf_transferFrom]
  exact decodeCalldataValues_address_address_uint256_none_noncanon0 hsz100 hbig hnc

theorem erc20Args_transferFrom_none_noncanon1 {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hcanon0 : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (transferFromToWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigTransferFrom sigOf_transferFrom]
  exact decodeCalldataValues_address_address_uint256_none_noncanon1 hsz100 hbig hcanon0 hnc

theorem erc20Args_transferFrom_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigTransferFrom sigOf_transferFrom]
  exact decodeCalldataValues_address_address_uint256_none_huge hbig

/-! ## The spec derivations -/

def tfFrame (f t : EVM.Address) (w : UInt256) : Frame :=
  (((({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "from" addrTy (some .memory)
    (.address f)).bind "to" addrTy (some .memory) (.address t)).bind "value" u256 (some .memory)
    (u256Val w.toNat)).bind "#ret0" .bool (some .memory) (.bool false)

def tfAllowanceExpr : Expr := .index (.index (.ident "allowance") (.ident "from")) msgSender
def tfCond1 : Expr := .binary .ge (.ident "currentAllowance") (.ident "value")
def tfMsg1 : Expr := .lit (.str "ERC20: insufficient allowance")
def tfCond2 : Expr := .binary .ge (.index (.ident "balanceOf") (.ident "from")) (.ident "value")
def tfMsg2 : Expr := .lit (.str "ERC20: insufficient balance")

def tfStmts : Block :=
  [ .varDecl u256 none "currentAllowance" (some tfAllowanceExpr),
    .exprStmt (.call (.ident "require") [] (.positional [tfCond1, tfMsg1])),
    .exprStmt (.call (.ident "require") [] (.positional [tfCond2, tfMsg2])),
    .exprStmt (.assign .assign tfAllowanceExpr (.binary .sub (.ident "currentAllowance") (.ident "value"))),
    .exprStmt (.assign .sub (.index (.ident "balanceOf") (.ident "from")) (.ident "value")),
    .exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")),
    .emit (.ident "Transfer") (.positional [.ident "from", .ident "to", .ident "value"]),
    .return (some (.lit (.bool true))) ]

theorem tfEnter (m : Machine) (f t : EVM.Address) (w : UInt256) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnTransferFrom.decl [.address f, .address t, u256Val w.toNat] m =
      some (.ok (tfFrame f t w, m)) := by
  simp [enterFn, declare, coerce, fnTransferFrom, tfFrame, fuelDefault]
  try rfl

abbrev tfFr (f t : EVM.Address) (w : UInt256) : Frame := bodyFrame (tfFrame f t w) tfStmts

/-- `allowance[from][msg.sender]`. -/
abbrev curAllow (m : Machine) (f : EVM.Address) : UInt256 :=
  Storage.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner
    (erc20AllowanceSlot (.address f) (.address m.evm.executionEnv.source))

/-- The frame after `uint256 currentAllowance = allowance[from][msg.sender];`. -/
abbrev tfFr2 (f t : EVM.Address) (w : UInt256) (m : Machine) : Frame :=
  (tfFr f t w).bind "currentAllowance" u256 none (u256Val (curAllow m f).toNat)

/-- `balanceOf[from]`. -/
abbrev fromBal (m : Machine) (f : EVM.Address) : UInt256 :=
  Storage.EVM.storageLoad m.evm m.evm.executionEnv.codeOwner (erc20BalanceOfSlot (.address f))

/-- After the allowance store. -/
def tfM1 (m : Machine) (f : EVM.Address) (w : UInt256) : Machine :=
  { m with evm := (Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner
      (erc20AllowanceSlot (.address f) (.address m.evm.executionEnv.source))
      (UInt256.ofNat ((curAllow m f).toNat - w.toNat))) }

/-- After the sender's debit. -/
def tfM2 (m : Machine) (f : EVM.Address) (w : UInt256) : Machine :=
  { tfM1 m f w with evm := (Storage.EVM.storageStore (tfM1 m f w).evm (tfM1 m f w).evm.executionEnv.codeOwner
      (erc20BalanceOfSlot (.address f)) (UInt256.ofNat ((fromBal (tfM1 m f w) f).toNat - w.toNat))) }

/-- After the recipient's credit. -/
def tfM3 (m : Machine) (f t : EVM.Address) (w : UInt256) : Machine :=
  { tfM2 m f w with evm := (Storage.EVM.storageStore (tfM2 m f w).evm (tfM2 m f w).evm.executionEnv.codeOwner
      (erc20BalanceOfSlot (.address t)) (UInt256.ofNat ((fromBal (tfM2 m f w) t).toNat + w.toNat))) }

/-- `allowance[k][msg.sender]` as a value, for a local address `k`. -/
theorem evalAllowanceLocalSender (o : Oracle) (fr : Frame) (m : Machine) (x : Ident) (f : EVM.Address)
    (hx : fr.get? x = some { ty := addrTy, loc := some .memory, val := .address f })
    (hb : fr.get? "allowance" = none) :
    EvalExpr erc20Cfg o erc20Flat fr m (.index (.index (.ident "allowance") (.ident x)) msgSender)
      (.ok (u256Val (curAllow m f).toNat) fr m) := by
  have h1 : EvalExpr erc20Cfg o erc20Flat fr m (.index (.ident "allowance") (.ident x))
      (.ok (.storageRef ⟨"allowance", [.mindex (.address f)]⟩ (.mapping addrTy u256)) fr m) :=
    EvalExpr.indexStorage (EvalExpr.stateVar hb erc20Flat_var_allowance rfl (loadIfScalar_mapping ..))
      (EvalExpr.local hx) (storageIndex_mapping_address ..) (loadIfScalar_mapping ..)
  exact EvalExpr.indexStorage h1 (EvalExpr.envMember rfl (envMember_sender m)) (storageIndex_mapping_address ..)
    (loadIfScalar_u256 (env := erc20Flat.types) (erc20Layout_allowance f m.evm.executionEnv.source m.evm))

/-- `allowance[k][msg.sender]` as an lvalue, for a local address `k`. -/
theorem lvalAllowanceLocalSender (o : Oracle) (fr : Frame) (m : Machine) (x : Ident) (f : EVM.Address)
    (hx : fr.get? x = some { ty := addrTy, loc := some .memory, val := .address f })
    (hb : fr.get? "allowance" = none) :
    EvalLValue erc20Cfg o erc20Flat fr m (.index (.index (.ident "allowance") (.ident x)) msgSender)
      (.ok (.storage ⟨"allowance", [.mindex (.address f), .mindex (.address m.evm.executionEnv.source)]⟩ u256) fr m) := by
  have h1 : EvalExpr erc20Cfg o erc20Flat fr m (.index (.ident "allowance") (.ident x))
      (.ok (.storageRef ⟨"allowance", [.mindex (.address f)]⟩ (.mapping addrTy u256)) fr m) :=
    EvalExpr.indexStorage (EvalExpr.stateVar hb erc20Flat_var_allowance rfl (loadIfScalar_mapping ..))
      (EvalExpr.local hx) (storageIndex_mapping_address ..) (loadIfScalar_mapping ..)
  exact EvalLValue.indexStorage h1 (EvalExpr.envMember rfl (envMember_sender m)) (storageIndex_mapping_address ..)

/-- `uint256 currentAllowance = allowance[from][msg.sender];` -/
theorem tfDecl (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) :
    ExecStmt erc20Cfg o erc20Flat (tfFr f t w) m (.varDecl u256 none "currentAllowance" (some tfAllowanceExpr))
      (.normal (tfFr2 f t w m) m) := by
  refine ExecStmt.varDecl (v := u256Val (curAllow m f).toNat) (fr1 := tfFr f t w) (m1 := m)
    (evalAllowanceLocalSender o _ m "from" f (by frame_simp [tfFr, bodyFrame, tfFrame])
      (by frame_simp [tfFr, bodyFrame, tfFrame])) ?_
  frame_simp [declare, coerce, tfFr2]
  try rfl

theorem tfEvalCond1 (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) :
    EvalExpr erc20Cfg o erc20Flat (tfFr2 f t w m) m tfCond1
      (.ok (.bool (decide (w.toNat ≤ (curAllow m f).toNat))) (tfFr2 f t w m) m) :=
  EvalExpr.binary (by decide) (by decide)
    (EvalExpr.localVal u256 none (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])) (binop_ge_u256 ..)

theorem tfEvalCond2 (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) :
    EvalExpr erc20Cfg o erc20Flat (tfFr2 f t w m) m tfCond2
      (.ok (.bool (decide (w.toNat ≤ (fromBal m f).toNat))) (tfFr2 f t w m) m) :=
  EvalExpr.binary (by decide) (by decide)
    (evalBalanceOfIndex o _ m "from" f (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])
      (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])) (binop_ge_u256 ..)

/-- `allowance[from][msg.sender] = currentAllowance - value;` -/
theorem tfAllowStore (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hallow : w.toNat ≤ (curAllow m f).toNat) :
    ExecStmt erc20Cfg o erc20Flat (tfFr2 f t w m) m
      (.exprStmt (.assign .assign tfAllowanceExpr (.binary .sub (.ident "currentAllowance") (.ident "value"))))
      (.normal (tfFr2 f t w m) (tfM1 m f w)) := by
  have hb : (curAllow m f).toNat < UInt256.size := (curAllow m f).val.isLt
  have hassign := assign_storage_u256 (env := erc20Flat.types) (fr := tfFr2 f t w m)
    (erc20Layout_allowance f m.evm.executionEnv.source m.evm) (UInt256.ofNat ((curAllow m f).toNat - w.toNat))
  rw [ulit_toNat' _ (by omega)] at hassign
  refine ExecStmt.exprStmt (EvalExpr.assignPlain (v := u256Val ((curAllow m f).toNat - w.toNat)) (fr1 := tfFr2 f t w m)
    (m1 := m) rfl ?_
    (lvalAllowanceLocalSender o _ m "from" f (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])
      (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])) hassign)
  exact EvalExpr.binary (by decide) (by decide)
    (EvalExpr.localVal u256 none (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (EvalExpr.localVal u256 (some .memory) (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (binop_sub_u256_ok _ _ hb hallow)

/-- `balanceOf[from] -= value;` (no underflow). -/
theorem tfDebit (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hdebit : w.toNat ≤ (fromBal (tfM1 m f w) f).toNat) :
    ExecStmt erc20Cfg o erc20Flat (tfFr2 f t w m) (tfM1 m f w)
      (.exprStmt (.assign .sub (.index (.ident "balanceOf") (.ident "from")) (.ident "value")))
      (.normal (tfFr2 f t w m) (tfM2 m f w)) := by
  have hb : (fromBal (tfM1 m f w) f).toNat < UInt256.size := (fromBal (tfM1 m f w) f).val.isLt
  have hassign := assign_storage_u256 (env := erc20Flat.types) (fr := tfFr2 f t w m)
    (erc20Layout_balanceOf f (tfM1 m f w).evm) (UInt256.ofNat ((fromBal (tfM1 m f w) f).toNat - w.toNat))
  rw [ulit_toNat' _ (by omega)] at hassign
  refine ExecStmt.exprStmt (EvalExpr.assignCompound (cur := u256Val (fromBal (tfM1 m f w) f).toNat)
    (r := u256Val ((fromBal (tfM1 m f w) f).toNat - w.toNat))
    rfl (by decide) (EvalExpr.localVal u256 (some .memory) (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (lvalBalanceOfLocal o _ _ "from" f (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])
      (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (readLValue_storage_u256 (erc20Layout_balanceOf f (tfM1 m f w).evm))
    (binop_sub_u256_ok _ _ hb hdebit) hassign)

/-- `balanceOf[from] -= value;` underflows: `Panic(0x11)`. -/
theorem tfDebitUnderflow (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hlt : (fromBal (tfM1 m f w) f).toNat < w.toNat) :
    ExecStmt erc20Cfg o erc20Flat (tfFr2 f t w m) (tfM1 m f w)
      (.exprStmt (.assign .sub (.index (.ident "balanceOf") (.ident "from")) (.ident "value")))
      (.reverted (panicData 0x11)) :=
  ExecStmt.exprStmtRevert (EvalExpr.assignCompoundPanic (cur := u256Val (fromBal (tfM1 m f w) f).toNat) (p := .overflow)
    rfl (by decide) (EvalExpr.localVal u256 (some .memory) (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (lvalBalanceOfLocal o _ _ "from" f (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])
      (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (readLValue_storage_u256 (erc20Layout_balanceOf f (tfM1 m f w).evm))
    (binop_sub_u256_underflow _ _ hlt))

/-- `balanceOf[to] += value;` (no overflow). -/
theorem tfCredit (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hfit : (fromBal (tfM2 m f w) t).toNat + w.toNat < UInt256.size) :
    ExecStmt erc20Cfg o erc20Flat (tfFr2 f t w m) (tfM2 m f w)
      (.exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")))
      (.normal (tfFr2 f t w m) (tfM3 m f t w)) := by
  have hassign := assign_storage_u256 (env := erc20Flat.types) (fr := tfFr2 f t w m)
    (erc20Layout_balanceOf t (tfM2 m f w).evm) (UInt256.ofNat ((fromBal (tfM2 m f w) t).toNat + w.toNat))
  rw [ulit_toNat' _ hfit] at hassign
  refine ExecStmt.exprStmt (EvalExpr.assignCompound (cur := u256Val (fromBal (tfM2 m f w) t).toNat)
    (r := u256Val ((fromBal (tfM2 m f w) t).toNat + w.toNat))
    rfl (by decide) (EvalExpr.localVal u256 (some .memory) (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (lvalBalanceOfLocal o _ _ "to" t (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])
      (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (readLValue_storage_u256 (erc20Layout_balanceOf t (tfM2 m f w).evm))
    (binop_add_u256_ok _ _ hfit) hassign)

/-- `balanceOf[to] += value;` overflows: `Panic(0x11)`. -/
theorem tfCreditOverflow (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hover : UInt256.size ≤ (fromBal (tfM2 m f w) t).toNat + w.toNat) :
    ExecStmt erc20Cfg o erc20Flat (tfFr2 f t w m) (tfM2 m f w)
      (.exprStmt (.assign .add (.index (.ident "balanceOf") (.ident "to")) (.ident "value")))
      (.reverted (panicData 0x11)) :=
  ExecStmt.exprStmtRevert (EvalExpr.assignCompoundPanic (cur := u256Val (fromBal (tfM2 m f w) t).toNat) (p := .overflow)
    rfl (by decide) (EvalExpr.localVal u256 (some .memory) (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (lvalBalanceOfLocal o _ _ "to" t (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame])
      (by frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]))
    (readLValue_storage_u256 (erc20Layout_balanceOf t (tfM2 m f w).evm))
    (binop_add_u256_overflow _ _ hover))

/-! ## The bodies -/

theorem tfBodyInsufficientAllowance (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hlt : (curAllow m f).toNat < w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (tfFr f t w) m tfStmts
      (.reverted (errorStringData "ERC20: insufficient allowance".toUTF8)) := by
  have hc := tfEvalCond1 o m f t w
  rw [decide_eq_false (by omega)] at hc
  exact ExecBlock.cons (tfDecl o m f t w)
    (ExecBlock.consRevert (ExecStmt.exprStmtRevert (EvalExpr.requireMsg rfl hc (EvalExpr.lit rfl) rfl)))

theorem tfBodyInsufficientBalance (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hallow : w.toNat ≤ (curAllow m f).toNat) (hlt : (fromBal m f).toNat < w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (tfFr f t w) m tfStmts
      (.reverted (errorStringData "ERC20: insufficient balance".toUTF8)) := by
  have hc1 := tfEvalCond1 o m f t w
  rw [decide_eq_true hallow] at hc1
  have hc2 := tfEvalCond2 o m f t w
  rw [decide_eq_false (by omega)] at hc2
  exact ExecBlock.cons (tfDecl o m f t w)
    (ExecBlock.cons (ExecStmt.exprStmt (EvalExpr.requireTrue hc1))
      (ExecBlock.consRevert (ExecStmt.exprStmtRevert (EvalExpr.requireMsg rfl hc2 (EvalExpr.lit rfl) rfl))))

theorem tfBodyDebitUnderflow (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hallow : w.toNat ≤ (curAllow m f).toNat) (hbal : w.toNat ≤ (fromBal m f).toNat)
    (hlt : (fromBal (tfM1 m f w) f).toNat < w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (tfFr f t w) m tfStmts (.reverted (panicData 0x11)) := by
  have hc1 := tfEvalCond1 o m f t w
  rw [decide_eq_true hallow] at hc1
  have hc2 := tfEvalCond2 o m f t w
  rw [decide_eq_true hbal] at hc2
  exact ExecBlock.cons (tfDecl o m f t w)
    (ExecBlock.cons (ExecStmt.exprStmt (EvalExpr.requireTrue hc1))
      (ExecBlock.cons (ExecStmt.exprStmt (EvalExpr.requireTrue hc2))
        (ExecBlock.cons (tfAllowStore o m f t w hallow)
          (ExecBlock.consRevert (tfDebitUnderflow o m f t w hlt)))))

theorem tfBodyOverflow (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hallow : w.toNat ≤ (curAllow m f).toNat) (hbal : w.toNat ≤ (fromBal m f).toNat)
    (hdebit : w.toNat ≤ (fromBal (tfM1 m f w) f).toNat)
    (hover : UInt256.size ≤ (fromBal (tfM2 m f w) t).toNat + w.toNat) :
    ExecBlock erc20Cfg o erc20Flat (tfFr f t w) m tfStmts (.reverted (panicData 0x11)) := by
  have hc1 := tfEvalCond1 o m f t w
  rw [decide_eq_true hallow] at hc1
  have hc2 := tfEvalCond2 o m f t w
  rw [decide_eq_true hbal] at hc2
  exact ExecBlock.cons (tfDecl o m f t w)
    (ExecBlock.cons (ExecStmt.exprStmt (EvalExpr.requireTrue hc1))
      (ExecBlock.cons (ExecStmt.exprStmt (EvalExpr.requireTrue hc2))
        (ExecBlock.cons (tfAllowStore o m f t w hallow)
          (ExecBlock.cons (tfDebit o m f t w hdebit)
            (ExecBlock.consRevert (tfCreditOverflow o m f t w hover))))))

theorem tfBodyOk (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hallow : w.toNat ≤ (curAllow m f).toNat) (hbal : w.toNat ≤ (fromBal m f).toNat)
    (hdebit : w.toNat ≤ (fromBal (tfM1 m f w) f).toNat)
    (hfit : (fromBal (tfM2 m f w) t).toNat + w.toNat < UInt256.size) :
    ∃ le, ExecBlock erc20Cfg o erc20Flat (tfFr f t w) m tfStmts
      (.returned ((tfFr2 f t w m).setVal "#ret0" (.bool true)) ((tfM3 m f t w).pushLog le)) := by
  obtain ⟨le, hle⟩ := mkLogEntry_evTransfer (tfM3 m f t w).this f t w
  have hc1 := tfEvalCond1 o m f t w
  rw [decide_eq_true hallow] at hc1
  have hc2 := tfEvalCond2 o m f t w
  rw [decide_eq_true hbal] at hc2
  refine ⟨le, ExecBlock.cons (tfDecl o m f t w)
    (ExecBlock.cons (ExecStmt.exprStmt (EvalExpr.requireTrue hc1))
      (ExecBlock.cons (ExecStmt.exprStmt (EvalExpr.requireTrue hc2))
        (ExecBlock.cons (tfAllowStore o m f t w hallow)
          (ExecBlock.cons (tfDebit o m f t w hdebit)
            (ExecBlock.cons (tfCredit o m f t w hfit)
              (ExecBlock.cons (fr1 := tfFr2 f t w m) (m1 := (tfM3 m f t w).pushLog le) ?_
                (ExecBlock.consReturn ?_)))))))⟩
  · refine ExecStmt.emit (vs := [.address f, .address t, u256Val w.toNat]) (fr1 := tfFr2 f t w m) (m1 := tfM3 m f t w)
      erc20Flat_event_Transfer rfl ?_ (abiArgs_addr_addr_u256 ..) hle
    refine EvalExprs.cons (EvalExpr.localVal addrTy (some .memory) ?_)
      (EvalExprs.cons (EvalExpr.localVal addrTy (some .memory) ?_)
        (EvalExprs.cons (EvalExpr.localVal u256 (some .memory) ?_) EvalExprs.nil))
    · frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]
    · frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]
    · frame_simp [tfFr2, tfFr, bodyFrame, tfFrame]
  · refine ExecStmt.returnSingle (r := "#ret0") (v := .bool true) (fr1 := tfFr2 f t w m)
      (m1 := (tfM3 m f t w).pushLog le) rfl (EvalExpr.lit rfl) ?_
    frame_simp [assign, coerce, tfFr2, tfFr, bodyFrame, tfFrame]
    try rfl

/-! ## The calls -/

theorem tfCallOk (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256)
    (hallow : w.toNat ≤ (curAllow m f).toNat) (hbal : w.toNat ≤ (fromBal m f).toNat)
    (hdebit : w.toNat ≤ (fromBal (tfM1 m f w) f).toNat)
    (hfit : (fromBal (tfM2 m f w) t).toNat + w.toNat < UInt256.size) :
    ∃ le, CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTransferFrom [.address f, .address t, u256Val w.toNat]
      (.ok [.bool true] ((tfM3 m f t w).pushLog le)) := by
  obtain ⟨le, hb⟩ := tfBodyOk o m f t w hallow hbal hdebit hfit
  refine ⟨le, CallFn.ok (tfEnter m f t w) EvalMods.nil rfl (ExecChain.body hb) rfl ?_⟩
  frame_simp [retVals, tfFr2, tfFr, bodyFrame, tfFrame]

theorem tfCallRevert (o : Oracle) (m : Machine) (f t : EVM.Address) (w : UInt256) (d : ByteArray)
    (hb : ExecBlock erc20Cfg o erc20Flat (tfFr f t w) m tfStmts (.reverted d)) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnTransferFrom [.address f, .address t, u256Val w.toNat]
      (.reverted d) :=
  CallFn.reverted (tfEnter m f t w) EvalMods.nil rfl (ExecChain.body hb)

/-! ## The dispatch-level spec runs -/

abbrev tfFrom (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (transferFromFromWord I).toNat
abbrev tfTo (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (transferFromToWord I).toNat

theorem erc20TransferFromSpecOk (o : Oracle) {cA gh bl σ σ₀ g A I}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hallow : (transferFromValueWord I).toNat ≤ (curAllow (trM cA gh bl σ σ₀ g A I) (tfFrom I)).toNat)
    (hbal : (transferFromValueWord I).toNat ≤ (fromBal (trM cA gh bl σ σ₀ g A I) (tfFrom I)).toNat)
    (hdebit : (transferFromValueWord I).toNat ≤
      (fromBal (tfM1 (trM cA gh bl σ σ₀ g A I) (tfFrom I) (transferFromValueWord I)) (tfFrom I)).toNat)
    (hfit : (fromBal (tfM2 (trM cA gh bl σ σ₀ g A I) (tfFrom I) (transferFromValueWord I)) (tfTo I)).toNat +
      (transferFromValueWord I).toNat < UInt256.size) :
    ∃ le, solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I
      (.returned ((tfM3 (trM cA gh bl σ σ₀ g A I) (tfFrom I) (tfTo I) (transferFromValueWord I)).pushLog le)
        [.bool true]) (.abi [.elem .bool]) := by
  obtain ⟨le, hc⟩ := tfCallOk o (trM cA gh bl σ σ₀ g A I) (tfFrom I) (tfTo I) (transferFromValueWord I) hallow hbal
    hdebit hfit
  exact ⟨le, solidityExec.call (erc20Dispatch_transferFrom hsel) erc20Flat_fns3 (Or.inr hwv) rfl
    (erc20Args_transferFrom_ok hsz100 hbig hcanonFrom hcanonTo) (by simp [ofAbiList, fnTransferFrom, fuelDefault]) hc
    (by simp [fuelDefault])⟩

theorem erc20TransferFromSpecRevert (o : Oracle) {cA gh bl σ σ₀ g A I} {d : ByteArray}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hb : ExecBlock erc20Cfg o erc20Flat (tfFr (tfFrom I) (tfTo I) (transferFromValueWord I)) (trM cA gh bl σ σ₀ g A I)
      tfStmts (.reverted d)) :
    solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I (.reverted d) (.abi [.elem .bool]) :=
  solidityExec.callReverted (erc20Dispatch_transferFrom hsel) erc20Flat_fns3 (Or.inr hwv) rfl
    (erc20Args_transferFrom_ok hsz100 hbig hcanonFrom hcanonTo) (by simp [ofAbiList, fnTransferFrom, fuelDefault])
    (tfCallRevert o _ _ _ _ d hb)

theorem erc20TransferFromRejects {I : ExecutionEnv}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hdec : decodeArgs erc20Cfg erc20Flat.types fnTransferFrom.decl I.calldata = none)
    {cA gh bl σ_evm σ_spec σ₀ A} {g : UInt256} (hcode : I.code = erc20Bytecode)
    (h : RDrev erc20Bytecode (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have := RDrev.specDecodingFailedCore (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode h
    (erc20Dispatch_transferFrom hsel) erc20Flat_fns3 (Or.inr hwv) hdec
  simpa [Sat256.ofUInt256, Sat256.toUInt256] using this

/-! ## The coupled result -/

theorem erc20TransferFromCore {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨178⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hsz4 := erc20TransferFromSelector_size hsel
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_spec σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hAllowance : transferFromCurrentAllowanceWord evmE I = transferFromCurrentAllowanceWord evmS I := by
    simpa [transferFromCurrentAllowanceWord, transferFromAllowanceSlot, evmE, evmS, initState]
      using hσ.storageLoad_codeOwner
      (erc20AllowanceSlot (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)) (.address I.source))
  have hσAllowance : EVMStateEquiv (transferFromAfterAllowanceState evmE I) (transferFromAfterAllowanceState evmS I) := by
    simpa [transferFromAfterAllowanceState, transferFromAllowanceSlot, evmE, evmS, initState]
      using hσ.storageStore_codeOwner
      (erc20AllowanceSlot (.address (AccountAddress.ofNat (transferFromFromWord I).toNat)) (.address I.source)) (by
        simpa [transferFromAllowanceDebitWord, evmE, evmS] using
          congrArg (fun w : UInt256 => UInt256.ofNat (w.toNat - (transferFromValueWord I).toNat)) hAllowance)
  have hFromBalance : transferFromFromBalanceWord evmE I = transferFromFromBalanceWord evmS I := by
    simpa [transferFromFromBalanceWord] using hσ.storageLoad_codeOwner (transferFromFromSlot I)
  have hAfterAllowanceFromBalance :
      transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I =
        transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I := by
    simpa [transferFromFromBalanceWord] using hσAllowance.storageLoad_codeOwner (transferFromFromSlot I)
  have hσBalance : EVMStateEquiv (transferFromAfterBalanceState evmE I) (transferFromAfterBalanceState evmS I) := by
    simpa [transferFromAfterBalanceState] using
      hσAllowance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromFromSlot I)
      (by simp [transferFromBalanceDebitWord, hAfterAllowanceFromBalance])
  have hToBalance : transferFromToBalanceWord evmE I = transferFromToBalanceWord evmS I := by
    simpa [transferFromToBalanceWord] using
      hσBalance.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromToSlot I)
  have hNewToNat : transferFromNewToNat evmE I = transferFromNewToNat evmS I := by
    simp [transferFromNewToNat, hToBalance]
  have hσPost : EVMStateEquiv (transferFromPostState evmE I) (transferFromPostState evmS I) := by
    simpa [transferFromPostState] using
      hσBalance.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferFromToSlot I)
      (by simp [transferFromNewToWord, hNewToNat])
  -- the spec machines are the Sol⁻ post-states over `σ_spec`
  let mS := trM cA gh bl σ_spec σ₀ g A I
  have hmS : mS.evm = evmS := rfl
  have hCur : curAllow mS (tfFrom I) = transferFromCurrentAllowanceWord evmS I := rfl
  have hFrom : fromBal mS (tfFrom I) = transferFromFromBalanceWord evmS I := rfl
  have hM1 : (tfM1 mS (tfFrom I) (transferFromValueWord I)).evm = transferFromAfterAllowanceState evmS I := rfl
  have hFrom1 : fromBal (tfM1 mS (tfFrom I) (transferFromValueWord I)) (tfFrom I) =
      transferFromFromBalanceWord (transferFromAfterAllowanceState evmS I) I := rfl
  have hM2 : (tfM2 mS (tfFrom I) (transferFromValueWord I)).evm = transferFromAfterBalanceState evmS I := by
    show Storage.EVM.storageStore (transferFromAfterAllowanceState evmS I)
      (transferFromAfterAllowanceState evmS I).executionEnv.codeOwner (transferFromFromSlot I)
      (UInt256.ofNat ((fromBal (tfM1 mS (tfFrom I) (transferFromValueWord I)) (tfFrom I)).toNat -
        (transferFromValueWord I).toNat)) = _
    rw [hFrom1, transferFromAfterBalanceState, transferFromAfterAllowance_codeOwner]
    rfl
  have hTo2 : fromBal (tfM2 mS (tfFrom I) (transferFromValueWord I)) (tfTo I) = transferFromToBalanceWord evmS I := by
    show Storage.EVM.storageLoad (tfM2 mS (tfFrom I) (transferFromValueWord I)).evm
      (tfM2 mS (tfFrom I) (transferFromValueWord I)).evm.executionEnv.codeOwner (transferFromToSlot I) = _
    rw [hM2, transferFromAfterBalance_codeOwner]
    rfl
  have hM3 : (tfM3 mS (tfFrom I) (tfTo I) (transferFromValueWord I)).evm = transferFromPostState evmS I := by
    show Storage.EVM.storageStore (tfM2 mS (tfFrom I) (transferFromValueWord I)).evm
      (tfM2 mS (tfFrom I) (transferFromValueWord I)).evm.executionEnv.codeOwner (transferFromToSlot I)
      (UInt256.ofNat ((fromBal (tfM2 mS (tfFrom I) (transferFromValueWord I)) (tfTo I)).toNat +
        (transferFromValueWord I).toNat)) = _
    rw [hTo2, hM2, transferFromAfterBalance_codeOwner]
    rfl
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus
      · by_cases hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus
        · by_cases hallowance : (transferFromValueWord I).toNat ≤ (transferFromCurrentAllowanceWord evmE I).toNat
          · have hallowS : (transferFromValueWord I).toNat ≤ (curAllow mS (tfFrom I)).toNat := by
              rw [hCur, ← hAllowance]; exact hallowance
            by_cases hbalance : (transferFromValueWord I).toNat ≤ (transferFromFromBalanceWord evmE I).toNat
            · have hbalS : (transferFromValueWord I).toNat ≤ (fromBal mS (tfFrom I)).toNat := by
                rw [hFrom, ← hFromBalance]; exact hbalance
              by_cases hbalanceDebit : (transferFromValueWord I).toNat ≤
                  (transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I).toNat
              · have hdebitS : (transferFromValueWord I).toNat ≤
                    (fromBal (tfM1 mS (tfFrom I) (transferFromValueWord I)) (tfFrom I)).toNat := by
                  rw [hFrom1, ← hAfterAllowanceFromBalance]; exact hbalanceDebit
                by_cases hfit : transferFromNewToNat evmE I < UInt256.size
                · have hfitS : (fromBal (tfM2 mS (tfFrom I) (transferFromValueWord I)) (tfTo I)).toNat +
                      (transferFromValueWord I).toNat < UInt256.size := by
                    rw [hTo2, ← hToBalance]; exact hfit
                  have hX := erc20X_transferFrom (g := Sat256.ofUInt256 g) hsz100 hsize hbig hperm hcanonFrom hcanonTo
                    hallowance hbalance hbalanceDebit hfit hreach
                  obtain ⟨le, hspec⟩ := erc20TransferFromSpecOk (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec)
                    (σ₀ := σ₀) (g := g) (A := A) noOracle hsel hwv hsz100 hbig hcanonFrom hcanonTo hallowS hbalS
                    hdebitS hfitS
                  have h := RDret.specExecutionCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
                    (by
                      rw [pushLog_evm_createdAccounts, hM3, ← hσPost.createdAccounts]
                      simp [evmE, initState, transferFromPostState, transferFromAfterBalanceState,
                        transferFromAfterAllowanceState, storageStore_createdAccounts])
                    (by
                      rw [pushLog_evm_accountMap, hM3]
                      refine Refinement.accountMapEquiv.trans (Refinement.accountMapEquiv.of_eq ?_) hσPost.accountMap
                      simp [evmE, initState, transferFromPostState, transferFromAfterBalanceState,
                        transferFromAfterAllowanceState, transferFromAllowanceSlot, transferFromAllowanceSlotI,
                        storageStore_accountMap, storageStore_executionEnv])
                    (.abi boolTrueReturnEncoding)
                  simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
                · have hover : UInt256.size ≤ transferFromNewToNat evmE I := by omega
                  have hoverS : UInt256.size ≤ (fromBal (tfM2 mS (tfFrom I) (transferFromValueWord I)) (tfTo I)).toNat +
                      (transferFromValueWord I).toNat := by
                    rw [hTo2, ← hToBalance]; exact hover
                  have hX := erc20TransferFromX_overflow (g := Sat256.ofUInt256 g) hsz100 hsize hbig hperm hcanonFrom
                    hcanonTo hallowance hbalance hbalanceDebit hover hreach
                  have hspec := erc20TransferFromSpecRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀)
                    (g := g) (A := A) noOracle hsel hwv hsz100 hbig hcanonFrom hcanonTo
                    (tfBodyOverflow noOracle _ _ _ _ hallowS hbalS hdebitS hoverS)
                  have h := RDrev.specRevertCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
                  simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
              · have hltDebit : (transferFromFromBalanceWord (transferFromAfterAllowanceState evmE I) I).toNat <
                    (transferFromValueWord I).toNat := by omega
                have hltS : (fromBal (tfM1 mS (tfFrom I) (transferFromValueWord I)) (tfFrom I)).toNat <
                    (transferFromValueWord I).toNat := by
                  rw [hFrom1, ← hAfterAllowanceFromBalance]; exact hltDebit
                have hX := erc20TransferFromX_balanceDebitUnderflow (g := Sat256.ofUInt256 g) hsz100 hsize hbig hperm
                  hcanonFrom hcanonTo hallowance hbalance hltDebit hreach
                have hspec := erc20TransferFromSpecRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀)
                  (g := g) (A := A) noOracle hsel hwv hsz100 hbig hcanonFrom hcanonTo
                  (tfBodyDebitUnderflow noOracle _ _ _ _ hallowS hbalS hltS)
                have h := RDrev.specRevertCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
                simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
            · have hlt : (transferFromFromBalanceWord evmE I).toNat < (transferFromValueWord I).toNat := by omega
              have hltS : (fromBal mS (tfFrom I)).toNat < (transferFromValueWord I).toNat := by
                rw [hFrom, ← hFromBalance]; exact hlt
              have hX := erc20TransferFromX_insufficientBalance (g := Sat256.ofUInt256 g) hsz100 hsize hbig hcanonFrom
                hcanonTo hallowance hlt hreach
              have hspec := erc20TransferFromSpecRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀)
                (g := g) (A := A) noOracle hsel hwv hsz100 hbig hcanonFrom hcanonTo
                (tfBodyInsufficientBalance noOracle _ _ _ _ hallowS hltS)
              have h := RDrev.specRevertCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
              simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
          · have hlt : (transferFromCurrentAllowanceWord evmE I).toNat < (transferFromValueWord I).toNat := by omega
            have hltS : (curAllow mS (tfFrom I)).toNat < (transferFromValueWord I).toNat := by
              rw [hCur, ← hAllowance]; exact hlt
            have hX := erc20TransferFromX_insufficientAllowance (g := Sat256.ofUInt256 g) hsz100 hsize hbig hcanonFrom
              hcanonTo hlt hreach
            have hspec := erc20TransferFromSpecRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀)
              (g := g) (A := A) noOracle hsel hwv hsz100 hbig hcanonFrom hcanonTo
              (tfBodyInsufficientAllowance noOracle _ _ _ _ hltS)
            have h := RDrev.specRevertCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
            simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
        · have hnc : UInt256.eq (transferFromToWord I) (UInt256.land (transferFromToWord I) erc20AddrMask) = ⟨0⟩ :=
            erc20Ueq_zero_of_ne (fun he => hcanonTo (erc20Word_canonical_of_clean he))
          exact erc20TransferFromRejects hsel hwv (erc20Args_transferFrom_none_noncanon1 hsz100 hbig hcanonFrom hcanonTo)
            hcode (erc20TransferFromX_noncanon_to (g := Sat256.ofUInt256 g) hsz100 hsize hbig hcanonFrom hnc hreach)
      · have hnc : UInt256.eq (transferFromFromWord I) (UInt256.land (transferFromFromWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanonFrom (erc20Word_canonical_of_clean he))
        exact erc20TransferFromRejects hsel hwv (erc20Args_transferFrom_none_noncanon0 hsz100 hbig hcanonFrom) hcode
          (erc20TransferFromX_noncanon_from (g := Sat256.ofUInt256 g) hsz100 hsize hbig hnc hreach)
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact erc20TransferFromRejects hsel hwv (erc20Args_transferFrom_none_huge hbigge) hcode
        (erc20TransferFromX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
  · have hshort : I.calldata.size < 100 := by omega
    exact erc20TransferFromRejects hsel hwv (erc20Args_transferFrom_none_short hsz4 hshort) hcode
      (erc20TransferFromX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)

end ERC20.SolidityProof
