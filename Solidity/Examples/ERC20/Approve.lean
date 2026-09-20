import Solidity.Examples.ERC20.Common

/-!
# ERC20 — `approve(address,uint256)` refines its Solidity body (core relation)
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace ERC20.SolidityProof

/-! ## Arguments -/

theorem erc20Args_approve_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnApprove.decl I.calldata =
      some [.address (AccountAddress.ofNat (approveSpenderWord I).toNat),
        .int (Int.ofNat (approveValueWord I).toNat)] := by
  rw [decodeArgs_unfold _ _ sigApprove sigOf_approve]
  exact decodeCalldataValues_addr_uint256_ok hsz68 hbig hcanon

theorem erc20Args_approve_none_short {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 68) :
    decodeArgs erc20Cfg erc20Flat.types fnApprove.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigApprove sigOf_approve]
  exact decodeCalldataValues_addr_uint256_none_short hsz4 hshort

theorem erc20Args_approve_none_noncanon {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) (hnc : ¬ (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeArgs erc20Cfg erc20Flat.types fnApprove.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigApprove sigOf_approve]
  exact decodeCalldataValues_addr_uint256_none_noncanon hsz68 hbig hnc

theorem erc20Args_approve_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeArgs erc20Cfg erc20Flat.types fnApprove.decl I.calldata = none := by
  rw [decodeArgs_unfold _ _ sigApprove sigOf_approve]
  exact decodeCalldataValues_addr_uint256_none_huge hbig

/-! ## The spec derivation -/

def apFrame (a : EVM.Address) (w : UInt256) : Frame :=
  ((({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "spender" addrTy (some .memory)
    (.address a)).bind "value" u256 (some .memory) (u256Val w.toNat)).bind "#ret0" .bool (some .memory) (.bool false)

def apStmts : Block :=
  [ .exprStmt (.assign .assign (.index (.index (.ident "allowance") msgSender) (.ident "spender")) (.ident "value")),
    .emit (.ident "Approval") (.positional [msgSender, .ident "spender", .ident "value"]),
    .return (some (.lit (.bool true))) ]

theorem apEnter (m : Machine) (a : EVM.Address) (w : UInt256) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnApprove.decl [.address a, u256Val w.toNat] m =
      some (.ok (apFrame a w, m)) := by
  simp [enterFn, declare, coerce, fnApprove, apFrame, fuelDefault]
  try rfl

/-- The machine after the allowance store. -/
def apStored (m : Machine) (a : EVM.Address) (w : UInt256) : Machine :=
  { m with evm := (Storage.EVM.storageStore m.evm m.evm.executionEnv.codeOwner
      (erc20AllowanceSlot (.address m.evm.executionEnv.source) (.address a)) w) }

/-- `allowance[msg.sender][k]` as an lvalue, for a local address `k`. -/
theorem lvalAllowanceSender (o : Oracle) (fr : Frame) (m : Machine) (x : Ident) (a : EVM.Address)
    (hx : fr.get? x = some { ty := addrTy, loc := some .memory, val := .address a })
    (hb : fr.get? "allowance" = none) :
    EvalLValue erc20Cfg o erc20Flat fr m (.index (.index (.ident "allowance") msgSender) (.ident x))
      (.ok (.storage ⟨"allowance", [.mindex (.address m.evm.executionEnv.source), .mindex (.address a)]⟩ u256) fr m) := by
  have h1 : EvalExpr erc20Cfg o erc20Flat fr m (.index (.ident "allowance") msgSender)
      (.ok (.storageRef ⟨"allowance", [.mindex (.address m.evm.executionEnv.source)]⟩ (.mapping addrTy u256)) fr m) :=
    EvalExpr.indexStorage (EvalExpr.stateVar hb erc20Flat_var_allowance rfl (loadIfScalar_mapping ..))
      (EvalExpr.envMember rfl (envMember_sender m)) (storageIndex_mapping_address ..) (loadIfScalar_mapping ..)
  exact EvalLValue.indexStorage h1 (EvalExpr.local hx) (storageIndex_mapping_address ..)

theorem apBody (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) :
    ∃ le, ExecBlock erc20Cfg o erc20Flat (bodyFrame (apFrame a w) apStmts) m apStmts
      (.returned ((bodyFrame (apFrame a w) apStmts).setVal "#ret0" (.bool true)) ((apStored m a w).pushLog le)) := by
  obtain ⟨le, hle⟩ := mkLogEntry_evApproval (apStored m a w).this m.evm.executionEnv.source a w
  refine ⟨le, ExecBlock.cons (fr1 := bodyFrame (apFrame a w) apStmts) (m1 := apStored m a w) ?_
    (ExecBlock.cons (fr1 := bodyFrame (apFrame a w) apStmts) (m1 := (apStored m a w).pushLog le) ?_
      (ExecBlock.consReturn ?_))⟩
  · refine ExecStmt.exprStmt (EvalExpr.assignPlain (v := u256Val w.toNat) (fr1 := bodyFrame (apFrame a w) apStmts)
      (m1 := m) rfl (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, apFrame]))
      (lvalAllowanceSender o _ m "spender" a (by frame_simp [bodyFrame, apFrame]) (by frame_simp [bodyFrame, apFrame]))
      ?_)
    exact assign_storage_u256 (erc20Layout_allowance m.evm.executionEnv.source a m.evm) w
  · refine ExecStmt.emit (vs := [.address m.evm.executionEnv.source, .address a, u256Val w.toNat])
      (fr1 := bodyFrame (apFrame a w) apStmts) (m1 := apStored m a w) erc20Flat_event_Approval rfl ?_
      (abiArgs_addr_addr_u256 ..) ?_
    · refine EvalExprs.cons (EvalExpr.envMember rfl ?_) (EvalExprs.cons (EvalExpr.localVal addrTy (some .memory) ?_)
        (EvalExprs.cons (EvalExpr.localVal u256 (some .memory) ?_) EvalExprs.nil))
      · rw [envMember_sender]; simp [apStored, storageStore_executionEnv]
      · frame_simp [bodyFrame, apFrame]
      · frame_simp [bodyFrame, apFrame]
    · exact hle
  · refine ExecStmt.returnSingle (r := "#ret0") (v := .bool true) (fr1 := bodyFrame (apFrame a w) apStmts)
      (m1 := (apStored m a w).pushLog le) rfl (EvalExpr.lit rfl) ?_
    frame_simp [assign, coerce, bodyFrame, apFrame]
    try rfl

theorem apCall (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) :
    ∃ le, CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnApprove [.address a, u256Val w.toNat]
      (.ok [.bool true] ((apStored m a w).pushLog le)) := by
  obtain ⟨le, hb⟩ := apBody o m a w
  refine ⟨le, CallFn.ok (apEnter m a w) EvalMods.nil rfl (ExecChain.body hb) rfl ?_⟩
  frame_simp [retVals, bodyFrame, apFrame]

theorem erc20ApproveSpec (o : Oracle) {cA gh bl σ σ₀ g A I}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus) :
    ∃ le, solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I
      (.returned ((apStored (initMachine cA gh bl σ σ₀ g A I) (AccountAddress.ofNat (approveSpenderWord I).toNat)
        (approveValueWord I)).pushLog le) [.bool true]) (.abi [.elem .bool]) := by
  obtain ⟨le, hc⟩ := apCall o (initMachine cA gh bl σ σ₀ g A I) (AccountAddress.ofNat (approveSpenderWord I).toNat)
    (approveValueWord I)
  exact ⟨le, solidityExec.call (erc20Dispatch_approve hsel) erc20Flat_fns2 (Or.inr hwv) rfl
    (erc20Args_approve_ok hsz68 hbig hcanon) (by simp [ofAbiList, fnApprove, fuelDefault]) hc
    (by simp [fuelDefault])⟩

theorem erc20ApproveRejects {I : ExecutionEnv}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hwv : I.weiValue = ⟨0⟩) (hdec : decodeArgs erc20Cfg erc20Flat.types fnApprove.decl I.calldata = none)
    {cA gh bl σ_evm σ_spec σ₀ A} {g : UInt256} (hcode : I.code = erc20Bytecode)
    (h : RDrev erc20Bytecode (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have := RDrev.specDecodingFailedCore (σ_spec := σ_spec) (g := Sat256.ofUInt256 g) hcode h
    (erc20Dispatch_approve hsel) erc20Flat_fns2 (Or.inr hwv) hdec
  simpa [Sat256.ofUInt256, Sat256.toUInt256] using this

/-! ## The coupled result -/

theorem erc20ApproveCore {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨100⟩ [erc20SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    runtimeEquivalenceForCore erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hsz4 := erc20ApproveSelector_size hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (approveSpenderWord I).toNat < EVM.addressModulus
      · have hX := erc20X_approve (g := Sat256.ofUInt256 g) hsz68 hsize hbig hperm hcanon hreach
        obtain ⟨le, hspec⟩ := erc20ApproveSpec (cA := cA) (gh := gh) (bl := bl) (σ := σ_spec) (σ₀ := σ₀) (g := g)
          (A := A) noOracle hsel hwv hsz68 hbig hcanon
        have h := RDret.specExecutionCore (g := Sat256.ofUInt256 g) noOracle hcode hX hspec
          (by simp [apStored, initMachine, initEvm, storageStore_createdAccounts])
          (by
            simp only [pushLog_evm_accountMap, apStored, storageStore_accountMap, initMachine_evm, initState,
              approveSlotI]
            exact accountMapEquiv_sstoreAccountMap _ _ _ hAccounts)
          (.abi boolTrueReturnEncoding)
        simpa [Sat256.ofUInt256, Sat256.toUInt256] using h
      · have hnc : UInt256.eq (approveSpenderWord I)
            (UInt256.land (approveSpenderWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanon (erc20Word_canonical_of_clean he))
        exact erc20ApproveRejects hsel hwv (erc20Args_approve_none_noncanon hsz68 hbig hcanon) hcode
          (erc20ApproveX_noncanon_spender (g := Sat256.ofUInt256 g) hsz68 hsize hbig hnc hreach)
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact erc20ApproveRejects hsel hwv (erc20Args_approve_none_huge hbigge) hcode
        (erc20ApproveX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
  · have hshort : I.calldata.size < 68 := by omega
    exact erc20ApproveRejects hsel hwv (erc20Args_approve_none_short hsz4 hshort) hcode
      (erc20ApproveX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)

end ERC20.SolidityProof
