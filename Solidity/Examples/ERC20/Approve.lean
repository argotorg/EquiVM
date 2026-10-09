import Solidity.Examples.ERC20.Shapes

/-!
# ERC20 — `approve(address,uint256)` refines its Solidity body

EVM side: the decoder at `0x437`, the body at `0x112` (two scratch-memory hashes, `SSTORE`, the
`Approval` `LOG3` from `0x80`) and the `bool` return tail.  Spec side: the assignment, the `emit`
and `return true`.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-! ## The EVM runs -/

theorem apEntry {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 0)) :
    ∃ k C, Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x437⟩, ⟨4⟩ :: UInt256.ofNat (initState σ σ₀ g A I).executionEnv.calldata.size :: ⟨0x72⟩ :: ⟨0x77⟩ ::
        [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := reachBodyOf 0 (by omega) ⟨0x64⟩ hcode hwv hsize hsel (by jump_dest) (by decide)
  exact ⟨_, _, evm_run h with [jumpdest, push2 ⟨0x77⟩, push2 ⟨0x72⟩, calldatasize, push1 ⟨4⟩, push2 ⟨0x437⟩,
    jump (by jump_dest)]⟩

abbrev apSpender (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4
abbrev apValue (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36
/-- `keccak256(msg.sender ++ 1)`, then `keccak256(spender ++ that)`: the slot of
    `allowance[msg.sender][spender]`. -/
abbrev apSlot1 (I : ExecutionEnv) : UInt256 := solcMappingSlot ⟨1⟩ (callerW I)
abbrev apSlot (I : ExecutionEnv) : UInt256 := solcMappingSlot (apSlot1 I) (apSpender I)
noncomputable abbrev apMem2 (I : ExecutionEnv) : ByteArray := twoWordHashMem (callerW I) ⟨1⟩ solcFreePtrMem
noncomputable abbrev apMem4 (I : ExecutionEnv) : ByteArray := twoWordHashMem (apSpender I) (apSlot1 I) (apMem2 I)
noncomputable abbrev apMem5 (I : ExecutionEnv) : ByteArray := (UInt256.toByteArray (apValue I)).write 0 (apMem4 I) 128 32
def approvalTopic : UInt256 := ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩
/-- The `Approval(msg.sender, spender, value)` entry the bytecode logs. -/
abbrev apLog (I : ExecutionEnv) : LogEntry :=
  ⟨I.codeOwner, #[approvalTopic, callerW I, apSpender I], UInt256.toByteArray (apValue I)⟩

theorem apMem4_size (I : ExecutionEnv) : (apMem4 I).size = 96 :=
  twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
theorem apMem4_read64 (I : ExecutionEnv) : (apMem4 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)
theorem apMem4_gap (I : ExecutionEnv) : 128 - (apMem4 I).size < USize.size := by
  rw [apMem4_size]; exact lt_usize _ (by norm_num)

theorem apRun {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hsel : selIs I (selBytes 0))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc : (apSpender I).toNat < EVM.addressModulus) :
    Returned erc20Runtime (initState σ σ₀ g A I)
      ⟨A.createdAccounts, sstoreAccountMap I.codeOwner σ (apSlot I) (apValue I), A.logSeries.push (apLog I)⟩
      (UInt256.toByteArray ⟨1⟩) := by
  obtain ⟨_, _, h⟩ := apEntry hcode hwv hsize hsel
  obtain ⟨_, _, h1'⟩ := decAddrU256Ok h hsz68 hbig hc (by jump_dest) (by simp)
  have h1 : Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x72⟩, apValue I :: apSpender I :: ⟨0x77⟩ :: [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3,
        ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ _ _ := h1'
  have h2 := evm_run h1 with [jumpdest, push2 ⟨0x112⟩, jump (by jump_dest), jumpdest, caller, push0, dup2, dup2,
    raw mstore 0 (wordAt0Mem (callerW I) solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide)
      (by evm_ov),
    push1 ⟨1⟩, push1 ⟨0x20⟩, swap1, dup2,
    raw mstore 0 (apMem2 I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup1, dup4,
    raw keccak256 0 (apSlot1 I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (callerW I) solcFreePtrMem_size) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨0xa0⟩, shl, sub, dup8, and]
  have hland : UInt256.land (apSpender I) (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = apSpender I := by
    rw [solcAddrMask_lit]; exact land_solcAddrMask_of_canon hc
  rw [hland] at h2
  have h3 := evm_run h2 with [dup1, dup6,
    raw mstore 0 (wordAt0Mem (apSpender I) (apMem2 I)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide)
      (by evm_ov),
    swap3,
    raw mstore 0 (apMem4 I) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    dup1, dup4,
    raw keccak256 0 (apSlot I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (twoWordHashMem_solcMappingSlot (apSlot1 I) (apSpender I) (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
      (by decide) (by evm_ov),
    dup6, swap1]
  obtain ⟨_, _, h4⟩ := h3.sstore hperm (by native_decide) (by evm_ov)
  have hm4 : 96 ≤ (apMem4 I).size := by rw [apMem4_size]
  obtain ⟨hsz5, hr5, hb5⟩ := freePtr_after_write128 (apValue I) hm4 (apMem4_read64 I) (apMem4_gap I)
  have hs5 : 128 + 32 ≤ (apMem5 I).size := toByteArray_write_size_ge_off_add32 _ _ 128 (apMem4_gap I)
  have h5 := evm_run h4 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by omega) (apMem4_read64 I)) (by decide) (by evm_ov),
    swap2, swap3, swap1, swap2]
  have h6 := h5.pushConst (width := 32) (op := .PUSH32) approvalTopic (by decide) (by native_decide) (by evm_ov)
  have h7 := evm_run h6 with [swap1, push2 ⟨0x16c⟩, swap1, dup7, dup2,
    raw mstore 6 (apMem5 I) (UInt256.ofNat 5) (by native_decide) mem_cost rfl (by native_decide) (by evm_ov),
    push1 ⟨0x20⟩, add, swap1, jump (by jump_dest), jumpdest, push1 ⟨0x40⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost (mloadFreePtrValue hsz5 hr5)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  rw [show UInt256.sub (⟨32⟩ + ⟨128⟩) ⟨128⟩ = ⟨32⟩ from by decide] at h7
  have h8 := h7.log3 0 (UInt256.ofNat 5) (by native_decide) hperm mem_cost (by decide) (by evm_ov)
  rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl, show (⟨32⟩ : UInt256).toNat = 32 from rfl, hb5] at h8
  have h9 := evm_run h8 with [pop, push1 ⟨1⟩, jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact retBoolTrue h9 (by omega) hr5 (lt_usize _ (by omega)) (by simp)

theorem apRunShort {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 0)) (hshort : I.calldata.size < 68) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := apEntry hcode hwv hsize hsel
  exact decAddrU256LenRevert h (lenCheck_short (by norm_num) (size_ge_of_sel rfl hsel) hshort) (by simp)

theorem apRunHuge {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 0)) (hhuge : 2 ^ 255 + 4 ≤ I.calldata.size) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := apEntry hcode hwv hsize hsel
  exact decAddrU256LenRevert h (lenCheck_huge (by norm_num) hhuge hsize) (by simp)

theorem apRunDirty {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 0))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (apSpender I).toNat < EVM.addressModulus) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := apEntry hcode hwv hsize hsel
  exact decAddrU256DirtyRevert h hsz68 hbig hnc (by simp)

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

/-- The `Approval` entry the spec logs (on the machine after the store). -/
noncomputable abbrev apLe (m : Machine) (a : EVM.Address) (w : UInt256) : LogEntry :=
  { address := (storeU256 m (alwSlot m.evm.executionEnv.source a) w).this,
    topics := #[hashWord evApproval.sigStr.toUTF8,
      UInt256.ofNat (storeU256 m (alwSlot m.evm.executionEnv.source a) w).evm.executionEnv.source.toNat,
      UInt256.ofNat a.toNat],
    data := UInt256.toByteArray w }

/-- The machine after the body: the allowance stored, the `Approval` entry logged. -/
noncomputable abbrev apFinal (m : Machine) (a : EVM.Address) (w : UInt256) : Machine :=
  (storeU256 m (alwSlot m.evm.executionEnv.source a) w).pushLog (apLe m a w)

theorem apBody (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (apFrame a w) apStmts) m apStmts
      (.returned ((bodyFrame (apFrame a w) apStmts).setVal "#ret0" (.bool true)) (apFinal m a w)) := by
  refine ExecBlock.cons (ExecStmt.assignStorageU256 (w := w) (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, apFrame]))
    (EvalLValue.mapping2Addr (by frame_simp [bodyFrame, apFrame]) erc20Flat_var_allowance rfl rfl EvalExpr.msgSender
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, apFrame])))
    (erc20Leaf_allowance _ a)) ?_
  refine ExecBlock.cons (ExecStmt.emitAddrAddrU256
    (a := (storeU256 m (alwSlot m.evm.executionEnv.source a) w).evm.executionEnv.source) (b := a) (n := w)
    erc20Flat_eventsNamed_Approval rfl rfl rfl
    (EvalExprs.three EvalExpr.msgSender (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, apFrame]))
      (EvalExpr.localVal u256 (some .memory) (by frame_simp [bodyFrame, apFrame])))) ?_
  exact ExecBlock.consReturn (ExecStmt.returnBool { ty := .bool, loc := some .memory, val := .bool false } rfl
    (EvalExpr.boolLit true) (by frame_simp [bodyFrame, apFrame]) rfl (by frame_simp [bodyFrame, apFrame]))

theorem apCall (o : Oracle) (m : Machine) (a : EVM.Address) (w : UInt256) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnApprove [.address a, u256Val w.toNat]
      (.ok [.bool true] (apFinal m a w)) :=
  CallFn.plain (apEnter m a w) rfl rfl (apBody o m a w) rfl
    (retVals_exitScope (by frame_simp [bodyFrame, apFrame]) (by frame_simp [bodyFrame, apFrame])
      (by frame_simp [retVals, bodyFrame, apFrame]))

abbrev apSpenderA (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (apSpender I).toNat

theorem apSpec (o : Oracle) {σ σ₀ g A I} (hsel : selIs I (selBytes 0)) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc : (apSpender I).toNat < EVM.addressModulus) :
    solidityExec erc20Cfg o erc20Flat ∅ σ σ₀ g A I
      (.returned (apFinal (initMachine σ σ₀ g A I ∅) (apSpenderA I) (apValue I)) [.bool true])
      (.abi [.elem .bool]) := by
  have hsvs : decodeArgs erc20Cfg erc20Flat.types fnApprove.decl I.calldata =
      some [.address (apSpenderA I), .int (Int.ofNat (apValue I).toNat)] := by
    rw [decodeArgs_approve]; exact decodeCalldataValues_addr_uint256_ok hsz68 hbig hc
  have hvs : ofAbiParams erc20Flat.types I.calldata fnApprove.decl.params
      [.address (apSpenderA I), .int (Int.ofNat (apValue I).toNat)] {} =
      some ([.address (apSpenderA I), u256Val (apValue I).toNat], {}) := by
    simp [ofAbiParams, fnApprove, fuelDefault, calldataRef]
  have hprep : prepareArgs erc20Flat.types I.calldata fuelDefault
      (apFinal (initMachine σ σ₀ g A I ∅) (apSpenderA I) (apValue I)).heap [.bool true] =
      some (.ok ([.bool true], (apFinal (initMachine σ σ₀ g A I ∅) (apSpenderA I) (apValue I)).heap)) :=
    prepareArgs_of_noRaw (fuel := 1023) (by simp)
  exact solidityExec.call (erc20Dispatch_approve hsel) erc20Flat_fns2 (Or.inr hwv) rfl hsvs hvs
    (apCall o (initMachine σ σ₀ g A I ∅) (apSpenderA I) (apValue I)) hprep (by simp [fuelDefault])

/-! ## The coupled result -/

theorem approveCorrect {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Runtime) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I (selBytes 0)) :
    runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := size_ge_of_sel rfl hsel
  have hdec : decodeArgs erc20Cfg erc20Flat.types fnApprove.decl I.calldata = none →
      Reverted erc20Runtime (initState σ σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty →
      runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I := fun hd h =>
    Reverted.specDecodingFailed hcode h (erc20Dispatch_approve hsel) erc20Flat_fns2 (Or.inr hwv)
      (decodeCallArgs_none_of_decodeArgs hd)
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc : (apSpender I).toNat < EVM.addressModulus
      · have hw0 : WorldEquiv ⟨A.createdAccounts, σ, A.logSeries⟩ (initMachine σ σ₀ g A I ∅) :=
          WorldEquiv.init ∅ {}
        have hslot : alwSlot (initMachine σ σ₀ g A I ∅).evm.executionEnv.source (apSpenderA I) = apSlot I := by
          rw [alwSlot_eq, initMachine_executionEnv]
          show solcMappingSlot (solcMappingSlot ⟨1⟩ (UInt256.ofNat I.source.val))
            (UInt256.ofNat (AccountAddress.ofNat (apSpender I).toNat).toNat) = _
          rw [addrWord_canon hc]
        have hw1 := hw0.sstore (owner := I.codeOwner) rfl
          (alwSlot (initMachine σ σ₀ g A I ∅).evm.executionEnv.source (apSpenderA I)) (apValue I)
        have hle : apLe (initMachine σ σ₀ g A I ∅) (apSpenderA I) (apValue I) = apLog I := by
          simp only [apLe, Machine.this, storeU256, storageStore_executionEnv, initMachine_executionEnv,
            evApproval_topic, addrWord_canon hc, apLog, approvalTopic, callerW]
          rfl
        have hw2 := hw1.pushLog (apLe (initMachine σ σ₀ g A I ∅) (apSpenderA I) (apValue I))
        have hrun := apRun (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          hcode hwv hsize hperm hsel hsz68 hbig hc
        rw [← hslot, ← hle] at hrun
        exact Returned.specExecutionW default hcode hrun (apSpec default hsel hwv hsz68 hbig hc) hw2
          (.abi boolTrueReturnEncoding)
      · exact hdec (by rw [decodeArgs_approve]; exact decodeCalldataValues_addr_uint256_none_noncanon hsz68 hbig hc)
          (apRunDirty hcode hwv hsize hsel hsz68 hbig hc)
    · exact hdec (by rw [decodeArgs_approve]; exact decodeCalldataValues_addr_uint256_none_huge (by omega))
        (apRunHuge hcode hwv hsize hsel (by omega))
  · exact hdec (by rw [decodeArgs_approve]; exact decodeCalldataValues_addr_uint256_none_short hsz4 (by omega))
      (apRunShort hcode hwv hsize hsel (by omega))

end ERC20.Opt
