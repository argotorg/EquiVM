import Solidity.Examples.ERC20.Shapes

/-!
# ERC20 — `allowance(address,address)` refines its Solidity getter

EVM side: the decoder at `0x4b9`, the two scratch-memory hashes at `0xf6` (`keccak256(owner ++ 1)`,
then `keccak256(spender ++ that)`), the load and the one-word tail.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-! ## The EVM runs -/

theorem alEntry {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 5)) :
    ∃ k C, Run erc20Runtime (initState cA gh bl σ σ₀ g A I)
      ⟨⟨0x4b9⟩, ⟨4⟩ :: UInt256.ofNat (initState cA gh bl σ σ₀ g A I).executionEnv.calldata.size :: ⟨0xf6⟩ :: ⟨0x95⟩ ::
        [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty, ⟨cA, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := reachBodyOf 5 (by omega) ⟨0xe8⟩ hcode hwv hsize hsel (by jump_dest) (by decide)
  exact ⟨_, _, evm_run h with [jumpdest, push2 ⟨0x95⟩, push2 ⟨0xf6⟩, calldatasize, push1 ⟨4⟩, push2 ⟨0x4b9⟩,
    jump (by jump_dest)]⟩

/-- The slot of `allowance[owner][spender]` as the bytecode computes it. -/
abbrev alSlotW (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) (calldataWord I.calldata 36)

theorem alRun {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 5))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    Returned erc20Runtime (initState cA gh bl σ σ₀ g A I) ⟨cA, σ, A.logSeries⟩
      (UInt256.toByteArray (solcSlotWord σ I (alSlotW I))) := by
  obtain ⟨_, _, h⟩ := alEntry hcode hwv hsize hsel
  obtain ⟨_, _, h1⟩ := decAddrAddrOk h hsz68 hbig hc0 hc1 (by jump_dest) (by simp)
  have h2 := evm_run h1 with [jumpdest, push1 ⟨1⟩, push1 ⟨0x20⟩, swap1, dup2,
    raw mstore 0 (wordAt32Mem ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    push0, swap3, dup4,
    raw mstore 0 (solcMappingHashMem ⟨1⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl
      (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup1, dup5,
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3) (by native_decide) mem_cost
      (solcMappingKeccakSlot ⟨1⟩ (calldataWord I.calldata 4)) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (wordAt32Mem (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) (solcMappingHashMem ⟨1⟩ (calldataWord I.calldata 4)))
      (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    swap1, dup3,
    raw mstore 0 (hashMem (calldataWord I.calldata 36) (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4))
        (solcMappingHashMem ⟨1⟩ (calldataWord I.calldata 4)))
      (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (alSlotW I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (hashMem_keccak _ _ (solcMappingHashMem_size _ _)) (by decide) (by evm_ov)]
  obtain ⟨_, _, h3⟩ := h2.sload (by native_decide) (by evm_ov)
  have h4 := evm_run h3 with [dup2, jump (by jump_dest)]
  exact retWord h4 (by rw [hashMem_size _ _ (solcMappingHashMem_size _ _)])
    (hashMem_read64 _ _ (solcMappingHashMem_size _ _) (solcMappingHashMem_read64 _ _))
    (by rw [hashMem_size _ _ (solcMappingHashMem_size _ _)]; exact lt_usize _ (by norm_num)) (by simp)

theorem alRunShort {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 5)) (hshort : I.calldata.size < 68) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := alEntry hcode hwv hsize hsel
  exact decAddrAddrLenRevert h (lenCheck_short (by norm_num) (size_ge_of_sel rfl hsel) hshort) (by simp)

theorem alRunHuge {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 5)) (hhuge : 2 ^ 255 + 4 ≤ I.calldata.size) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := alEntry hcode hwv hsize hsel
  exact decAddrAddrLenRevert h (lenCheck_huge (by norm_num) hhuge hsize) (by simp)

theorem alRunDirty0 {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 5))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := alEntry hcode hwv hsize hsel
  exact decAddrAddrDirty0Revert h hsz68 hbig hnc0 (by simp)

theorem alRunDirty1 {cA gh bl σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 5))
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    Reverted erc20Runtime (initState cA gh bl σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := alEntry hcode hwv hsize hsel
  exact decAddrAddrDirty1Revert h hsz68 hbig hc0 hnc1 (by simp)

/-! ## The spec derivation -/

def alFrame (a b : EVM.Address) : Frame :=
  ((({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "arg0" addrTy (some .memory) (.address a)).bind
    "arg1" addrTy (some .memory) (.address b)).bind "#ret0" u256 (some .memory) (u256Val 0)

def alStmts : Block := [.return (some (.index (.index (.ident "allowance") (.ident "arg0")) (.ident "arg1")))]

theorem alEnter (m : Machine) (a b : EVM.Address) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnAllowance.decl [.address a, .address b] m = some (.ok (alFrame a b, m)) := by
  simp [enterFn, declare, coerce, fnAllowance, alFrame, fuelDefault]
  try rfl

theorem alBody (o : Oracle) (m : Machine) (a b : EVM.Address) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (alFrame a b) alStmts) m alStmts
      (.returned ((bodyFrame (alFrame a b) alStmts).setVal "#ret0" (u256Val (loadU256 m (alwSlot a b)).toNat)) m) :=
  ExecBlock.consReturn (ExecStmt.returnU256 { ty := u256, loc := some .memory, val := u256Val 0 } rfl
    (EvalExpr.mapping2AddrU256 (by frame_simp [bodyFrame, alFrame]) erc20Flat_var_allowance rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, alFrame]))
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, alFrame]))
      (erc20Layout_allowance a b m.evm))
    (by frame_simp [bodyFrame, alFrame]) rfl (by frame_simp [bodyFrame, alFrame]))

theorem alCall (o : Oracle) (m : Machine) (a b : EVM.Address) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnAllowance [.address a, .address b]
      (.ok [u256Val (loadU256 m (alwSlot a b)).toNat] m) :=
  CallFn.plain (alEnter m a b) rfl rfl (alBody o m a b) rfl
    (retVals_exitScope (by frame_simp [bodyFrame, alFrame]) (by frame_simp [bodyFrame, alFrame])
      (by frame_simp [retVals, bodyFrame, alFrame]))

abbrev alOwner (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
abbrev alSpender (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (calldataWord I.calldata 36).toNat

theorem alSpec (o : Oracle) {cA gh bl σ σ₀ g A I} (hsel : selIs I (selBytes 5)) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    solidityExec erc20Cfg o erc20Flat cA gh bl σ σ₀ g A I
      (.returned (initMachine cA gh bl σ σ₀ g A I)
        [.int ((loadU256 (initMachine cA gh bl σ σ₀ g A I) (alwSlot (alOwner I) (alSpender I))).toNat : Int)])
      (.abi [abiU256]) := by
  have hsvs : decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl I.calldata =
      some [.address (alOwner I), .address (alSpender I)] := by
    rw [decodeArgs_allowance]; exact decodeCalldataValues_address_address_ok hsz68 hbig hc0 hc1
  have hvs : ofAbiParams erc20Flat.types I.calldata fnAllowance.decl.params [.address (alOwner I), .address (alSpender I)] {} =
      some ([.address (alOwner I), .address (alSpender I)], {}) := by
    simp [ofAbiParams, fnAllowance, fuelDefault, calldataRef]
  have hprep : prepareArgs erc20Flat.types I.calldata fuelDefault (initMachine cA gh bl σ σ₀ g A I).heap
      [u256Val (loadU256 (initMachine cA gh bl σ σ₀ g A I) (alwSlot (alOwner I) (alSpender I))).toNat] =
      some (.ok ([u256Val (loadU256 (initMachine cA gh bl σ σ₀ g A I) (alwSlot (alOwner I) (alSpender I))).toNat],
        (initMachine cA gh bl σ σ₀ g A I).heap)) :=
    prepareArgs_of_noRaw (fuel := 1023) (by simp [fuelDefault, u256Val])
  exact solidityExec.call (erc20Dispatch_allowance hsel) erc20Flat_fns5 (Or.inr hwv) rfl hsvs hvs
    (alCall o (initMachine cA gh bl σ σ₀ g A I) (alOwner I) (alSpender I)) hprep (by simp [fuelDefault, u256Val])

/-! ## The coupled result -/

theorem allowanceCorrect {cA gh bl σ_evm σ_spec σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Runtime) (hsize : I.calldata.size < UInt256.size) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selBytes 5)) (hAccounts : Refinement.accountMapEquiv σ_evm σ_spec) :
    runtimeEquivalenceFor erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := size_ge_of_sel rfl hsel
  have hdec : decodeArgs erc20Cfg erc20Flat.types fnAllowance.decl I.calldata = none →
      Reverted erc20Runtime (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty →
      runtimeEquivalenceFor erc20Cfg erc20Flat cA gh bl σ_evm σ_spec σ₀ g A I := fun hd h =>
    Reverted.specDecodingFailed hcode h (erc20Dispatch_allowance hsel) erc20Flat_fns5 (Or.inr hwv)
      (decodeCallArgs_none_of_decodeArgs hd)
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · have hw : WorldEquiv ⟨cA, σ_evm, A.logSeries⟩ (initMachine cA gh bl σ_spec σ₀ g A I) :=
            WorldEquiv.init {} hAccounts
          have hslot : alwSlot (alOwner I) (alSpender I) = alSlotW I := by
            simp only [alwSlot, mappingSlot, solcMappingSlot, alSlotW, keyValueToWord_address_of_canonical _ hc0,
              keyValueToWord_address_of_canonical _ hc1]
          have hword : solcSlotWord σ_evm I (alSlotW I) =
              loadU256 (initMachine cA gh bl σ_spec σ₀ g A I) (alwSlot (alOwner I) (alSpender I)) := by
            rw [hslot]; exact hw.sload rfl _
          refine Returned.specExecutionW default hcode (alRun hcode hwv hsize hsel hsz68 hbig hc0 hc1)
            (alSpec default hsel hwv hsz68 hbig hc0 hc1) hw ?_
          rw [hword]
          exact .abi (uint256ReturnEncoding _)
        · exact hdec (by rw [decodeArgs_allowance]; exact decodeCalldataValues_address_address_none_noncanon1 hsz68 hbig hc0 hc1)
            (alRunDirty1 hcode hwv hsize hsel hsz68 hbig hc0 hc1)
      · exact hdec (by rw [decodeArgs_allowance]; exact decodeCalldataValues_address_address_none_noncanon0 hsz68 hbig hc0)
          (alRunDirty0 hcode hwv hsize hsel hsz68 hbig hc0)
    · exact hdec (by rw [decodeArgs_allowance]; exact decodeCalldataValues_address_address_none_huge (by omega))
        (alRunHuge hcode hwv hsize hsel (by omega))
  · exact hdec (by rw [decodeArgs_allowance]; exact decodeCalldataValues_address_address_none_short hsz4 (by omega))
      (alRunShort hcode hwv hsize hsel (by omega))

end ERC20.Opt
