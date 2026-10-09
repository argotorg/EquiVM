import Solidity.Examples.ERC20.Shapes

/-!
# ERC20 — `balanceOf(address)` refines its Solidity getter

EVM side: the decoder at `0x499`, the slot `keccak256(owner ++ 0)` hashed in scratch memory at
`0xc4`, the load and the one-word tail.  The three decoding failures (short calldata, calldata of
`2^255 + 4` bytes or more, an address word that is not canonical) are the relation's
`decodingFailed` case.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-! ## The EVM runs -/

/-- From the body entry to the decoder, `4 :: calldatasize :: 0xc4 :: 0x95 :: sel` on the stack. -/
theorem boEntry {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 3)) :
    ∃ k C, Run erc20Runtime (initState σ σ₀ g A I)
      ⟨⟨0x499⟩, ⟨4⟩ :: UInt256.ofNat (initState σ σ₀ g A I).executionEnv.calldata.size :: ⟨0xc4⟩ :: ⟨0x95⟩ ::
        [solcSelectorWord I], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ k C := by
  obtain ⟨_, _, h⟩ := reachBodyOf 3 (by omega) ⟨0xb6⟩ hcode hwv hsize hsel (by jump_dest) (by decide)
  exact ⟨_, _, evm_run h with [jumpdest, push2 ⟨0x95⟩, push2 ⟨0xc4⟩, calldatasize, push1 ⟨4⟩, push2 ⟨0x499⟩,
    jump (by jump_dest)]⟩

theorem boRun {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 3))
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    Returned erc20Runtime (initState σ σ₀ g A I) ⟨A.createdAccounts, σ, A.logSeries⟩
      (UInt256.toByteArray (solcSlotWord σ I (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)))) := by
  obtain ⟨_, _, h⟩ := boEntry hcode hwv hsize hsel
  obtain ⟨_, _, h1⟩ := decAddrOk h hsz36 hbig hcanon (by jump_dest) (by simp)
  have h2 := evm_run h1 with [jumpdest, push0, push1 ⟨0x20⟩, dup2, swap1,
    raw mstore 0 (wordAt32Mem ⟨0⟩ solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost rfl (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 0 (solcMappingHashMem ⟨0⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3) (by native_decide) mem_cost rfl
      (by decide) (by evm_ov),
    push1 ⟨0x40⟩, swap1,
    raw keccak256 0 (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3) (by native_decide) mem_cost
      (solcMappingKeccakSlot ⟨0⟩ (calldataWord I.calldata 4)) (by decide) (by evm_ov)]
  obtain ⟨_, _, h3⟩ := h2.sload (by native_decide) (by evm_ov)
  have h4 := evm_run h3 with [dup2, jump (by jump_dest)]
  exact retWord h4 (by rw [solcMappingHashMem_size]) (solcMappingHashMem_read64 _ _)
    (by rw [solcMappingHashMem_size]; exact lt_usize _ (by norm_num)) (by simp)

theorem boRunShort {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 3)) (hshort : I.calldata.size < 36) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := boEntry hcode hwv hsize hsel
  exact decAddrLenRevert h (lenCheck_short (by norm_num) (size_ge_of_sel rfl hsel) hshort) (by simp)

theorem boRunHuge {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 3)) (hhuge : 2 ^ 255 + 4 ≤ I.calldata.size) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := boEntry hcode hwv hsize hsel
  exact decAddrLenRevert h (lenCheck_huge (by norm_num) hhuge hsize) (by simp)

theorem boRunDirty {σ σ₀ A I} {g : Sat256} (hcode : I.code = erc20Runtime) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (selBytes 3))
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    Reverted erc20Runtime (initState σ σ₀ g A I) ByteArray.empty := by
  obtain ⟨_, _, h⟩ := boEntry hcode hwv hsize hsel
  exact decAddrDirtyRevert h hsz36 hbig hnc (by simp)

/-! ## The spec derivation -/

def boFrame (a : EVM.Address) : Frame :=
  (({ here := "ERC20", locals := ∅, retVars := ["#ret0"] } : Frame).bind "arg0" addrTy (some .memory) (.address a)).bind
    "#ret0" u256 (some .memory) (u256Val 0)

def boStmts : Block := [.return (some (.index (.ident "balanceOf") (.ident "arg0")))]

theorem boEnter (m : Machine) (a : EVM.Address) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnBalanceOf.decl [.address a] m = some (.ok (boFrame a, m)) := by
  simp [enterFn, declare, coerce, fnBalanceOf, boFrame, fuelDefault]
  try rfl

theorem boBody (o : Oracle) (m : Machine) (a : EVM.Address) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (boFrame a) boStmts) m boStmts
      (.returned ((bodyFrame (boFrame a) boStmts).setVal "#ret0" (u256Val (loadU256 m (balSlot a)).toNat)) m) :=
  ExecBlock.consReturn (ExecStmt.returnU256 { ty := u256, loc := some .memory, val := u256Val 0 } rfl
    (EvalExpr.mappingAddrU256 (by frame_simp [bodyFrame, boFrame]) erc20Flat_var_balanceOf rfl rfl
      (EvalExpr.localVal addrTy (some .memory) (by frame_simp [bodyFrame, boFrame])) (erc20Leaf_balanceOf a))
    (by frame_simp [bodyFrame, boFrame]) rfl (by frame_simp [bodyFrame, boFrame]))

theorem boCall (o : Oracle) (m : Machine) (a : EVM.Address) :
    CallFn erc20Cfg o erc20Flat (rootFrame erc20Flat) m fnBalanceOf [.address a]
      (.ok [u256Val (loadU256 m (balSlot a)).toNat] m) :=
  CallFn.plain (boEnter m a) rfl rfl (boBody o m a) rfl
    (retVals_exitScope (by frame_simp [bodyFrame, boFrame]) (by frame_simp [bodyFrame, boFrame])
      (by frame_simp [retVals, bodyFrame, boFrame]))

/-- The owner argument. -/
abbrev boOwner (I : ExecutionEnv) : EVM.Address := AccountAddress.ofNat (calldataWord I.calldata 4).toNat

theorem boSpec (o : Oracle) {σ σ₀ g A I} (hsel : selIs I (selBytes 3)) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    solidityExec erc20Cfg o erc20Flat ∅ σ σ₀ g A I
      (.returned (initMachine σ σ₀ g A I ∅)
        [.int ((loadU256 (initMachine σ σ₀ g A I ∅) (balSlot (boOwner I))).toNat : Int)])
      (.abi [abiU256]) := by
  have hsvs : decodeArgs erc20Cfg erc20Flat.types fnBalanceOf.decl I.calldata = some [.address (boOwner I)] := by
    rw [decodeArgs_balanceOf]; exact decodeCalldataValues_address_ok hsz36 hbig hcanon
  have hvs : ofAbiParams erc20Flat.types I.calldata fnBalanceOf.decl.params [.address (boOwner I)] {} =
      some ([.address (boOwner I)], {}) := by
    simp [ofAbiParams, fnBalanceOf, fuelDefault, calldataRef]
  have hprep : prepareArgs erc20Flat.types I.calldata fuelDefault (initMachine σ σ₀ g A I ∅).heap
      [u256Val (loadU256 (initMachine σ σ₀ g A I ∅) (balSlot (boOwner I))).toNat] =
      some (.ok ([u256Val (loadU256 (initMachine σ σ₀ g A I ∅) (balSlot (boOwner I))).toNat],
        (initMachine σ σ₀ g A I ∅).heap)) :=
    prepareArgs_of_noRaw (fuel := 1023) (by simp [fuelDefault, u256Val])
  exact solidityExec.call (erc20Dispatch_balanceOf hsel) erc20Flat_fns4 (Or.inr hwv) rfl hsvs hvs
    (boCall o (initMachine σ σ₀ g A I ∅) (boOwner I)) hprep (by simp [fuelDefault, u256Val])

/-! ## The coupled result -/

theorem balanceOfCorrect {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Runtime) (hsize : I.calldata.size < UInt256.size) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selBytes 3)) :
    runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := size_ge_of_sel rfl hsel
  have hdec : decodeArgs erc20Cfg erc20Flat.types fnBalanceOf.decl I.calldata = none →
      Reverted erc20Runtime (initState σ σ₀ (Sat256.ofUInt256 g) A I) ByteArray.empty →
      runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I := fun hd h =>
    Reverted.specDecodingFailed hcode h (erc20Dispatch_balanceOf hsel) erc20Flat_fns4 (Or.inr hwv)
      (decodeCallArgs_none_of_decodeArgs hd)
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hw : WorldEquiv ⟨A.createdAccounts, σ, A.logSeries⟩ (initMachine σ σ₀ g A I ∅) :=
          WorldEquiv.init ∅ {}
        have hslot : balSlot (boOwner I) = solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4) := by
          simp only [balSlot, mappingSlot, solcMappingSlot, keyValueToWord_address_of_canonical _ hcanon]
        have hword : solcSlotWord σ I (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)) =
            loadU256 (initMachine σ σ₀ g A I ∅) (balSlot (boOwner I)) := by
          rw [hslot]; exact hw.sload rfl _
        refine Returned.specExecutionW default hcode (boRun hcode hwv hsize hsel hsz36 hbig hcanon)
          (boSpec default hsel hwv hsz36 hbig hcanon) hw ?_
        rw [hword]
        exact .abi (uint256ReturnEncoding _)
      · exact hdec (by rw [decodeArgs_balanceOf]; exact decodeCalldataValues_address_none_noncanon hsz36 hbig hcanon)
          (boRunDirty hcode hwv hsize hsel hsz36 hbig hcanon)
    · exact hdec (by rw [decodeArgs_balanceOf]; exact decodeCalldataValues_address_none_huge (by omega))
        (boRunHuge hcode hwv hsize hsel (by omega))
  · exact hdec (by rw [decodeArgs_balanceOf]; exact decodeCalldataValues_address_none_short hsz4 (by omega))
      (boRunShort hcode hwv hsize hsel (by omega))

end ERC20.Opt
