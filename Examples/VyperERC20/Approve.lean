import Examples.VyperERC20.Allowance
import Examples.ERC20.Approve

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

abbrev approveSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev approveValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev approveSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (approveSpenderWord I).toNat)

abbrev approveValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (approveValueWord I).toNat)

abbrev approveStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (approveSpenderValue I)).insert "value" (approveValueValue I)

abbrev approveOwnerWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def approveSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  erc20AllowanceSlot (.address evm.executionEnv.source)
    (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))

def approveSlotI (I : ExecutionEnv) : UInt256 :=
  erc20AllowanceSlot (.address I.source)
    (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))

def approvePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveSlot evm I) (approveValueWord I)

def approveSelectorWord : UInt256 :=
  ⟨0x095ea7b3⟩

theorem approveOwnerWord_toNat (I : ExecutionEnv) :
    (approveOwnerWord I).toNat = I.source.val := by
  unfold approveOwnerWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem approveOwnerWord_canonical (I : ExecutionEnv) :
    (approveOwnerWord I).toNat < EVM.addressModulus := by
  rw [approveOwnerWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem approveOwner_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (approveOwnerWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [approveOwnerWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem approveStore_spender (I : ExecutionEnv) :
    (approveStore I).get? "spender" = some (approveSpenderValue I) := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_self]

theorem approveStore_value (I : ExecutionEnv) :
    (approveStore I).get? "value" = some (approveValueValue I) := by
  rw [approveStore, store_get_self]

theorem approveStore_allowance (I : ExecutionEnv) :
    (approveStore I).get? "allowance" = none := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_approve_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := approveStore I } evm
      (.var "spender") = .ok (approveSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_spender]

theorem evalExpr_approve_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := approveStore I } evm
      (.var "value") = .ok (approveValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_value]

def approveEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))] }

theorem evalStorageRef_approve_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef vyperERC20Config { contract := erc20Contract, locals := approveStore I } evm
      { base := "allowance", steps := [.mindex sender, .mindex (.var "spender")] } =
        EvalResult.ok (approveEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, sender, envValue, evalExpr_approve_spender,
    ERC20.sender, approveEvaledRef, approveSpenderValue, valueToKey?, EvalResult.seqList,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? vyperERC20Config { contract := erc20Contract, locals := approveStore I } evm
      .storage (allowanceRef sender (.var "spender")) (approveValueValue I) =
        .ok ({ contract := erc20Contract, locals := approveStore I }, approvePostState evm I) := by
  simp only [allowanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := approveStore_allowance I)
      (her := evalStorageRef_approve_allowance evm I)
      (hty := by simp [storageTypeAt?, approveEvaledRef, erc20Contract, ERC20.erc20Contract,
                       ERC20.erc20StorageDecls, uint256Storage, ERC20.uint256Storage,
                       storageTypeStep?])
      (hloc := vyperERC20Config_storage_allowance (.address evm.executionEnv.source)
          (.address (AccountAddress.ofNat (approveSpenderWord I).toNat)))
  rw [vyperERC20StorageLocStore_uint256]
  simp [approvePostState, approveSlot, approveEvaledRef]

theorem erc20Decode_approve_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.approveTransition.params.map Param.name)
      (transitionSignature ERC20.approveTransition).paramTypes I.calldata = some (approveStore I) := by
  show decodeCalldataWithMode DecodeMode.vyper ["spender", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, approveStore, approveSpenderValue, approveValueValue,
    approveSpenderWord, approveValueWord, calldataWord]
    using decodeCalldataWithMode_vyper_addr_uint256_ok
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hcanon

theorem erc20Decode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.approveTransition.params.map Param.name)
      (transitionSignature ERC20.approveTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldataWithMode_vyper_addr_uint256_none_short
      (cd := I.calldata) (x := "spender") (y := "value") hsz4 hshort

theorem erc20Decode_approve_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hnc : ¬ (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.approveTransition.params.map Param.name)
      (transitionSignature ERC20.approveTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, approveSpenderWord]
    using decodeCalldataWithMode_vyper_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hnc

theorem erc20ApproveBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody vyperERC20Config erc20Contract evm (approveStore I) ERC20.approveTransition.body
      (.returned { contract := erc20Contract, locals := approveStore I }
        (approvePostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (evalExpr_approve_value evm I) (approveAssign evm I)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

def approveDispatchMem : ByteArray :=
  vyperERC20Bytecode.write 807 ByteArray.empty 30 2

theorem approveDispatchMem_size : approveDispatchMem.size = 32 := by
  decide +native

def approveSpenderArgMem (spender : UInt256) : ByteArray :=
  (UInt256.toByteArray spender).write 0 approveDispatchMem 64 32

noncomputable def approveInnerKeyMem (owner spender : UInt256) : ByteArray :=
  wordAt32Mem owner (approveSpenderArgMem spender)

noncomputable def approveInnerHashMem (owner spender : UInt256) : ByteArray :=
  wordAt0Mem ⟨1⟩ (approveInnerKeyMem owner spender)

noncomputable def approveInnerSlotWord (owner spender : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((approveInnerHashMem owner spender).readWithPadding 0 64)))

noncomputable def approveOuterKeyMem (owner spender : UInt256) : ByteArray :=
  wordAt32Mem spender (approveInnerHashMem owner spender)

noncomputable def approveOuterHashMem (owner spender : UInt256) : ByteArray :=
  wordAt0Mem (approveInnerSlotWord owner spender) (approveOuterKeyMem owner spender)

noncomputable def approveLogMem (owner spender val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (approveOuterHashMem owner spender) 96 32

noncomputable def approveReturnMem (owner spender val : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (approveLogMem owner spender val) 96 32

theorem approveSpenderArgMem_size (spender : UInt256) :
    (approveSpenderArgMem spender).size = 96 := by
  unfold approveSpenderArgMem
  rw [toByteArray_write_eq _ _ _ (by rw [approveDispatchMem_size]; omega)
      (by rw [approveDispatchMem_size]; exact lt_usize 32 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, approveDispatchMem_size, ByteArray_zeroes_size,
    toByteArray_size]

theorem approveInnerKeyMem_size (owner spender : UInt256) :
    (approveInnerKeyMem owner spender).size = 96 := by
  unfold approveInnerKeyMem
  exact wordAt32Mem_size_96 owner (approveSpenderArgMem_size spender)

theorem approveInnerHashMem_size (owner spender : UInt256) :
    (approveInnerHashMem owner spender).size = 96 := by
  unfold approveInnerHashMem
  exact wordAt0Mem_size_96 ⟨1⟩ (approveInnerKeyMem_size owner spender)

theorem approveOuterKeyMem_size (owner spender : UInt256) :
    (approveOuterKeyMem owner spender).size = 96 := by
  unfold approveOuterKeyMem
  exact wordAt32Mem_size_96 spender (approveInnerHashMem_size owner spender)

theorem approveOuterHashMem_size (owner spender : UInt256) :
    (approveOuterHashMem owner spender).size = 96 := by
  unfold approveOuterHashMem
  exact wordAt0Mem_size_96 (approveInnerSlotWord owner spender)
    (approveOuterKeyMem_size owner spender)

theorem approveLogMem_size (owner spender val : UInt256) :
    (approveLogMem owner spender val).size = 128 := by
  unfold approveLogMem
  simpa [approveOuterHashMem_size] using
    write_end_size_from (UInt256.toByteArray val) (approveOuterHashMem owner spender) 0 32
      (by decide)
      (by rw [toByteArray_size])

theorem approveSpenderArgMem_read64 (spender : UInt256) :
    (approveSpenderArgMem spender).readWithPadding 64 32 = UInt256.toByteArray spender := by
  unfold approveSpenderArgMem
  exact toByteArray_write_read_back_of_gap spender approveDispatchMem 64
    (by rw [approveDispatchMem_size]; exact lt_usize 32 (by norm_num))

theorem approveInnerKeyMem_read32 (owner spender : UInt256) :
    (approveInnerKeyMem owner spender).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold approveInnerKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [approveSpenderArgMem_size spender]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray owner).size ≤ 32
    rw [toByteArray_size])

theorem approveInnerHashMem_read0 (owner spender : UInt256) :
    (approveInnerHashMem owner spender).readWithPadding 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold approveInnerHashMem
  exact wordAt0Mem_read0 ⟨1⟩ (approveInnerKeyMem owner spender)

theorem approveInnerHashMem_read32 (owner spender : UInt256) :
    (approveInnerHashMem owner spender).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold approveInnerHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [approveInnerKeyMem_size owner spender]; omega)
    (by omega)
    (by rw [approveInnerKeyMem_size owner spender]; omega)]
  exact approveInnerKeyMem_read32 owner spender

theorem approveInnerHashMem_read64 (owner spender : UInt256) :
    (approveInnerHashMem owner spender).readWithPadding 64 32 = UInt256.toByteArray spender := by
  unfold approveInnerHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [approveInnerKeyMem_size owner spender]; omega)
    (by omega)
    (by rw [approveInnerKeyMem_size owner spender])]
  unfold approveInnerKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [approveSpenderArgMem_size spender]; omega)
    (by omega)
    (by rw [approveSpenderArgMem_size spender])]
  exact approveSpenderArgMem_read64 spender

theorem approveInnerHashMem_read0_64 (owner spender : UInt256) :
    (approveInnerHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray (⟨1⟩ : UInt256) ++ UInt256.toByteArray owner := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [approveInnerHashMem_size owner spender]; omega)]
  have hleft :
      (approveInnerHashMem owner spender).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [approveInnerHashMem_size owner spender]; omega),
      approveInnerHashMem_read0 owner spender]
  have hright :
      (approveInnerHashMem owner spender).extract 32 64 = UInt256.toByteArray owner := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [approveInnerHashMem_size owner spender]; omega),
      approveInnerHashMem_read32 owner spender]
  rw [show (approveInnerHashMem owner spender).extract 0 64 =
      (approveInnerHashMem owner spender).extract 0 32 ++
        (approveInnerHashMem owner spender).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem approveInnerKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (approveOwnerWord I).toNat < EVM.addressModulus) :
    approveInnerSlotWord (approveOwnerWord I) (approveSpenderWord I) =
      erc20AllowanceOwnerSlot
        (.address (AccountAddress.ofNat (approveOwnerWord I).toNat)) := by
  unfold approveInnerSlotWord
  rw [approveInnerHashMem_read0_64]
  unfold erc20AllowanceOwnerSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanonOwner]
  exact keccakSlot_eq _

theorem approveOuterKeyMem_read32 (owner spender : UInt256) :
    (approveOuterKeyMem owner spender).readWithPadding 32 32 =
      UInt256.toByteArray spender := by
  unfold approveOuterKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [approveInnerHashMem_size owner spender]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray spender).size ≤ 32
    rw [toByteArray_size])

theorem approveOuterHashMem_read0 (owner spender : UInt256) :
    (approveOuterHashMem owner spender).readWithPadding 0 32 =
      UInt256.toByteArray (approveInnerSlotWord owner spender) := by
  unfold approveOuterHashMem
  exact wordAt0Mem_read0 (approveInnerSlotWord owner spender) (approveOuterKeyMem owner spender)

theorem approveOuterHashMem_read32 (owner spender : UInt256) :
    (approveOuterHashMem owner spender).readWithPadding 32 32 =
      UInt256.toByteArray spender := by
  unfold approveOuterHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [approveOuterKeyMem_size owner spender]; omega)
    (by omega)
    (by rw [approveOuterKeyMem_size owner spender]; omega)]
  exact approveOuterKeyMem_read32 owner spender

theorem approveOuterHashMem_read64 (owner spender : UInt256) :
    (approveOuterHashMem owner spender).readWithPadding 64 32 = UInt256.toByteArray spender := by
  unfold approveOuterHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [approveOuterKeyMem_size owner spender]; omega)
    (by omega)
    (by rw [approveOuterKeyMem_size owner spender])]
  unfold approveOuterKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [approveInnerHashMem_size owner spender]; omega)
    (by omega)
    (by rw [approveInnerHashMem_size owner spender])]
  exact approveInnerHashMem_read64 owner spender

theorem approveOuterHashMem_read0_64 (owner spender : UInt256) :
    (approveOuterHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray (approveInnerSlotWord owner spender) ++ UInt256.toByteArray spender := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [approveOuterHashMem_size owner spender]; omega)]
  have hleft :
      (approveOuterHashMem owner spender).extract 0 32 =
        UInt256.toByteArray (approveInnerSlotWord owner spender) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [approveOuterHashMem_size owner spender]; omega),
      approveOuterHashMem_read0 owner spender]
  have hright :
      (approveOuterHashMem owner spender).extract 32 64 = UInt256.toByteArray spender := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [approveOuterHashMem_size owner spender]; omega),
      approveOuterHashMem_read32 owner spender]
  rw [show (approveOuterHashMem owner spender).extract 0 64 =
      (approveOuterHashMem owner spender).extract 0 32 ++
        (approveOuterHashMem owner spender).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem approveOuterKeccakSlot (I : ExecutionEnv)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((approveOuterHashMem (approveOwnerWord I) (approveSpenderWord I))
          |>.readWithPadding 0 64)))
      = approveSlotI I := by
  rw [approveOuterHashMem_read0_64, approveInnerKeccakSlot I (approveOwnerWord_canonical I)]
  unfold approveSlotI erc20AllowanceSlot erc20AllowanceOwnerSlot vyperMappingSlot
  rw [approveOwner_ofNat I, keyValueToWord_address_of_canonical _ hcanonSpender]
  exact keccakSlot_eq _

theorem approveLogMem_read96 (owner spender val : UInt256) :
    (approveLogMem owner spender val).readWithPadding 96 32 = UInt256.toByteArray val := by
  unfold approveLogMem
  exact toByteArray_write_read_back_of_gap val (approveOuterHashMem owner spender) 96
    (by rw [approveOuterHashMem_size]; exact lt_usize 0 (by norm_num))

theorem approveReturnMem_read96 (owner spender val : UInt256) :
    (approveReturnMem owner spender val).readWithPadding 96 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold approveReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [approveLogMem_size owner spender val]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem approveDispatchMem_mload0 :
    (if (⟨0⟩ : UInt256).toNat ≥ approveDispatchMem.size ∨
        (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (approveDispatchMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
      = (⟨206⟩ : UInt256) := by
  decide +native

macro "vyper_erc20_approve_decode" : tactic =>
  `(tactic| decide +native)

theorem erc20X_approveFromEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨206⟩
      [approveSelectorWord] approveDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDret vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (approveSlotI I) (approveValueWord I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨k, C, rd206⟩ := hreach
  have hslot := approveOuterKeccakSlot I hcanonSpender
  have hsizeGuard := calldataSizeGuard68 (n := I.calldata.size) hsz68 hsize
  have hcanonSpenderGuard : UInt256.shiftRight (approveSpenderWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (approveSpenderWord I) hcanonSpender
  have rdBeforeStore := evm_run rd206 with [
    jumpdest,
    raw push4 approveSelectorWord (by vyper_erc20_approve_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiNT (by rw [hsizeGuard, hwv]; decide),
    push1 ⟨4⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiNT (by simpa [approveSpenderWord, calldataWord] using hcanonSpenderGuard),
    push1 ⟨64⟩,
    raw mstore 6 (approveSpenderArgMem (approveSpenderWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨36⟩, calldataload,
    push1 ⟨1⟩, caller, push1 ⟨32⟩,
    raw mstore 0 (approveInnerKeyMem (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov),
    push0,
    raw mstore 0 (approveInnerHashMem (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (approveInnerSlotWord (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov),
    dup1, push1 ⟨64⟩,
    raw mload 0 (approveSpenderWord I) (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := approveInnerHashMem (approveOwnerWord I) (approveSpenderWord I))
          (aw := UInt256.ofNat 3) (off := ⟨64⟩) (v := approveSpenderWord I)
          (by rw [approveInnerHashMem_size]; decide)
          (by decide)
          (approveInnerHashMem_read64 (approveOwnerWord I) (approveSpenderWord I)))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (approveOuterKeyMem (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov),
    push0,
    raw mstore 0 (approveOuterHashMem (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (approveSlotI I) (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost hslot (by decide) (by evm_ov),
    swap1, pop]
  obtain ⟨k1, C1, rdAfterStore⟩ :=
    rdBeforeStore.sstore hperm (by vyper_erc20_approve_decode) (by evm_ov)
  have rdAfterTopic := (evm_run rdAfterStore with [
    push1 ⟨64⟩,
    raw mload 0 (approveSpenderWord I) (UInt256.ofNat 3)
      (by vyper_erc20_approve_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := approveOuterHashMem (approveOwnerWord I) (approveSpenderWord I))
          (aw := UInt256.ofNat 3) (off := ⟨64⟩) (v := approveSpenderWord I)
          (by rw [approveOuterHashMem_size]; decide)
          (by decide)
          (approveOuterHashMem_read64 (approveOwnerWord I) (approveSpenderWord I)))
      (by decide) (by evm_ov),
    caller]).pushConst ERC20.approveApprovalTopic (width := 32) (op := .PUSH32)
      (by decide) (by vyper_erc20_approve_decode) (by evm_ov)
  have rdBeforeLog := evm_run rdAfterTopic with [
    push1 ⟨36⟩, calldataload,
    push1 ⟨96⟩,
    raw mstore 3 (approveLogMem (approveOwnerWord I) (approveSpenderWord I) (approveValueWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨96⟩]
  have rdAfterLog := rdBeforeLog.log3 0 (UInt256.ofNat 4)
    (by vyper_erc20_approve_decode) hperm mem_cost (by decide) (by evm_ov)
  have rdBeforeReturn := evm_run rdAfterLog with [
    push1 ⟨1⟩, push1 ⟨96⟩,
    raw mstore 0 (approveReturnMem (approveOwnerWord I) (approveSpenderWord I) (approveValueWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_approve_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨96⟩]
  exact rdBeforeReturn.ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256))
    (by vyper_erc20_approve_decode)
    mem_cost
    (approveReturnMem_read96 (approveOwnerWord I) (approveSpenderWord I) (approveValueWord I))
    (by evm_ov)

theorem erc20ApproveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨206⟩
      [approveSelectorWord] approveDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd206⟩ := hreach
  have hsizeGuard := calldataSizeGuardShort (n := I.calldata.size) (m := 68)
    hsize (by norm_num [UInt256.size]) hshort
  have hsizeGuard68 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨68⟩ = ⟨1⟩ := by
    simpa using hsizeGuard
  have rd801 := evm_run rd206 with [
    jumpdest,
    raw push4 approveSelectorWord (by vyper_erc20_approve_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiT (by rw [hwv, hsizeGuard68]; decide) (by vyper_erc20_approve_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by norm_num)

theorem erc20ApproveX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨206⟩
      [approveSelectorWord] approveDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd206⟩ := hreach
  have hsizeGuard := calldataSizeGuard68 (n := I.calldata.size) hsz68 hsize
  have hcanonSpenderGuard : UInt256.shiftRight (approveSpenderWord I) ⟨160⟩ ≠ ⟨0⟩ := by
    intro hzero
    exact hnc (u256_lt_addressModulus_of_shiftRight160_zero (approveSpenderWord I) hzero)
  have rd801 := evm_run rd206 with [
    jumpdest,
    raw push4 approveSelectorWord (by vyper_erc20_approve_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by decide +native),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiNT (by rw [hwv, hsizeGuard]; decide),
    push1 ⟨4⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiT (by
      simp [approveSpenderWord, calldataWord]
      exact hcanonSpenderGuard) (by vyper_erc20_approve_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20ApproveSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem approveSelectorWord_of_calldata {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ =
      approveSelectorWord := by
  have h := evmSelectorDecode hsz 0x09 0x5e 0xa7 0xb3 approveSelectorWord (by decide +native)
  rw [hsel] at h
  unfold UInt256.eq at h
  by_cases heq :
      approveSelectorWord =
        UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩
  · exact heq.symm
  · simp [heq] at h
    have hne : UInt256.ofNat 0 ≠ (⟨1⟩ : UInt256) := by decide
    exact False.elim (hne h)

theorem erc20X_approveReach {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨206⟩
      [approveSelectorWord] approveDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have hsz := erc20ApproveSelector_size hsel
  have hword := approveSelectorWord_of_calldata (I := I) hsz hsel
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdBeforeCopy := by
    simpa [hword, approveSelectorWord] using rdBeforeCopy0
  have rdAfterCopy := rdBeforeCopy.codecopy 3 approveDispatchMem (UInt256.ofNat 1)
    (by vyper_erc20_approve_decode) mem_cost (by decide +native) (by decide) (by evm_ov)
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨206⟩ (UInt256.ofNat 1)
      (by vyper_erc20_approve_decode)
      mem_cost
      approveDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_approve_decode) (by decide +native) (by evm_ov)⟩

theorem erc20Dispatch_approve {cd : ByteArray}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some ERC20.approveTransition :=
  dispatchMsg_eq_some_of_split (contract := erc20Contract)
    (pre := []) (post := [ERC20.totalSupplyTransition, ERC20.transferFromTransition,
      ERC20.balanceOfTransition, ERC20.transferTransition, ERC20.allowanceTransition])
    rfl rfl (by simp) (by rw [selectorOf, vyperERC20ApproveSelectorBytes]; exact hsel)

theorem erc20ApproveBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨206⟩
      [approveSelectorWord] approveDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := erc20Dispatch_approve (cd := I.calldata) hsel
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hbody := erc20ApproveBodyReturns evmS I (by simp only [evmS, initState]; exact hwv)
  have hσPost : EVMStateEquiv (approvePostState evmE I) (approvePostState evmS I) := by
    unfold approvePostState approveSlot
    rw [hσ.executionEnv]
    exact hσ.storageStore_codeOwner
      (erc20AllowanceSlot (.address evmS.executionEnv.source)
        (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))) rfl
  have hsz4 := erc20ApproveSelector_size hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus
    · have hdec0 := erc20Decode_approve_ok (I := I) hsz68 hcanonSpender
      have hdec :
          decodeCalldataWithMode vyperERC20Config.abiDecodeMode
            (ERC20.approveTransition.params.map Param.name)
            (transitionSignature ERC20.approveTransition).paramTypes I.calldata =
              some (approveStore I) := by
        simpa [vyperERC20Config] using hdec0
      exact (erc20X_approveFromEntry (g := Sat256.ofUInt256 g)
          hwv hperm hsz68 hsize hcanonSpender hreach)
        |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
          (by simp [evmE, approvePostState, approveSlot, approveSlotI, initState,
            vyperERC20StorageStore_createdAccounts])
          (accountMapEquiv.of_eq (by
            simp [evmE, approvePostState, approveSlot, approveSlotI, initState,
              vyperERC20StorageStore_accountMap]))
          hσPost
          (returnEquiv_of_encode ERC20.erc20BoolTrueReturnEncoding)
    · have hdec0 := erc20Decode_approve_none_noncanon (I := I) hsz68 hcanonSpender
      have hdec :
          decodeCalldataWithMode vyperERC20Config.abiDecodeMode
            (ERC20.approveTransition.params.map Param.name)
            (transitionSignature ERC20.approveTransition).paramTypes I.calldata = none := by
        simpa [vyperERC20Config] using hdec0
      exact (erc20ApproveX_noncanon_spender (g := Sat256.ofUInt256 g)
          hwv hsz68 hsize hcanonSpender hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec0 := erc20Decode_approve_none_short (I := I) hsz4 hshort
    have hdec :
        decodeCalldataWithMode vyperERC20Config.abiDecodeMode
          (ERC20.approveTransition.params.map Param.name)
          (transitionSignature ERC20.approveTransition).paramTypes I.calldata = none := by
      simpa [vyperERC20Config] using hdec0
    exact (erc20ApproveX_shortarg (g := Sat256.ofUInt256 g) hwv hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem erc20ApproveRuntimeSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20ApproveBodyCore hcode hwv hperm hsize hsel
    (erc20X_approveReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsel)
    hAccounts

end VyperERC20
