import Examples.ERC20.Allowance
import Examples.ERC20.Storage
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace ERC20

/-! ## ABI decode and source-level body for `approve(address,uint256)` -/

/-- The raw ABI word for `approve`'s `spender` argument. -/
abbrev approveSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `approve`'s `value` argument. -/
abbrev approveValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev approveSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (approveSpenderWord I).toNat)

abbrev approveValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (approveValueWord I).toNat)

abbrev approveStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "spender" (approveSpenderValue I)).insert "value" (approveValueValue I)

def approveSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  erc20AllowanceSlot (.address evm.executionEnv.source)
    (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))

def approveSlotI (I : ExecutionEnv) : UInt256 :=
  erc20AllowanceSlot (.address I.source)
    (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))

def approvePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveSlot evm I) (approveValueWord I)

theorem erc20Decode_approve_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = some (approveStore I) := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, approveStore, approveSpenderValue, approveValueValue,
    approveSpenderWord, approveValueWord, calldataWord]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hcanon

theorem erc20Decode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_short
      (cd := I.calldata) (x := "spender") (y := "value") hsz4 hshort

theorem erc20Decode_approve_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, approveSpenderWord]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "spender") (y := "value") hsz68 hbig hnc

theorem erc20Decode_approve_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_huge
      (cd := I.calldata) (x := "spender") (y := "value") hbig

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
    evalExpr? erc20Config { contract := erc20Contract, locals := approveStore I } evm
      (.var "spender") = .ok (approveSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_spender]

theorem evalExpr_approve_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := approveStore I } evm
      (.var "value") = .ok (approveValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_value]

def approveEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))] }

theorem evalStorageRef_approve_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config { contract := erc20Contract, locals := approveStore I } evm
      { base := "allowance", steps := [.mindex sender, .mindex (.var "spender")] } =
        EvalResult.ok (approveEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, sender, envValue, evalExpr_approve_spender,
    approveEvaledRef, approveSpenderValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? erc20Config { contract := erc20Contract, locals := approveStore I } evm
      (allowanceRef sender (.var "spender")) (approveValueValue I) =
        .ok ({ contract := erc20Contract, locals := approveStore I }, approvePostState evm I) := by
  unfold assignStorageRef?
  simp only [allowanceRef]
  rw [approveStore_allowance]
  rw [evalStorageRef_approve_allowance]
  simp [approvePostState, approveSlot, approveEvaledRef, approveValueValue, EvalResult.bind,
    EvalResult.ofOption, bind, pure]
  change (match
      match storageLocStore evm (erc20Uint256Loc (approveSlot evm I))
          (.int (Int.ofNat (approveValueWord I).toNat)) with
      | some a => EvalResult.ok a
      | none => EvalResult.error EvalError.storageError,
      fun evm' =>
        EvalResult.ok (({ contract := erc20Contract, locals := approveStore I } : Frame), evm') with
    | EvalResult.ok a, f => f a
    | EvalResult.revert, _ => EvalResult.revert
    | EvalResult.error e, _ => EvalResult.error e) =
      EvalResult.ok (({ contract := erc20Contract, locals := approveStore I } : Frame),
        approvePostState evm I)
  rw [erc20StorageLocStore_uint256]
  simp [approvePostState]

theorem erc20ApproveBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody erc20Config erc20Contract evm (approveStore I) approveTransition.body
      (.returned { contract := erc20Contract, locals := approveStore I }
        (approvePostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (evalExpr_approve_value evm I) (approveAssign evm I)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

/-! ## EVM scratch memory and slot facts for `approve(address,uint256)` -/

abbrev approveOwnerWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

theorem approveSource_keyValueToWord (a : AccountAddress) :
    keyValueToWord (.address a) = UInt256.ofNat a.val := by
  apply u256_inj
  unfold keyValueToWord UInt256.ofNat
  change a.val = (Fin.ofNat UInt256.size a.val).val
  rw [Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))).symm

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

theorem allowanceInnerKeccakSlot_word (owner : UInt256)
    (hcanonOwner : owner.toNat < EVM.addressModulus) :
    allowanceInnerSlot owner =
      erc20AllowanceOwnerSlot (.address (AccountAddress.ofNat owner.toNat)) := by
  unfold allowanceInnerSlot
  rw [allowanceInnerHashMem_read0_64]
  unfold erc20AllowanceOwnerSlot erc20MappingSlot
  rw [erc20KeyValueToWord_address_of_canonical _ hcanonOwner]
  exact mappingSlot_single owner ⟨1⟩

theorem erc20AddrMask_clean {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.land w erc20AddrMask = w := by
  apply u256_inj
  show Nat.land w.toNat erc20AddrMask.toNat % EVM.twoPow 256 = w.toNat
  rw [show erc20AddrMask.toNat = 2 ^ 160 - 1 from by decide,
    erc20Land_mask160 _ (by
      rw [show EVM.addressModulus = 2 ^ 160 from by decide] at hcanon
      exact hcanon)]
  exact Nat.mod_eq_of_lt (by
    change w.val.val < EVM.twoPow 256
    exact w.val.isLt)

theorem erc20AddrMask_clean_left {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.land erc20AddrMask w = w := by
  apply u256_inj
  show Nat.land erc20AddrMask.toNat w.toNat % EVM.twoPow 256 = w.toNat
  rw [show Nat.land erc20AddrMask.toNat w.toNat = Nat.land w.toNat erc20AddrMask.toNat
    from Nat.and_comm _ _]
  show Nat.land w.toNat erc20AddrMask.toNat % EVM.twoPow 256 = w.toNat
  exact congrArg UInt256.toNat (erc20AddrMask_clean hcanon)

/-- Approve stores the owner key at scratch offset `0x00` before it stores the allowance base slot. -/
noncomputable def approveInnerOwnerMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32

theorem approveInnerOwnerMem_size (owner : UInt256) :
    (approveInnerOwnerMem owner).size = 96 := by
  unfold approveInnerOwnerMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem approveInnerOwnerMem_writeSlot (owner : UInt256) :
    (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (approveInnerOwnerMem owner) 32 32 =
      allowanceInnerHashMem owner := by
  unfold approveInnerOwnerMem allowanceInnerHashMem allowanceInnerBaseMem
  rw [write32_eq _ solcFreePtrMem 0 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
    omega)]
  rw [write32_eq _ solcFreePtrMem 32 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
    omega)]
  have hownerFull : (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have honeFull :
      (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hownerFull, honeFull]
  have hsolc0 : solcFreePtrMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hsolc0, ByteArray.empty_append]
  rw [show 0 + 32 = 32 from rfl, show 32 + 32 = 64 from rfl, solcFreePtrMem_size]
  have hleft0 :
      (UInt256.toByteArray owner ++ solcFreePtrMem.extract 32 96).extract 0 32 =
        UInt256.toByteArray owner := by
    rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
    exact hownerFull
  rw [hleft0]
  have hleftTail :
      (UInt256.toByteArray owner ++ solcFreePtrMem.extract 32 96).extract 64
          (UInt256.toByteArray owner ++ solcFreePtrMem.extract 32 96).size =
        solcFreePtrMem.extract 64 96 := by
    rw [extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega)]
    rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract, solcFreePtrMem_size]
    rw [extract_extract_BA]
    rfl
  rw [hleftTail]
  have hrightZero :
      (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨1⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hrightZero, ByteArray.empty_append]
  have hrightTail :
      (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨1⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).extract 32
        (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨1⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).size =
      UInt256.toByteArray (⟨1⟩ : UInt256) ++ solcFreePtrMem.extract 64 96 := by
    rw [ByteArray.append_assoc]
    exact extract_append_right' _ _ _ _
      (by rw [ByteArray.size_extract, solcFreePtrMem_size]; omega)
      (by
        rw [ByteArray.size_append, ByteArray.size_extract, solcFreePtrMem_size])
  rw [hrightTail]
  exact ByteArray.append_assoc

/-- Approve stores the spender key at scratch offset `0x00` before replacing the inner base slot. -/
noncomputable def approveOuterSpenderMem (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray spender).write 0 (allowanceInnerHashMem owner) 0 32

theorem approveOuterSpenderMem_size (owner spender : UInt256) :
    (approveOuterSpenderMem owner spender).size = 96 := by
  unfold approveOuterSpenderMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [allowanceInnerHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, allowanceInnerHashMem_size, toByteArray_size]
  omega

theorem approveOuterSpenderMem_writeSlot (owner spender : UInt256) :
    (UInt256.toByteArray (allowanceInnerSlot owner)).write 0
        (approveOuterSpenderMem owner spender) 32 32 =
      allowanceOuterHashMem owner spender := by
  unfold approveOuterSpenderMem allowanceOuterHashMem allowanceOuterBaseMem
  rw [write32_eq _ (allowanceInnerHashMem owner) 0 (by rw [toByteArray_size])
      (by rw [allowanceInnerHashMem_size]; omega)]
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, allowanceInnerHashMem_size, toByteArray_size]
    omega)]
  rw [write32_eq _ (allowanceInnerHashMem owner) 32 (by rw [toByteArray_size])
      (by rw [allowanceInnerHashMem_size]; omega)]
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, allowanceInnerHashMem_size, toByteArray_size]
    omega)]
  have hspenderFull : (UInt256.toByteArray spender).extract 0 32 = UInt256.toByteArray spender := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray spender).size ≤ 32
      rw [toByteArray_size])
  have hslotFull :
      (UInt256.toByteArray (allowanceInnerSlot owner)).extract 0 32 =
        UInt256.toByteArray (allowanceInnerSlot owner) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (allowanceInnerSlot owner)).size ≤ 32
      rw [toByteArray_size])
  rw [hspenderFull, hslotFull]
  have hbase0 : (allowanceInnerHashMem owner).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hbase0, ByteArray.empty_append]
  rw [show 0 + 32 = 32 from rfl, show 32 + 32 = 64 from rfl,
    allowanceInnerHashMem_size]
  have hleft0 :
      (UInt256.toByteArray spender ++ (allowanceInnerHashMem owner).extract 32 96).extract 0 32 =
        UInt256.toByteArray spender := by
    rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
    exact hspenderFull
  rw [hleft0]
  have hleftTail :
      (UInt256.toByteArray spender ++ (allowanceInnerHashMem owner).extract 32 96).extract 64
          (UInt256.toByteArray spender ++ (allowanceInnerHashMem owner).extract 32 96).size =
        (allowanceInnerHashMem owner).extract 64 96 := by
    rw [extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega)]
    rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract, allowanceInnerHashMem_size]
    rw [extract_extract_BA]
    rfl
  rw [hleftTail]
  have hrightZero :
      ((allowanceInnerHashMem owner).extract 0 32 ++
          UInt256.toByteArray (allowanceInnerSlot owner) ++
          (allowanceInnerHashMem owner).extract 64 96).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hrightZero, ByteArray.empty_append]
  have hrightTail :
      ((allowanceInnerHashMem owner).extract 0 32 ++
          UInt256.toByteArray (allowanceInnerSlot owner) ++
          (allowanceInnerHashMem owner).extract 64 96).extract 32
        ((allowanceInnerHashMem owner).extract 0 32 ++
          UInt256.toByteArray (allowanceInnerSlot owner) ++
          (allowanceInnerHashMem owner).extract 64 96).size =
      UInt256.toByteArray (allowanceInnerSlot owner) ++
        (allowanceInnerHashMem owner).extract 64 96 := by
    rw [ByteArray.append_assoc]
    exact extract_append_right' _ _ _ _
      (by rw [ByteArray.size_extract, allowanceInnerHashMem_size]; omega)
      (by
        rw [ByteArray.size_append, ByteArray.size_extract, allowanceInnerHashMem_size])
  rw [hrightTail]
  exact ByteArray.append_assoc

theorem allowanceOuterKeccakSlot_word (owner spender : UInt256)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hcanonSpender : spender.toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceOuterHashMem owner spender).readWithPadding 0 64)))
      =
        erc20AllowanceSlot (.address (AccountAddress.ofNat owner.toNat))
          (.address (AccountAddress.ofNat spender.toNat)) := by
  rw [allowanceOuterHashMem_read0_64, allowanceInnerKeccakSlot_word owner hcanonOwner]
  unfold erc20AllowanceSlot erc20AllowanceOwnerSlot erc20MappingSlot
  rw [erc20KeyValueToWord_address_of_canonical _ hcanonOwner,
    erc20KeyValueToWord_address_of_canonical _ hcanonSpender]
  exact mappingSlot_single spender (erc20MappingSlot owner ⟨1⟩)

theorem approveOuterKeccakSlot (I : ExecutionEnv)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceOuterHashMem (approveOwnerWord I) (approveSpenderWord I))
          |>.readWithPadding 0 64)))
      = approveSlotI I := by
  have howner := approveOwnerWord_canonical I
  rw [allowanceOuterKeccakSlot_word (approveOwnerWord I) (approveSpenderWord I)
    howner hcanonSpender]
  unfold approveSlotI
  rw [approveOwner_ofNat]

/-- Memory after approve's bool-return encoder overwrites the event data word at `0x80`. -/
noncomputable def approveReturnMem (owner spender value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (allowanceReturnMem owner spender value) 128 32

theorem approveReturnMem_size (owner spender value : UInt256) :
    (approveReturnMem owner spender value).size = 160 := by
  unfold approveReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, allowanceReturnMem_size,
    toByteArray_size]
  omega

theorem approveReturnMem_read64 (owner spender value : UInt256) :
    (approveReturnMem owner spender value).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold approveReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [allowanceReturnMem_size]; omega) (by omega),
    allowanceReturnMem_read64]

theorem approveReturnMem_mload64 (owner spender value : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveReturnMem owner spender value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveReturnMem owner spender value).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveReturnMem_size]; decide) (by decide)
    (approveReturnMem_read64 owner spender value)

theorem approveReturnMem_read128 (owner spender value : UInt256) :
    (approveReturnMem owner spender value).readWithPadding 128 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold approveReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceReturnMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem erc20RoutineBoolCleanup {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2007⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret (UInt256.isZero (UInt256.isZero v) :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, dup2, iszero, iszero, swap1, pop, swap2, swap1, pop,
    jump hret ]⟩

theorem erc20RoutineEncodeBoolFromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {mem memout : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2033⟩ (⟨128⟩ :: val :: ret :: R)
        mem (UInt256.ofNat 5) rdata acc k C)
    (hmemout : (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0 mem 128 32
        = memout)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      memout (UInt256.ofNat 5) rdata acc k' C' := by
  let rd2007 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨2052⟩, push0, dup4, add, dup5, push2 ⟨2018⟩,
    jump erc20_jd,
    jumpdest, push2 ⟨2027⟩, dup2, push2 ⟨2007⟩,
    jump erc20_jd ]
  obtain ⟨k1, C1, rd2027⟩ := erc20RoutineBoolCleanup rd2007 erc20_jd (by evm_ov)
  let rd := evm_run rd2027 with [
    jumpdest, dup3,
    raw mstore 0 memout (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    pop, pop,
    jump erc20_jd,
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩

/-! ## EVM trace for `approve(address,uint256)` -/

def approveApprovalTopic : UInt256 :=
  ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩

/-- Wrapper pc 100 sets up calldata bounds for `approve(address,uint256)` and jumps to the
    `(address,uint256)` tuple decoder at pc 1945. -/
theorem erc20ApproveX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1945⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨121⟩, ⟨126⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨126⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨121⟩, swap2, swap1, push2 ⟨1945⟩, jump erc20_jd ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

/-- The approve tuple decoder accepts two static words and jumps to the address decoder for
    the `spender` argument. -/
theorem erc20ApproveX_dec1874_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
        [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨1980⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
          ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨121⟩, ⟨126⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨k, C, rd⟩ := erc20ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1967⟩, jumpiT (by rw [hslt]; decide) erc20_jd,
    jumpdest, push0, push2 ⟨1980⟩, dup6, dup3, dup7, add, push2 ⟨1874⟩,
    jump erc20_jd ]⟩

/-- The `spender` address decode (success): one application of the shared `RD.erc20DecodeAddrOk`
    routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec1980` spender chain. -/
theorem erc20ApproveX_dec1980 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1980⟩
        [approveSpenderWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨121⟩, ⟨126⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20ApproveX_dec1874_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.erc20DecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem erc20ApproveX_dec1925_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
        [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨1997⟩, ⟨32⟩, ⟨0⟩,
          approveSpenderWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨121⟩, ⟨126⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20ApproveX_dec1980 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨1997⟩, dup6, dup3, dup7,
    add, push2 ⟨1925⟩, jump erc20_jd ]⟩

theorem erc20ApproveX_dec1903_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1903⟩
        [approveValueWord I, ⟨1939⟩, approveValueWord I, ⟨4⟩ + ⟨32⟩,
          UInt256.ofNat I.calldata.size, ⟨1997⟩, ⟨32⟩, ⟨0⟩, approveSpenderWord I,
          ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨121⟩, ⟨126⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20ApproveX_dec1925_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨1939⟩, dup2,
    push2 ⟨1903⟩, jump erc20_jd ]⟩

theorem erc20ApproveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨370⟩
        [approveValueWord I, approveSpenderWord I, ⟨126⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd1903⟩ := erc20ApproveX_dec1903_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have rd1894 := evm_run rd1903 with [
    jumpdest, push2 ⟨1912⟩, dup2, push2 ⟨1894⟩, jump erc20_jd ]
  have rd1912 := rd1894.erc20Routine0766 erc20_jd (by evm_ov)
  have hclean : UInt256.eq (approveValueWord I) (approveValueWord I) = ⟨1⟩ :=
    erc20Ueq_self (approveValueWord I)
  have rd1939 := evm_run rd1912 with [
    jumpdest, dup2, eq, push2 ⟨1922⟩, jumpiT (by rw [hclean]; decide) erc20_jd,
    jumpdest, pop, jump erc20_jd ]
  exact ⟨_, _, evm_run rd1939 with [
    jumpdest, swap3, swap2, pop, pop, jump erc20_jd,
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump erc20_jd,
    jumpdest, push2 ⟨370⟩, jump erc20_jd ]⟩

theorem erc20ApproveX_stored {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨496⟩
        [approveValueWord I, ⟨0⟩, approveValueWord I, approveSpenderWord I, ⟨126⟩, sel]
        (allowanceOuterHashMem (approveOwnerWord I) (approveSpenderWord I)) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (approveSlotI I) (approveValueWord I)) k C := by
  obtain ⟨k, C, rd370⟩ := erc20ApproveX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have hownerCleanL : UInt256.land erc20AddrMask (approveOwnerWord I) = approveOwnerWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have hspenderCleanL :
      UInt256.land erc20AddrMask (approveSpenderWord I) = approveSpenderWord I :=
    erc20AddrMask_clean_left hcanonSpender
  have hslot := approveOuterKeccakSlot I hcanonSpender
  have rd421₀ := evm_run rd370 with [
    jumpdest, push0, dup2, push1 ⟨1⟩, push0, caller, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd421 := rd421₀
  rw [hownerCleanL, hownerCleanL] at rd421
  have rd434 := evm_run rd421 with [
    dup2,
    raw mstore 0 (approveInnerOwnerMem (approveOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (allowanceInnerHashMem (approveOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (approveInnerOwnerMem_writeSlot (approveOwnerWord I)) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (allowanceInnerSlot (approveOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd480₀ := evm_run rd434 with [
    push0, dup6, push20 erc20AddrMask, and, push20 erc20AddrMask, and ]
  have rd480 := rd480₀
  rw [hspenderCleanL, hspenderCleanL] at rd480
  have rd493 := evm_run rd480 with [
    dup2,
    raw mstore 0 (approveOuterSpenderMem (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, swap1, dup2,
    raw mstore 0 (allowanceOuterHashMem (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (approveOuterSpenderMem_writeSlot (approveOwnerWord I) (approveSpenderWord I))
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push0,
    raw keccak256 0 (approveSlotI I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov),
    dup2, swap1 ]
  exact rd493.sstore hperm (by decide) (by evm_ov)

theorem erc20X_approve {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc20Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (approveSlotI I) (approveValueWord I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨k, C, rd496⟩ := erc20ApproveX_stored (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonSpender hreach
  have hownerCleanL : UInt256.land erc20AddrMask (approveOwnerWord I) = approveOwnerWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have hspenderCleanL :
      UInt256.land erc20AddrMask (approveSpenderWord I) = approveSpenderWord I :=
    erc20AddrMask_clean_left hcanonSpender
  have rd576₀ := evm_run rd496 with [
    pop, dup3, push20 erc20AddrMask, and, caller, push20 erc20AddrMask, and ]
  have rd543₀ := rd576₀.pushConst approveApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd543 := rd543₀
  rw [hspenderCleanL, hownerCleanL] at rd543
  have rd2073 := evm_run rd543 with [
    dup5, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (allowanceOuterHashMem_mload64 (approveOwnerWord I) (approveSpenderWord I))
      (by decide) (by evm_ov),
    push2 ⟨589⟩, swap2, swap1, push2 ⟨2073⟩, jump erc20_jd ]
  obtain ⟨k1, C1, rd589⟩ := erc20RoutineEncodeUint256FromMem
    (val := approveValueWord I) (ret := ⟨589⟩)
    (R := [approveApprovalTopic, approveOwnerWord I, approveSpenderWord I, ⟨0⟩,
      approveValueWord I, approveSpenderWord I, ⟨126⟩, sel])
    rd2073 (by rfl) erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have rd597 := evm_run rd589 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (allowanceReturnMem_mload64 (approveOwnerWord I) (approveSpenderWord I)
        (approveValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd598 := rd597.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  have rd126 := evm_run rd598 with [
    push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop, jump erc20_jd ]
  have rd2033 := evm_run rd126 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (allowanceReturnMem_mload64 (approveOwnerWord I) (approveSpenderWord I)
        (approveValueWord I))
      (by decide) (by evm_ov),
    push2 ⟨139⟩, swap2, swap1, push2 ⟨2033⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd139⟩ := erc20RoutineEncodeBoolFromMem
    (val := (⟨1⟩ : UInt256)) (ret := ⟨139⟩) (R := [sel])
    rd2033
    (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide])
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd139 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (approveReturnMem_mload64 (approveOwnerWord I) (approveSpenderWord I)
        (approveValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, erc20SubRet32_toNat]
        change (approveReturnMem (approveOwnerWord I) (approveSpenderWord I)
            (approveValueWord I)).readWithPadding 128 32 =
          UInt256.toByteArray (⟨1⟩ : UInt256)
        exact approveReturnMem_read128 (approveOwnerWord I) (approveSpenderWord I)
          (approveValueWord I))
      (by evm_ov) ]

/-! ## Decode-failure traces and top-level body theorem -/

theorem erc20ApproveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨k, C, rd⟩ := erc20ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1967⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨1966⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20ApproveX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨k, C, rd⟩ := erc20ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1967⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨1966⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20ApproveX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (approveSpenderWord I)
      (UInt256.land (approveSpenderWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc20ApproveX_dec1874_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.erc20DecodeAddrRevert rd hnc (by evm_ov)

theorem erc20ApproveSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc20Dispatch_approve {cd : ByteArray}
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some approveTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) :=
    (erc20ByteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [approveTransition, totalSupplyTransition, transferFromTransition, balanceOfTransition,
      transferTransition, allowanceTransition] cd = some approveTransition
  rw [dispatchList_cons, selectorOf, erc20ApproveSelectorBytes]
  rw [if_pos (by rw [hcd]; decide)]

theorem erc20ApproveBodyCore {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨100⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  have hsz4 := erc20ApproveSelector_size hsel
  have hd := erc20Dispatch_approve (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus
      · have hdec := erc20Decode_approve_ok (I := I) hsz68 hbig hcanonSpender
        have hbody := erc20ApproveBodyReturns
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
        exact (erc20X_approve (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hperm hcanonSpender hreach)
          |>.reEquivExecutionGen hcode hd hdec hbody
            (by
              simp [approvePostState, approveSlot, approveSlotI, initState,
                erc20StorageStore_createdAccounts, erc20StorageStore_accountMap])
            (returnEquiv_of_encode erc20BoolTrueReturnEncoding)
      · have hdec := erc20Decode_approve_none_noncanon (I := I) hsz68 hbig hcanonSpender
        have hnc : UInt256.eq (approveSpenderWord I)
            (UInt256.land (approveSpenderWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanonSpender (erc20Word_canonical_of_clean he))
        exact (erc20ApproveX_noncanon_spender (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc20Decode_approve_none_huge (I := I) hbigge
      exact (erc20ApproveX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := erc20Decode_approve_none_short (I := I) hsz4 hshort
    exact (erc20ApproveX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end ERC20
