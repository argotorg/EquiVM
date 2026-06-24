import Examples.OpenZeppelinBench.ERC6909.Storage
import Examples.OpenZeppelinBench.Pausable.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ABI decode and source-level body for `isOperator(address,address)` -/

/-- The raw ABI word for `isOperator`'s `owner` argument. -/
abbrev isOperatorOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `isOperator`'s `spender` argument. -/
abbrev isOperatorSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev isOperatorOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (isOperatorOwnerWord I).toNat)

abbrev isOperatorSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (isOperatorSpenderWord I).toNat)

abbrev isOperatorStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (isOperatorOwnerValue I)).insert "spender"
    (isOperatorSpenderValue I)

def isOperatorSlot (I : ExecutionEnv) : UInt256 :=
  operatorApprovalSlot
    (.address (AccountAddress.ofNat (isOperatorOwnerWord I).toNat))
    (.address (AccountAddress.ofNat (isOperatorSpenderWord I).toNat))

def isOperatorStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (isOperatorSlot I) ⟨0⟩)

abbrev isOperatorMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (isOperatorStorageWord σ I) ⟨255⟩

abbrev isOperatorReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (isOperatorMaskedWord σ I))

theorem erc6909Decode_isOperator_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (isOperatorSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (isOperatorTransition.params.map Param.name)
      (transitionSignature isOperatorTransition).paramTypes I.calldata =
        some (isOperatorStore I) := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = _
  simpa [isOperatorStore, isOperatorOwnerValue, isOperatorSpenderValue, isOperatorOwnerWord,
    isOperatorSpenderWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hcanonSpender

theorem erc6909Decode_isOperator_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (isOperatorTransition.params.map Param.name)
      (transitionSignature isOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "owner") (y := "spender") hsz4 hshort

theorem erc6909Decode_isOperator_none_noncanon_owner {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncOwner : ¬ (isOperatorOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (isOperatorTransition.params.map Param.name)
      (transitionSignature isOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, isOperatorOwnerWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") hsz68 hbig hncOwner

theorem erc6909Decode_isOperator_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hncSpender : ¬ (isOperatorSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (isOperatorTransition.params.map Param.name)
      (transitionSignature isOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, isOperatorOwnerWord, isOperatorSpenderWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hncSpender

theorem erc6909Decode_isOperator_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (isOperatorTransition.params.map Param.name)
      (transitionSignature isOperatorTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "owner") (y := "spender") hbig

theorem isOperatorStore_owner (I : ExecutionEnv) :
    (isOperatorStore I).get? "owner" = some (isOperatorOwnerValue I) := by
  rw [isOperatorStore, store_get_ne _ _ (by decide), store_get_self]

theorem isOperatorStore_spender (I : ExecutionEnv) :
    (isOperatorStore I).get? "spender" = some (isOperatorSpenderValue I) := by
  rw [isOperatorStore, store_get_self]

theorem isOperatorStore_owner_getElem? (I : ExecutionEnv) :
    (isOperatorStore I)["owner"]? = some (isOperatorOwnerValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, isOperatorStore_owner]

theorem isOperatorStore_spender_getElem? (I : ExecutionEnv) :
    (isOperatorStore I)["spender"]? = some (isOperatorSpenderValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, isOperatorStore_spender]

theorem isOperatorStore_operatorApprovals (I : ExecutionEnv) :
    (isOperatorStore I).get? "_operatorApprovals" = none := by
  rw [isOperatorStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_isOperator_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := isOperatorStore I } evm
      (.storage (operatorApprovalRef (.var "owner") (.var "spender"))) =
        .ok (wordToElem .bool
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (isOperatorSlot I)) ⟨255⟩)) := by
  have hgowner := isOperatorStore_owner_getElem? I
  have hgspender := isOperatorStore_spender_getElem? I
  have her : evalStorageRef config { contract := contract, locals := isOperatorStore I }
      evm (operatorApprovalRef (.var "owner") (.var "spender")) =
      .ok { base := "_operatorApprovals",
            steps := [.mindex (.address (AccountAddress.ofNat (isOperatorOwnerWord I).toNat)),
                      .mindex (.address (AccountAddress.ofNat (isOperatorSpenderWord I).toNat))] } := by
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, operatorApprovalRef,
      evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
      Std.HashMap.get?_eq_getElem?, hgowner, hgspender, isOperatorOwnerValue,
      isOperatorSpenderValue]
  have hty : storageTypeAt? contract.storage
      { base := "_operatorApprovals",
        steps := [.mindex (.address (AccountAddress.ofNat (isOperatorOwnerWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (isOperatorSpenderWord I).toNat))] } =
      some (.elem .bool) := by
    simp [storageTypeAt?, contract, storageDecls, boolSt, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "_operatorApprovals",
        steps := [.mindex (.address (AccountAddress.ofNat (isOperatorOwnerWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (isOperatorSpenderWord I).toNat))] } =
      fun _ => some (boolLoc (isOperatorSlot I)) := by
    simp [config, storageLayout, isOperatorSlot, operatorApprovalSlot]
  rw [evalExpr_storage_scalar (t := .bool)
    (hbase := isOperatorStore_operatorApprovals I)
    (her := her) (hty := hty) (hloc := hloc)]
  simpa [boolLoc, boolOffset0Loc] using storageLocLoad_bool_offset0 evm (isOperatorSlot I)

theorem erc6909IsOperatorBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (isOperatorStore I) isOperatorTransition.body
      (.returned { contract := contract, locals := isOperatorStore I } evm
        (some (wordToElem .bool
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (isOperatorSlot I)) ⟨255⟩)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simpa [operatorApprovalRef] using evalExpr_isOperator_storage evm I)

/-! ## EVM scratch memory for the `_operatorApprovals` nested mapping access -/

noncomputable def isOperatorOwnerMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32

noncomputable def isOperatorInnerHashMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (isOperatorOwnerMem owner) 32 32

noncomputable def isOperatorInnerSlot (owner : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((isOperatorInnerHashMem owner).readWithPadding 0 64)))

noncomputable def isOperatorSpenderMem (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray spender).write 0 (isOperatorInnerHashMem owner) 0 32

noncomputable def isOperatorOuterHashMem (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray (isOperatorInnerSlot owner)).write 0
    (isOperatorSpenderMem owner spender) 32 32

noncomputable def isOperatorReturnMem (owner spender val : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0
    (isOperatorOuterHashMem owner spender) 128 32

theorem isOperatorOwnerMem_size (owner : UInt256) :
    (isOperatorOwnerMem owner).size = 96 := by
  unfold isOperatorOwnerMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem isOperatorInnerHashMem_size (owner : UInt256) :
    (isOperatorInnerHashMem owner).size = 96 := by
  unfold isOperatorInnerHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [isOperatorOwnerMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, isOperatorOwnerMem_size, toByteArray_size]
  omega

theorem isOperatorSpenderMem_size (owner spender : UInt256) :
    (isOperatorSpenderMem owner spender).size = 96 := by
  unfold isOperatorSpenderMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [isOperatorInnerHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, isOperatorInnerHashMem_size, toByteArray_size]
  omega

theorem isOperatorOuterHashMem_size (owner spender : UInt256) :
    (isOperatorOuterHashMem owner spender).size = 96 := by
  unfold isOperatorOuterHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [isOperatorSpenderMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, isOperatorSpenderMem_size, toByteArray_size]
  omega

theorem isOperatorOwnerMem_read0 (owner : UInt256) :
    (isOperatorOwnerMem owner).readWithPadding 0 32 = UInt256.toByteArray owner := by
  unfold isOperatorOwnerMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray owner).size ≤ 32
    rw [toByteArray_size])

theorem isOperatorInnerHashMem_read0 (owner : UInt256) :
    (isOperatorInnerHashMem owner).readWithPadding 0 32 = UInt256.toByteArray owner := by
  unfold isOperatorInnerHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [isOperatorOwnerMem_size]; omega) (by omega),
    isOperatorOwnerMem_read0]

theorem isOperatorInnerHashMem_read32 (owner : UInt256) :
    (isOperatorInnerHashMem owner).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold isOperatorInnerHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [isOperatorOwnerMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem isOperatorInnerHashMem_read64 (owner : UInt256) :
    (isOperatorInnerHashMem owner).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold isOperatorInnerHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [isOperatorOwnerMem_size]; omega) (by omega)
      (by rw [isOperatorOwnerMem_size])]
  unfold isOperatorOwnerMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem isOperatorInnerHashMem_read0_64 (owner : UInt256) :
    (isOperatorInnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [isOperatorInnerHashMem_size]; omega)]
  have hleft :
      (isOperatorInnerHashMem owner).extract 0 32 = UInt256.toByteArray owner := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [isOperatorInnerHashMem_size]; omega),
      isOperatorInnerHashMem_read0]
  have hright :
      (isOperatorInnerHashMem owner).extract 32 64 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [isOperatorInnerHashMem_size]; omega),
      isOperatorInnerHashMem_read32]
  rw [show (isOperatorInnerHashMem owner).extract 0 64 =
      (isOperatorInnerHashMem owner).extract 0 32 ++
        (isOperatorInnerHashMem owner).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem isOperatorInnerKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus) :
    isOperatorInnerSlot (isOperatorOwnerWord I) =
      mapSlot (keyValueToWord (.address (AccountAddress.ofNat (isOperatorOwnerWord I).toNat))) ⟨1⟩ := by
  unfold isOperatorInnerSlot mapSlot
  rw [isOperatorInnerHashMem_read0_64]
  rw [keyValueToWord_address_of_canonical _ hcanonOwner]
  exact mappingSlot_single (isOperatorOwnerWord I) ⟨1⟩

theorem isOperatorSpenderMem_read0 (owner spender : UInt256) :
    (isOperatorSpenderMem owner spender).readWithPadding 0 32 =
      UInt256.toByteArray spender := by
  unfold isOperatorSpenderMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [isOperatorInnerHashMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray spender).size ≤ 32
    rw [toByteArray_size])

theorem isOperatorOuterHashMem_read0 (owner spender : UInt256) :
    (isOperatorOuterHashMem owner spender).readWithPadding 0 32 =
      UInt256.toByteArray spender := by
  unfold isOperatorOuterHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [isOperatorSpenderMem_size]; omega) (by omega),
    isOperatorSpenderMem_read0]

theorem isOperatorOuterHashMem_read32 (owner spender : UInt256) :
    (isOperatorOuterHashMem owner spender).readWithPadding 32 32 =
      UInt256.toByteArray (isOperatorInnerSlot owner) := by
  unfold isOperatorOuterHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [isOperatorSpenderMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (isOperatorInnerSlot owner)).size ≤ 32
    rw [toByteArray_size])

theorem isOperatorOuterHashMem_read64 (owner spender : UInt256) :
    (isOperatorOuterHashMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold isOperatorOuterHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [isOperatorSpenderMem_size]; omega)
      (by omega)
      (by rw [isOperatorSpenderMem_size])]
  unfold isOperatorSpenderMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [isOperatorInnerHashMem_size]; omega) (by omega)
      (by rw [isOperatorInnerHashMem_size]),
    isOperatorInnerHashMem_read64]

theorem isOperatorOuterHashMem_mload64 (owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (isOperatorOuterHashMem owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((isOperatorOuterHashMem owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [isOperatorOuterHashMem_size]; decide) (by decide)
    (isOperatorOuterHashMem_read64 owner spender)

theorem isOperatorOuterHashMem_read0_64 (owner spender : UInt256) :
    (isOperatorOuterHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (isOperatorInnerSlot owner) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [isOperatorOuterHashMem_size]; omega)]
  have hleft :
      (isOperatorOuterHashMem owner spender).extract 0 32 = UInt256.toByteArray spender := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [isOperatorOuterHashMem_size]; omega),
      isOperatorOuterHashMem_read0]
  have hright :
      (isOperatorOuterHashMem owner spender).extract 32 64 =
        UInt256.toByteArray (isOperatorInnerSlot owner) := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [isOperatorOuterHashMem_size]; omega),
      isOperatorOuterHashMem_read32]
  rw [show (isOperatorOuterHashMem owner spender).extract 0 64 =
      (isOperatorOuterHashMem owner spender).extract 0 32 ++
        (isOperatorOuterHashMem owner spender).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem isOperatorOuterKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (isOperatorSpenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((isOperatorOuterHashMem (isOperatorOwnerWord I) (isOperatorSpenderWord I))
          |>.readWithPadding 0 64)))
      = isOperatorSlot I := by
  rw [isOperatorOuterHashMem_read0_64, isOperatorInnerKeccakSlot I hcanonOwner]
  unfold isOperatorSlot operatorApprovalSlot mapSlot
  rw [keyValueToWord_address_of_canonical _ hcanonOwner,
    keyValueToWord_address_of_canonical _ hcanonSpender]
  exact mappingSlot_single (isOperatorSpenderWord I)
    (mapSlot (isOperatorOwnerWord I) ⟨1⟩)

theorem isOperatorReturnMem_size (owner spender val : UInt256) :
    (isOperatorReturnMem owner spender val).size = 160 := by
  unfold isOperatorReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [isOperatorOuterHashMem_size]; omega)
      (by rw [isOperatorOuterHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, isOperatorOuterHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem isOperatorReturnMem_read64 (owner spender val : UInt256) :
    (isOperatorReturnMem owner spender val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold isOperatorReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [isOperatorOuterHashMem_size]; omega)
      (by rw [isOperatorOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, isOperatorOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, isOperatorOuterHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [isOperatorOuterHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [isOperatorOuterHashMem_size]),
    isOperatorOuterHashMem_read64]

theorem isOperatorReturnMem_mload64 (owner spender val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (isOperatorReturnMem owner spender val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((isOperatorReturnMem owner spender val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [isOperatorReturnMem_size]; decide) (by decide)
    (isOperatorReturnMem_read64 owner spender val)

theorem isOperatorReturnMem_read128 (owner spender val : UInt256) :
    (isOperatorReturnMem owner spender val).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.isZero (UInt256.isZero val)) := by
  unfold isOperatorReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [isOperatorOuterHashMem_size]; omega)
      (by rw [isOperatorOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, isOperatorOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size])]
  rw [extract_append_right_window
      (isOperatorOuterHashMem owner spender ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (isOperatorOuterHashMem owner spender).size)))
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) 128 160 (by
        rw [ByteArray.size_append, isOperatorOuterHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, isOperatorOuterHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).size ≤ 32
    rw [toByteArray_size])

theorem erc6909BoolTrueReturnEncoding :
    encodeReturnValue? boolTy (.bool true) = some (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  simpa [boolTy] using boolTrueReturnEncoding

theorem erc6909BoolReturnEncoding (w : UInt256) :
    encodeReturnValue? boolTy (wordToElem .bool (UInt256.land w ⟨255⟩)) =
      some (UInt256.toByteArray
        (UInt256.isZero (UInt256.isZero (UInt256.land w ⟨255⟩)))) := by
  by_cases hval : (UInt256.land w ⟨255⟩).val = 0
  · have hz : UInt256.land w ⟨255⟩ = ⟨0⟩ := by
      apply u256_inj
      exact congrArg Fin.val hval
    have hnorm : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by decide
    simpa [boolTy, wordToElem, hz, hnorm] using boolFalseReturnEncoding
  · have hz : UInt256.land w ⟨255⟩ ≠ ⟨0⟩ := by
      intro hx
      apply hval
      rw [hx]
    have hiz : UInt256.isZero (UInt256.land w ⟨255⟩) = ⟨0⟩ := isZero_eq_zero_of_ne hz
    have hnorm : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by decide
    simpa [wordToElem, hval, hiz, hnorm] using erc6909BoolTrueReturnEncoding

/-! ## EVM trace for `isOperator(address,address)` -/


theorem erc6909IsOperatorX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1905⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨343⟩, ⟨193⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨193⟩, push2 ⟨343⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1905⟩, jump (by jump_dest) ]⟩

theorem erc6909IsOperatorX_dec1629_owner {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
        [⟨4⟩, ⟨1931⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨343⟩,
          ⟨193⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1922⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1931⟩, dup4, push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909IsOperatorX_dec1931 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1931⟩
        [isOperatorOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨343⟩, ⟨193⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_dec1629_owner (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact erc6909DecodeAddrOk rd hcanonOwner (by jump_dest) (by evm_ov)

theorem erc6909IsOperatorX_dec1629_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
        [⟨4⟩ + ⟨32⟩, ⟨1945⟩, ⟨0⟩, isOperatorOwnerWord I, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨343⟩, ⟨193⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_dec1931 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap2, pop, push2 ⟨1945⟩, push1 ⟨32⟩, dup5, add,
    push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909IsOperatorX_dec1945 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (isOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1945⟩
        [isOperatorSpenderWord I, ⟨0⟩, isOperatorOwnerWord I, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨343⟩, ⟨193⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_dec1629_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact erc6909DecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem erc6909IsOperatorX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (isOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨343⟩
        [isOperatorSpenderWord I, isOperatorOwnerWord I, ⟨193⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_dec1945 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap1, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest) ]⟩

theorem erc6909X_isOperator {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (isOperatorSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (isOperatorReturnWord σ I)) := by
  obtain ⟨_, _, rd343⟩ := erc6909IsOperatorX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hcanonSpender hreach
  have hslot := isOperatorOuterKeccakSlot I hcanonOwner hcanonSpender
  have rd373 := evm_run rd343 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap2, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (isOperatorOwnerMem (isOperatorOwnerWord I)) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonOwner]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (isOperatorInnerHashMem (isOperatorOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (isOperatorInnerSlot (isOperatorOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap4, swap1 ]
  have rd374 := RD.swap5 rd373 (by decide) (by evm_ov)
  have rd382 := evm_run rd374 with [
    and, dup3,
    raw mstore 0 (isOperatorSpenderMem (isOperatorOwnerWord I) (isOperatorSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonSpender]
        rfl)
      (by decide) (by evm_ov),
    swap2, swap1, swap2,
    raw mstore 0 (isOperatorOuterHashMem (isOperatorOwnerWord I) (isOperatorSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw keccak256 0 (isOperatorSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd383⟩ := rd382.sload (by decide) (by evm_ov)
  have rd193 := evm_run rd383 with [
    push1 ⟨255⟩, and, swap1, jump (by jump_dest) ]
  have hmaskComm : UInt256.land ⟨255⟩ (isOperatorStorageWord σ I) =
      UInt256.land (isOperatorStorageWord σ I) ⟨255⟩ := by
    exact Reasoning.Theory.u256_land_comm ⟨255⟩ (isOperatorStorageWord σ I)
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (isOperatorOuterHashMem_mload64 (isOperatorOwnerWord I) (isOperatorSpenderWord I))
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (isOperatorReturnMem (isOperatorOwnerWord I) (isOperatorSpenderWord I)
        (isOperatorMaskedWord σ I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        unfold isOperatorReturnMem isOperatorMaskedWord
        rw [← hmaskComm]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  simpa [isOperatorReturnWord, isOperatorMaskedWord, hmaskComm] using
    (evm_run rd165 with [
      jumpdest, push1 ⟨64⟩,
      raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
        mem_cost
        (isOperatorReturnMem_mload64 (isOperatorOwnerWord I) (isOperatorSpenderWord I)
          (isOperatorMaskedWord σ I))
        (by decide) (by evm_ov),
      dup1, swap2, sub, swap1,
      raw ret 0 (UInt256.toByteArray (isOperatorReturnWord σ I)) (by decide)
        mem_cost
        (by
          rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
          change (isOperatorReturnMem (isOperatorOwnerWord I) (isOperatorSpenderWord I)
              (isOperatorMaskedWord σ I)).readWithPadding 128 32 =
            UInt256.toByteArray (isOperatorReturnWord σ I)
          rw [isOperatorReturnWord]
          exact isOperatorReturnMem_read128 (isOperatorOwnerWord I) (isOperatorSpenderWord I)
            (isOperatorMaskedWord σ I))
        (by evm_ov) ])

/-! ## Decode-failure traces and top-level body theorem -/

theorem erc6909IsOperatorX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1922⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909IsOperatorX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1922⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909IsOperatorX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (isOperatorOwnerWord I)
      (UInt256.land (isOperatorOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_dec1629_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  simpa [isOperatorOwnerWord] using erc6909DecodeAddrRevert rd hnc (by evm_ov)

theorem erc6909IsOperatorX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (isOperatorSpenderWord I)
      (UInt256.land (isOperatorSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc6909IsOperatorX_dec1629_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  simpa [isOperatorSpenderWord] using erc6909DecodeAddrRevert rd hnc (by evm_ov)

theorem erc6909IsOperatorSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xb6, 0x36, 0x3c, 0xf2]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xb6, 0x36, 0x3c, 0xf2]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_isOperator {cd : ByteArray}
    (hsel : ((⟨#[0xb6, 0x36, 0x3c, 0xf2]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some isOperatorTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xb6, 0x36, 0x3c, 0xf2]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition])
    (post := [setOperatorTransition, supportsInterfaceTransition, transferTransition,
      transferFromTransition])
    rfl ?_ (by rw [selectorOf, erc6909IsOperatorSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909BalanceOfSelectorBytes, hcd]; decide

theorem erc6909IsOperatorBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0xb6, 0x36, 0x3c, 0xf2]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true)
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨329⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc6909IsOperatorSelector_size hsel
  have hd := erc6909Dispatch_isOperator (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonOwner : (isOperatorOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcanonSpender : (isOperatorSpenderWord I).toNat < EVM.addressModulus
        · have hdec := erc6909Decode_isOperator_ok (I := I) hsz68 hbig
            hcanonOwner hcanonSpender
          have hword : isOperatorStorageWord σ_evm I = isOperatorStorageWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (isOperatorSlot I) ⟨0⟩
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (isOperatorStore I)
                isOperatorTransition.body
                (.returned { contract := contract, locals := isOperatorStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some (wordToElem .bool
                    (UInt256.land (isOperatorStorageWord σ_solm I) ⟨255⟩)))) := by
            simpa [isOperatorStorageWord, isOperatorSlot, initState, Solm.EVM.storageLoad,
              State.lookupAccount] using erc6909IsOperatorBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
          exact (erc6909X_isOperator (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonOwner hcanonSpender hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword])
              hAccounts
              (returnEquiv_of_encode (erc6909BoolReturnEncoding (isOperatorStorageWord σ_evm I)))
        · have hdec := erc6909Decode_isOperator_none_noncanon_spender
            (I := I) hsz68 hbig hcanonOwner hcanonSpender
          have hnc : UInt256.eq (isOperatorSpenderWord I)
              (UInt256.land (isOperatorSpenderWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne (fun he => hcanonSpender (solcAddrCanonical_of_clean he))
          exact (erc6909IsOperatorX_noncanon_spender (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonOwner hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc6909Decode_isOperator_none_noncanon_owner (I := I)
          hsz68 hbig hcanonOwner
        have hnc : UInt256.eq (isOperatorOwnerWord I)
            (UInt256.land (isOperatorOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonOwner (solcAddrCanonical_of_clean he))
        exact (erc6909IsOperatorX_noncanon_owner (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_isOperator_none_huge (I := I) hbigge
      exact (erc6909IsOperatorX_hugearg (g := Sat256.ofUInt256 g)
          hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := erc6909Decode_isOperator_none_short (I := I) hsz4 hshort
    exact (erc6909IsOperatorX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
