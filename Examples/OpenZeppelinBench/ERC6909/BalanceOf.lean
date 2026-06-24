import Examples.OpenZeppelinBench.ERC6909.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ABI decode and source-level body for `balanceOf(address,uint256)` -/

/-- The raw ABI word for `balanceOf`'s `owner` argument. -/
abbrev balanceOfOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- The raw ABI word for `balanceOf`'s `id` argument. -/
abbrev balanceOfIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev balanceOfOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)

abbrev balanceOfIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (balanceOfIdWord I).toNat)

abbrev balanceOfStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (balanceOfOwnerValue I)).insert "id" (balanceOfIdValue I)

def balanceOfSlot (I : ExecutionEnv) : UInt256 :=
  balanceSlot
    (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat))
    (.int (Int.ofNat (balanceOfIdWord I).toNat))

def balanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (balanceOfSlot I) ⟨0⟩)

theorem erc6909BalanceOfSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x00, 0xfd, 0xd5, 0x8e]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x00, 0xfd, 0xd5, 0x8e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_balanceOf {cd : ByteArray}
    (hsel : ((⟨#[0x00, 0xfd, 0xd5, 0x8e]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some balanceOfTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x00, 0xfd, 0xd5, 0x8e]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition])
    (post := [isOperatorTransition, setOperatorTransition, supportsInterfaceTransition,
      transferTransition, transferFromTransition])
    rfl ?_ (by rw [selectorOf, erc6909BalanceOfSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]; decide
  · rw [selectorOf, erc6909ApproveSelectorBytes, hcd]; decide

theorem erc6909Decode_balanceOf_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = some (balanceOfStore I) := by
  show decodeCalldata ["owner", "id"] [addr, uint256] I.calldata = some (balanceOfStore I)
  simpa [addr, uint256, abiUInt256, balanceOfStore, balanceOfOwnerValue, balanceOfIdValue,
    balanceOfOwnerWord, balanceOfIdWord]
    using decodeCalldata_addr_uint256_ok (cd := I.calldata) (x := "owner") (y := "id")
      hsz68 hbig hcanon

theorem erc6909Decode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "id"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_addr_uint256_none_short (cd := I.calldata) (x := "owner") (y := "id")
      hsz4 hshort

theorem erc6909Decode_balanceOf_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "id"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, balanceOfOwnerWord] using
    decodeCalldata_addr_uint256_none_noncanon (cd := I.calldata) (x := "owner") (y := "id")
      hsz68 hbig hnc

theorem erc6909Decode_balanceOf_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "id"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_addr_uint256_none_huge (cd := I.calldata) (x := "owner") (y := "id") hbig

theorem balanceOfStore_owner (I : ExecutionEnv) :
    (balanceOfStore I).get? "owner" = some (balanceOfOwnerValue I) := by
  rw [balanceOfStore, store_get_ne _ _ (by decide), store_get_self]

theorem balanceOfStore_id (I : ExecutionEnv) :
    (balanceOfStore I).get? "id" = some (balanceOfIdValue I) := by
  rw [balanceOfStore, store_get_self]

theorem balanceOfStore_owner_getElem? (I : ExecutionEnv) :
    (balanceOfStore I)["owner"]? = some (balanceOfOwnerValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, balanceOfStore_owner]

theorem balanceOfStore_id_getElem? (I : ExecutionEnv) :
    (balanceOfStore I)["id"]? = some (balanceOfIdValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, balanceOfStore_id]

theorem evalExpr_balanceOf_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := balanceOfStore I } evm
      (.var "owner") = .ok (balanceOfOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [balanceOfStore_owner]

theorem evalExpr_balanceOf_id (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := balanceOfStore I } evm
      (.var "id") = .ok (balanceOfIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [balanceOfStore_id]

def balanceOfEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_balances",
    steps := [.mindex (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)),
      .mindex (.int (Int.ofNat (balanceOfIdWord I).toNat))] }

theorem evalStorageRef_balanceOf_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := balanceOfStore I } evm
      (balanceRef (.var "owner") (.var "id")) = .ok (balanceOfEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, balanceRef, balanceOfEvaledRef,
    evalExpr_balanceOf_owner, evalExpr_balanceOf_id, balanceOfOwnerValue, balanceOfIdValue,
    valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem erc6909BalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (balanceOfStore I) balanceOfTransition.body
      (.returned { contract := contract, locals := balanceOfStore I } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (balanceOfSlot I)).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (loc := wordLoc (balanceOfSlot I))
        (hbase := by simp [balanceOfStore, balanceRef])
        (her := evalStorageRef_balanceOf_balance evm I)
        (hty := by
          simp [storageTypeAt?, balanceOfEvaledRef, contract, storageDecls, uint256St,
            storageTypeStep?])
        (hloc := by
          simp [config, storageLayout, balanceOfEvaledRef, balanceOfSlot])]
      rw [erc6909StorageLocLoad_uint256])

/-! ## EVM scratch memory for the nested `_balances[owner][id]` access -/

theorem balanceOfKeyValueToWord_address_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) = w :=
  keyValueToWord_address_of_canonical w hcanon

theorem balanceOfKeyValueToWord_uint256 (w : UInt256) :
    keyValueToWord (.int (Int.ofNat w.toNat)) = w := by
  exact erc6909WordOfInt_ofNat_toNat w

/-- Memory after the body stores the masked owner key at scratch offset `0x00`. -/
noncomputable def balanceOfOwnerMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray (UInt256.land owner solcAddrMask)).write 0 solcFreePtrMem 0 32

/-- Memory after the body stores `_balances`' base slot `0` at scratch offset `0x20`. -/
noncomputable def balanceOfInnerHashMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0 (balanceOfOwnerMem owner) 32 32

/-- The first keccak slot, Solidity's base for `_balances[owner]`. -/
noncomputable def balanceOfInnerSlot (owner : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((balanceOfInnerHashMem owner).readWithPadding 0 64)))

/-- Memory after the body stores the `id` key at scratch offset `0x00`. -/
noncomputable def balanceOfOuterIdMem (owner id : UInt256) : ByteArray :=
  (UInt256.toByteArray id).write 0 (balanceOfInnerHashMem owner) 0 32

/-- Memory after the body stores the inner mapping slot at scratch offset `0x20`. -/
noncomputable def balanceOfOuterHashMem (owner id : UInt256) : ByteArray :=
  (UInt256.toByteArray (balanceOfInnerSlot owner)).write 0 (balanceOfOuterIdMem owner id) 32 32

theorem balanceOfOwnerMem_size (owner : UInt256) : (balanceOfOwnerMem owner).size = 96 := by
  unfold balanceOfOwnerMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem balanceOfInnerHashMem_size (owner : UInt256) :
    (balanceOfInnerHashMem owner).size = 96 := by
  unfold balanceOfInnerHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [balanceOfOwnerMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, balanceOfOwnerMem_size, toByteArray_size]
  omega

theorem balanceOfOuterIdMem_size (owner id : UInt256) :
    (balanceOfOuterIdMem owner id).size = 96 := by
  unfold balanceOfOuterIdMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [balanceOfInnerHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, balanceOfInnerHashMem_size, toByteArray_size]
  omega

theorem balanceOfOuterHashMem_size (owner id : UInt256) :
    (balanceOfOuterHashMem owner id).size = 96 := by
  unfold balanceOfOuterHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [balanceOfOuterIdMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, balanceOfOuterIdMem_size, toByteArray_size]
  omega

theorem balanceOfOwnerMem_read0 (owner : UInt256) :
    (balanceOfOwnerMem owner).readWithPadding 0 32 =
      UInt256.toByteArray (UInt256.land owner solcAddrMask) := by
  unfold balanceOfOwnerMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (UInt256.land owner solcAddrMask)).size ≤ 32
    rw [toByteArray_size])

theorem balanceOfOwnerMem_read64 (owner : UInt256) :
    (balanceOfOwnerMem owner).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfOwnerMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega) (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem balanceOfInnerHashMem_read0 (owner : UInt256) :
    (balanceOfInnerHashMem owner).readWithPadding 0 32 =
      UInt256.toByteArray (UInt256.land owner solcAddrMask) := by
  unfold balanceOfInnerHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [balanceOfOwnerMem_size]; omega) (by omega),
    balanceOfOwnerMem_read0]

theorem balanceOfInnerHashMem_read32 (owner : UInt256) :
    (balanceOfInnerHashMem owner).readWithPadding 32 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfInnerHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [balanceOfOwnerMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨0⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem balanceOfInnerHashMem_read64 (owner : UInt256) :
    (balanceOfInnerHashMem owner).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfInnerHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [balanceOfOwnerMem_size]; omega) (by omega) (by rw [balanceOfOwnerMem_size]),
    balanceOfOwnerMem_read64]

set_option maxHeartbeats 800000 in
theorem balanceOfInnerHashMem_read0_64 (owner : UInt256) :
    (balanceOfInnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray (UInt256.land owner solcAddrMask) ++
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [balanceOfInnerHashMem_size]; omega)]
  have hleft :
      (balanceOfInnerHashMem owner).extract 0 32 =
        UInt256.toByteArray (UInt256.land owner solcAddrMask) := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [balanceOfInnerHashMem_size]; omega),
      balanceOfInnerHashMem_read0]
  have hright :
      (balanceOfInnerHashMem owner).extract 32 64 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [balanceOfInnerHashMem_size]; omega),
      balanceOfInnerHashMem_read32]
  rw [show (balanceOfInnerHashMem owner).extract 0 64 =
      (balanceOfInnerHashMem owner).extract 0 32 ++
        (balanceOfInnerHashMem owner).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem balanceOfInnerKeccakSlot (I : ExecutionEnv)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    balanceOfInnerSlot (balanceOfOwnerWord I) =
      mapSlot (keyValueToWord
        (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat))) ⟨0⟩ := by
  unfold balanceOfInnerSlot mapSlot
  rw [balanceOfInnerHashMem_read0_64, solcAddrMask_clean hcanon]
  rw [balanceOfKeyValueToWord_address_of_canonical _ hcanon]
  exact mappingSlot_single (balanceOfOwnerWord I) ⟨0⟩

theorem balanceOfOuterIdMem_read0 (owner id : UInt256) :
    (balanceOfOuterIdMem owner id).readWithPadding 0 32 = UInt256.toByteArray id := by
  unfold balanceOfOuterIdMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfInnerHashMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray id).size ≤ 32
    rw [toByteArray_size])

theorem balanceOfOuterIdMem_read64 (owner id : UInt256) :
    (balanceOfOuterIdMem owner id).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfOuterIdMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [balanceOfInnerHashMem_size]; omega) (by omega)
      (by rw [balanceOfInnerHashMem_size]),
    balanceOfInnerHashMem_read64]

theorem balanceOfOuterHashMem_read0 (owner id : UInt256) :
    (balanceOfOuterHashMem owner id).readWithPadding 0 32 = UInt256.toByteArray id := by
  unfold balanceOfOuterHashMem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [balanceOfOuterIdMem_size]; omega) (by omega),
    balanceOfOuterIdMem_read0]

theorem balanceOfOuterHashMem_read32 (owner id : UInt256) :
    (balanceOfOuterHashMem owner id).readWithPadding 32 32 =
      UInt256.toByteArray (balanceOfInnerSlot owner) := by
  unfold balanceOfOuterHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfOuterIdMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (balanceOfInnerSlot owner)).size ≤ 32
    rw [toByteArray_size])

theorem balanceOfOuterHashMem_read64 (owner id : UInt256) :
    (balanceOfOuterHashMem owner id).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfOuterHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [balanceOfOuterIdMem_size]; omega) (by omega) (by rw [balanceOfOuterIdMem_size]),
    balanceOfOuterIdMem_read64]

theorem balanceOfOuterHashMem_mload64 (owner id : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfOuterHashMem owner id).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfOuterHashMem owner id).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [balanceOfOuterHashMem_size]; decide) (by decide)
    (balanceOfOuterHashMem_read64 owner id)

set_option maxHeartbeats 800000 in
theorem balanceOfOuterHashMem_read0_64 (owner id : UInt256) :
    (balanceOfOuterHashMem owner id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (balanceOfInnerSlot owner) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [balanceOfOuterHashMem_size]; omega)]
  have hleft :
      (balanceOfOuterHashMem owner id).extract 0 32 = UInt256.toByteArray id := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [balanceOfOuterHashMem_size]; omega),
      balanceOfOuterHashMem_read0]
  have hright :
      (balanceOfOuterHashMem owner id).extract 32 64 =
        UInt256.toByteArray (balanceOfInnerSlot owner) := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [balanceOfOuterHashMem_size]; omega),
      balanceOfOuterHashMem_read32]
  rw [show (balanceOfOuterHashMem owner id).extract 0 64 =
      (balanceOfOuterHashMem owner id).extract 0 32 ++
        (balanceOfOuterHashMem owner id).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem balanceOfOuterKeccakSlot (I : ExecutionEnv)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((balanceOfOuterHashMem (balanceOfOwnerWord I) (balanceOfIdWord I))
          |>.readWithPadding 0 64)))
      = balanceOfSlot I := by
  rw [balanceOfOuterHashMem_read0_64, balanceOfInnerKeccakSlot I hcanon]
  unfold balanceOfSlot balanceSlot mapSlot
  rw [balanceOfKeyValueToWord_address_of_canonical _ hcanon, balanceOfKeyValueToWord_uint256]
  exact mappingSlot_single (balanceOfIdWord I)
    (uInt256OfByteArray (ffi.KEC ((balanceOfOwnerWord I).toByteArray ++
      (⟨0⟩ : UInt256).toByteArray)))

/-- Memory after the shared uint256 return tail writes the loaded balance at `0x80`. -/
noncomputable def balanceOfReturnMem (owner id val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (balanceOfOuterHashMem owner id) 128 32

theorem balanceOfReturnMem_size (owner id val : UInt256) :
    (balanceOfReturnMem owner id val).size = 160 := by
  unfold balanceOfReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfOuterHashMem_size]; omega)
      (by rw [balanceOfOuterHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, balanceOfOuterHashMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem balanceOfReturnMem_read64 (owner id val : UInt256) :
    (balanceOfReturnMem owner id val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfOuterHashMem_size]; omega)
      (by rw [balanceOfOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, balanceOfOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, balanceOfOuterHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [balanceOfOuterHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [balanceOfOuterHashMem_size]),
    balanceOfOuterHashMem_read64]

theorem balanceOfReturnMem_mload64 (owner id val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfReturnMem owner id val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfReturnMem owner id val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [balanceOfReturnMem_size]; decide) (by decide)
    (balanceOfReturnMem_read64 owner id val)

theorem balanceOfReturnMem_read128 (owner id val : UInt256) :
    (balanceOfReturnMem owner id val).readWithPadding 128 32 = UInt256.toByteArray val := by
  unfold balanceOfReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfOuterHashMem_size]; omega)
      (by rw [balanceOfOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, balanceOfOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size])]
  rw [extract_append_right_window
      (balanceOfOuterHashMem owner id ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (balanceOfOuterHashMem owner id).size)))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, balanceOfOuterHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, balanceOfOuterHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

end OpenZeppelinBench.ERC6909

namespace Reasoning.Reach

open OpenZeppelinBench.ERC6909

-- PROMOTE -> Common.lean / Reasoning.Stepping
theorem erc6909BalanceOfSwap5_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP5, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t)
    (hov : t.length + 6 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (f :: b :: c :: d :: e :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP5, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap5 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 6 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Common.lean / Reasoning.Reach
theorem RD.erc6909BalanceOfSwap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909BalanceOfSwap5_xstep hc hp hdec hs hov)

-- PROMOTE -> Common.lean
-- GENERALIZES `Examples.ERC20.Common.RD.erc20DecodeAddrOk`: same solc address decoder shape with
-- ERC6909's optimizer-on inlined mask/check routine at pc 1629.
set_option maxHeartbeats 400000 in
theorem RD.erc6909BalanceOfDecodeAddrOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨1629⟩ (off :: ret :: R) mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat <
      EVM.addressModulus)
    (hret : (D_J erc6909BenchBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD erc6909BenchBytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R) mem aw rdata acc k' C' := by
  have hclean : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        solcAddrMask) = ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  exact ⟨_, _, evm_run h with [
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1651⟩,
    jumpiT (by rw [hmask, hclean]; decide) (by jump_dest),
    jumpdest, swap2, swap1, pop, jump hret ]⟩

-- PROMOTE -> Common.lean
set_option maxHeartbeats 400000 in
theorem RD.erc6909BalanceOfDecodeAddrRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨1629⟩ (off :: ret :: R) mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) solcAddrMask) =
        ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev erc6909BenchBytecode g s0 := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  exact (evm_run h with [
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1651⟩, jumpiNT (by rw [hmask, hnc]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ] :
    RDrev erc6909BenchBytecode g s0)

end Reasoning.Reach

namespace OpenZeppelinBench.ERC6909

/-! ## EVM trace for `balanceOf(address,uint256)` -/

theorem erc6909BalanceOfX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1656⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨150⟩, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨155⟩, push2 ⟨150⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1656⟩, jump (by jump_dest) ]⟩

theorem erc6909BalanceOfX_dec1629_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
      [⟨4⟩, ⟨1682⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨150⟩,
        ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨k, C, rd⟩ := erc6909BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1673⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1682⟩, dup4, push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909BalanceOfX_dec1682 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1682⟩
      [balanceOfOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨150⟩, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909BalanceOfX_dec1629_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  simpa [balanceOfOwnerWord, calldataWord] using
    RD.erc6909BalanceOfDecodeAddrOk rd hcanon (by jump_dest) (by evm_ov)

theorem erc6909BalanceOfX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨407⟩
      [balanceOfIdWord I, balanceOfOwnerWord I, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909BalanceOfX_dec1682 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanon hreach
  have rd1683 := evm_run rd with [jumpdest]
  have rd1684 := RD.erc6909BalanceOfSwap5 rd1683 (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [balanceOfIdWord, calldataWord] using evm_run rd1684 with [
      push1 ⟨32⟩, swap4, swap1, swap4, add, calldataload,
      swap4, pop, pop, pop, jump (by jump_dest),
      jumpdest, push2 ⟨407⟩, jump (by jump_dest) ]⟩

theorem erc6909X_balanceOf {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (balanceOfWord σ I)) := by
  obtain ⟨_, _, rd407⟩ := erc6909BalanceOfX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanon hreach
  have hslot := balanceOfOuterKeccakSlot I hcanon
  have rd440 := evm_run rd407 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push0, swap1, dup2,
    raw mstore 0 (balanceOfOwnerMem (balanceOfOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (balanceOfInnerHashMem (balanceOfOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (balanceOfInnerSlot (balanceOfOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup5, dup5,
    raw mstore 0 (balanceOfOuterIdMem (balanceOfOwnerWord I) (balanceOfIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (balanceOfOuterHashMem (balanceOfOwnerWord I) (balanceOfIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap1,
    raw keccak256 0 (balanceOfSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd441⟩ := rd440.sload (by decide) (by evm_ov)
  have rd155 := evm_run rd441 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd155 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfOuterHashMem_mload64 (balanceOfOwnerWord I) (balanceOfIdWord I))
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6
      (balanceOfReturnMem (balanceOfOwnerWord I) (balanceOfIdWord I) (balanceOfWord σ I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (balanceOfOwnerWord I) (balanceOfIdWord I)
        (balanceOfWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (balanceOfWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
          from by decide]
        change (balanceOfReturnMem (balanceOfOwnerWord I) (balanceOfIdWord I)
            (balanceOfWord σ I)).readWithPadding 128 32 =
          UInt256.toByteArray (balanceOfWord σ I)
        exact balanceOfReturnMem_read128 (balanceOfOwnerWord I) (balanceOfIdWord I)
          (balanceOfWord σ I))
      (by evm_ov) ]

/-! ## Decode-failure traces and top-level body theorem -/

theorem erc6909BalanceOfX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨k, C, rd⟩ := erc6909BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1673⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909BalanceOfX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (_hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨k, C, rd⟩ := erc6909BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1673⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909BalanceOfX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (balanceOfOwnerWord I)
      (UInt256.land (balanceOfOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc6909BalanceOfX_dec1629_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  simpa [balanceOfOwnerWord, calldataWord] using
    RD.erc6909BalanceOfDecodeAddrRevert rd hnc (by evm_ov)

theorem erc6909BalanceOfBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x00, 0xfd, 0xd5, 0x8e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true)
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨136⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc6909BalanceOfSelector_size hsel
  have hd := erc6909Dispatch_balanceOf (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus
      · have hdec := erc6909Decode_balanceOf_ok (I := I) hsz68 hbig hcanon
        have hword : balanceOfWord σ_evm I = balanceOfWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (balanceOfSlot I) ⟨0⟩
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (balanceOfStore I)
              balanceOfTransition.body
              (.returned { contract := contract, locals := balanceOfStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (some (.int (Int.ofNat (balanceOfWord σ_solm I).toNat)))) := by
          simpa [balanceOfWord, balanceOfSlot, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using erc6909BalanceOfBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
        exact (erc6909X_balanceOf (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hcanon hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [← hword])
            hAccounts
            (returnEquiv_of_encode (by
              simpa [uint256] using uint256ReturnEncoding (balanceOfWord σ_evm I)))
      · have hdec := erc6909Decode_balanceOf_none_noncanon (I := I) hsz68 hbig hcanon
        have hnc : UInt256.eq (balanceOfOwnerWord I)
            (UInt256.land (balanceOfOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (erc6909BalanceOfX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_balanceOf_none_huge (I := I) hbigge
      exact (erc6909BalanceOfX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := erc6909Decode_balanceOf_none_short (I := I) hsz4 hshort
    exact (erc6909BalanceOfX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
