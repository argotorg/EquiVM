import Examples.OpenZeppelinBench.ERC6909.Storage
import Examples.ERC20.TransferFrom
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ABI decode and source-level body for `allowance(address,address,uint256)` -/

/-- The raw ABI word for `allowance`'s `owner` argument. -/
abbrev allowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- The raw ABI word for `allowance`'s `spender` argument. -/
abbrev allowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

/-- The raw ABI word for `allowance`'s `id` argument. -/
abbrev allowanceIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev allowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (allowanceIdWord I).toNat)

abbrev allowanceStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "owner" (allowanceOwnerValue I)).insert "spender"
    (allowanceSpenderValue I)).insert "id" (allowanceIdValue I)

def allowanceSlotI (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat))
    (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))
    (.int (Int.ofNat (allowanceIdWord I).toNat))

def allowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (allowanceSlotI I) ⟨0⟩)

-- PROMOTE -> Common.lean
-- Generalization candidate: this reuses the ERC20 `(address,address,uint256)` calldata decoder.
theorem erc6909Decode_allowance_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = some (allowanceStore I) := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = _
  simpa [allowanceStore, allowanceOwnerValue, allowanceSpenderValue, allowanceIdValue,
    allowanceOwnerWord, allowanceSpenderWord, allowanceIdWord, calldataWord, addr, uint256,
    ERC20.addr, ERC20.uint256]
    using ERC20.decodeCalldata_address_address_uint256_ok
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id")
      hsz100 hbig hcanonOwner hcanonSpender

-- PROMOTE -> Common.lean
theorem erc6909Decode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, ERC20.addr, ERC20.uint256] using
    ERC20.decodeCalldata_address_address_uint256_none_short
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id") hsz4 hshort

-- PROMOTE -> Common.lean
theorem erc6909Decode_allowance_none_noncanon_owner {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncOwner : ¬ (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = none
  simpa [allowanceOwnerWord, calldataWord, addr, uint256, ERC20.addr, ERC20.uint256] using
    ERC20.decodeCalldata_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id")
      hsz100 hbig hncOwner

-- PROMOTE -> Common.lean
theorem erc6909Decode_allowance_none_noncanon_spender {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hncSpender : ¬ (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = none
  simpa [allowanceOwnerWord, allowanceSpenderWord, calldataWord, addr, uint256,
    ERC20.addr, ERC20.uint256] using
    ERC20.decodeCalldata_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id")
      hsz100 hbig hcanonOwner hncSpender

-- PROMOTE -> Common.lean
theorem erc6909Decode_allowance_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, ERC20.addr, ERC20.uint256] using
    ERC20.decodeCalldata_address_address_uint256_none_huge
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id") hbig

theorem allowanceStore_owner (I : ExecutionEnv) :
    (allowanceStore I).get? "owner" = some (allowanceOwnerValue I) := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem allowanceStore_spender (I : ExecutionEnv) :
    (allowanceStore I).get? "spender" = some (allowanceSpenderValue I) := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_self]

theorem allowanceStore_id (I : ExecutionEnv) :
    (allowanceStore I).get? "id" = some (allowanceIdValue I) := by
  rw [allowanceStore, store_get_self]

theorem allowanceStore_owner_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["owner"]? = some (allowanceOwnerValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_owner]

theorem allowanceStore_spender_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["spender"]? = some (allowanceSpenderValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_spender]

theorem allowanceStore_id_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["id"]? = some (allowanceIdValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_id]

theorem allowanceStore_allowances (I : ExecutionEnv) :
    (allowanceStore I).get? "_allowances" = none := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

def allowanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_allowances",
    steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
      .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)),
      .mindex (.int (Int.ofNat (allowanceIdWord I).toNat))] }

theorem evalStorageRef_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := allowanceStore I } evm
      (allowanceRef (.var "owner") (.var "spender") (.var "id")) =
        EvalResult.ok (allowanceEvaledRef I) := by
  have hgowner := allowanceStore_owner_getElem? I
  have hgspender := allowanceStore_spender_getElem? I
  have hgid := allowanceStore_id_getElem? I
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef,
    allowanceEvaledRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, Std.HashMap.get?_eq_getElem?, hgowner, hgspender, hgid, allowanceOwnerValue,
    allowanceSpenderValue, allowanceIdValue]

theorem evalExpr_allowance_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := allowanceStore I } evm
      (.storage (allowanceRef (.var "owner") (.var "spender") (.var "id"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlotI I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (hbase := by simp [allowanceRef])
    (her := evalStorageRef_allowance evm I)
    (hty := by
      simp [storageTypeAt?, allowanceEvaledRef, contract, storageDecls, uint256St,
        storageTypeStep?])
    (hloc := by
      show config.storage.layout (allowanceEvaledRef I) =
        fun _ => some (wordLoc (allowanceSlotI I))
      simp [config, storageLayout, allowanceEvaledRef, allowanceSlotI])]
  rw [erc6909StorageLocLoad_uint256]

theorem erc6909AllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (allowanceStore I) allowanceTransition.body
      (.returned { contract := contract, locals := allowanceStore I } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlotI I)).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simpa [allowanceRef] using evalExpr_allowance_storage evm I)

/-! ## EVM scratch memory for the three-level `_allowances` mapping access -/

noncomputable def wordAt0Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 0 32

noncomputable def wordAt32Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 32 32

noncomputable def twoWordHashMem (key slot : UInt256) (mem : ByteArray) : ByteArray :=
  wordAt32Mem slot (wordAt0Mem key mem)

-- PROMOTE -> Common.lean
theorem wordAt0Mem_size {mem : ByteArray} (word : UInt256) (hmem : mem.size = 96) :
    (wordAt0Mem word mem).size = 96 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

-- PROMOTE -> Common.lean
theorem wordAt32Mem_size {mem : ByteArray} (word : UInt256) (hmem : mem.size = 96) :
    (wordAt32Mem word mem).size = 96 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

-- PROMOTE -> Common.lean
theorem twoWordHashMem_size {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 96) :
    (twoWordHashMem key slot mem).size = 96 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size slot (wordAt0Mem_size key hmem)

-- PROMOTE -> Common.lean
theorem twoWordHashMem_read0 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

-- PROMOTE -> Common.lean
theorem twoWordHashMem_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

-- PROMOTE -> Common.lean
theorem twoWordHashMem_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size key hmem])]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem])]
  exact hread64

-- PROMOTE -> Common.lean
set_option maxHeartbeats 800000 in
theorem twoWordHashMem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [twoWordHashMem_size key slot hmem]; omega),
      twoWordHashMem_read0 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [twoWordHashMem_size key slot hmem]; omega),
      twoWordHashMem_read32 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

/-- Memory after the owner key and `_allowances` base slot `2` are in scratch memory. -/
noncomputable def allowanceOwnerHashMem (owner : UInt256) : ByteArray :=
  twoWordHashMem owner ⟨2⟩ solcFreePtrMem

/-- The first keccak slot, Solidity's base for `_allowances[owner]`. -/
noncomputable def allowanceOwnerSlot (owner : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((allowanceOwnerHashMem owner).readWithPadding 0 64)))

/-- Memory after the spender key and `_allowances[owner]` slot are in scratch memory. -/
noncomputable def allowanceSpenderMem (owner spender : UInt256) : ByteArray :=
  wordAt0Mem spender (allowanceOwnerHashMem owner)

/-- Memory after the spender key and `_allowances[owner]` slot are in scratch memory. -/
noncomputable def allowanceSpenderHashMem (owner spender : UInt256) : ByteArray :=
  wordAt32Mem (allowanceOwnerSlot owner) (allowanceSpenderMem owner spender)

/-- The second keccak slot, Solidity's base for `_allowances[owner][spender]`. -/
noncomputable def allowanceSpenderSlot (owner spender : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((allowanceSpenderHashMem owner spender).readWithPadding 0 64)))

/-- Memory after the token id and `_allowances[owner][spender]` slot are in scratch memory. -/
noncomputable def allowanceIdMem (owner spender id : UInt256) : ByteArray :=
  wordAt0Mem id (allowanceSpenderHashMem owner spender)

/-- Memory after the token id and `_allowances[owner][spender]` slot are in scratch memory. -/
noncomputable def allowanceIdHashMem (owner spender id : UInt256) : ByteArray :=
  wordAt32Mem (allowanceSpenderSlot owner spender) (allowanceIdMem owner spender id)

/-- Memory after the return wrapper stores the loaded allowance word at `0x80`. -/
noncomputable def allowanceReturnMem (owner spender id val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (allowanceIdHashMem owner spender id) 128 32

theorem allowanceOwnerHashMem_size (owner : UInt256) :
    (allowanceOwnerHashMem owner).size = 96 := by
  unfold allowanceOwnerHashMem
  exact twoWordHashMem_size owner ⟨2⟩ solcFreePtrMem_size

theorem allowanceSpenderHashMem_size (owner spender : UInt256) :
    (allowanceSpenderHashMem owner spender).size = 96 := by
  unfold allowanceSpenderHashMem
  apply wordAt32Mem_size
  unfold allowanceSpenderMem
  exact wordAt0Mem_size spender (allowanceOwnerHashMem_size owner)

theorem allowanceIdHashMem_size (owner spender id : UInt256) :
    (allowanceIdHashMem owner spender id).size = 96 := by
  unfold allowanceIdHashMem
  apply wordAt32Mem_size
  unfold allowanceIdMem
  exact wordAt0Mem_size id (allowanceSpenderHashMem_size owner spender)

theorem allowanceOwnerHashMem_read0_64 (owner : UInt256) :
    (allowanceOwnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨2⟩ : UInt256) := by
  unfold allowanceOwnerHashMem
  exact twoWordHashMem_read0_64 owner ⟨2⟩ solcFreePtrMem_size

theorem allowanceSpenderHashMem_read0_64 (owner spender : UInt256) :
    (allowanceSpenderHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (allowanceOwnerSlot owner) := by
  change (twoWordHashMem spender (allowanceOwnerSlot owner) (allowanceOwnerHashMem owner)
      ).readWithPadding 0 64 =
    UInt256.toByteArray spender ++ UInt256.toByteArray (allowanceOwnerSlot owner)
  exact twoWordHashMem_read0_64 spender (allowanceOwnerSlot owner)
    (allowanceOwnerHashMem_size owner)

theorem allowanceIdHashMem_read0_64 (owner spender id : UInt256) :
    (allowanceIdHashMem owner spender id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (allowanceSpenderSlot owner spender) := by
  change (twoWordHashMem id (allowanceSpenderSlot owner spender)
      (allowanceSpenderHashMem owner spender)).readWithPadding 0 64 =
    UInt256.toByteArray id ++ UInt256.toByteArray (allowanceSpenderSlot owner spender)
  exact twoWordHashMem_read0_64 id (allowanceSpenderSlot owner spender)
    (allowanceSpenderHashMem_size owner spender)

theorem allowanceIdHashMem_read64 (owner spender id : UInt256) :
    (allowanceIdHashMem owner spender id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  change (twoWordHashMem id (allowanceSpenderSlot owner spender)
      (allowanceSpenderHashMem owner spender)).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  apply twoWordHashMem_read64
  · exact allowanceSpenderHashMem_size owner spender
  · change (twoWordHashMem spender (allowanceOwnerSlot owner) (allowanceOwnerHashMem owner)
        ).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩
    apply twoWordHashMem_read64
    · exact allowanceOwnerHashMem_size owner
    · exact twoWordHashMem_read64 owner ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem allowanceIdHashMem_mload64 (owner spender id : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (allowanceIdHashMem owner spender id).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((allowanceIdHashMem owner spender id).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [allowanceIdHashMem_size]; decide) (by decide)
    (allowanceIdHashMem_read64 owner spender id)

theorem allowanceReturnMem_size (owner spender id val : UInt256) :
    (allowanceReturnMem owner spender id val).size = 160 := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceIdHashMem_size]; omega)
      (by rw [allowanceIdHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, allowanceIdHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem allowanceReturnMem_read64 (owner spender id val : UInt256) :
    (allowanceReturnMem owner spender id val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceIdHashMem_size]; omega)
      (by rw [allowanceIdHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, allowanceIdHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, allowanceIdHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [allowanceIdHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [allowanceIdHashMem_size]),
    allowanceIdHashMem_read64]

theorem allowanceReturnMem_mload64 (owner spender id val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (allowanceReturnMem owner spender id val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((allowanceReturnMem owner spender id val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [allowanceReturnMem_size]; decide) (by decide)
    (allowanceReturnMem_read64 owner spender id val)

theorem allowanceReturnMem_read128 (owner spender id val : UInt256) :
    (allowanceReturnMem owner spender id val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceIdHashMem_size]; omega)
      (by rw [allowanceIdHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, allowanceIdHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size])]
  rw [extract_append_right_window
      (allowanceIdHashMem owner spender id ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (allowanceIdHashMem owner spender id).size)))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, allowanceIdHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, allowanceIdHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

theorem allowanceOwnerKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    allowanceOwnerSlot (allowanceOwnerWord I) =
      mapSlot (keyValueToWord
        (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat))) ⟨2⟩ := by
  unfold allowanceOwnerSlot mapSlot
  rw [allowanceOwnerHashMem_read0_64]
  rw [ERC20.erc20KeyValueToWord_address_of_canonical _ hcanonOwner]
  exact mappingSlot_single (allowanceOwnerWord I) ⟨2⟩

theorem allowanceSpenderKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    allowanceSpenderSlot (allowanceOwnerWord I) (allowanceSpenderWord I) =
      mapSlot (keyValueToWord
        (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)))
        (mapSlot (keyValueToWord
          (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat))) ⟨2⟩) := by
  unfold allowanceSpenderSlot mapSlot
  rw [allowanceSpenderHashMem_read0_64, allowanceOwnerKeccakSlot I hcanonOwner]
  rw [ERC20.erc20KeyValueToWord_address_of_canonical _ hcanonOwner,
    ERC20.erc20KeyValueToWord_address_of_canonical _ hcanonSpender]
  exact mappingSlot_single (allowanceSpenderWord I)
    (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (allowanceOwnerWord I) ++
      UInt256.toByteArray (⟨2⟩ : UInt256))))

theorem allowanceFinalKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceIdHashMem (allowanceOwnerWord I) (allowanceSpenderWord I)
          (allowanceIdWord I)).readWithPadding 0 64)))
      = allowanceSlotI I := by
  unfold allowanceSlotI allowanceSlot mapSlot
  rw [allowanceIdHashMem_read0_64, allowanceSpenderKeccakSlot I hcanonOwner hcanonSpender]
  rw [ERC20.erc20KeyValueToWord_address_of_canonical _ hcanonOwner,
    ERC20.erc20KeyValueToWord_address_of_canonical _ hcanonSpender]
  rw [show keyValueToWord (.int (Int.ofNat (allowanceIdWord I).toNat)) =
      allowanceIdWord I from erc6909WordOfInt_ofNat_toNat (allowanceIdWord I)]
  exact mappingSlot_single (allowanceIdWord I)
    (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (allowanceSpenderWord I) ++
      UInt256.toByteArray
        (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (allowanceOwnerWord I) ++
          UInt256.toByteArray (⟨2⟩ : UInt256)))))))

end OpenZeppelinBench.ERC6909

namespace Reasoning.Reach

open OpenZeppelinBench.ERC6909

/-! ## Local high-SWAP reachability helpers -/

-- PROMOTE -> Common.lean / Reasoning.Stepping: generic `SWAP5` xstep.
theorem erc6909AllowanceSwap5_xstep {s : State} {code : ByteArray}
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

-- PROMOTE -> Common.lean / Reasoning.Stepping: generic `SWAP6` xstep.
theorem erc6909AllowanceSwap6_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP6, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: t)
    (hov : t.length + 7 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP6, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap6 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: h :: t).length - 7 + 7 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- PROMOTE -> Common.lean / Reasoning.Reach: generic `RD.swap5`.
theorem RD.erc6909AllowanceSwap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909AllowanceSwap5_xstep hc hp hdec hs hov)

-- PROMOTE -> Common.lean / Reasoning.Reach: generic `RD.swap6`.
theorem RD.erc6909AllowanceSwap6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909AllowanceSwap6_xstep hc hp hdec hs hov)

-- PROMOTE -> Common.lean
-- Generalizes the optimizer-on ERC6909 address decoder routine at pc 1629.  The name is local to
-- `Allowance.lean` to avoid colliding with parallel per-function files that may promote the helper.
set_option maxHeartbeats 400000 in
theorem RD.erc6909AllowanceDecodeAddrOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨1629⟩ (off :: ret :: R) mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
        < EVM.addressModulus)
    (hret : (D_J erc6909BenchBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD erc6909BenchBytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R)
        mem aw rdata acc k' C' := by
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
theorem RD.erc6909AllowanceDecodeAddrRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {off ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨1629⟩ (off :: ret :: R) mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          solcAddrMask) = ⟨0⟩)
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

/-! ## EVM trace for `allowance(address,address,uint256)` -/

theorem erc6909AllowanceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1847⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨280⟩, ⟨155⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨155⟩, push2 ⟨280⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1847⟩, jump (by jump_dest) ]⟩

theorem erc6909AllowanceX_dec1629_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
        [⟨4⟩, ⟨1874⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨280⟩, ⟨155⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    simpa using solcCalldataStaticLenCheckOk (words := 3) hsz100 hszhi hsize
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1865⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1874⟩, dup5, push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909AllowanceX_dec1874 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
        [allowanceOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨280⟩, ⟨155⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_dec1629_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  simpa [allowanceOwnerWord, calldataWord] using
    RD.erc6909AllowanceDecodeAddrOk rd hcanonOwner (by jump_dest) (by evm_ov)

theorem erc6909AllowanceX_dec1629_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
        [⟨4⟩ + ⟨32⟩, ⟨1888⟩, ⟨0⟩, ⟨0⟩, allowanceOwnerWord I, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨280⟩, ⟨155⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_dec1874 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, push2 ⟨1888⟩, push1 ⟨32⟩, dup6, add,
    push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909AllowanceX_dec1888 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1888⟩
        [allowanceSpenderWord I, ⟨0⟩, ⟨0⟩, allowanceOwnerWord I, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨280⟩, ⟨155⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_dec1629_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hreach
  simpa [allowanceSpenderWord, calldataWord] using
    RD.erc6909AllowanceDecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem erc6909AllowanceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
        [allowanceIdWord I, allowanceSpenderWord I, allowanceOwnerWord I, ⟨155⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_dec1888 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hcanonSpender hreach
  have rd1889 := evm_run rd with [jumpdest, swap3]
  have rd1890 := RD.erc6909AllowanceSwap6 rd1889 (by decide) (by evm_ov)
  have rd1891 := evm_run rd1890 with [swap3]
  have rd1892 := RD.erc6909AllowanceSwap5 rd1891 (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [allowanceIdWord, calldataWord] using (evm_run rd1892 with [
      pop, pop, pop, push1 ⟨64⟩, swap2, swap1, swap2, add, calldataload, swap1,
      jump (by jump_dest) ])⟩

theorem erc6909X_allowance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  obtain ⟨_, _, rd280⟩ := erc6909AllowanceX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hcanonSpender hreach
  have hslot := allowanceFinalKeccakSlot I hcanonOwner hcanonSpender
  have rd306 := evm_run rd280 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    push0, swap1, dup2,
    raw mstore 0 (wordAt0Mem (allowanceOwnerWord I) solcFreePtrMem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonOwner]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (allowanceOwnerHashMem (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (allowanceOwnerSlot (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd307 := RD.erc6909AllowanceSwap5 rd306 (by decide) (by evm_ov)
  have rd308 := evm_run rd307 with [swap1]
  have rd309 := RD.erc6909AllowanceSwap6 rd308 (by decide) (by evm_ov)
  have rd326 := evm_run rd309 with [
    and, dup3,
    raw mstore 0 (allowanceSpenderMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonSpender]
        rfl)
      (by decide) (by evm_ov),
    swap3, dup4,
    raw mstore 0 (allowanceSpenderHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup4, dup2,
    raw keccak256 0 (allowanceSpenderSlot (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap2, dup2,
    raw mstore 0
      (allowanceIdMem (allowanceOwnerWord I) (allowanceSpenderWord I) (allowanceIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap2,
    raw mstore 0
      (allowanceIdHashMem (allowanceOwnerWord I) (allowanceSpenderWord I) (allowanceIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw keccak256 0 (allowanceSlotI I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd327⟩ := rd326.sload (by decide) (by evm_ov)
  have rd155 := evm_run rd327 with [swap1, jump (by jump_dest)]
  simpa [allowanceWord] using (evm_run rd155 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (allowanceIdHashMem_mload64 (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceIdWord I))
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6
      (allowanceReturnMem (allowanceOwnerWord I) (allowanceSpenderWord I) (allowanceIdWord I)
        (allowanceWord σ I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (allowanceReturnMem_mload64 (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceIdWord I) (allowanceWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (allowanceWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
          from by decide]
        change (allowanceReturnMem (allowanceOwnerWord I) (allowanceSpenderWord I)
            (allowanceIdWord I) (allowanceWord σ I)).readWithPadding 128 32 =
          UInt256.toByteArray (allowanceWord σ I)
        exact allowanceReturnMem_read128 (allowanceOwnerWord I) (allowanceSpenderWord I)
          (allowanceIdWord I) (allowanceWord σ I))
      (by evm_ov) ])

theorem erc6909AllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckShort (words := 3) hsz4 hshort hsize
      (by norm_num)
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1865⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909AllowanceX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckHuge (words := 3) hbig hsize (by norm_num)
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1865⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909AllowanceX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (allowanceOwnerWord I)
      (UInt256.land (allowanceOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_dec1629_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.erc6909AllowanceDecodeAddrRevert rd (by simpa [allowanceOwnerWord, calldataWord] using hnc)
    (by evm_ov)

theorem erc6909AllowanceX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (allowanceSpenderWord I)
      (UInt256.land (allowanceSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := erc6909AllowanceX_dec1629_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hreach
  exact RD.erc6909AllowanceDecodeAddrRevert rd
    (by simpa [allowanceSpenderWord, calldataWord] using hnc) (by evm_ov)

theorem erc6909AllowanceSelector_size {I : ExecutionEnv}
    (hsel : selIs I (erc6909SelBytes 5)) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (erc6909SelBytes 5).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_allowance {cd : ByteArray}
    (hsel : (erc6909SelBytes 5 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some allowanceTransition := by
  refine dispatchMsg_eq_some_of_split
    (pre := [])
    (post := [approveTransition, balanceOfTransition, isOperatorTransition, setOperatorTransition,
      supportsInterfaceTransition, transferTransition, transferFromTransition])
    rfl ?_ (by
      rw [selectorOf, erc6909AllowanceSelectorBytes]
      simpa [erc6909SelBytes] using hsel)
  intro t ht
  simp at ht

theorem erc6909AllowanceBodyCore
    {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (erc6909SelBytes 5))
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨266⟩
      [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have hsz4 := erc6909AllowanceSelector_size hsel
  have hd := erc6909Dispatch_allowance (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus
        · have hdec := erc6909Decode_allowance_ok (I := I) hsz100 hbig hcanonOwner
            hcanonSpender
          have hword : allowanceWord σ_evm I = allowanceWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (allowanceSlotI I) ⟨0⟩
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
                (allowanceStore I)
                allowanceTransition.body
                (.returned { contract := contract, locals := allowanceStore I }
                  (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
                  (some (.int (Int.ofNat (allowanceWord σ_solm I).toNat)))) := by
            simpa [allowanceWord, allowanceSlotI, initState, Solm.EVM.storageLoad,
              State.lookupAccount] using erc6909AllowanceBodyReturns
                (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
          exact (erc6909X_allowance (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonOwner hcanonSpender hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword])
              hAccounts
              (returnEquiv_of_encode (uint256ReturnEncoding (allowanceWord σ_evm I)))
        · have hdec := erc6909Decode_allowance_none_noncanon_spender
            (I := I) hsz100 hbig hcanonOwner hcanonSpender
          have hnc : UInt256.eq (allowanceSpenderWord I)
              (UInt256.land (allowanceSpenderWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanonSpender (solcAddrCanonical_of_clean he))
          exact (erc6909AllowanceX_noncanon_spender (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonOwner hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc6909Decode_allowance_none_noncanon_owner (I := I) hsz100 hbig
          hcanonOwner
        have hnc : UInt256.eq (allowanceOwnerWord I)
            (UInt256.land (allowanceOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonOwner (solcAddrCanonical_of_clean he))
        exact (erc6909AllowanceX_noncanon_owner (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_allowance_none_huge (I := I) hbigge
      exact (erc6909AllowanceX_hugearg (g := Sat256.ofUInt256 g) hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := erc6909Decode_allowance_none_short (I := I) hsz4 hshort
    exact (erc6909AllowanceX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
