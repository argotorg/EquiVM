import Examples.ERC20.Common
import Reasoning.Refinement
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace ERC20

/-! ## ABI decode and source-level body for `allowance(address,address)` -/

/-- The raw ABI word for `allowance`'s `owner` argument. -/
abbrev allowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `allowance`'s `spender` argument. -/
abbrev allowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev allowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (allowanceOwnerValue I)).insert "spender" (allowanceSpenderValue I)

def allowanceSlot (I : ExecutionEnv) : UInt256 :=
  erc20AllowanceSlot
    (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat))
    (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))

def allowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (allowanceSlot I) ⟨0⟩)

theorem erc20Decode_allowance_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = some (allowanceStore I) := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = _
  simpa [allowanceStore, allowanceOwnerValue, allowanceSpenderValue, allowanceOwnerWord,
    allowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hcanonSpender

theorem erc20Decode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "owner") (y := "spender") hsz4 hshort

theorem erc20Decode_allowance_none_noncanon_owner {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncOwner : ¬ (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, allowanceOwnerWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") hsz68 hbig hncOwner

theorem erc20Decode_allowance_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hncSpender : ¬ (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, allowanceOwnerWord, allowanceSpenderWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hbig hcanonOwner hncSpender

theorem erc20Decode_allowance_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "owner") (y := "spender") hbig

theorem allowanceStore_owner (I : ExecutionEnv) :
    (allowanceStore I).get? "owner" = some (allowanceOwnerValue I) := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_self]

theorem allowanceStore_spender (I : ExecutionEnv) :
    (allowanceStore I).get? "spender" = some (allowanceSpenderValue I) := by
  rw [allowanceStore, store_get_self]

theorem allowanceStore_owner_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["owner"]? = some (allowanceOwnerValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_owner]

theorem allowanceStore_spender_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["spender"]? = some (allowanceSpenderValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_spender]

theorem evalExpr_allowance_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := allowanceStore I } evm
      (.var "owner") = .ok (allowanceOwnerValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [allowanceStore_owner]

theorem evalExpr_allowance_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := allowanceStore I } evm
      (.var "spender") = .ok (allowanceSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [allowanceStore_spender]

theorem evalExpr_allowance_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := allowanceStore I } evm
      (.storage (allowanceRef (.var "owner") (.var "spender"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlot I)).toNat)) := by
  have hgowner := allowanceStore_owner_getElem? I
  have hgspender := allowanceStore_spender_getElem? I
  have her : evalStorageRef erc20Config { contract := erc20Contract, locals := allowanceStore I }
      evm (allowanceRef (.var "owner") (.var "spender")) =
      .ok { base := "allowance",
            steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                      .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))] } := by
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef, evalExpr?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
      Std.HashMap.get?_eq_getElem?, hgowner, hgspender,
      allowanceOwnerValue, allowanceSpenderValue]
  have hty : storageTypeAt? erc20Contract.storage
      { base := "allowance",
        steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))] } =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, erc20Contract, erc20StorageDecls, uint256Storage,
          List.find?, List.foldlM, storageTypeStep?]
  have hloc : erc20Config.storage.layout
      { base := "allowance",
        steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))] } =
      fun _ => some (erc20Uint256Loc (allowanceSlot I)) := by
    simp [allowanceSlot, erc20Config_storage_allowance, allowanceOwnerValue, allowanceSpenderValue,
          erc20AllowanceSlot]
  rw [evalExpr_storage_scalar
    (hbase := by rw [allowanceStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)];
                 simp)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  exact erc20StorageLocLoad_uint256 evm (allowanceSlot I)

theorem erc20AllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody erc20Config erc20Contract evm (allowanceStore I) allowanceTransition.body
      (.returned { contract := erc20Contract, locals := allowanceStore I } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlot I)).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simpa [allowanceRef] using evalExpr_allowance_storage evm I)

/-! ## EVM scratch memory for the `allowance` nested mapping access -/

/-- Memory after `allowance` stores the outer mapping base slot `1` at scratch offset `0x20`. -/
noncomputable def allowanceInnerBaseMem : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 solcFreePtrMem 32 32

/-- Memory after `allowance` stores the `owner` key at scratch offset `0x00`. -/
noncomputable def allowanceInnerHashMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0 allowanceInnerBaseMem 0 32

/-- The first keccak slot, Solidity's base for `allowance[owner]`. -/
noncomputable def allowanceInnerSlot (owner : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((allowanceInnerHashMem owner).readWithPadding 0 64)))

/-- Memory after `allowance` stores the inner mapping slot at scratch offset `0x20`. -/
noncomputable def allowanceOuterBaseMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray (allowanceInnerSlot owner)).write 0 (allowanceInnerHashMem owner) 32 32

/-- Memory after `allowance` stores the `spender` key at scratch offset `0x00`. -/
noncomputable def allowanceOuterHashMem (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray spender).write 0 (allowanceOuterBaseMem owner) 0 32

theorem allowanceInnerBaseMem_size : allowanceInnerBaseMem.size = 96 := by
  unfold allowanceInnerBaseMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem allowanceInnerHashMem_size (owner : UInt256) :
    (allowanceInnerHashMem owner).size = 96 := by
  unfold allowanceInnerHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [allowanceInnerBaseMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, allowanceInnerBaseMem_size, toByteArray_size]
  omega

theorem allowanceOuterBaseMem_size (owner : UInt256) :
    (allowanceOuterBaseMem owner).size = 96 := by
  unfold allowanceOuterBaseMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [allowanceInnerHashMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, allowanceInnerHashMem_size, toByteArray_size]
  omega

theorem allowanceOuterHashMem_size (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).size = 96 := by
  unfold allowanceOuterHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [allowanceOuterBaseMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, allowanceOuterBaseMem_size, toByteArray_size]
  omega

theorem allowanceInnerBaseMem_read32 :
    allowanceInnerBaseMem.readWithPadding 32 32 = UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold allowanceInnerBaseMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem allowanceInnerBaseMem_read64 :
    allowanceInnerBaseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceInnerBaseMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem allowanceInnerHashMem_read0 (owner : UInt256) :
    (allowanceInnerHashMem owner).readWithPadding 0 32 = UInt256.toByteArray owner := by
  unfold allowanceInnerHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner from by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray owner).size ≤ 32
        rw [toByteArray_size])]

theorem allowanceInnerHashMem_read32 (owner : UInt256) :
    (allowanceInnerHashMem owner).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold allowanceInnerHashMem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by omega)
      (by omega) (by rw [allowanceInnerBaseMem_size]; omega),
    allowanceInnerBaseMem_read32]

theorem allowanceInnerHashMem_read64 (owner : UInt256) :
    (allowanceInnerHashMem owner).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceInnerHashMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by omega) (by rw [allowanceInnerBaseMem_size]),
    allowanceInnerBaseMem_read64]

theorem allowanceInnerHashMem_read0_64 (owner : UInt256) :
    (allowanceInnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [allowanceInnerHashMem_size]; omega)]
  unfold allowanceInnerHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  have hownerFull :
      (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hbase32 :
      (allowanceInnerBaseMem.extract 32 allowanceInnerBaseMem.size).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    rw [extract_extract_BA, show 32 + 0 = 32 from rfl,
      show min (32 + 32) allowanceInnerBaseMem.size = 64 from by
        rw [allowanceInnerBaseMem_size]; rfl]
    have hread := allowanceInnerBaseMem_read32
    rw [readWithPadding_eq_extract _ 32 (by rw [allowanceInnerBaseMem_size]; omega)] at hread
    exact hread
  have hleft0 : allowanceInnerBaseMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    show allowanceInnerBaseMem.data.extract 0 0 = #[]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hleft0, ByteArray.empty_append, hownerFull]
  rw [extract_append_span (UInt256.toByteArray owner)
      (allowanceInnerBaseMem.extract 32 allowanceInnerBaseMem.size) 0 64
      (by omega) (by rw [toByteArray_size]; omega)]
  rw [show (UInt256.toByteArray owner).size = 32 from toByteArray_size owner]
  rw [show 64 - 32 = 32 from rfl]
  rw [hownerFull, hbase32]

theorem allowanceInnerKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    allowanceInnerSlot (allowanceOwnerWord I) =
      erc20AllowanceOwnerSlot
        (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)) := by
  unfold allowanceInnerSlot
  rw [allowanceInnerHashMem_read0_64]
  unfold erc20AllowanceOwnerSlot erc20MappingSlot
  rw [erc20KeyValueToWord_address_of_canonical _ hcanonOwner]
  exact mappingSlot_single (allowanceOwnerWord I) ⟨1⟩

theorem allowanceOuterBaseMem_read32 (owner : UInt256) :
    (allowanceOuterBaseMem owner).readWithPadding 32 32 =
      UInt256.toByteArray (allowanceInnerSlot owner) := by
  unfold allowanceOuterBaseMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [allowanceInnerHashMem_size]; omega),
    show (UInt256.toByteArray (allowanceInnerSlot owner)).extract 0 32 =
      UInt256.toByteArray (allowanceInnerSlot owner) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (allowanceInnerSlot owner)).size ≤ 32
          rw [toByteArray_size])]

theorem allowanceOuterBaseMem_read64 (owner : UInt256) :
    (allowanceOuterBaseMem owner).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceOuterBaseMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [allowanceInnerHashMem_size]; omega) (by omega)
      (by rw [allowanceInnerHashMem_size]),
    allowanceInnerHashMem_read64]

theorem allowanceOuterHashMem_read0 (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).readWithPadding 0 32 =
      UInt256.toByteArray spender := by
  unfold allowanceOuterHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray spender).extract 0 32 = UInt256.toByteArray spender from by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray spender).size ≤ 32
        rw [toByteArray_size])]

theorem allowanceOuterHashMem_read32 (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).readWithPadding 32 32 =
      UInt256.toByteArray (allowanceInnerSlot owner) := by
  unfold allowanceOuterHashMem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by omega)
      (by omega) (by rw [allowanceOuterBaseMem_size]; omega),
    allowanceOuterBaseMem_read32]

theorem allowanceOuterHashMem_read64 (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceOuterHashMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by omega) (by rw [allowanceOuterBaseMem_size]),
    allowanceOuterBaseMem_read64]

theorem allowanceOuterHashMem_mload64 (owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (allowanceOuterHashMem owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((allowanceOuterHashMem owner spender).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [allowanceOuterHashMem_size]; decide) (by decide)
    (allowanceOuterHashMem_read64 owner spender)

theorem allowanceOuterHashMem_read0_64 (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (allowanceInnerSlot owner) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [allowanceOuterHashMem_size]; omega)]
  unfold allowanceOuterHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  have hspenderFull :
      (UInt256.toByteArray spender).extract 0 32 = UInt256.toByteArray spender := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray spender).size ≤ 32
      rw [toByteArray_size])
  have hbase32 :
      ((allowanceOuterBaseMem owner).extract 32 (allowanceOuterBaseMem owner).size).extract 0 32 =
        UInt256.toByteArray (allowanceInnerSlot owner) := by
    rw [extract_extract_BA, show 32 + 0 = 32 from rfl,
      show min (32 + 32) (allowanceOuterBaseMem owner).size = 64 from by
        rw [allowanceOuterBaseMem_size]; rfl]
    have hread := allowanceOuterBaseMem_read32 owner
    rw [readWithPadding_eq_extract _ 32 (by rw [allowanceOuterBaseMem_size]; omega)] at hread
    exact hread
  have hleft0 : (allowanceOuterBaseMem owner).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    show (allowanceOuterBaseMem owner).data.extract 0 0 = #[]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hleft0, ByteArray.empty_append, hspenderFull]
  rw [extract_append_span (UInt256.toByteArray spender)
      ((allowanceOuterBaseMem owner).extract 32 (allowanceOuterBaseMem owner).size) 0 64
      (by omega) (by rw [toByteArray_size]; omega)]
  rw [show (UInt256.toByteArray spender).size = 32 from toByteArray_size spender]
  rw [show 64 - 32 = 32 from rfl]
  rw [hspenderFull, hbase32]

theorem allowanceOuterKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceOuterHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
          |>.readWithPadding 0 64)))
      = allowanceSlot I := by
  rw [allowanceOuterHashMem_read0_64, allowanceInnerKeccakSlot I hcanonOwner]
  unfold allowanceSlot erc20AllowanceSlot erc20AllowanceOwnerSlot erc20MappingSlot
  rw [erc20KeyValueToWord_address_of_canonical _ hcanonOwner,
    erc20KeyValueToWord_address_of_canonical _ hcanonSpender]
  exact mappingSlot_single (allowanceSpenderWord I)
    (erc20MappingSlot (allowanceOwnerWord I) ⟨1⟩)

/-- Memory after the shared uint256 encoder writes the `allowance` return word at `0x80`. -/
noncomputable def allowanceReturnMem (owner spender val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (allowanceOuterHashMem owner spender) 128 32

theorem allowanceReturnMem_size (owner spender val : UInt256) :
    (allowanceReturnMem owner spender val).size = 160 := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceOuterHashMem_size]; omega)
      (by rw [allowanceOuterHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, allowanceOuterHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem allowanceReturnMem_read64 (owner spender val : UInt256) :
    (allowanceReturnMem owner spender val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceOuterHashMem_size]; omega)
      (by rw [allowanceOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, allowanceOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, allowanceOuterHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [allowanceOuterHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [allowanceOuterHashMem_size]),
    allowanceOuterHashMem_read64]

theorem allowanceReturnMem_mload64 (owner spender val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (allowanceReturnMem owner spender val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((allowanceReturnMem owner spender val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [allowanceReturnMem_size]; decide) (by decide)
    (allowanceReturnMem_read64 owner spender val)

theorem allowanceReturnMem_read128 (owner spender val : UInt256) :
    (allowanceReturnMem owner spender val).readWithPadding 128 32 = UInt256.toByteArray val := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceOuterHashMem_size]; omega)
      (by rw [allowanceOuterHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, allowanceOuterHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      )]
  rw [extract_append_right_window
      (allowanceOuterHashMem owner spender ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (allowanceOuterHashMem owner spender).size)))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, allowanceOuterHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        )]
  rw [ByteArray.size_append, allowanceOuterHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

/-! ## EVM trace for `allowance(address,address)` -/

/-- Wrapper pc 322 sets up calldata bounds for `allowance(address,address)` and jumps to the
    two-address tuple decoder at pc 2221. -/
theorem erc20AllowanceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2221⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨343⟩, ⟨348⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨348⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨343⟩, swap2, swap1, push2 ⟨2221⟩, jump erc20_jd ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

/-- The two-address tuple decoder accepts two static words and jumps to the address decoder for
    the `owner` argument. -/
theorem erc20AllowanceX_dec1874_owner {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
        [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨2256⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
          ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨343⟩, ⟨348⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2243⟩, jumpiT (by rw [hslt]; decide) erc20_jd,
    jumpdest, push0, push2 ⟨2256⟩, dup6, dup3, dup7, add, push2 ⟨1874⟩,
    jump erc20_jd ]⟩

/-- The `owner` address decode (success): one application of the shared `RD.erc20DecodeAddrOk`
    routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec2256` chain. -/
theorem erc20AllowanceX_dec2256 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2256⟩
        [allowanceOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨343⟩, ⟨348⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_dec1874_owner (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.erc20DecodeAddrOk rd hcanonOwner (by jump_dest) (by evm_ov)

/-- After the first address has been decoded, the tuple decoder jumps to the address decoder for
    the `spender` argument. -/
theorem erc20AllowanceX_dec1874_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
        [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨2273⟩, ⟨32⟩, ⟨0⟩,
          allowanceOwnerWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨343⟩, ⟨348⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_dec2256 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hcanonOwner hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨2273⟩, dup6, dup3, dup7,
    add, push2 ⟨1874⟩, jump erc20_jd ]⟩

/-- The `spender` address decode (success): a second application of the shared
    `RD.erc20DecodeAddrOk` routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec2273`
    chain. -/
theorem erc20AllowanceX_dec2273 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2273⟩
        [allowanceSpenderWord I, ⟨32⟩, ⟨0⟩, allowanceOwnerWord I, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨343⟩, ⟨348⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_dec1874_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hcanonOwner hreach
  exact RD.erc20DecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

/-- The two-address tuple decoder returns to the external wrapper, which jumps to the internal
    `allowance` body at pc 1768. -/
theorem erc20AllowanceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1768⟩
        [allowanceSpenderWord I, allowanceOwnerWord I, ⟨348⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_dec2273 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump erc20_jd,
    jumpdest, push2 ⟨1768⟩, jump erc20_jd ]⟩

/-- The EVM `allowance(address,address)` path loads the explicit nested mapping slot and returns
    it as a single ABI word. -/
theorem erc20X_allowance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc20Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  obtain ⟨k, C, rd1768⟩ := erc20AllowanceX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hcanonSpender hreach
  have hslot := allowanceOuterKeccakSlot I hcanonOwner hcanonSpender
  have rd1797 := evm_run rd1768 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 allowanceInnerBaseMem (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup2, push0,
    raw mstore 0 (allowanceInnerHashMem (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (allowanceInnerSlot (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (allowanceOuterBaseMem (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, push0,
    raw mstore 0 (allowanceOuterHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (allowanceSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov),
    push0, swap2, pop, swap2, pop, pop ]
  obtain ⟨k1, C1, rd1798⟩ := rd1797.sload (by decide) (by evm_ov)
  have rd348 := evm_run rd1798 with [
    dup2, jump erc20_jd ]
  have rd2073 := evm_run rd348 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (allowanceOuterHashMem_mload64 (allowanceOwnerWord I) (allowanceSpenderWord I))
      (by decide) (by evm_ov),
    push2 ⟨361⟩, swap2, swap1, push2 ⟨2073⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd361⟩ := erc20RoutineEncodeUint256FromMem
    (val := allowanceWord σ I) (ret := ⟨361⟩) (R := [⟨348⟩, sel])
    rd2073 (by rfl) erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd361 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (allowanceReturnMem_mload64 (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (allowanceWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, erc20SubRet32_toNat]
        change (allowanceReturnMem (allowanceOwnerWord I) (allowanceSpenderWord I)
            (allowanceWord σ I)).readWithPadding 128 32 =
          UInt256.toByteArray (allowanceWord σ I)
        exact allowanceReturnMem_read128 (allowanceOwnerWord I) (allowanceSpenderWord I)
          (allowanceWord σ I))
      (by evm_ov) ]

/-! ## Decode-failure traces and top-level body theorem -/

theorem erc20AllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2243⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2242⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20AllowanceX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2243⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2242⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20AllowanceX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (allowanceOwnerWord I)
      (UInt256.land (allowanceOwnerWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_dec1874_owner (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.erc20DecodeAddrRevert rd hnc (by evm_ov)

theorem erc20AllowanceX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (allowanceSpenderWord I)
      (UInt256.land (allowanceSpenderWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc20AllowanceX_dec1874_spender (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonOwner hreach
  exact RD.erc20DecodeAddrRevert rd hnc (by evm_ov)

theorem erc20AllowanceSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc20Dispatch_allowance {cd : ByteArray}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some allowanceTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) :=
    (erc20ByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [approveTransition, totalSupplyTransition, transferFromTransition, balanceOfTransition,
      transferTransition])
    (post := [])
    rfl ?_ (by rw [selectorOf, erc20AllowanceSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, erc20ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc20TotalSupplySelectorBytes, hcd]; decide
  · rw [selectorOf, erc20TransferFromSelectorBytes, hcd]; decide
  · rw [selectorOf, erc20BalanceOfSelectorBytes, hcd]; decide
  · rw [selectorOf, erc20TransferSelectorBytes, hcd]; decide

theorem erc20AllowanceBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨322⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc20AllowanceSelector_size hsel
  have hd := erc20Dispatch_allowance (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus
        · have hdec := erc20Decode_allowance_ok (I := I) hsz68 hbig hcanonOwner hcanonSpender
          have hword : allowanceWord σ_evm I = allowanceWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (allowanceSlot I) ⟨0⟩
          have hbody :
              ExecTransitionBody erc20Config erc20Contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (allowanceStore I)
                allowanceTransition.body
                (.returned { contract := erc20Contract, locals := allowanceStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some (.int (Int.ofNat (allowanceWord σ_solm I).toNat)))) := by
            simpa [allowanceWord, allowanceSlot, initState, Solm.EVM.storageLoad,
              State.lookupAccount] using erc20AllowanceBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
          exact (erc20X_allowance (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonOwner hcanonSpender hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword])
              hAccounts
              (returnEquiv_of_encode (erc20Uint256ReturnEncoding (allowanceWord σ_evm I)))
        · have hdec := erc20Decode_allowance_none_noncanon_spender
            (I := I) hsz68 hbig hcanonOwner hcanonSpender
          have hnc : UInt256.eq (allowanceSpenderWord I)
              (UInt256.land (allowanceSpenderWord I) erc20AddrMask) = ⟨0⟩ :=
            erc20Ueq_zero_of_ne (fun he => hcanonSpender (erc20Word_canonical_of_clean he))
          exact (erc20AllowanceX_noncanon_spender (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonOwner hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc20Decode_allowance_none_noncanon_owner (I := I) hsz68 hbig hcanonOwner
        have hnc : UInt256.eq (allowanceOwnerWord I)
            (UInt256.land (allowanceOwnerWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanonOwner (erc20Word_canonical_of_clean he))
        exact (erc20AllowanceX_noncanon_owner (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc20Decode_allowance_none_huge (I := I) hbigge
      exact (erc20AllowanceX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := erc20Decode_allowance_none_short (I := I) hsz4 hshort
    exact (erc20AllowanceX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end ERC20
