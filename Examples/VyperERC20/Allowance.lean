import Examples.VyperERC20.BalanceOf

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

abbrev allowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev allowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev allowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (allowanceOwnerValue I)).insert "spender" (allowanceSpenderValue I)

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

theorem allowanceStore_allowance (I : ExecutionEnv) :
    (allowanceStore I).get? "allowance" = none := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

def allowanceSlot (I : ExecutionEnv) : UInt256 :=
  erc20AllowanceSlot
    (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat))
    (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))

def allowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (allowanceSlot I) ⟨0⟩)

def allowanceSelectorWord : UInt256 :=
  ⟨0xdd62ed3e⟩

theorem erc20Decode_allowance_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.allowanceTransition.params.map Param.name)
      (transitionSignature ERC20.allowanceTransition).paramTypes I.calldata =
        some (allowanceStore I) := by
  show decodeCalldataWithMode DecodeMode.vyper ["owner", "spender"] [addr, addr] I.calldata = _
  simpa [allowanceStore, allowanceOwnerValue, allowanceSpenderValue,
    allowanceOwnerWord, allowanceSpenderWord, calldataWord]
    using decodeCalldataWithMode_vyper_address_address_ok
      (cd := I.calldata) (x := "owner") (y := "spender")
      hsz68 hcanonOwner hcanonSpender

theorem erc20Decode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.allowanceTransition.params.map Param.name)
      (transitionSignature ERC20.allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr]
    using decodeCalldataWithMode_vyper_address_address_none_short
      (cd := I.calldata) (x := "owner") (y := "spender") hsz4 hshort

theorem erc20Decode_allowance_none_noncanon_owner {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hnc : ¬ (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.allowanceTransition.params.map Param.name)
      (transitionSignature ERC20.allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, allowanceOwnerWord, calldataWord]
    using decodeCalldataWithMode_vyper_address_address_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") hsz68 hnc

theorem erc20Decode_allowance_none_noncanon_spender {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.allowanceTransition.params.map Param.name)
      (transitionSignature ERC20.allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["owner", "spender"] [addr, addr] I.calldata = none
  simpa [addr, allowanceOwnerWord, allowanceSpenderWord, calldataWord]
    using decodeCalldataWithMode_vyper_address_address_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender") hsz68 hcanonOwner hnc

theorem erc20AllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody vyperERC20Config erc20Contract evm (allowanceStore I)
      ERC20.allowanceTransition.body
      (.returned { contract := erc20Contract, locals := allowanceStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlot I)).toNat))])) := by
  have hgowner := allowanceStore_owner_getElem? I
  have hgspender := allowanceStore_spender_getElem? I
  have her : evalStorageRef vyperERC20Config { contract := erc20Contract, locals := allowanceStore I }
      evm (allowanceRef (.var "owner") (.var "spender")) =
      .ok { base := "allowance",
            steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                      .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))] } := by
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef,
      ERC20.allowanceRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      valueToKey?, Std.HashMap.get?_eq_getElem?, hgowner, hgspender,
      allowanceOwnerValue, allowanceSpenderValue]
  have hty : storageTypeAt? erc20Contract.storage
      { base := "allowance",
        steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))] } =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, erc20Contract, ERC20.erc20Contract, ERC20.erc20StorageDecls,
      uint256Storage, ERC20.uint256Storage, List.find?, List.foldlM, storageTypeStep?]
  have hloc : vyperERC20Config.storage.layout
      { base := "allowance",
        steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))] } =
      fun _ => some (vyperUint256Loc (allowanceSlot I)) := by
    simp [allowanceSlot, vyperERC20Config_storage_allowance, allowanceOwnerValue,
      allowanceSpenderValue, erc20AllowanceSlot]
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := allowanceStore_allowance I)
        (her := her)
        (hty := hty)
        (hloc := hloc)]
      rw [vyperERC20StorageLocLoad_uint256])

def allowanceDispatchMem : ByteArray :=
  vyperERC20Bytecode.write 817 ByteArray.empty 30 2

theorem allowanceDispatchMem_size : allowanceDispatchMem.size = 32 := by
  native_decide

def allowanceOwnerArgMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0 allowanceDispatchMem 64 32

def allowanceSpenderArgMem (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray spender).write 0 (allowanceOwnerArgMem owner) 96 32

noncomputable def allowanceInnerKeyMem (owner spender : UInt256) : ByteArray :=
  wordAt32Mem owner (allowanceSpenderArgMem owner spender)

noncomputable def allowanceInnerHashMem (owner spender : UInt256) : ByteArray :=
  wordAt0Mem ⟨1⟩ (allowanceInnerKeyMem owner spender)

noncomputable def allowanceInnerSlotWord (owner spender : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((allowanceInnerHashMem owner spender).readWithPadding 0 64)))

noncomputable def allowanceOuterKeyMem (owner spender : UInt256) : ByteArray :=
  wordAt32Mem spender (allowanceInnerHashMem owner spender)

noncomputable def allowanceOuterHashMem (owner spender : UInt256) : ByteArray :=
  wordAt0Mem (allowanceInnerSlotWord owner spender) (allowanceOuterKeyMem owner spender)

noncomputable def allowanceReturnMem (owner spender val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (allowanceOuterHashMem owner spender) 128 32

theorem allowanceOwnerArgMem_size (owner : UInt256) :
    (allowanceOwnerArgMem owner).size = 96 := by
  unfold allowanceOwnerArgMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceDispatchMem_size]; omega)
      (by rw [allowanceDispatchMem_size]; exact lt_usize 32 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, allowanceDispatchMem_size, ByteArray_zeroes_size,
    toByteArray_size]

theorem allowanceSpenderArgMem_size (owner spender : UInt256) :
    (allowanceSpenderArgMem owner spender).size = 128 := by
  unfold allowanceSpenderArgMem
  simpa [allowanceOwnerArgMem_size] using
    write_end_size_from (UInt256.toByteArray spender) (allowanceOwnerArgMem owner) 0 32
      (by decide)
      (by rw [toByteArray_size])

theorem allowanceInnerKeyMem_size (owner spender : UInt256) :
    (allowanceInnerKeyMem owner spender).size = 128 := by
  unfold allowanceInnerKeyMem
  change ((UInt256.toByteArray owner).write 0 (allowanceSpenderArgMem owner spender) 32 32).size = 128
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceSpenderArgMem_size owner spender]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, allowanceSpenderArgMem_size,
    toByteArray_size]
  omega

theorem allowanceInnerHashMem_size (owner spender : UInt256) :
    (allowanceInnerHashMem owner spender).size = 128 := by
  unfold allowanceInnerHashMem
  change ((UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (allowanceInnerKeyMem owner spender) 0 32).size = 128
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceInnerKeyMem_size owner spender]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, allowanceInnerKeyMem_size,
    toByteArray_size]
  omega

theorem allowanceOuterKeyMem_size (owner spender : UInt256) :
    (allowanceOuterKeyMem owner spender).size = 128 := by
  unfold allowanceOuterKeyMem
  change ((UInt256.toByteArray spender).write 0 (allowanceInnerHashMem owner spender) 32 32).size = 128
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceInnerHashMem_size owner spender]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, allowanceInnerHashMem_size,
    toByteArray_size]
  omega

theorem allowanceOuterHashMem_size (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).size = 128 := by
  unfold allowanceOuterHashMem
  change ((UInt256.toByteArray (allowanceInnerSlotWord owner spender)).write 0
    (allowanceOuterKeyMem owner spender) 0 32).size = 128
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceOuterKeyMem_size owner spender]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, allowanceOuterKeyMem_size,
    toByteArray_size]
  omega

theorem allowanceOwnerArgMem_read64 (owner : UInt256) :
    (allowanceOwnerArgMem owner).readWithPadding 64 32 = UInt256.toByteArray owner := by
  unfold allowanceOwnerArgMem
  exact toByteArray_write_read_back_of_gap owner allowanceDispatchMem 64
    (by rw [allowanceDispatchMem_size]; exact lt_usize 32 (by norm_num))

theorem allowanceSpenderArgMem_read64 (owner spender : UInt256) :
    (allowanceSpenderArgMem owner spender).readWithPadding 64 32 = UInt256.toByteArray owner := by
  unfold allowanceSpenderArgMem
  rw [write32_read_below _ _ 96 64 (by rw [toByteArray_size])
      (by rw [allowanceOwnerArgMem_size owner]) (by omega)]
  exact allowanceOwnerArgMem_read64 owner

theorem allowanceSpenderArgMem_read96 (owner spender : UInt256) :
    (allowanceSpenderArgMem owner spender).readWithPadding 96 32 = UInt256.toByteArray spender := by
  unfold allowanceSpenderArgMem
  exact toByteArray_write_read_back_of_gap spender (allowanceOwnerArgMem owner) 96
    (by rw [allowanceOwnerArgMem_size]; exact lt_usize 0 (by norm_num))

theorem allowanceInnerKeyMem_read32 (owner spender : UInt256) :
    (allowanceInnerKeyMem owner spender).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold allowanceInnerKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [allowanceSpenderArgMem_size owner spender]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray owner).size ≤ 32
    rw [toByteArray_size])

theorem allowanceInnerKeyMem_read96 (owner spender : UInt256) :
    (allowanceInnerKeyMem owner spender).readWithPadding 96 32 = UInt256.toByteArray spender := by
  unfold allowanceInnerKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 96 (by rw [toByteArray_size])
      (by rw [allowanceSpenderArgMem_size owner spender]; omega)
      (by omega)
      (by rw [allowanceSpenderArgMem_size owner spender])]
  exact allowanceSpenderArgMem_read96 owner spender

theorem allowanceInnerHashMem_read0 (owner spender : UInt256) :
    (allowanceInnerHashMem owner spender).readWithPadding 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold allowanceInnerHashMem
  exact wordAt0Mem_read0 ⟨1⟩ (allowanceInnerKeyMem owner spender)

theorem allowanceInnerHashMem_read32 (owner spender : UInt256) :
    (allowanceInnerHashMem owner spender).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold allowanceInnerHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [allowanceInnerKeyMem_size owner spender]; omega)
    (by omega)
    (by rw [allowanceInnerKeyMem_size owner spender]; omega)]
  exact allowanceInnerKeyMem_read32 owner spender

theorem allowanceInnerHashMem_read96 (owner spender : UInt256) :
    (allowanceInnerHashMem owner spender).readWithPadding 96 32 = UInt256.toByteArray spender := by
  unfold allowanceInnerHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 96 (by rw [toByteArray_size])
    (by rw [allowanceInnerKeyMem_size owner spender]; omega)
    (by omega)
    (by rw [allowanceInnerKeyMem_size owner spender])]
  exact allowanceInnerKeyMem_read96 owner spender

theorem allowanceInnerHashMem_read0_64 (owner spender : UInt256) :
    (allowanceInnerHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray (⟨1⟩ : UInt256) ++ UInt256.toByteArray owner := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [allowanceInnerHashMem_size owner spender]; omega)]
  have hleft :
      (allowanceInnerHashMem owner spender).extract 0 32 =
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [allowanceInnerHashMem_size owner spender]; omega),
      allowanceInnerHashMem_read0 owner spender]
  have hright :
      (allowanceInnerHashMem owner spender).extract 32 64 = UInt256.toByteArray owner := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [allowanceInnerHashMem_size owner spender]; omega),
      allowanceInnerHashMem_read32 owner spender]
  rw [show (allowanceInnerHashMem owner spender).extract 0 64 =
      (allowanceInnerHashMem owner spender).extract 0 32 ++
        (allowanceInnerHashMem owner spender).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem allowanceInnerKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    allowanceInnerSlotWord (allowanceOwnerWord I) (allowanceSpenderWord I) =
      erc20AllowanceOwnerSlot
        (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)) := by
  unfold allowanceInnerSlotWord
  rw [allowanceInnerHashMem_read0_64]
  unfold erc20AllowanceOwnerSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanonOwner]
  exact keccakSlot_eq _

theorem allowanceOuterKeyMem_read32 (owner spender : UInt256) :
    (allowanceOuterKeyMem owner spender).readWithPadding 32 32 =
      UInt256.toByteArray spender := by
  unfold allowanceOuterKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [allowanceInnerHashMem_size owner spender]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray spender).size ≤ 32
    rw [toByteArray_size])

theorem allowanceOuterHashMem_read0 (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).readWithPadding 0 32 =
      UInt256.toByteArray (allowanceInnerSlotWord owner spender) := by
  unfold allowanceOuterHashMem
  exact wordAt0Mem_read0 (allowanceInnerSlotWord owner spender) (allowanceOuterKeyMem owner spender)

theorem allowanceOuterHashMem_read32 (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).readWithPadding 32 32 =
      UInt256.toByteArray spender := by
  unfold allowanceOuterHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [allowanceOuterKeyMem_size owner spender]; omega)
    (by omega)
    (by rw [allowanceOuterKeyMem_size owner spender]; omega)]
  exact allowanceOuterKeyMem_read32 owner spender

theorem allowanceOuterHashMem_read0_64 (owner spender : UInt256) :
    (allowanceOuterHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray (allowanceInnerSlotWord owner spender) ++ UInt256.toByteArray spender := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [allowanceOuterHashMem_size owner spender]; omega)]
  have hleft :
      (allowanceOuterHashMem owner spender).extract 0 32 =
        UInt256.toByteArray (allowanceInnerSlotWord owner spender) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [allowanceOuterHashMem_size owner spender]; omega),
      allowanceOuterHashMem_read0 owner spender]
  have hright :
      (allowanceOuterHashMem owner spender).extract 32 64 = UInt256.toByteArray spender := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [allowanceOuterHashMem_size owner spender]; omega),
      allowanceOuterHashMem_read32 owner spender]
  rw [show (allowanceOuterHashMem owner spender).extract 0 64 =
      (allowanceOuterHashMem owner spender).extract 0 32 ++
        (allowanceOuterHashMem owner spender).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem allowanceOuterKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceOuterHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
          |>.readWithPadding 0 64)))
      = allowanceSlot I := by
  rw [allowanceOuterHashMem_read0_64, allowanceInnerKeccakSlot I hcanonOwner]
  unfold allowanceSlot erc20AllowanceSlot erc20AllowanceOwnerSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanonOwner,
    keyValueToWord_address_of_canonical _ hcanonSpender]
  exact keccakSlot_eq _

theorem allowanceReturnMem_size (owner spender val : UInt256) :
    (allowanceReturnMem owner spender val).size = 160 := by
  unfold allowanceReturnMem
  simpa [allowanceOuterHashMem_size] using
    write_end_size_from (UInt256.toByteArray val) (allowanceOuterHashMem owner spender) 0 32
      (by decide)
      (by rw [toByteArray_size])

theorem allowanceReturnMem_read128 (owner spender val : UInt256) :
    (allowanceReturnMem owner spender val).readWithPadding 128 32 = UInt256.toByteArray val := by
  unfold allowanceReturnMem
  exact toByteArray_write_read_back_of_gap val (allowanceOuterHashMem owner spender) 128
    (by rw [allowanceOuterHashMem_size]; exact lt_usize 0 (by norm_num))

macro "vyper_erc20_allowance_decode" : tactic =>
  `(tactic| native_decide)

theorem calldataSizeGuard68 {n : Nat} (hsz68 : 68 ≤ n) (hsize : n < UInt256.size) :
    UInt256.lt (UInt256.ofNat n) ⟨68⟩ = ⟨0⟩ := by
  have hnot : ¬ (UInt256.ofNat n < (⟨68⟩ : UInt256)) := by
    intro hlt
    have hltNat : (UInt256.ofNat n).toNat < (⟨68⟩ : UInt256).toNat := hlt
    have hn : (UInt256.ofNat n).toNat = n := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hsize
    rw [hn] at hltNat
    change n < 68 at hltNat
    omega
  unfold UInt256.lt UInt256.fromBool Bool.toUInt256
  rw [show decide (UInt256.ofNat n < (⟨68⟩ : UInt256)) = false from by
    exact decide_eq_false hnot]
  native_decide

theorem erc20X_allowanceFromEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨681⟩
      [allowanceSelectorWord] allowanceDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDret vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  obtain ⟨k, C, rd681⟩ := hreach
  have hslot := allowanceOuterKeccakSlot I hcanonOwner hcanonSpender
  have hsizeGuard := calldataSizeGuard68 (n := I.calldata.size) hsz68 hsize
  have hcanonOwnerGuard : UInt256.shiftRight (allowanceOwnerWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (allowanceOwnerWord I) hcanonOwner
  have hcanonSpenderGuard : UInt256.shiftRight (allowanceSpenderWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (allowanceSpenderWord I) hcanonSpender
  have rdBeforeLoad := evm_run rd681 with [
    jumpdest,
    raw push4 allowanceSelectorWord (by vyper_erc20_allowance_decode) (by evm_ov),
    dup2,
    xor,
    push2 ⟨797⟩,
    jumpiNT (by native_decide),
    push1 ⟨68⟩,
    calldatasize,
    lt,
    callvalue,
    lor,
    push2 ⟨801⟩,
    jumpiNT (by rw [hsizeGuard, hwv]; decide),
    push1 ⟨4⟩,
    calldataload,
    dup1,
    push1 ⟨160⟩,
    shr,
    push2 ⟨801⟩,
    jumpiNT (by simpa [allowanceOwnerWord, calldataWord] using hcanonOwnerGuard),
    push1 ⟨64⟩,
    raw mstore 6 (allowanceOwnerArgMem (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨36⟩,
    calldataload,
    dup1,
    push1 ⟨160⟩,
    shr,
    push2 ⟨801⟩,
    jumpiNT (by simpa [allowanceSpenderWord, calldataWord] using hcanonSpenderGuard),
    push1 ⟨96⟩,
    raw mstore 3 (allowanceSpenderArgMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨64⟩,
    raw mload 0 (allowanceOwnerWord I) (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := allowanceSpenderArgMem (allowanceOwnerWord I) (allowanceSpenderWord I))
          (aw := UInt256.ofNat 4) (off := ⟨64⟩) (v := allowanceOwnerWord I)
          (by rw [allowanceSpenderArgMem_size]; decide)
          (by decide)
          (allowanceSpenderArgMem_read64 (allowanceOwnerWord I) (allowanceSpenderWord I)))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (allowanceInnerKeyMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mstore 0 (allowanceInnerHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    push0,
    raw keccak256 0 (allowanceInnerSlotWord (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    dup1,
    push1 ⟨96⟩,
    raw mload 0 (allowanceSpenderWord I) (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := allowanceInnerHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
          (aw := UInt256.ofNat 4) (off := ⟨96⟩) (v := allowanceSpenderWord I)
          (by rw [allowanceInnerHashMem_size]; decide)
          (by decide)
          (allowanceInnerHashMem_read96 (allowanceOwnerWord I) (allowanceSpenderWord I)))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (allowanceOuterKeyMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mstore 0 (allowanceOuterHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    push0,
    raw keccak256 0 (allowanceSlot I) (UInt256.ofNat 4)
      (by vyper_erc20_allowance_decode)
      mem_cost
      hslot
      (by decide) (by evm_ov),
    swap1,
    pop]
  obtain ⟨k1, C1, rdAfterLoad⟩ :=
    rdBeforeLoad.sload (by vyper_erc20_allowance_decode) (by evm_ov)
  have rdBeforeReturn := evm_run rdAfterLoad with [
    push1 ⟨128⟩,
    raw mstore 3 (allowanceReturnMem (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceWord σ I)) (UInt256.ofNat 5)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    push1 ⟨128⟩]
  exact rdBeforeReturn.ret 0 (UInt256.toByteArray (allowanceWord σ I))
    (by vyper_erc20_allowance_decode)
    mem_cost
    (allowanceReturnMem_read128 (allowanceOwnerWord I) (allowanceSpenderWord I) (allowanceWord σ I))
    (by evm_ov)

theorem erc20AllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨681⟩
      [allowanceSelectorWord] allowanceDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd681⟩ := hreach
  have hsizeGuard := calldataSizeGuardShort (n := I.calldata.size) (m := 68)
    hsize (by norm_num [UInt256.size]) hshort
  have hsizeGuard68 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨68⟩ = ⟨1⟩ := by
    simpa using hsizeGuard
  have rd801 := evm_run rd681 with [
    jumpdest,
    raw push4 allowanceSelectorWord (by vyper_erc20_allowance_decode) (by evm_ov),
    dup2,
    xor,
    push2 ⟨797⟩,
    jumpiNT (by native_decide),
    push1 ⟨68⟩,
    calldatasize,
    lt,
    callvalue,
    lor,
    push2 ⟨801⟩,
    jumpiT (by rw [hwv, hsizeGuard68]; decide) (by vyper_erc20_allowance_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by norm_num)

theorem erc20AllowanceX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨681⟩
      [allowanceSelectorWord] allowanceDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd681⟩ := hreach
  have hsizeGuard := calldataSizeGuard68 (n := I.calldata.size) hsz68 hsize
  have hcanonGuard : UInt256.shiftRight (allowanceOwnerWord I) ⟨160⟩ ≠ ⟨0⟩ := by
    intro hzero
    exact hnc (u256_lt_addressModulus_of_shiftRight160_zero (allowanceOwnerWord I) hzero)
  have rd801 := evm_run rd681 with [
    jumpdest,
    raw push4 allowanceSelectorWord (by vyper_erc20_allowance_decode) (by evm_ov),
    dup2,
    xor,
    push2 ⟨797⟩,
    jumpiNT (by native_decide),
    push1 ⟨68⟩,
    calldatasize,
    lt,
    callvalue,
    lor,
    push2 ⟨801⟩,
    jumpiNT (by rw [hwv, hsizeGuard]; decide),
    push1 ⟨4⟩,
    calldataload,
    dup1,
    push1 ⟨160⟩,
    shr,
    push2 ⟨801⟩,
    jumpiT (by
      simp [allowanceOwnerWord, calldataWord]
      exact hcanonGuard) (by vyper_erc20_allowance_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20AllowanceX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨681⟩
      [allowanceSelectorWord] allowanceDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd681⟩ := hreach
  have hsizeGuard := calldataSizeGuard68 (n := I.calldata.size) hsz68 hsize
  have hcanonOwnerGuard : UInt256.shiftRight (allowanceOwnerWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (allowanceOwnerWord I) hcanonOwner
  have hcanonSpenderGuard : UInt256.shiftRight (allowanceSpenderWord I) ⟨160⟩ ≠ ⟨0⟩ := by
    intro hzero
    exact hnc (u256_lt_addressModulus_of_shiftRight160_zero (allowanceSpenderWord I) hzero)
  have rd801 := evm_run rd681 with [
    jumpdest,
    raw push4 allowanceSelectorWord (by vyper_erc20_allowance_decode) (by evm_ov),
    dup2,
    xor,
    push2 ⟨797⟩,
    jumpiNT (by native_decide),
    push1 ⟨68⟩,
    calldatasize,
    lt,
    callvalue,
    lor,
    push2 ⟨801⟩,
    jumpiNT (by rw [hwv, hsizeGuard]; decide),
    push1 ⟨4⟩,
    calldataload,
    dup1,
    push1 ⟨160⟩,
    shr,
    push2 ⟨801⟩,
    jumpiNT (by simpa [allowanceOwnerWord, calldataWord] using hcanonOwnerGuard),
    push1 ⟨64⟩,
    raw mstore 6 (allowanceOwnerArgMem (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_allowance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨36⟩,
    calldataload,
    dup1,
    push1 ⟨160⟩,
    shr,
    push2 ⟨801⟩,
    jumpiT (by
      simp [allowanceSpenderWord, calldataWord]
      exact hcanonSpenderGuard) (by vyper_erc20_allowance_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20AllowanceSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem allowanceSelectorWord_of_calldata {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ =
      allowanceSelectorWord := by
  have h := evmSelectorDecode hsz 0xdd 0x62 0xed 0x3e allowanceSelectorWord (by native_decide)
  rw [hsel] at h
  unfold UInt256.eq at h
  by_cases heq :
      allowanceSelectorWord =
        UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩
  · exact heq.symm
  · simp [heq] at h
    have hne : UInt256.ofNat 0 ≠ (⟨1⟩ : UInt256) := by decide
    exact False.elim (hne h)

theorem allowanceDispatchMem_mload0 :
    (if (⟨0⟩ : UInt256).toNat ≥ allowanceDispatchMem.size ∨
        (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (allowanceDispatchMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
      = (⟨681⟩ : UInt256) := by
  native_decide

theorem erc20X_allowanceReach {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨681⟩
      [allowanceSelectorWord] allowanceDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have hsz := erc20AllowanceSelector_size hsel
  have hword := allowanceSelectorWord_of_calldata (I := I) hsz hsel
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0,
    calldataload,
    push1 ⟨224⟩,
    shr,
    push1 ⟨2⟩,
    push1 ⟨7⟩,
    dup3,
    mod,
    push1 ⟨1⟩,
    shl,
    push2 ⟨805⟩,
    add,
    push1 ⟨30⟩]
  have rdBeforeCopy := by
    simpa [hword, allowanceSelectorWord] using rdBeforeCopy0
  have rdAfterCopy := rdBeforeCopy.codecopy 3 allowanceDispatchMem (UInt256.ofNat 1)
    (by vyper_erc20_allowance_decode)
    mem_cost
    (by native_decide)
    (by decide)
    (by evm_ov)
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨681⟩ (UInt256.ofNat 1)
      (by vyper_erc20_allowance_decode)
      mem_cost
      allowanceDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_allowance_decode) (by native_decide) (by evm_ov)⟩

theorem erc20Dispatch_allowance {cd : ByteArray}
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some ERC20.allowanceTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (contract := erc20Contract)
    (pre := [ERC20.approveTransition, ERC20.totalSupplyTransition, ERC20.transferFromTransition,
      ERC20.balanceOfTransition, ERC20.transferTransition])
    (post := [])
    (hfallback := rfl) (htr := rfl) ?_
    (by rw [selectorOf, vyperERC20AllowanceSelectorBytes]; exact hsel)
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, vyperERC20ApproveSelectorBytes, hcd]; decide
    · rw [selectorOf, vyperERC20TotalSupplySelectorBytes, hcd]; decide
    · rw [selectorOf, vyperERC20TransferFromSelectorBytes, hcd]; decide
    · rw [selectorOf, vyperERC20BalanceOfSelectorBytes, hcd]; decide
    · rw [selectorOf, vyperERC20TransferSelectorBytes, hcd]; decide

theorem erc20AllowanceBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨681⟩
      [allowanceSelectorWord] allowanceDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := erc20Dispatch_allowance (cd := I.calldata) hsel
  have hword : allowanceWord σ_evm I = allowanceWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (allowanceSlot I) ⟨0⟩
  have hbody :
      ExecTransitionBody vyperERC20Config erc20Contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (allowanceStore I)
        ERC20.allowanceTransition.body
        (.returned { contract := erc20Contract, locals := allowanceStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (allowanceWord σ_solm I).toNat))])) := by
    simpa [allowanceWord, allowanceSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using erc20AllowanceBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  have hsz4 := erc20AllowanceSelector_size hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus
    · by_cases hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus
      · have hdec0 := erc20Decode_allowance_ok (I := I) hsz68 hcanonOwner hcanonSpender
        have hdec :
            decodeCalldataWithMode vyperERC20Config.abiDecodeMode
              (ERC20.allowanceTransition.params.map Param.name)
              (transitionSignature ERC20.allowanceTransition).paramTypes I.calldata =
                some (allowanceStore I) := by
          simpa [vyperERC20Config] using hdec0
        exact (erc20X_allowanceFromEntry (g := Sat256.ofUInt256 g) hwv hsz68 hsize hcanonOwner
            hcanonSpender hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
            (returnEquiv_of_encode (ERC20.erc20Uint256ReturnEncoding (allowanceWord σ_evm I)))
      · have hdec0 := erc20Decode_allowance_none_noncanon_spender
            (I := I) hsz68 hcanonOwner hcanonSpender
        have hdec :
            decodeCalldataWithMode vyperERC20Config.abiDecodeMode
              (ERC20.allowanceTransition.params.map Param.name)
              (transitionSignature ERC20.allowanceTransition).paramTypes I.calldata = none := by
          simpa [vyperERC20Config] using hdec0
        exact (erc20AllowanceX_noncanon_spender (g := Sat256.ofUInt256 g)
            hwv hsz68 hsize hcanonOwner hcanonSpender hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hdec0 := erc20Decode_allowance_none_noncanon_owner (I := I) hsz68 hcanonOwner
      have hdec :
          decodeCalldataWithMode vyperERC20Config.abiDecodeMode
            (ERC20.allowanceTransition.params.map Param.name)
            (transitionSignature ERC20.allowanceTransition).paramTypes I.calldata = none := by
        simpa [vyperERC20Config] using hdec0
      exact (erc20AllowanceX_noncanon_owner (g := Sat256.ofUInt256 g)
          hwv hsz68 hsize hcanonOwner hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec0 := erc20Decode_allowance_none_short (I := I) hsz4 hshort
    have hdec :
        decodeCalldataWithMode vyperERC20Config.abiDecodeMode
          (ERC20.allowanceTransition.params.map Param.name)
          (transitionSignature ERC20.allowanceTransition).paramTypes I.calldata = none := by
      simpa [vyperERC20Config] using hdec0
    exact (erc20AllowanceX_shortarg (g := Sat256.ofUInt256 g) hwv hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem erc20AllowanceRuntimeSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20AllowanceBodyCore hcode hwv hsize hsel
    (erc20X_allowanceReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsel)
    hAccounts

end VyperERC20
