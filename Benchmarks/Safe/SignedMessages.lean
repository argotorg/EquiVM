import Benchmarks.Safe.Routines

/-! # Safe `signedMessages(bytes32)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

abbrev safeSignedMessagesArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev safeSignedMessagesKey (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev safeSignedMessagesValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (safeSignedMessagesArgBytes I)

abbrev safeSignedMessagesLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (safeSignedMessagesValue I)

abbrev safeSignedMessagesKeyValue (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (safeSignedMessagesArgBytes I)

abbrev safeSignedMessagesEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "signedMessages", steps := [.mindex (safeSignedMessagesKeyValue I)] }

abbrev safeSignedMessagesSlotFor (I : ExecutionEnv) : UInt256 :=
  signedMessagesSlot (safeSignedMessagesKeyValue I)

def safeSignedMessagesWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (safeSignedMessagesSlotFor I)

noncomputable def safeSignedMessagesHashMem (key : UInt256) : ByteArray :=
  wordAt0Mem key (wordAt32Mem ⟨7⟩ solcFreePtrMem)

theorem safeSignedMessagesArgBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (safeSignedMessagesArgBytes I).length = 32 := by
  simp [safeSignedMessagesArgBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem safeSignedMessagesKeyValue_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (safeSignedMessagesKeyValue I) = safeSignedMessagesKey I := by
  have hword :
      ABI.bytesToWord (safeSignedMessagesArgBytes I) = safeSignedMessagesKey I := by
    simpa [safeSignedMessagesArgBytes, safeSignedMessagesKey] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hbytes :
      EVM.Word.toBytesBE (safeSignedMessagesKey I) = safeSignedMessagesArgBytes I := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length (safeSignedMessagesArgBytes_length hsz36)
  rw [show safeSignedMessagesKeyValue I =
      .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (safeSignedMessagesKey I)) by
        simp [safeSignedMessagesKeyValue, bytes32Width, hbytes]]
  exact keyValueToWord_fixedBytes32 (safeSignedMessagesKey I)

theorem safeSignedMessagesSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    safeSignedMessagesSlotFor I = solcMappingSlot ⟨7⟩ (safeSignedMessagesKey I) := by
  unfold safeSignedMessagesSlotFor signedMessagesSlot mapSlot solcMappingSlot
  rw [safeSignedMessagesKeyValue_eq hsz36]

theorem safeSignedMessagesHashMem_size (key : UInt256) :
    (safeSignedMessagesHashMem key).size = 96 := by
  unfold safeSignedMessagesHashMem
  exact wordAt0Mem_size_96 key (wordAt32Mem_size_96 ⟨7⟩ solcFreePtrMem_size)

theorem wordAt32Mem_read32 (word : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (wordAt32Mem word mem).readWithPadding 32 32 = UInt256.toByteArray word := by
  unfold wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    toByteArray_extract_all]

theorem safeSignedMessagesHashMem_read32 (key : UInt256) :
    (safeSignedMessagesHashMem key).readWithPadding 32 32 = UInt256.toByteArray ⟨7⟩ := by
  unfold safeSignedMessagesHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [wordAt32Mem_size_96 ⟨7⟩ solcFreePtrMem_size]; omega) (by omega)
      (by rw [wordAt32Mem_size_96 ⟨7⟩ solcFreePtrMem_size]; omega)]
  exact wordAt32Mem_read32 ⟨7⟩ solcFreePtrMem_size

theorem safeSignedMessagesHashMem_read64 (key : UInt256) :
    (safeSignedMessagesHashMem key).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold safeSignedMessagesHashMem wordAt0Mem
  have hpres0 :
      ByteArray.readWithPadding
          ((UInt256.toByteArray key).write 0 (wordAt32Mem ⟨7⟩ solcFreePtrMem) 0 32)
          64 32 =
        (wordAt32Mem ⟨7⟩ solcFreePtrMem).readWithPadding 64 32 :=
    by
      refine write32_read_above _ _ _ _ ?_ ?_ ?_ ?_
      · rw [toByteArray_size]
      · rw [wordAt32Mem_size_96 ⟨7⟩ solcFreePtrMem_size]; omega
      · omega
      · rw [wordAt32Mem_size_96 ⟨7⟩ solcFreePtrMem_size]
  rw [hpres0]
  unfold wordAt32Mem
  have hpres32 :
      ByteArray.readWithPadding
          ((UInt256.toByteArray (⟨7⟩ : UInt256)).write 0 solcFreePtrMem 32 32)
          64 32 =
        solcFreePtrMem.readWithPadding 64 32 :=
    by
      refine write32_read_above _ _ _ _ ?_ ?_ ?_ ?_
      · rw [toByteArray_size]
      · rw [solcFreePtrMem_size]; omega
      · omega
      · rw [solcFreePtrMem_size]
  rw [hpres32]
  exact solcFreePtrMem_read64

theorem safeSignedMessagesHashMem_read0_64 (key : UInt256) :
    (safeSignedMessagesHashMem key).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray ⟨7⟩ := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [safeSignedMessagesHashMem_size key]; omega)]
  have hleft :
      (safeSignedMessagesHashMem key).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [safeSignedMessagesHashMem_size key]; omega)]
    exact wordAt0Mem_read0 key (wordAt32Mem ⟨7⟩ solcFreePtrMem)
  have hright :
      (safeSignedMessagesHashMem key).extract 32 64 = UInt256.toByteArray ⟨7⟩ := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [safeSignedMessagesHashMem_size key]; omega),
      safeSignedMessagesHashMem_read32 key]
  rw [show (safeSignedMessagesHashMem key).extract 0 64 =
      (safeSignedMessagesHashMem key).extract 0 32 ++
        (safeSignedMessagesHashMem key).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem safeSignedMessagesHashMem_slot (key : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((safeSignedMessagesHashMem key).readWithPadding 0 64))) =
      solcMappingSlot ⟨7⟩ key := by
  rw [safeSignedMessagesHashMem_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single key ⟨7⟩

theorem safeDecode_signedMessages_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (signedmessagesTransition.params.map Param.name)
      (transitionSignature signedmessagesTransition).paramTypes I.calldata =
        some (safeSignedMessagesLocals I) := by
  simpa [config, safeDecodeMode, signedmessagesTransition, safeSignedMessagesValue,
    safeSignedMessagesArgBytes, safeSignedMessagesLocals, bytes32, bytes32Width] using
      (decodeCalldata_bytes32_ok (cd := I.calldata) (x := "arg0") hsz36 hsmall)

theorem safeDecode_signedMessages_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (signedmessagesTransition.params.map Param.name)
      (transitionSignature signedmessagesTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, signedmessagesTransition, bytes32, bytes32Width] using
    (decodeCalldata_bytes32_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem safeDecode_signedMessages_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (signedmessagesTransition.params.map Param.name)
      (transitionSignature signedmessagesTransition).paramTypes I.calldata = none := by
  simpa [config, safeDecodeMode, signedmessagesTransition, bytes32, bytes32Width] using
    (decodeCalldata_bytes32_none_huge (cd := I.calldata) (x := "arg0") hbig)

theorem safeSignedMessagesDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k' C', RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨957⟩
      [safeSignedMessagesKey I, ⟨974⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k' C' := by
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsmall hsize
  have h9894 := h.push2 ⟨974⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨957⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9894⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9903 := h9894.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9903' := h9903
  rw [hlt] at h9903'
  have h9906 := h9903'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9910⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h9906
  have h9910 := h9906.jumpiT (by native_decide) (by decide) (by native_decide)
    (by evm_ov)
  have h9916 := h9910.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [safeSignedMessagesKey, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using h9916.jump (by native_decide) (by native_decide) (by evm_ov)⟩

theorem safeSignedMessagesDecodeReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD safeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩) :
    RDrev safeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h9894 := h.push2 ⟨974⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨957⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨9894⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  have h9903 := h9894.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
  have h9903' := h9903
  rw [hlt] at h9903'
  have h9906 := h9903'
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨9910⟩ (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at h9906
  have h9907 := h9906.jumpiNT (by native_decide) (by decide) (by evm_ov)
  exact h9907.revertStub (by native_decide) (by native_decide) (by native_decide)
    (by evm_ov)

theorem safeSignedMessagesX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (safeSelBytes 28)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (safeSignedMessagesWord σ I)) := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h931⟩ := safeReachSignedMessagesBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h944⟩ := safeGuardPeelOk (gt := ⟨942⟩) h931 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  obtain ⟨_, _, h957⟩ := safeSignedMessagesDecodeOk h944 hsz36 hsmall hsize
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((safeSignedMessagesHashMem (safeSignedMessagesKey I)).readWithPadding 0 64))) =
        safeSignedMessagesSlotFor I := by
    rw [safeSignedMessagesSlotFor_eq hsz36]
    exact safeSignedMessagesHashMem_slot (safeSignedMessagesKey I)
  have h963 := h957.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨7⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have h964 := h963.mstore 0 (wordAt32Mem ⟨7⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have h966 := h964.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
  have h967 := h966.mstore 0 (safeSignedMessagesHashMem (safeSignedMessagesKey I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have h970 := h967.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have h971 := h970.keccak256 0 (safeSignedMessagesSlotFor I) (UInt256.ofNat 3)
    (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, h972⟩ := h971.sload (by native_decide) (by evm_ov)
  have h974 := h972.dup2 (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  exact RD.safeReturnWordFromScratchMem974
    (by simpa [safeSignedMessagesWord] using h974)
    (safeSignedMessagesHashMem_size (safeSignedMessagesKey I))
    (safeSignedMessagesHashMem_read64 (safeSignedMessagesKey I)) (by simp)

theorem safeSignedMessagesBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I)
      (safeSignedMessagesLocals I) signedmessagesTransition.body
      (.returned { contract := contract, locals := safeSignedMessagesLocals I }
        (initState cA gh bl σ σ₀ g A I)
        (some [(.int (Int.ofNat (safeSignedMessagesWord σ I).toNat))])) := by
  let locals : Store := safeSignedMessagesLocals I
  refine nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
    (by simp only [initState]; exact hwv) ?_
  show evalExpr? config { contract := contract, locals := locals }
    (initState cA gh bl σ σ₀ g A I) (.storage (signedMessagesRef (.var "arg0"))) =
      .ok (.int (Int.ofNat (safeSignedMessagesWord σ I).toNat))
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := signedMessagesRef (.var "arg0"))
    (er := safeSignedMessagesEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (safeSignedMessagesSlotFor I) (.int uint256Int))
    (value := .int (Int.ofNat (safeSignedMessagesWord σ I).toNat))
    (hbase := by simp [signedMessagesRef, locals, safeSignedMessagesLocals])
    (her := by
      have hlen : (safeSignedMessagesArgBytes I).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using safeSignedMessagesArgBytes_length (I := I) hsz36
      simp [safeSignedMessagesEvaledRef, safeSignedMessagesValue, locals,
        safeSignedMessagesKeyValue, safeSignedMessagesArgBytes, hlen,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, signedMessagesRef,
        evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [safeSignedMessagesWord] using
        safeStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I)
          (safeSignedMessagesSlotFor I))]

theorem safeSignedMessagesBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hsel : selIs I (safeSelBytes 28))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : safeSignedMessagesWord σ_evm I = safeSignedMessagesWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (safeSignedMessagesSlotFor I) ⟨0⟩
  exact safeReEquivExecTransport hcode
    (safeSignedMessagesX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hsmall hsize hsel)
    (safeSelectorDispatchSignedMessages hsel)
    (safeDecode_signedMessages_ok hsz36 hsmall)
    (safeSignedMessagesBodyReturns hwv hsz36) (by rw [← hword])
    hAccounts
    (returnEquiv_of_encode
      (by simpa [uint256] using
        uint256ReturnEncoding (safeSignedMessagesWord σ_evm I)))

theorem safeSignedMessagesBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36) (hsel : selIs I (safeSelBytes 28)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h931⟩ := safeReachSignedMessagesBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h944⟩ := safeGuardPeelOk (gt := ⟨942⟩) h931 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact safeReEquivDecodeFailed hcode (safeSignedMessagesDecodeReverts h944 hlt)
    (safeSelectorDispatchSignedMessages hsel)
    (safeDecode_signedMessages_none_short hsz4 hshort)

theorem safeSignedMessagesBodyCoreDecodeFailed_huge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsel : selIs I (safeSelBytes 28)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h931⟩ := safeReachSignedMessagesBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hsz4 hsize hsel
  obtain ⟨_, _, h944⟩ := safeGuardPeelOk (gt := ⟨942⟩) h931 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have hlt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact safeReEquivDecodeFailed hcode (safeSignedMessagesDecodeReverts h944 hlt)
    (safeSelectorDispatchSignedMessages hsel)
    (safeDecode_signedMessages_none_huge hbig)

theorem safeSignedMessagesBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 28))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 28) (by native_decide) hsel
    by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · by_cases hsz36 : 36 ≤ I.calldata.size
      · exact safeSignedMessagesBodyCoreOk hcode hsize hwv hsz36 hsmall hsel hAccounts
      · exact safeSignedMessagesBodyCoreDecodeFailed_short hcode hsize hwv hsz4 (by omega)
          hsel
    · exact safeSignedMessagesBodyCoreDecodeFailed_huge hcode hsize hwv hsz4 (by omega) hsel
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 28) (by native_decide) hsel
    obtain ⟨_, _, h931⟩ := safeReachSignedMessagesBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode
      hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨942⟩) h931 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchSignedMessages hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
