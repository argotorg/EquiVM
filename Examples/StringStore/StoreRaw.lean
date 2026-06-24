import Examples.StringStore.Clear

/-!
# StringStore — `storeRaw(bytes)` branch scaffolding

This module factors the dispatcher/reach facts and the Solm-side body execution for
`storeRaw(bytes)`.  The remaining runtime branch proof has to connect solc's ABI bytes decoder and
storage-copy bytecode to the same whole-`bytes` write summarized by `writeStorage?`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

theorem stringStoreDispatch_storeRaw {cd : ByteArray}
    (hsel : ((⟨#[0x68, 0xb3, 0x91, 0x68]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some storeRawTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x68, 0xb3, 0x91, 0x68]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [setTransition, appendToHistoryTransition, replaceFromHistoryTransition,
      dropLastTransition, clearCurrentTransition, clearAllTransition])
    (post := [currentLengthGetter, historyLengthGetter, rawLengthGetter]) rfl ?_
    (by rw [selectorOf, storeRawSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, setSelectorBytes, hcd]; decide
  · rw [selectorOf, appendToHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, replaceFromHistorySelectorBytes, hcd]; decide
  · rw [selectorOf, dropLastSelectorBytes, hcd]; decide
  · rw [selectorOf, clearCurrentSelectorBytes, hcd]; decide
  · rw [selectorOf, clearAllSelectorBytes, hcd]; decide

theorem stringStoreReachStoreRaw {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨286⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreLowMatches 3 (by omega) hsz hsel
  exact stringStoreReachLowBody 3 (by omega) ⟨286⟩ hcode hwv hsz hsize
    (stringStorePivotTaken 3 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem stringStoreReachStoreRawDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2975⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨307⟩, ⟨312⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k0, C0, hreach⟩ := stringStoreReachStoreRaw
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hsizeWord :
      (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size := by
    exact uadd_lit_usub_ofNat_lit hsz hsize
  exact ⟨_, _, by
    simpa [hsizeWord] using
      (evm_run hreach with [
      jumpdest, push2 ⟨312⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
        push2 ⟨307⟩, swap2, swap1, push2 ⟨2975⟩,
      jump (by jump_dest) ])⟩

theorem stringStoreX_storeRawDecoderHeadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (hshort : I.calldata.size < 36) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachStoreRawDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2997⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2996⟩, push2 ⟨2406⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_storeRawDecoderHeadHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachStoreRawDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2997⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2996⟩, push2 ⟨2406⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_storeRawDecoderOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachStoreRawDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa [ABI.solcMaxU64] using hoff)
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd3002 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2997⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd3011 := RD.pushConst rd3002 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd3011 with [
    dup2, gt, iszero, push2 ⟨3026⟩,
    jumpiNT (by rw [hgt']; decide),
    push2 ⟨3025⟩, push2 ⟨2410⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_bytesDecoder2890LengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2890⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨2911⟩,
    jumpiNT (by exact hstart),
    push2 ⟨2910⟩, push2 ⟨2718⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

set_option maxHeartbeats 1200000 in
theorem stringStoreX_storeRawDecoderLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachStoreRawDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hoffLeMax : (calldataWord I.calldata 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord I.calldata 4).toNat < 2 ^ 255 := by
    omega
  have hstart31ToNat :
      ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩).toNat) =
        4 + (calldataWord I.calldata 4).toNat + 31 := by
    have hoffSize : (calldataWord I.calldata 4).toNat < UInt256.size :=
      (calldataWord I.calldata 4).val.isLt
    have hoffOfNat :
        (UInt256.ofNat (calldataWord I.calldata 4).toNat).toNat =
          (calldataWord I.calldata 4).toNat :=
      ulit_toNat' _ hoffSize
    rw [← u256_ofNat_toNat (calldataWord I.calldata 4)]
    simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
      (b := (calldataWord I.calldata 4).toNat)
      (c := 31)
      (by norm_num [UInt256.size])
      (lt_size_of_lt_sign hoffSmall)
      (by norm_num [UInt256.size])
      (lt_size_of_lt_sign (by omega : 4 + (calldataWord I.calldata 4).toNat < 2 ^ 255))
      (lt_size_of_lt_sign (by omega :
        4 + (calldataWord I.calldata 4).toNat + 31 < 2 ^ 255)))
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · apply slt_lit_zero hsizeSign
      · rw [hstart31ToNat]
        omega
      · rw [hstart31ToNat]
        omega
    · apply slt_zero_of_left_low_right_high
      · rw [hstart31ToNat]
        omega
      · rw [ulit_toNat' I.calldata.size hsize]
        omega
  have rd3002 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2997⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd3011 := RD.pushConst rd3002 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd3026 := evm_run rd3011 with [
    dup2, gt, iszero, push2 ⟨3026⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd2890 := evm_run rd3026 with [
    jumpdest, push2 ⟨3038⟩, dup6, dup3, dup7, add, push2 ⟨2890⟩,
    jump (by jump_dest)]
  exact stringStoreX_bytesDecoder2890LengthShort rd2890
    (by simpa [calldataWord] using hstart) (by evm_ov)

theorem decodeCalldata_storeRaw_none_headShort {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (storeRawTransition.params.map Param.name)
      (transitionSignature storeRawTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen4 : ¬ I.calldata.toList.length < 4 := by
    omega
  have hnotRead : ¬ 32 ≤ I.calldata.toList.length - 4 := by
    omega
  have hread : ABI.readNat? (I.calldata.toList.drop 4) 0 = none := by
    unfold ABI.readNat? ABI.readWord? ABI.readBytes?
    simp [hnotRead]
  rw [if_neg hlen4]
  have hnotHuge :
      ¬ ([ABIType.bytes].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  rw [if_neg hnotHuge]
  change (match decodeCalldata.decodeArgs ["value"] [.bytes] (I.calldata.toList.drop 4) ∅ with
    | some (store, _) => some store
    | none => none) = none
  simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
    ABI.isDynamicABIType, hread, bind, Option.bind_none, Option.bind_some, if_true]

theorem decodeCalldata_storeRaw_none_offsetHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldata (storeRawTransition.params.map Param.name)
      (transitionSignature storeRawTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_offset_huge (x := "value") hsz36 hoff

theorem decodeCalldata_storeRaw_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (storeRawTransition.params.map Param.name)
      (transitionSignature storeRawTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_huge (x := "value") hbig

theorem decodeCalldata_storeRaw_none_lengthShort {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldata (storeRawTransition.params.map Param.name)
      (transitionSignature storeRawTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.bytes] I.calldata = none
  exact decodeCalldata_bytes_none_length_short (x := "value") hsz36 hhi hshort

theorem storeRawBodyReturns {evm evm' : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? stringStoreConfig evm { base := "raw", steps := [] } .bytes
        (.bytes value) = .ok evm') :
    ExecTransitionBody stringStoreConfig stringStoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) storeRawTransition.body
      (.returned
        { contract := stringStoreContract
          locals := (∅ : Store).insert "value" (.bytes value) }
        evm' (some emptyBytesKeccakValue)) := by
  let locals : Store := (∅ : Store).insert "value" (.bytes value)
  let solm : Frame := { contract := stringStoreContract, locals := locals }
  have hvar :
      evalExpr? stringStoreConfig solm evm (.var "value") = .ok (.bytes value) := by
    simp [solm, locals, evalExpr?, EvalResult.ofOption]
  have hrawLocal : locals["raw"]? = none := by
    simp [locals]
  have hwriteCfg :
      writeStorage?
          { storage := stringStoreStorageLayout
            externalABI := defaultExternalCallABI
            selfDeployment := genSolidityConstructorDeployment [] }
          evm { base := "raw" } .bytes (.bytes value) = .ok evm' := by
    simpa [stringStoreConfig] using hwrite
  have hassign :
      assignStorageRef? stringStoreConfig solm evm .storage rawRef (.bytes value) =
        .ok (solm, evm') := by
    simp [assignStorageRef?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, rawRef,
      storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, bytesSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure, solm, hrawLocal, hwriteCfg]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvar hassign) <|
        ExecBlock.consReturn (ExecStmt.return evalKeccakNewBytesZero)

theorem storeRawBodyRevertsOfWrite {evm : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? stringStoreConfig evm { base := "raw", steps := [] } .bytes
        (.bytes value) = .revert) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) storeRawTransition.body .reverted := by
  let locals : Store := (∅ : Store).insert "value" (.bytes value)
  let solm : Frame := { contract := stringStoreContract, locals := locals }
  have hvar :
      evalExpr? stringStoreConfig solm evm (.var "value") = .ok (.bytes value) := by
    simp [solm, locals, evalExpr?, EvalResult.ofOption]
  have hrawLocal : locals["raw"]? = none := by
    simp [locals]
  have hwriteCfg :
      writeStorage?
          { storage := stringStoreStorageLayout
            externalABI := defaultExternalCallABI
            selfDeployment := genSolidityConstructorDeployment [] }
          evm { base := "raw" } .bytes (.bytes value) = .revert := by
    simpa [stringStoreConfig] using hwrite
  have hassign :
      assignStorageRef? stringStoreConfig solm evm .storage rawRef (.bytes value) = .revert := by
    simp [assignStorageRef?, resolveStorageRef?, evalStorageRef, evalStorageRefSteps, rawRef,
      storageTypeAt?, stringStoreConfig, stringStoreContract, storageDecls, bytesSt,
      EvalResult.ofOption, EvalResult.bind, bind, pure, solm, hrawLocal, hwriteCfg]
  exact ExecFuncBody.execBlockRevert <|
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvar hassign)

theorem stringStoreStoreRawHeadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x68, 0xb3, 0x91, 0x68]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_storeRaw (cd := I.calldata) hsel'
  have hdec := decodeCalldata_storeRaw_none_headShort (I := I) hsz hshort
  have hrev := stringStoreX_storeRawDecoderHeadShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreStoreRawHeadHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x68, 0xb3, 0x91, 0x68]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_storeRaw (cd := I.calldata) hsel'
  have hdec := decodeCalldata_storeRaw_none_huge (I := I) hbig
  have hrev := stringStoreX_storeRawDecoderHeadHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hbig
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreStoreRawOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x68, 0xb3, 0x91, 0x68]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_storeRaw (cd := I.calldata) hsel'
  have hdec := decodeCalldata_storeRaw_none_offsetHuge (I := I) hsz36 hoff
  have hrev := stringStoreX_storeRawDecoderOffsetHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoff
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreStoreRawLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x68, 0xb3, 0x91, 0x68]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x68, 0xb3, 0x91, 0x68]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_storeRaw (cd := I.calldata) hsel'
  have hdec := decodeCalldata_storeRaw_none_lengthShort (I := I) hsz36 hhi hshort
  have hrev := stringStoreX_storeRawDecoderLengthShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

end StringStore
