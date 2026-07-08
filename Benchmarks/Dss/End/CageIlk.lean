import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `cage(bytes32)` transition -/

abbrev endCageIlkConcreteSelector : ByteArray := selectorBytes 0xe2 0x70 0x2f 0xdc

abbrev endCageIlkIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endCageIlkIlkValue (I : ExecutionEnv) : Value := endBytes32ArgValue I

abbrev endCageIlkStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (endCageIlkIlkValue I)

abbrev endCageIlkIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endCageIlkTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endCageIlkIlkKey I)] }

abbrev endCageIlkTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endCageIlkIlkKey I)

abbrev endCageIlkTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endCageIlkTagSlot I) σ I

abbrev endCageIlkLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨8⟩ σ I

abbrev endCageIlkLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

abbrev endCageIlkEntryPc : UInt256 := ⟨1171⟩
abbrev endCageIlkReturnPc : UInt256 := ⟨562⟩
abbrev endCageIlkDecodedPc : UInt256 := ⟨1193⟩
abbrev endCageIlkBodyPc : UInt256 := ⟨8832⟩
abbrev endCageIlkTagDefinedRawWord : UInt256 :=
  ⟨0x456e642f7461672d696c6b2d616c72656164792d646566696e65640000000000⟩

theorem endCageIlkTagSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endCageIlkTagSlot I = solcMappingSlot ⟨12⟩ (endCageIlkIlkWord I) := by
  unfold endCageIlkTagSlot endCageIlkIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem RD.endCageIlkTagDefinedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨8923⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst endCageIlkTagDefinedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ endCageIlkTagDefinedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ endCageIlkTagDefinedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem endDecode_cageIlk_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageIlkTransition.params.map Param.name)
      (transitionSignature cageIlkTransition).paramTypes I.calldata =
        some (endCageIlkStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = _
  simpa [config, endCageIlkStore, endCageIlkIlkValue, endCageIlkIlkWord,
    cageIlkTransition, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36

theorem endDecode_cageIlk_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (cageIlkTransition.params.map Param.name)
      (transitionSignature cageIlkTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = none
  simpa [config, cageIlkTransition, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_none_short (cd := I.calldata) (x := "ilk") hsz4 hshort

theorem endReachCageIlkBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endCageIlkConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endCageIlkEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xe2702fdc⟩ :=
    endSelWord_eq_of_beq I hsz 0xe2 0x70 0x2f 0xdc ⟨0xe2702fdc⟩
      (by native_decide)
      (by simpa [selIs, endCageIlkConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup114FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup114FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup114FirstArmPc 2))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endCageIlkEntryPc 2 hfirst
    (fun j hj => endGroup114ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endCageIlkX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCageIlkEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endCageIlkEntryPc)
    (ret := endCageIlkReturnPc) (decoded := endCageIlkDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endCageIlkDecodedPc) (ret := endCageIlkReturnPc)
    (routine := endCageIlkBodyPc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endCageIlkIlkWord, calldataWord] using hroutine⟩

theorem endCageIlkX_liveNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endCageIlkLiveWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd8835 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd8836raw⟩ := rd8835.sload (by native_decide) (by evm_ov)
  have rd8836 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8836⟩
        (endCageIlkLiveWord σ I :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [endCageIlkLiveWord, endSlotWord, solcSlotWord] using rd8836raw⟩
  obtain ⟨_, _, rd8836⟩ := rd8836
  have rd8837raw := rd8836.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endCageIlkLiveWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlive
  have rd8837 := rd8837raw
  rw [hzero] at rd8837
  have rd8840 := rd8837.push2 ⟨8902⟩ (by native_decide) (by evm_ov)
  have rd8841 := rd8840.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨8841⟩) (len := ⟨14⟩)
    (rawWord := ⟨0x456e642f7374696c6c2d6c697665⟩) (shift := ⟨144⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f7374696c6c2d6c697665⟩ ⟨144⟩)
    (op := .PUSH14) (width := 14)
    (by simpa using rd8841)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageIlkX_tagNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endCageIlkBodyPc
      [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endCageIlkIlkWord I
  have hslot : endCageIlkTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endCageIlkTagSlot_eq (I := I) hsz36
  have rd8835 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd8836raw⟩ := rd8835.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endCageIlkLiveWord, endSlotWord, solcSlotWord] using hlive
  have rd8836zero := rd8836raw
  rw [hliveRaw] at rd8836zero
  obtain ⟨_, _, rd8836⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8836⟩
        (⟨0⟩ :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endCageIlkBodyPc] using rd8836zero⟩
  have rd8837raw := rd8836.iszero (by native_decide) (by evm_ov)
  have rd8837 := rd8837raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8837
  have rd8840 := rd8837.push2 ⟨8902⟩ (by native_decide) (by evm_ov)
  have rd8902 := rd8840.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd8906pre := evm_run rd8902 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8907 := rd8906pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8912pre := evm_run rd8907 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd8913 := rd8912pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8916pre := evm_run rd8913 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd8917pre := rd8916pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd8918raw⟩ := rd8917pre.sload (by native_decide) (by evm_ov)
  have rd8918 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8918⟩
        (endCageIlkTagWord σ I :: endCageIlkIlkWord I :: endCageIlkReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    have htagRaw :
        solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = endCageIlkTagWord σ I := by
      rw [← hslot]
      simp [endCageIlkTagWord, endSlotWord]
    exact ⟨_, _, by simpa [htagRaw] using rd8918raw⟩
  obtain ⟨_, _, rd8918⟩ := rd8918
  have rd8919raw := rd8918.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endCageIlkTagWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne htag
  have rd8919 := rd8919raw
  rw [hzero] at rd8919
  have rd8922 := rd8919.push2 ⟨8999⟩ (by native_decide) (by evm_ov)
  have rd8923 := rd8922.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rdTail⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8923⟩
        [endCageIlkIlkWord I, endCageIlkReturnPc, sel]
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd8923⟩
  exact RD.endCageIlkTagDefinedRevert rdTail
    (twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalStorageRef_endCageIlk_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endCageIlkStore I } evm
      liveRef = .ok endCageIlkLiveEvaledRef := by
  simp [endCageIlkLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps,
    EvalResult.bind, pure, bind]

theorem evalExpr_endCageIlk_live_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endCageIlkStore I })
      (slot := liveRef)
      (er := endCageIlkLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [endCageIlkStore, liveRef])
      (her := evalStorageRef_endCageIlk_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 0) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_endCageIlk_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm (.var "ilk") =
      .ok (endCageIlkIlkValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endCageIlkStore I).get? "ilk") =
    .ok (endCageIlkIlkValue I)
  rw [endCageIlkStore, store_get_self]
  rfl

theorem evalStorageRef_endCageIlk_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endCageIlkStore I } evm
      (tagRef (.var "ilk")) = .ok (endCageIlkTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endCageIlk_ilk evm I
  simp [endCageIlkTagEvaledRef, endCageIlkIlkKey, hilk, endCageIlkIlkValue,
    endBytes32ArgValue, endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef,
    evalStorageRefSteps, evalStorageRefStep, tagRef, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endCageIlk_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endCageIlkTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endCageIlkStore I })
    (slot := tagRef (.var "ilk"))
    (er := endCageIlkTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endCageIlkTagSlot I))
    (hbase := by simp [endCageIlkStore, tagRef])
    (her := evalStorageRef_endCageIlk_tag evm I hsz36)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endCageIlkTagSlot I))

theorem evalExpr_endCageIlk_tag_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCageIlkTagSlot I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
      (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endCageIlkTagSlot I)).toNat)) :=
    evalExpr_endCageIlk_tag evm I hsz36
  have hzero :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_eq_int_false hstorage hzero
  intro hbad
  apply htag
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem endCageIlkBodyReverts_liveNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endCageIlkLiveWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hlive
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkLiveWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endCageIlk_live_zero_false evm0 I hliveLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageIlkTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endCageIlkStore I })
      (evm := evm0)
      (guard := .binary .eq (.storage liveRef) (.intLit 0))
      (rest :=
        [ .require (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .assign .storage (ArtRef (.var "ilk")) (.tupleGet (.var "vatIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "spotIlks" (.intLit 0) [.var "ilk"]
          "spotIlk" (perm := false) ++
        [ .letDecl "pip" (some addr) (.tupleGet (.var "spotIlk") 0) ] ++
        checkedExternalCallStmts (.storage spotRef) "par" (.intLit 0) [] "parV"
          (perm := false) ++
        checkedExternalCallStmts (.var "pip") "read" (.intLit 0) [] "pipRead"
          (perm := false) ++
        [ .internalCall "wdiv" [.var "parV", .cast (.var "pipRead") uint256St] "tagV",
          .assign .storage (tagRef (.var "ilk")) (.var "tagV") ])
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endCageIlkBodyReverts_tagNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hlive : endCageIlkLiveWord σ I = ⟨0⟩)
    (htag : endCageIlkTagWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endCageIlkStore I) cageIlkTransition.body
      .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkLiveWord, endSlotWord, solcSlotWord] using hlive
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endCageIlkTagSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply htag
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endCageIlkTagWord, endSlotWord, solcSlotWord] using hbad
  have hguardLive :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
          (.storage liveRef) = .ok (.int 0) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := endCageIlkStore I })
        (slot := liveRef)
        (er := endCageIlkLiveEvaledRef)
        (t := .int uint256Int)
        (loc := wordLoc ⟨8⟩)
        (value := .int 0)
        (hbase := by simp [endCageIlkStore, liveRef])
        (her := evalStorageRef_endCageIlk_live evm0 I)
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by simpa [hliveLoad] using endStorageLocLoad_uint256 evm0 ⟨8⟩)]
    have hzero :
        evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
          (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
    exact endEvalExpr_eq_int_true hstorage hzero rfl
  have hguardTag :
      evalExpr? config { contract := contract, locals := endCageIlkStore I } evm0
        (.binary .eq (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endCageIlk_tag_eq_false evm0 I hsz36 htagLoad
  have hblock :
      ExecBlock config { contract := contract, locals := endCageIlkStore I } evm0
        cageIlkTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardTag)
  simpa [ExecTransitionBody, cageIlkTransition, nonpayable, checkedExternalCallStmts, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem endCageIlkX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCageIlkEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endCageIlkEntryPc)
    (ret := endCageIlkReturnPc)
    (decoded := endCageIlkDecodedPc) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endCageIlkBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some cageIlkTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endCageIlkEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endCageIlkX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_cageIlk_none_short hsz4 hshort)

theorem endCageIlkBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf cageIlkTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endCageIlkConcreteSelector := by
    simpa [endCageIlkSelectorBytes, endCageIlkConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endCageIlkConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some cageIlkTransition :=
    endDispatchCageIlk hsel
  have hreach := endReachCageIlkBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_cageIlk_ok (I := I) hsz36
    obtain ⟨_, _, hbodyReach⟩ :=
      endCageIlkX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hliveCouple : endCageIlkLiveWord σ_evm I = endCageIlkLiveWord σ_solm I := by
      simpa [endCageIlkLiveWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    by_cases hlive : endCageIlkLiveWord σ_evm I = ⟨0⟩
    · have hliveSolm : endCageIlkLiveWord σ_solm I = ⟨0⟩ := by
        rw [← hliveCouple]
        exact hlive
      have htagCouple : endCageIlkTagWord σ_evm I = endCageIlkTagWord σ_solm I := by
        simpa [endCageIlkTagWord, endSlotWord] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner (endCageIlkTagSlot I) ⟨0⟩
      by_cases htag : endCageIlkTagWord σ_evm I = ⟨0⟩
      · sorry
      · have htagSolm : endCageIlkTagWord σ_solm I ≠ ⟨0⟩ := by
          intro hbad
          exact htag (by rw [htagCouple, hbad])
        have hbody :
            ExecTransitionBody config contract evmSolm (endCageIlkStore I)
              cageIlkTransition.body .reverted := by
          simpa [evmSolm] using
            endCageIlkBodyReverts_tagNonzero
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hsz36 hliveSolm htagSolm
        exact (endCageIlkX_tagNonzero (g := Sat256.ofUInt256 g) hsz36 hlive htag hbodyReach)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hliveSolm : endCageIlkLiveWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hlive (by rw [hliveCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (endCageIlkStore I)
            cageIlkTransition.body .reverted := by
        simpa [evmSolm] using
          endCageIlkBodyReverts_liveNonzero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hliveSolm
      exact (endCageIlkX_liveNonzero (g := Sat256.ofUInt256 g) hlive hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endCageIlkBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
