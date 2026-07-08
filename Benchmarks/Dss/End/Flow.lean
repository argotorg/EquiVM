import Benchmarks.Dss.End.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `flow(bytes32)` transition -/

abbrev endFlowConcreteSelector : ByteArray := selectorBytes 0x4a 0x10 0xea 0xa6

abbrev endFlowIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endFlowIlkValue (I : ExecutionEnv) : Value := endBytes32ArgValue I

abbrev endFlowStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (endFlowIlkValue I)

abbrev endFlowIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endFlowFixEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "fix", steps := [.mindex (endFlowIlkKey I)] }

abbrev endFlowFixSlot (I : ExecutionEnv) : UInt256 := fixSlot (endFlowIlkKey I)

abbrev endFlowFixWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endFlowFixSlot I) σ I

abbrev endFlowDebtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨11⟩ σ I

abbrev endFlowEntryPc : UInt256 := ⟨635⟩
abbrev endFlowReturnPc : UInt256 := ⟨562⟩
abbrev endFlowDecodedPc : UInt256 := ⟨657⟩
abbrev endFlowBodyPc : UInt256 := ⟨2718⟩
abbrev endFlowFixDefinedRawWord : UInt256 :=
  ⟨0x456e642f6669782d696c6b2d616c72656164792d646566696e65640000000000⟩

theorem endFlowFixSlot_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    endFlowFixSlot I = solcMappingSlot ⟨15⟩ (endFlowIlkWord I) := by
  unfold endFlowFixSlot endFlowIlkKey fixSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem RD.endFlowFixDefinedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨2807⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
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
  have rdRaw := rdPrefix.pushConst endFlowFixDefinedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ endFlowFixDefinedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ endFlowFixDefinedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem endDecode_flow_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flowTransition.params.map Param.name)
      (transitionSignature flowTransition).paramTypes I.calldata = some (endFlowStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = _
  simpa [config, endFlowStore, endFlowIlkValue, endFlowIlkWord, bytes32, bytes32Width,
    abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36

theorem endDecode_flow_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (flowTransition.params.map Param.name)
      (transitionSignature flowTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = none
  simpa [config, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_none_short (cd := I.calldata) (x := "ilk") hsz4 hshort

theorem endReachFlowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endFlowConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endFlowEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x4a10eaa6⟩ :=
    endSelWord_eq_of_beq I hsz 0x4a 0x10 0xea 0xa6 ⟨0x4a10eaa6⟩
      (by native_decide)
      (by simpa [selIs, endFlowConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup403FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc 0))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endFlowEntryPc 0 hfirst
    (fun j hj => endGroup403ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem endFlowX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFlowEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endFlowEntryPc) (ret := endFlowReturnPc)
    (decoded := endFlowDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endFlowDecodedPc) (ret := endFlowReturnPc)
    (routine := endFlowBodyPc) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endFlowIlkWord, calldataWord] using hroutine⟩

theorem endFlowX_debtZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hdebt : endFlowDebtWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd2721 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2722raw⟩ := rd2721.sload (by native_decide) (by evm_ov)
  have hdebtRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨11⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endFlowDebtWord, endSlotWord, solcSlotWord] using hdebt
  have rd2722zero := rd2722raw
  rw [hdebtRaw] at rd2722zero
  obtain ⟨_, _, rd2722⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2722⟩
        (⟨0⟩ :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endFlowBodyPc] using rd2722zero⟩
  have rd2725 := rd2722.push2 ⟨2786⟩ (by native_decide) (by evm_ov)
  have rd2726 := rd2725.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rdTail⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2726⟩
        [endFlowIlkWord I, endFlowReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd2726⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2726⟩) (len := ⟨13⟩)
    (rawWord := ⟨5500907680949753345960233497199⟩) (shift := ⟨152⟩)
    (word := UInt256.shiftLeft ⟨5500907680949753345960233497199⟩ ⟨152⟩)
    (op := .PUSH13) (width := 13)
    rdTail
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFlowX_fixNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFlowBodyPc
      [endFlowIlkWord I, endFlowReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endFlowIlkWord I
  have hslot : endFlowFixSlot I = solcMappingSlot ⟨15⟩ key := by
    simpa [key] using endFlowFixSlot_eq (I := I) hsz36
  have rd2721 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨11⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2722raw⟩ := rd2721.sload (by native_decide) (by evm_ov)
  have rd2722 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2722⟩
        (endFlowDebtWord σ I :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endFlowDebtWord, endSlotWord, solcSlotWord] using rd2722raw⟩
  obtain ⟨_, _, rd2722⟩ := rd2722
  have rd2725 := rd2722.push2 ⟨2786⟩ (by native_decide) (by evm_ov)
  have rd2786 := rd2725.jumpiT (by native_decide) hdebt (by jump_dest) (by evm_ov)
  have rd2790pre := evm_run rd2786 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2791 := rd2790pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2796pre := evm_run rd2791 with [
    raw push1 ⟨15⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2797 := rd2796pre.mstore 0 (twoWordHashMem key ⟨15⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2800pre := evm_run rd2797 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨15⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨15⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨15⟩ key solcFreePtrMem_size
  have rd2801pre := rd2800pre.keccak256 0 (solcMappingSlot ⟨15⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2802raw⟩ := rd2801pre.sload (by native_decide) (by evm_ov)
  have rd2802 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2802⟩
        (endFlowFixWord σ I :: endFlowIlkWord I :: endFlowReturnPc :: sel :: [])
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    have hfixRaw :
        solcSlotWord σ I (solcMappingSlot ⟨15⟩ key) = endFlowFixWord σ I := by
      rw [← hslot]
      simp [endFlowFixWord, endSlotWord]
    exact ⟨_, _, by simpa [hfixRaw] using rd2802raw⟩
  obtain ⟨_, _, rd2802⟩ := rd2802
  have rd2803raw := rd2802.iszero (by native_decide) (by evm_ov)
  have hzero : UInt256.isZero (endFlowFixWord σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hfix
  have rd2803 := rd2803raw
  rw [hzero] at rd2803
  have rd2806 := rd2803.push2 ⟨2883⟩ (by native_decide) (by evm_ov)
  have rd2807 := rd2806.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rdTail⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2807⟩
        [endFlowIlkWord I, endFlowReturnPc, sel]
        (twoWordHashMem key ⟨15⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd2807⟩
  exact RD.endFlowFixDefinedRevert rdTail
    (twoWordHashMem_size_96 key ⟨15⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨15⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem evalStorageRef_endFlow_debt (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endFlowStore I } evm
      debtRef = .ok ({ base := "debt", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind]

theorem evalExpr_endFlow_debt (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.storage debtRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endFlowStore I })
    (slot := debtRef)
    (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int)
    (loc := wordLoc ⟨11⟩)
    (hbase := by simp [endFlowStore, debtRef])
    (her := evalStorageRef_endFlow_debt evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm ⟨11⟩)

theorem evalExpr_endFlow_debt_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage debtRef) = .ok (.int 0) := by
    simpa [hdebt] using evalExpr_endFlow_debt evm I
  have hzero :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem evalExpr_endFlow_debt_ne_true (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage debtRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) :=
    evalExpr_endFlow_debt evm I
  have hzero :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_ne_int_true hstorage hzero
  intro hbad
  apply hdebt
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem evalExpr_endFlow_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm (.var "ilk") =
      .ok (endFlowIlkValue I) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endFlowStore I).get? "ilk") =
    .ok (endFlowIlkValue I)
  rw [endFlowStore, store_get_self]
  rfl

theorem evalStorageRef_endFlow_fix (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endFlowStore I } evm
      (fixRef (.var "ilk")) = .ok (endFlowFixEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endFlow_ilk evm I
  simp [endFlowFixEvaledRef, endFlowIlkKey, hilk, endFlowIlkValue, endBytes32ArgValue,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, fixRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endFlow_fix (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.storage (fixRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endFlowFixSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endFlowStore I })
    (slot := fixRef (.var "ilk"))
    (er := endFlowFixEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endFlowFixSlot I))
    (hbase := by simp [endFlowStore, fixRef])
    (her := evalStorageRef_endFlow_fix evm I hsz36)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endFlowFixSlot I))

theorem evalExpr_endFlow_fix_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfix :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowFixSlot I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage (fixRef (.var "ilk"))) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endFlowFixSlot I)).toNat)) :=
    evalExpr_endFlow_fix evm I hsz36
  have hzero :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_eq_int_false hstorage hzero
  intro hbad
  apply hfix
  exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)

theorem endFlowBodyReverts_debtZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : endFlowDebtWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowDebtWord, endSlotWord, solcSlotWord] using hdebt
  have hguard :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endFlow_debt_ne_false evm0 I hdebtLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [flowTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endFlowStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage debtRef) (.intLit 0))
      (rest :=
        [ .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
          .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
          .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
          .internalCall "mul" [.var "num0", .intLit RAY] "num",
          .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
          .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
          .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endFlowBodyReverts_fixNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWord σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFlowStore I) flowTransition.body .reverted := by
  intro evm0
  have hdebtLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hdebt
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowDebtWord, endSlotWord, solcSlotWord] using hbad
  have hfixLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endFlowFixSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply hfix
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endFlowFixWord, endSlotWord, solcSlotWord] using hbad
  have hguardDebt :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFlow_debt_ne_true evm0 I hdebtLoad
  have hguardFix :
      evalExpr? config { contract := contract, locals := endFlowStore I } evm0
        (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endFlow_fix_eq_false evm0 I hsz36 hfixLoad
  have hblock :
      ExecBlock config { contract := contract, locals := endFlowStore I } evm0
        flowTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardDebt) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardFix)
  simpa [ExecTransitionBody, flowTransition, nonpayable, checkedExternalCallStmts, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem endFlowX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFlowEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endFlowEntryPc) (ret := endFlowReturnPc)
    (decoded := endFlowDecodedPc) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endFlowBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some flowTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endFlowEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endFlowX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_flow_none_short hsz4 hshort)

theorem endFlowBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf flowTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endFlowConcreteSelector := by
    simpa [endFlowSelectorBytes, endFlowConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endFlowConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some flowTransition :=
    endDispatchFlow hsel
  have hreach := endReachFlowBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_flow_ok (I := I) hsz36
    obtain ⟨_, _, hbodyReach⟩ :=
      endFlowX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hdebtCouple : endFlowDebtWord σ_evm I = endFlowDebtWord σ_solm I := by
      simpa [endFlowDebtWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
    by_cases hdebt : endFlowDebtWord σ_evm I = ⟨0⟩
    · have hdebtSolm : endFlowDebtWord σ_solm I = ⟨0⟩ := by
        rw [← hdebtCouple]
        exact hdebt
      have hbody :
          ExecTransitionBody config contract evmSolm (endFlowStore I)
            flowTransition.body .reverted := by
        simpa [evmSolm] using
          endFlowBodyReverts_debtZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hdebtSolm
      exact (endFlowX_debtZero (g := Sat256.ofUInt256 g) hdebt hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdebtSolm : endFlowDebtWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hdebt (by rw [hdebtCouple, hbad])
      have hfixCouple : endFlowFixWord σ_evm I = endFlowFixWord σ_solm I := by
        simpa [endFlowFixWord, endSlotWord] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner (endFlowFixSlot I) ⟨0⟩
      by_cases hfix : endFlowFixWord σ_evm I = ⟨0⟩
      · sorry
      · have hfixSolm : endFlowFixWord σ_solm I ≠ ⟨0⟩ := by
          intro hbad
          exact hfix (by rw [hfixCouple, hbad])
        have hbody :
            ExecTransitionBody config contract evmSolm (endFlowStore I)
              flowTransition.body .reverted := by
          simpa [evmSolm] using
            endFlowBodyReverts_fixNonzero
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hsz36 hdebtSolm hfixSolm
        exact (endFlowX_fixNonzero (g := Sat256.ofUInt256 g) hsz36 hdebt hfix hbodyReach)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endFlowBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
