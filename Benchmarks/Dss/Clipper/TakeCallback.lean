import Benchmarks.Dss.Clipper.TakeVatMoveSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeWhoAddressOfMaskEq {I : ExecutionEnv} {target : UInt256}
    (hwho : UInt256.land (clipperTakeWhoWord I) solcAddrMask = target) :
    AccountAddress.ofNat (clipperTakeWhoWord I).toNat =
      AccountAddress.ofNat target.toNat := by
  have hval := solcAddressValue_masked (clipperTakeWhoWord I)
  rw [u256_land_comm solcAddrMask (clipperTakeWhoWord I), hwho] at hval
  simpa using hval

theorem clipperTakeWhoAddressVatOfMaskEq (v : ClipperImmutables) {I : ExecutionEnv}
    (hwho : UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v) :
    AccountAddress.ofNat (clipperTakeWhoWord I).toNat = v.vat := by
  rw [clipperTakeWhoAddressOfMaskEq hwho]
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact clipperTakeVatTargetAddress v

theorem clipperEvalTakeDataLength (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat (bytesLength "data") =
        .ok (.int (Int.ofNat (clipperTakeDataBytes I).length)) := by
  simp only [bytesLength, localRef, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  rw [clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_ne _ _ (by decide),
    clipperTakeLocalsSt, store_get_ne _ _ (by decide),
    clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_self]
  change EvalResult.ok
      (Value.int (Int.ofNat (ByteArray.mk (clipperTakeDataBytes I).toArray).size)) =
    EvalResult.ok (Value.int (Int.ofNat (clipperTakeDataBytes I).length))
  rw [show (ByteArray.mk (clipperTakeDataBytes I).toArray).size =
      (clipperTakeDataBytes I).length by
    simp only [ByteArray.size]
    simp]

theorem clipperEvalTakeWhoAtDogLoaded (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat (.var "who") =
        .ok (.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
    clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
    clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
    clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
    clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
    clipperTakeLocalsTab, store_get_ne _ _ (by decide),
    clipperTakeLocalsLot, store_get_ne _ _ (by decide),
    clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
    clipperTakeLocalsDone, store_get_ne _ _ (by decide),
    clipperTakeLocalsSt, store_get_ne _ _ (by decide),
    clipperTakeLocalsTic, store_get_ne _ _ (by decide),
    clipperTakeLocalsUsr, store_get_ne _ _ (by decide),
    clipperTakeStore, store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalTakeDogAtDogLoaded (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat (.var "dog_") =
        .ok (.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat)) := by
  simp only [evalExpr?]
  rw [clipperTakeLocalsDogLoaded, store_get_self]
  rfl

theorem clipperEvalTakeCallbackGuardWhoVat (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hwho : UInt256.land (clipperTakeWhoWord I) solcAddrMask = clipperTakeVatTarget v) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) =
        .ok (.bool false) := by
  have hwhoAddr := clipperTakeWhoAddressVatOfMaskEq v hwho
  have hlen := clipperEvalTakeDataLength v evmLoc evmRead evmVat I price slice owe0 owe
    slice' tabNew lotNew
  have hwhoEval := clipperEvalTakeWhoAtDogLoaded v evmLoc evmRead evmVat I price slice
    owe0 owe slice' tabNew lotNew
  have hwhoGet := hwhoEval
  simp only [evalExpr?] at hwhoGet
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hlen]
  by_cases hpos : 0 < (clipperTakeDataBytes I).length
  · have hgt :
        evalBinaryOp? .gt (.int (Int.ofNat (clipperTakeDataBytes I).length))
          (.int 0) = .ok (.bool true) := by
        cases hlen' : (clipperTakeDataBytes I).length with
        | zero =>
            omega
        | succ n =>
            simp only [evalBinaryOp?]
            change EvalResult.ok
                (Value.bool (decide (Int.ofNat (Nat.succ n) > 0))) =
              EvalResult.ok (Value.bool true)
            rw [show decide (Int.ofNat (Nat.succ n) > 0) = true by
              rw [decide_eq_true]
              norm_num]
    simp only [hgt]
    rw [hwhoGet, clipperEvalVat]
    rw [hwhoAddr]
    dsimp [evalBinaryOp?]
    simp
  · have hgt :
        evalBinaryOp? .gt (.int (Int.ofNat (clipperTakeDataBytes I).length))
          (.int 0) = .ok (.bool false) := by
        have hzero : (clipperTakeDataBytes I).length = 0 := Nat.eq_zero_of_not_pos hpos
        rw [hzero]
        native_decide
    simp only [hgt]

theorem clipperEvalTakeCallbackGuardWhoDog (v : ClipperImmutables)
    (evmLoc evmRead evmVat : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hwho :
      UInt256.land (clipperTakeWhoWord I) solcAddrMask =
        UInt256.land (clipperTakeDogEVMWord evmVat) solcAddrMask) :
    evalExpr? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDogLoaded evmLoc evmRead evmVat I price slice owe0 owe slice'
          tabNew lotNew))
      evmVat
      (.binary .and
        (.binary .gt (bytesLength "data") (.intLit 0))
        (.binary .and
          (.binary .ne (.var "who") (vatExpr v))
          (.binary .ne (.var "who") (.var "dog_")))) =
        .ok (.bool false) := by
  have hwhoAddr :
      Solm.Value.address (AccountAddress.ofNat (clipperTakeWhoWord I).toNat) =
        Solm.Value.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat) := by
    rw [solcAddressValue_masked (clipperTakeWhoWord I),
      solcAddressValue_masked (clipperTakeDogEVMWord evmVat),
      u256_land_comm solcAddrMask (clipperTakeWhoWord I),
      u256_land_comm solcAddrMask (clipperTakeDogEVMWord evmVat), hwho]
  have hlen := clipperEvalTakeDataLength v evmLoc evmRead evmVat I price slice owe0 owe
    slice' tabNew lotNew
  have hwhoEval := clipperEvalTakeWhoAtDogLoaded v evmLoc evmRead evmVat I price slice
    owe0 owe slice' tabNew lotNew
  have hdogEval := clipperEvalTakeDogAtDogLoaded v evmLoc evmRead evmVat I price slice
    owe0 owe slice' tabNew lotNew
  have hwhoGet := hwhoEval
  have hdogGet := hdogEval
  simp only [evalExpr?] at hwhoGet hdogGet
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hlen]
  by_cases hpos : 0 < (clipperTakeDataBytes I).length
  · have hgt :
        evalBinaryOp? .gt (.int (Int.ofNat (clipperTakeDataBytes I).length))
          (.int 0) = .ok (.bool true) := by
        cases hlen' : (clipperTakeDataBytes I).length with
        | zero =>
            omega
        | succ n =>
            simp only [evalBinaryOp?]
            change EvalResult.ok
                (Value.bool (decide (Int.ofNat (Nat.succ n) > 0))) =
              EvalResult.ok (Value.bool true)
            rw [show decide (Int.ofNat (Nat.succ n) > 0) = true by
              rw [decide_eq_true]
              norm_num]
    simp only [hgt]
    rw [hwhoGet, clipperEvalVat, hdogGet, hwhoAddr]
    dsimp [evalBinaryOp?]
    cases hvat :
        (Value.address (AccountAddress.ofNat (clipperTakeDogEVMWord evmVat).toNat) ==
          Value.address v.vat) <;> simp
  · have hgt :
        evalBinaryOp? .gt (.int (Int.ofNat (clipperTakeDataBytes I).length))
          (.int 0) = .ok (.bool false) := by
        have hzero : (clipperTakeDataBytes I).length = 0 := Nat.eq_zero_of_not_pos hpos
        rw [hzero]
        native_decide
    simp only [hgt]

theorem clipperTakeVatPatchPayload4441 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 4441 4473 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑v.vat : Nat))
  have hpost :
      PatchesWindowDisjoint32 4441 4473
        [(4751, vatBytes), (5115, vatBytes), (6295, vatBytes), (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | hfalse
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes), (1463, vatBytes), (2437, vatBytes), (3145, vatBytes),
        (4318, vatBytes)])
    (post := [(4751, vatBytes), (5115, vatBytes), (6295, vatBytes), (7936, vatBytes)])
    (off := 4441) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperTakeVatPush32Decode4440 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨4440⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (clipperRuntimePatchesWindowDisjoint32Bool v (⟨4440⟩ : UInt256).toNat
      ((⟨4440⟩ : UInt256).toNat + 1) (by native_decide))]
  norm_num
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 4441 4473), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32))
  rw [clipperTakeVatPatchPayload4441 v hpatch]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem RD.clipperTakeSkipClipperCallWhoVat {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice owe tabNew lotNew tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨4414⟩
      (⟨260⟩ :: clipperTakeVatFluxSelectorWord :: clipperTakeVatTarget v ::
        slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k C)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask = clipperTakeVatTarget v)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4701⟩
      (UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask ::
        slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k' C' := by
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hwhoVat' : UInt256.land solcAddrMask who = clipperTakeVatTarget v := by
    simpa [u256_land_comm] using hwhoVat
  have rd4417pre := evm_run rd with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd4418raw⟩ := rd4417pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd4438pre := evm_run rd4418raw with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4494⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4439 := rd4438pre.jumpiNT (by clipper_runtime_decode)
    (isZero_eq_zero_of_ne hdataLen) (by evm_ov)
  have rd4440 := evm_run rd4439 with [
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd4473 := rd4440.pushConst vatWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [vatWord] using clipperTakeVatPush32Decode4440 v hpatch)
    (by evm_ov)
  have rd4494pre := evm_run rd4473 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup13 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4494pre
  rw [show UInt256.land solcAddrMask vatWord = clipperTakeVatTarget v from by rfl]
    at rd4494pre
  rw [hwhoVat', u256_eq_refl] at rd4494pre
  have rd4500pre := evm_run rd4494pre with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4524⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4524 := rd4500pre.jumpiT (by clipper_runtime_decode) (by native_decide)
    (clipperTakeJumpDest4524 v hpatch) (by evm_ov)
  have rd4529pre := evm_run rd4524 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4701⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4701 := rd4529pre.jumpiT (by clipper_runtime_decode) (by native_decide)
    (clipperTakeJumpDest4701 v hpatch) (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_land_comm] using rd4701⟩

theorem RD.clipperTakeSkipClipperCallWhoDog {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {price slice owe tabNew lotNew tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨4414⟩
      (⟨260⟩ :: clipperTakeVatFluxSelectorWord :: clipperTakeVatTarget v ::
        slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k C)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hwhoVat : UInt256.land who solcAddrMask ≠ clipperTakeVatTarget v)
    (hwhoDog :
      UInt256.land who solcAddrMask =
        UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4701⟩
      (UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask ::
        slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k' C' := by
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hwhoVat' : UInt256.land solcAddrMask who ≠ clipperTakeVatTarget v := by
    intro h
    exact hwhoVat (by simpa [u256_land_comm] using h)
  have hwhoDog' :
      UInt256.land solcAddrMask who =
        UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask := by
    simpa [u256_land_comm] using hwhoDog
  have hdogClean :
      UInt256.land (UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩)) solcAddrMask =
        UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (solcSlotWord σ ee ⟨1⟩)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (solcSlotWord σ ee ⟨1⟩))
  have hdogCleanLeft :
      UInt256.land solcAddrMask (UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩)) =
        UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (UInt256.land solcAddrMask (solcSlotWord σ ee ⟨1⟩))]
    exact hdogClean
  have heqVat :
      UInt256.eq (UInt256.land solcAddrMask who) (clipperTakeVatTarget v) = ⟨0⟩ :=
    u256_eq_of_ne hwhoVat'
  have rd4417pre := evm_run rd with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd4418raw⟩ := rd4417pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd4438pre := evm_run rd4418raw with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4494⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4439 := rd4438pre.jumpiNT (by clipper_runtime_decode)
    (isZero_eq_zero_of_ne hdataLen) (by evm_ov)
  have rd4440 := evm_run rd4439 with [
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd4473 := rd4440.pushConst vatWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [vatWord] using clipperTakeVatPush32Decode4440 v hpatch)
    (by evm_ov)
  have rd4494pre := evm_run rd4473 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup13 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4494pre
  rw [show UInt256.land solcAddrMask vatWord = clipperTakeVatTarget v from by rfl]
    at rd4494pre
  rw [heqVat] at rd4494pre
  have rd4500pre := evm_run rd4494pre with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4524⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4501 := rd4500pre.jumpiNT (by clipper_runtime_decode) (by native_decide)
    (by evm_ov)
  have rd4524pre := evm_run rd4501 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup13 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4524pre
  rw [hwhoDog', hdogCleanLeft, u256_eq_refl] at rd4524pre
  have rd4529pre := evm_run rd4524pre with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4701⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4701 := rd4529pre.jumpiT (by clipper_runtime_decode) (by native_decide)
    (clipperTakeJumpDest4701 v hpatch) (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_land_comm] using rd4701⟩

end Benchmarks.Dss.Clipper
