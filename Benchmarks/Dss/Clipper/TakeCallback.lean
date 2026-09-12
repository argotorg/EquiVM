import Benchmarks.Dss.Clipper.TakeVatMoveSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: `DUP12`/`DUP16` stepping primitives, analogous to the existing
-- `DUP13`--`DUP15` helpers in `Reasoning.Stepping`.
theorem clipperDup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s
          (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length -
          12 + 13 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem clipperDup16_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s
          (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
            mm :: nn :: oo :: pp :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
          nn :: oo :: pp :: t).length - 16 + 17 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

theorem RD.clipperDup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs =>
    Reasoning.Theory.clipperDup12_xstep hc hp hdec hs hov)

theorem RD.clipperDup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none)) (hov : t.length + 17 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
        nn :: oo :: pp :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs =>
    Reasoning.Theory.clipperDup16_xstep hc hp hdec hs hov)

end Reasoning.Reach

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
        [(4751, vatBytes), (5115, vatBytes), (6295, vatBytes), (7936, vatBytes),
          (1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
          (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
          (8747, ilkBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | hfalse
    all_goals first | (unfold PatchWindowDisjoint32; omega) | cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes)])
    (post :=
      [(4751, vatBytes), (5115, vatBytes), (6295, vatBytes), (7936, vatBytes),
        (1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes)])
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

/-- Reach the callback calldata builder when `data` is nonempty and `who` is neither the vat nor
the cached dog address.  Keeping this guard trace separate lets all callback outcomes share the
same ABI-encoding proof. -/
theorem RD.clipperTakeClipperCallGuardTrue {code : ByteArray}
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
      UInt256.land who solcAddrMask ≠
        UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4530⟩
      (UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask ::
        slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw o (cA, σ) k' C' := by
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hwhoVat' : UInt256.land solcAddrMask who ≠ clipperTakeVatTarget v := by
    simpa [u256_land_comm] using hwhoVat
  have hwhoDog' :
      UInt256.land solcAddrMask who ≠
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
  have heqDog :
      UInt256.eq (UInt256.land solcAddrMask who)
          (UInt256.land (solcSlotWord σ ee ⟨1⟩) solcAddrMask) = ⟨0⟩ :=
    u256_eq_of_ne hwhoDog'
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
  rw [show UInt256.land solcAddrMask vatWord = clipperTakeVatTarget v from by rfl,
    heqVat] at rd4494pre
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
  rw [hdogCleanLeft, heqDog] at rd4524pre
  have rd4529pre := evm_run rd4524pre with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4701⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_land_comm] using
      rd4529pre.jumpiNT (by clipper_runtime_decode) (by native_decide) (by evm_ov)⟩

abbrev clipperTakeCallbackSelectorSeed : UInt256 := ⟨2220015886⟩

abbrev clipperTakeCallbackSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperTakeCallbackSelectorSeed ⟨224⟩

noncomputable def clipperTakeCallbackSelectorMem (mem : ByteArray) : ByteArray :=
  clipperTakeCallbackSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperTakeCallbackSenderMem (ee : ExecutionEnv) (mem : ByteArray) :
    ByteArray :=
  (solcSourceWord ee).toByteArray.write 0 (clipperTakeCallbackSelectorMem mem) 132 32

noncomputable def clipperTakeCallbackOweMem (ee : ExecutionEnv) (owe : UInt256)
    (mem : ByteArray) : ByteArray :=
  owe.toByteArray.write 0 (clipperTakeCallbackSenderMem ee mem) 164 32

noncomputable def clipperTakeCallbackSliceMem (ee : ExecutionEnv) (owe slice : UInt256)
    (mem : ByteArray) : ByteArray :=
  slice.toByteArray.write 0 (clipperTakeCallbackOweMem ee owe mem) 196 32

noncomputable def clipperTakeCallbackOffsetMem (ee : ExecutionEnv) (owe slice : UInt256)
    (mem : ByteArray) : ByteArray :=
  (⟨128⟩ : UInt256).toByteArray.write 0
    (clipperTakeCallbackSliceMem ee owe slice mem) 228 32

noncomputable def clipperTakeCallbackLengthMem (ee : ExecutionEnv)
    (owe slice dataLen : UInt256) (mem : ByteArray) : ByteArray :=
  dataLen.toByteArray.write 0 (clipperTakeCallbackOffsetMem ee owe slice mem) 260 32

noncomputable def clipperTakeCallbackPayloadMem (ee : ExecutionEnv)
    (owe slice dataLen dataStart : UInt256) (mem : ByteArray) : ByteArray :=
  ee.calldata.write dataStart.toNat
    (clipperTakeCallbackLengthMem ee owe slice dataLen mem) 292 dataLen.toNat

/-- The compiler writes one zero word immediately after the dynamic payload.  The call input ends
inside this word at the next 32-byte boundary, so the write supplies exactly the ABI right-padding. -/
noncomputable def clipperTakeCallbackCalldataMem (ee : ExecutionEnv)
    (owe slice dataLen dataStart : UInt256) (mem : ByteArray) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (clipperTakeCallbackPayloadMem ee owe slice dataLen dataStart mem)
    (292 + dataLen.toNat) 32

/-- Memory facts preserved after constructing the dynamic callback calldata.  The memory may be
larger than the fixed 260-byte pre-callback layout, but all later fixed-offset call builders remain
in bounds and the active-word multiplication remains unwrapped. -/
def clipperTakeMemoryWF (mem : ByteArray) (aw : UInt256) : Prop :=
  260 ≤ mem.size ∧
    mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
    mem.size ≤ aw.toNat * 32 ∧
    aw.toNat * 32 < UInt256.size

theorem clipperTakeCallbackSelectorMem_size {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackSelectorMem mem).size = 260 := by
  unfold clipperTakeCallbackSelectorMem
  exact toByteArray_write32_size_of_le mem clipperTakeCallbackSelectorShifted
    128 260 260 hmem (by omega) (by omega)

theorem clipperTakeCallbackSenderMem_size (ee : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeCallbackSenderMem ee mem).size = 260 := by
  unfold clipperTakeCallbackSenderMem
  exact toByteArray_write32_size_of_le (clipperTakeCallbackSelectorMem mem)
    (solcSourceWord ee) 132 260 260 (clipperTakeCallbackSelectorMem_size hmem)
    (by rw [clipperTakeCallbackSelectorMem_size hmem]; omega) (by omega)

theorem clipperTakeCallbackOweMem_size (ee : ExecutionEnv) (owe : UInt256)
    {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackOweMem ee owe mem).size = 260 := by
  unfold clipperTakeCallbackOweMem
  exact toByteArray_write32_size_of_le (clipperTakeCallbackSenderMem ee mem) owe
    164 260 260 (clipperTakeCallbackSenderMem_size ee hmem)
    (by rw [clipperTakeCallbackSenderMem_size ee hmem]; omega) (by omega)

theorem clipperTakeCallbackSliceMem_size (ee : ExecutionEnv) (owe slice : UInt256)
    {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackSliceMem ee owe slice mem).size = 260 := by
  unfold clipperTakeCallbackSliceMem
  exact toByteArray_write32_size_of_le (clipperTakeCallbackOweMem ee owe mem) slice
    196 260 260 (clipperTakeCallbackOweMem_size ee owe hmem)
    (by rw [clipperTakeCallbackOweMem_size ee owe hmem]; omega) (by omega)

theorem clipperTakeCallbackOffsetMem_size (ee : ExecutionEnv) (owe slice : UInt256)
    {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackOffsetMem ee owe slice mem).size = 260 := by
  unfold clipperTakeCallbackOffsetMem
  exact toByteArray_write32_size_of_le (clipperTakeCallbackSliceMem ee owe slice mem)
    (⟨128⟩ : UInt256) 228 260 260
    (clipperTakeCallbackSliceMem_size ee owe slice hmem)
    (by rw [clipperTakeCallbackSliceMem_size ee owe slice hmem]; omega) (by omega)

theorem clipperTakeCallbackLengthMem_size (ee : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackLengthMem ee owe slice dataLen mem).size = 292 := by
  unfold clipperTakeCallbackLengthMem
  exact toByteArray_write32_size_of_ge (clipperTakeCallbackOffsetMem ee owe slice mem)
    dataLen 260 260 292 (clipperTakeCallbackOffsetMem_size ee owe slice hmem)
    (by omega) (by norm_num) (by omega)

theorem clipperTakeCallbackPayloadMem_size (ee : ExecutionEnv)
    (owe slice dataLen dataStart : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) (hdataLen : dataLen ≠ ⟨0⟩)
    (hpayload : dataStart.toNat + dataLen.toNat ≤ ee.calldata.size) :
    (clipperTakeCallbackPayloadMem ee owe slice dataLen dataStart mem).size =
      292 + dataLen.toNat := by
  unfold clipperTakeCallbackPayloadMem
  have hlen : dataLen.toNat ≠ 0 := by
    intro h
    apply hdataLen
    apply u256_inj
    simpa using h
  rw [← clipperTakeCallbackLengthMem_size ee owe slice dataLen hmem]
  exact write_end_size_from ee.calldata
    (clipperTakeCallbackLengthMem ee owe slice dataLen mem)
    dataStart.toNat dataLen.toNat hlen hpayload

theorem clipperTakeCallbackCalldataMem_size (ee : ExecutionEnv)
    (owe slice dataLen dataStart : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) (hdataLen : dataLen ≠ ⟨0⟩)
    (hpayload : dataStart.toNat + dataLen.toNat ≤ ee.calldata.size) :
    (clipperTakeCallbackCalldataMem ee owe slice dataLen dataStart mem).size =
      324 + dataLen.toNat := by
  unfold clipperTakeCallbackCalldataMem
  exact toByteArray_write32_size_of_ge
    (clipperTakeCallbackPayloadMem ee owe slice dataLen dataStart mem)
    (⟨0⟩ : UInt256) (292 + dataLen.toNat) (292 + dataLen.toNat)
    (324 + dataLen.toNat)
    (clipperTakeCallbackPayloadMem_size ee owe slice dataLen dataStart hmem hdataLen
      hpayload)
    (by omega) (by norm_num) (by omega)

theorem clipperTakeCallbackLengthMem_read64 (ee : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeCallbackLengthMem ee owe slice dataLen mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeCallbackLengthMem
  rw [toByteArray_write_read_below_of_gap dataLen _ 260 64
      (by rw [clipperTakeCallbackOffsetMem_size ee owe slice hmem]; omega)
      (by omega)
      (by rw [clipperTakeCallbackOffsetMem_size ee owe slice hmem]; native_decide)]
  unfold clipperTakeCallbackOffsetMem
  rw [toByteArray_write_read_below_of_gap ⟨128⟩ _ 228 64
      (by rw [clipperTakeCallbackSliceMem_size ee owe slice hmem]; omega)
      (by omega)
      (by rw [clipperTakeCallbackSliceMem_size ee owe slice hmem]; native_decide)]
  unfold clipperTakeCallbackSliceMem
  rw [toByteArray_write_read_below_of_gap slice _ 196 64
      (by rw [clipperTakeCallbackOweMem_size ee owe hmem]; omega)
      (by omega)
      (by rw [clipperTakeCallbackOweMem_size ee owe hmem]; native_decide)]
  unfold clipperTakeCallbackOweMem
  rw [toByteArray_write_read_below_of_gap owe _ 164 64
      (by rw [clipperTakeCallbackSenderMem_size ee hmem]; omega)
      (by omega)
      (by rw [clipperTakeCallbackSenderMem_size ee hmem]; native_decide)]
  unfold clipperTakeCallbackSenderMem
  rw [toByteArray_write_read_below_of_gap (solcSourceWord ee) _ 132 64
      (by rw [clipperTakeCallbackSelectorMem_size hmem]; omega)
      (by omega)
      (by rw [clipperTakeCallbackSelectorMem_size hmem]; native_decide)]
  unfold clipperTakeCallbackSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperTakeCallbackSelectorShifted _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem clipperTakeCallbackCalldataMem_read64 (ee : ExecutionEnv)
    (owe slice dataLen dataStart : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) (hread64 :
      mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hpayload : dataStart.toNat + dataLen.toNat ≤ ee.calldata.size) :
    (clipperTakeCallbackCalldataMem ee owe slice dataLen dataStart mem).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeCallbackCalldataMem
  rw [toByteArray_write_read_below_of_gap ⟨0⟩ _ (292 + dataLen.toNat) 64
      (by rw [clipperTakeCallbackPayloadMem_size ee owe slice dataLen dataStart hmem
        hdataLen hpayload]; omega)
      (by omega)
      (by rw [clipperTakeCallbackPayloadMem_size ee owe slice dataLen dataStart hmem
        hdataLen hpayload]; simp)]
  unfold clipperTakeCallbackPayloadMem
  rw [show 292 =
      (clipperTakeCallbackLengthMem ee owe slice dataLen mem).size by
        symm
        exact clipperTakeCallbackLengthMem_size ee owe slice dataLen hmem]
  rw [write_read_below_end_from ee.calldata
    (clipperTakeCallbackLengthMem ee owe slice dataLen mem)
    dataStart.toNat dataLen.toNat 64
    (by
      intro hz
      apply hdataLen
      apply u256_inj
      simpa using hz)
    hpayload
    (by rw [clipperTakeCallbackLengthMem_size ee owe slice dataLen hmem]; omega)]
  exact clipperTakeCallbackLengthMem_read64 ee owe slice dataLen hmem hread64

theorem clipperTakePayloadEnd_le (I : ExecutionEnv)
    (hdataLen : clipperTakeDataLenWord I ≠ ⟨0⟩)
    (hpayload :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length =
          (clipperTakeDataLenWord I).toNat) :
    32 + (4 + (clipperTakeDataOffsetWord I).toNat) +
        (clipperTakeDataLenWord I).toNat ≤ I.calldata.size := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htailGe :
      (clipperTakeDataLenWord I).toNat ≤
        ((I.calldata.toList.drop 4).drop
          ((clipperTakeDataOffsetWord I).toNat + 32)).length := by
    rw [← hpayload, List.length_take]
    exact Nat.min_le_right _ _
  have hlenPos : 0 < (clipperTakeDataLenWord I).toNat := by
    have hne : (clipperTakeDataLenWord I).toNat ≠ 0 := by
      intro h
      apply hdataLen
      apply u256_inj
      simpa using h
    omega
  rw [List.length_drop, List.length_drop, htlen] at htailGe
  omega

theorem clipperTakeDataBytes_toByteArray_eq_extract (I : ExecutionEnv) :
    (clipperTakeDataBytes I).toByteArray =
      I.calldata.extract
        (32 + (4 + (clipperTakeDataOffsetWord I).toNat))
        (32 + (4 + (clipperTakeDataOffsetWord I).toNat) +
          (clipperTakeDataLenWord I).toNat) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  simp only [List.data_toByteArray]
  simp [clipperTakeDataBytes, List.drop_drop, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  rw [show
    4 + (32 + ((clipperTakeDataOffsetWord I).toNat +
      (clipperTakeDataLenWord I).toNat)) -
        (4 + (32 + (clipperTakeDataOffsetWord I).toNat)) =
      (clipperTakeDataLenWord I).toNat by omega]
  rw [byteArray_toList_eq]

theorem clipperTakeCallbackCalldataMem_eq (I : ExecutionEnv)
    (owe slice dataLen dataStart : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) (hdataLen : dataLen ≠ ⟨0⟩)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat =
      32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hpayload :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length =
          (clipperTakeDataLenWord I).toNat) :
    clipperTakeCallbackCalldataMem I owe slice dataLen dataStart mem =
      clipperTakeCallbackLengthMem I owe slice dataLen mem ++
        (clipperTakeDataBytes I).toByteArray ++ (UInt256.toByteArray ⟨0⟩) := by
  have hpayloadBound : dataStart.toNat + dataLen.toNat ≤ I.calldata.size := by
    rw [hdataStartEq, hdataLenEq]
    exact clipperTakePayloadEnd_le I (by simpa [hdataLenEq] using hdataLen) hpayload
  unfold clipperTakeCallbackCalldataMem clipperTakeCallbackPayloadMem
  rw [show 292 + dataLen.toNat =
      (I.calldata.write dataStart.toNat
        (clipperTakeCallbackLengthMem I owe slice dataLen mem) 292
        dataLen.toNat).size by
    symm
    exact clipperTakeCallbackPayloadMem_size I owe slice dataLen dataStart hmem
      hdataLen hpayloadBound]
  rw [write_at_end_eq _ _ 32 (by decide) (by rw [toByteArray_size])]
  rw [toByteArray_extract_all]
  rw [show 292 = (clipperTakeCallbackLengthMem I owe slice dataLen mem).size by
    symm
    exact clipperTakeCallbackLengthMem_size I owe slice dataLen hmem]
  have hlen : dataLen.toNat ≠ 0 := by
    intro h
    apply hdataLen
    apply u256_inj
    simpa using h
  rw [write_at_end_eq_from I.calldata
    (clipperTakeCallbackLengthMem I owe slice dataLen mem) dataStart.toNat dataLen.toNat
    hlen hpayloadBound]
  rw [hdataStartEq, hdataLenEq, ← clipperTakeDataBytes_toByteArray_eq_extract]

theorem clipperTakeCallbackSelectorMem_read128_4 {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeCallbackSelectorMem mem).readWithPadding 128 4 =
      clipperCallSelector := by
  unfold clipperTakeCallbackSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperTakeCallbackSelectorShifted mem
    128 0 4 (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperTakeCallbackLengthMem_read128_4 (I : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackLengthMem I owe slice dataLen mem).readWithPadding 128 4 =
      clipperCallSelector := by
  unfold clipperTakeCallbackLengthMem
  rw [write32_read_below_len _ _ 260 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackOffsetMem_size I owe slice hmem]) (by omega)
    (by rw [clipperTakeCallbackOffsetMem_size I owe slice hmem]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperTakeCallbackOffsetMem
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackSliceMem_size I owe slice hmem]; omega) (by omega)
    (by rw [clipperTakeCallbackSliceMem_size I owe slice hmem]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperTakeCallbackSliceMem
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackOweMem_size I owe hmem]; omega) (by omega)
    (by rw [clipperTakeCallbackOweMem_size I owe hmem]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperTakeCallbackOweMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackSenderMem_size I hmem]; omega) (by omega)
    (by rw [clipperTakeCallbackSenderMem_size I hmem]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperTakeCallbackSenderMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackSelectorMem_size hmem]; omega) (by omega)
    (by rw [clipperTakeCallbackSelectorMem_size hmem]; omega)
    (by norm_num) (by norm_num)]
  exact clipperTakeCallbackSelectorMem_read128_4 hmem

theorem clipperTakeCallbackLengthMem_read132_32 (I : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackLengthMem I owe slice dataLen mem).readWithPadding 132 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold clipperTakeCallbackLengthMem
  rw [write32_read_below _ _ 260 132 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackOffsetMem_size I owe slice hmem]) (by omega)]
  unfold clipperTakeCallbackOffsetMem
  rw [write32_read_below _ _ 228 132 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackSliceMem_size I owe slice hmem]; omega) (by omega)]
  unfold clipperTakeCallbackSliceMem
  rw [write32_read_below _ _ 196 132 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackOweMem_size I owe hmem]; omega) (by omega)]
  unfold clipperTakeCallbackOweMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackSenderMem_size I hmem]; omega) (by omega)]
  unfold clipperTakeCallbackSenderMem
  rw [toByteArray_write32_read_back _ _ _
    (by rw [clipperTakeCallbackSelectorMem_size hmem]; omega)]

theorem clipperTakeCallbackLengthMem_read164_32 (I : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackLengthMem I owe slice dataLen mem).readWithPadding 164 32 =
      UInt256.toByteArray owe := by
  unfold clipperTakeCallbackLengthMem
  rw [write32_read_below _ _ 260 164 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackOffsetMem_size I owe slice hmem]) (by omega)]
  unfold clipperTakeCallbackOffsetMem
  rw [write32_read_below _ _ 228 164 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackSliceMem_size I owe slice hmem]; omega) (by omega)]
  unfold clipperTakeCallbackSliceMem
  rw [write32_read_below _ _ 196 164 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackOweMem_size I owe hmem]; omega) (by omega)]
  unfold clipperTakeCallbackOweMem
  rw [toByteArray_write32_read_back _ _ _
    (by rw [clipperTakeCallbackSenderMem_size I hmem]; omega)]

theorem clipperTakeCallbackLengthMem_read196_32 (I : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackLengthMem I owe slice dataLen mem).readWithPadding 196 32 =
      UInt256.toByteArray slice := by
  unfold clipperTakeCallbackLengthMem
  rw [write32_read_below _ _ 260 196 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackOffsetMem_size I owe slice hmem]) (by omega)]
  unfold clipperTakeCallbackOffsetMem
  rw [write32_read_below _ _ 228 196 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackSliceMem_size I owe slice hmem]; omega) (by omega)]
  unfold clipperTakeCallbackSliceMem
  rw [toByteArray_write32_read_back _ _ _
    (by rw [clipperTakeCallbackOweMem_size I owe hmem]; omega)]

theorem clipperTakeCallbackLengthMem_read228_32 (I : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackLengthMem I owe slice dataLen mem).readWithPadding 228 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeCallbackLengthMem
  rw [write32_read_below _ _ 260 228 (by rw [toByteArray_size])
    (by rw [clipperTakeCallbackOffsetMem_size I owe slice hmem]) (by omega)]
  unfold clipperTakeCallbackOffsetMem
  rw [toByteArray_write32_read_back _ _ _
    (by rw [clipperTakeCallbackSliceMem_size I owe slice hmem]; omega)]

theorem clipperTakeCallbackLengthMem_read260_32 (I : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackLengthMem I owe slice dataLen mem).readWithPadding 260 32 =
      UInt256.toByteArray dataLen := by
  unfold clipperTakeCallbackLengthMem
  rw [toByteArray_write32_read_back _ _ _
    (by rw [clipperTakeCallbackOffsetMem_size I owe slice hmem])]

theorem clipperTakeCallbackLengthMem_read128_164 (I : ExecutionEnv)
    (owe slice dataLen : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (clipperTakeCallbackLengthMem I owe slice dataLen mem).readWithPadding 128 164 =
      clipperCallSelector ++ UInt256.toByteArray (solcSourceWord I) ++
        UInt256.toByteArray owe ++ UInt256.toByteArray slice ++
        UInt256.toByteArray ⟨128⟩ ++ UInt256.toByteArray dataLen := by
  rw [byteArray_readWithPadding_split _ 128 4 160 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeCallbackLengthMem_size I owe slice dataLen hmem])]
  rw [byteArray_readWithPadding_split _ 132 32 128 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeCallbackLengthMem_size I owe slice dataLen hmem])]
  rw [byteArray_readWithPadding_split _ 164 32 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeCallbackLengthMem_size I owe slice dataLen hmem])]
  rw [byteArray_readWithPadding_split _ 196 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeCallbackLengthMem_size I owe slice dataLen hmem])]
  rw [byteArray_readWithPadding_split _ 228 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeCallbackLengthMem_size I owe slice dataLen hmem])]
  rw [clipperTakeCallbackLengthMem_read128_4 I owe slice dataLen hmem,
    clipperTakeCallbackLengthMem_read132_32 I owe slice dataLen hmem,
    clipperTakeCallbackLengthMem_read164_32 I owe slice dataLen hmem,
    clipperTakeCallbackLengthMem_read196_32 I owe slice dataLen hmem,
    clipperTakeCallbackLengthMem_read228_32 I owe slice dataLen hmem,
    clipperTakeCallbackLengthMem_read260_32 I owe slice dataLen hmem]
  simp [ByteArray.append_assoc]

theorem clipperTake_le_paddedSize (n : Nat) : n ≤ ABI.paddedSize n := by
  have hdecomp := Nat.div_add_mod (n + 31) 32
  have hmod := Nat.mod_lt (n + 31) (by norm_num : 0 < 32)
  unfold ABI.paddedSize
  omega

theorem clipperTake_paddedSize_le (n : Nat) : ABI.paddedSize n ≤ n + 31 := by
  unfold ABI.paddedSize
  exact Nat.mul_div_le (n + 31) 32

theorem clipperTakePaddedSizeWord (dataLen : UInt256)
    (hlenMax : dataLen.toNat ≤ 4294967296) :
    UInt256.land (dataLen + ⟨31⟩) (UInt256.lnot ⟨31⟩) =
      UInt256.ofNat (ABI.paddedSize dataLen.toNat) := by
  apply u256_inj
  have hsum : dataLen.toNat + 31 < 2 ^ 256 := by
    omega
  have hpad : ABI.paddedSize dataLen.toNat < UInt256.size := by
    have hle := clipperTake_paddedSize_le dataLen.toNat
    change ABI.paddedSize dataLen.toNat < 2 ^ 256
    omega
  rw [uland_toNat, lnot31_toNat, uadd_toNat,
    show (⟨31⟩ : UInt256).toNat = 31 by decide,
    show UInt256.size = 2 ^ 256 by decide, Nat.mod_eq_of_lt hsum,
    nat_land_mask _ hsum, ulit_toNat' _ hpad]
  rfl

theorem clipperTakeCallbackInputSizeWord (dataLen : UInt256)
    (hlenMax : dataLen.toNat ≤ 4294967296) :
    UInt256.sub (⟨292⟩ + UInt256.ofNat (ABI.paddedSize dataLen.toNat)) ⟨128⟩ =
      UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat) := by
  apply u256_inj
  have hpadLe : ABI.paddedSize dataLen.toNat ≤ dataLen.toNat + 31 :=
    clipperTake_paddedSize_le _
  have hpadLt : ABI.paddedSize dataLen.toNat < UInt256.size := by
    change ABI.paddedSize dataLen.toNat < 2 ^ 256
    omega
  have hsumLt : 292 + ABI.paddedSize dataLen.toNat < UInt256.size := by
    change 292 + ABI.paddedSize dataLen.toNat < 2 ^ 256
    omega
  have hrhsLt : 164 + ABI.paddedSize dataLen.toNat < UInt256.size := by
    change 164 + ABI.paddedSize dataLen.toNat < 2 ^ 256
    omega
  have hsub : (⟨128⟩ : UInt256).toNat ≤
      (⟨292⟩ + UInt256.ofNat (ABI.paddedSize dataLen.toNat)).toNat := by
    rw [uadd_toNat, show (⟨292⟩ : UInt256).toNat = 292 by decide,
      ulit_toNat' _ hpadLt, Nat.mod_eq_of_lt hsumLt]
    change 128 ≤ 292 + ABI.paddedSize dataLen.toNat
    omega
  rw [usub_toNat hsub, uadd_toNat,
    show (⟨292⟩ : UInt256).toNat = 292 by decide,
    show (⟨128⟩ : UInt256).toNat = 128 by decide,
    ulit_toNat' _ hpadLt, Nat.mod_eq_of_lt hsumLt,
    ulit_toNat' _ hrhsLt]
  omega

theorem clipperTakeCallbackCalldataMem_read128 (I : ExecutionEnv)
    (owe slice dataLen dataStart : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) (hdataLen : dataLen ≠ ⟨0⟩)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat =
      32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hpayload :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length =
          (clipperTakeDataLenWord I).toNat) :
    (clipperTakeCallbackCalldataMem I owe slice dataLen dataStart mem).readWithPadding
        128 (164 + ABI.paddedSize dataLen.toNat) =
      clipperCallSelector ++ UInt256.toByteArray (solcSourceWord I) ++
        UInt256.toByteArray owe ++ UInt256.toByteArray slice ++
        UInt256.toByteArray ⟨128⟩ ++ UInt256.toByteArray dataLen ++
        (clipperTakeDataBytes I).toByteArray ++
        (UInt256.toByteArray ⟨0⟩).extract 0
          (ABI.paddedSize dataLen.toNat - dataLen.toNat) := by
  let H := clipperTakeCallbackLengthMem I owe slice dataLen mem
  let D := (clipperTakeDataBytes I).toByteArray
  let Z := UInt256.toByteArray (⟨0⟩ : UInt256)
  have hHSize : H.size = 292 := by
    simpa [H] using clipperTakeCallbackLengthMem_size I owe slice dataLen hmem
  have hDSize : D.size = dataLen.toNat := by
    simp only [D, List.data_toByteArray, ByteArray.size]
    rw [List.size_toArray]
    simpa [hdataLenEq] using hpayload
  have hZSize : Z.size = 32 := by simp [Z, toByteArray_size]
  have hpaddedLo : dataLen.toNat ≤ ABI.paddedSize dataLen.toNat :=
    clipperTake_le_paddedSize _
  have hpaddedHi : ABI.paddedSize dataLen.toNat ≤ dataLen.toNat + 31 :=
    clipperTake_paddedSize_le _
  rw [clipperTakeCallbackCalldataMem_eq I owe slice dataLen dataStart hmem hdataLen
    hdataLenEq hdataStartEq hpayload]
  change (H ++ D ++ Z).readWithPadding 128
      (164 + ABI.paddedSize dataLen.toNat) = _
  rw [readWithPadding_eq_extract' _ 128 (164 + ABI.paddedSize dataLen.toNat)
    (by omega) (by omega) (by
      rw [ByteArray.size_append, ByteArray.size_append, hHSize, hDSize, hZSize]
      omega)]
  rw [ByteArray.append_assoc]
  rw [extract_append_span H (D ++ Z) 128
    (128 + (164 + ABI.paddedSize dataLen.toNat)) (by omega) (by omega)]
  rw [show H.extract 128 H.size = H.readWithPadding 128 164 by
    rw [hHSize]
    exact (readWithPadding_eq_extract' H 128 164 (by norm_num) (by norm_num)
      (by omega)).symm]
  rw [clipperTakeCallbackLengthMem_read128_164 I owe slice dataLen hmem]
  rw [extract_append_span D Z 0
    (128 + (164 + ABI.paddedSize dataLen.toNat) - H.size) (by omega) (by
      rw [hHSize, hDSize]
      omega)]
  rw [hHSize, hDSize]
  rw [show 128 + (164 + ABI.paddedSize dataLen.toNat) - 292 =
      ABI.paddedSize dataLen.toNat by omega]
  rw [show D.extract 0 dataLen.toNat = D by
    rw [← hDSize]
    exact byteArray_extract_self D]
  simp [H, D, Z, ByteArray.append_assoc]

theorem clipperTakeZeroBytes_toByteArray (n : Nat) (hn : n ≤ 32) :
    (ABI.zeroBytes n).toByteArray =
      (UInt256.toByteArray ⟨0⟩).extract 0 n := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    toByteArray_eq_toBytesBE]
  have hz : EVM.Word.toBytesBE (⟨0⟩ : UInt256) = List.replicate 32 0 := by
    native_decide
  rw [show ((EVM.Word.toBytesBE (⟨0⟩ : UInt256)).toArray).toList =
      EVM.Word.toBytesBE (⟨0⟩ : UInt256) by simp, hz]
  rw [List.toList_data_toByteArray]
  simp only [ABI.zeroBytes, Nat.sub_zero, List.drop_zero]
  change List.replicate n 0 = (List.replicate 32 0).take n
  rw [List.take_replicate, Nat.min_eq_left hn]

theorem clipperTakeCallbackEncode_eq (v : ClipperImmutables) (I : ExecutionEnv)
    (owe slice dataLen dataStart : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) (hdataLen : dataLen ≠ ⟨0⟩)
    (hdataLenEq : dataLen = clipperTakeDataLenWord I)
    (hdataStartEq : dataStart.toNat =
      32 + (4 + (clipperTakeDataOffsetWord I).toNat))
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hpayload :
      (((I.calldata.toList.drop 4).drop
        ((clipperTakeDataOffsetWord I).toNat + 32)).take
        (clipperTakeDataLenWord I).toNat).length =
          (clipperTakeDataLenWord I).toNat) :
    (config v).externalABI.encode? "clipperCall"
        [.address I.source, .int (Int.ofNat owe.toNat),
          .int (Int.ofNat slice.toNat), clipperTakeDataValue I] =
      some ((clipperTakeCallbackCalldataMem I owe slice dataLen dataStart mem).readWithPadding
        128 (164 + ABI.paddedSize dataLen.toNat)) := by
  rw [clipperTakeCallbackCalldataMem_read128 I owe slice dataLen dataStart hmem
    hdataLen hdataLenEq hdataStartEq hlenMax hpayload]
  have hsource : EVM.word I.source.val = solcSourceWord I := by
    unfold solcSourceWord EVM.word EVM.uintN UInt256.ofNat
    rfl
  have howeWord : EVM.word owe.toNat = owe := u256_ofNat_toNat owe
  have hsliceWord : EVM.word slice.toNat = slice := u256_ofNat_toNat slice
  have howeLt : owe.toNat < EVM.twoPow 256 := by
    change owe.val.val < UInt256.size
    exact owe.val.isLt
  have hsliceLt : slice.toNat < EVM.twoPow 256 := by
    change slice.val.val < UInt256.size
    exact slice.val.isLt
  have hdataSize : (ByteArray.mk (clipperTakeDataBytes I).toArray).size = dataLen.toNat := by
    simp only [ByteArray.size, List.size_toArray]
    simpa [hdataLenEq] using hpayload
  have hpadLo : dataLen.toNat ≤ ABI.paddedSize dataLen.toNat :=
    clipperTake_le_paddedSize _
  have hpadHi : ABI.paddedSize dataLen.toNat ≤ dataLen.toNat + 31 :=
    clipperTake_paddedSize_le _
  have hpadCount : ABI.paddedSize dataLen.toNat - dataLen.toNat ≤ 32 := by omega
  have hdataBytes :
      (ByteArray.mk (clipperTakeDataBytes I).toArray).toList =
        clipperTakeDataBytes I := by
    rw [byteArray_toList_eq]
  have hdataListLen : (clipperTakeDataBytes I).length = dataLen.toNat := by
    simpa [clipperTakeDataBytes, hdataLenEq] using hpayload
  have h128Bytes :
      (ABI.natBytes 128).toByteArray = UInt256.toByteArray ⟨128⟩ := by
    exact word_toBytesBE_toByteArray_eq_toByteArray _
  have hlenBytes :
      (ABI.natBytes dataLen.toNat).toByteArray = UInt256.toByteArray dataLen := by
    unfold ABI.natBytes
    rw [word_toBytesBE_toByteArray_eq_toByteArray]
    exact congrArg UInt256.toByteArray (u256_ofNat_toNat dataLen)
  change externalABI.encode? "clipperCall"
      [.address I.source, .int (Int.ofNat owe.toNat),
        .int (Int.ofNat slice.toNat),
        .bytes (ByteArray.mk (clipperTakeDataBytes I).toArray)] = _
  unfold externalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr,
    uint256, uint256Int, bytesDyn, selectorBytes, clipperCallSelector, howeLt,
    hsliceLt, howeWord, hsliceWord, hsource, hdataSize, hdataBytes,
    hdataListLen, h128Bytes, hlenBytes,
    ABI.padRightToWord, word_toBytesBE_toByteArray_eq_toByteArray,
    List.toByteArray_append, clipperTakeZeroBytes_toByteArray _ hpadCount,
    ByteArray.append_assoc]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
theorem RD.clipperTakeClipperCallExtcodesizeGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨4530⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlenMax : dataLen.toNat ≤ 4294967296)
    (hdataLen : dataLen ≠ ⟨0⟩)
    (hpayload : dataStart.toNat + dataLen.toNat ≤ ee.calldata.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (aw : UInt256) (k' C' : ℕ),
      RD code ee g s0 ⟨4664⟩
        (UInt256.land solcAddrMask who :: UInt256.land solcAddrMask who :: ⟨0⟩ ::
          ⟨128⟩ :: UInt256.ofNat (164 + ABI.paddedSize dataLen.toNat) :: ⟨128⟩ ::
          ⟨0⟩ :: (⟨292⟩ + UInt256.ofNat (ABI.paddedSize dataLen.toNat)) ::
          clipperTakeCallbackSelectorSeed :: UInt256.land solcAddrMask who :: dog :: slice ::
          owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
          who :: max :: amt :: id :: R)
        (clipperTakeCallbackCalldataMem ee owe slice dataLen dataStart mem)
        aw o (cA, σ) k' C' ∧
      clipperTakeMemoryWF
        (clipperTakeCallbackCalldataMem ee owe slice dataLen dataStart mem) aw := by
  have hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 9)
      (by rw [hmem]; norm_num) (by native_decide) hread64
  have rd4531 := RD.clipperDup12 rd (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rd4548 := evm_run rd4531 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperTakeCallbackSelectorSeed (by clipper_runtime_decode) (by evm_ov),
    raw caller (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov)]
  have rd4549 := RD.clipperDup16 rd4548 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rd4550 := RD.clipperDup16 rd4549 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rd4552pre := evm_run rd4550 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4553 := rd4552pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hbaseMload64 (by native_decide) (by evm_ov)
  have rd4564pre := evm_run rd4553 with [
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.land ⟨4294967295⟩ clipperTakeCallbackSelectorSeed =
      clipperTakeCallbackSelectorSeed by native_decide] at rd4564pre
  rw [show UInt256.shiftLeft clipperTakeCallbackSelectorSeed ⟨224⟩ =
      clipperTakeCallbackSelectorShifted from rfl] at rd4564pre
  have rd4565 := rd4564pre.mstore 0 (clipperTakeCallbackSelectorMem mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4580pre := evm_run rd4565 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ by native_decide] at rd4580pre
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by native_decide] at rd4580pre
  have hsourceClean :
      UInt256.land solcAddrMask (UInt256.ofNat ee.source.val) = solcSourceWord ee := by
    exact solcAddrMask_clean_left (solcSourceWord_canonical ee)
  have rd4581 := rd4580pre.mstore 0 (clipperTakeCallbackSenderMem ee mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost
    (by rw [hsourceClean]; rfl)
    (by native_decide) (by evm_ov)
  have rd4586pre := evm_run rd4581 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨132⟩ = ⟨164⟩ by native_decide] at rd4586pre
  have rd4587 := rd4586pre.mstore 0 (clipperTakeCallbackOweMem ee owe mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4592pre := evm_run rd4587 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨164⟩ = ⟨196⟩ by native_decide] at rd4592pre
  have rd4593 := rd4592pre.mstore 0 (clipperTakeCallbackSliceMem ee owe slice mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4604pre := evm_run rd4593 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨196⟩ = ⟨228⟩ by native_decide] at rd4604pre
  rw [show (⟨32⟩ : UInt256) + ⟨228⟩ = ⟨260⟩ by native_decide] at rd4604pre
  rw [show UInt256.sub (⟨260⟩ : UInt256) ⟨132⟩ = ⟨128⟩ by native_decide]
    at rd4604pre
  have rd4605 := rd4604pre.mstore 0 (clipperTakeCallbackOffsetMem ee owe slice mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4610pre := evm_run rd4605 with [
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd4611 := rd4610pre.mstore
    (Cₘ (UInt256.ofNat 10) - Cₘ (UInt256.ofNat 9))
    (clipperTakeCallbackLengthMem ee owe slice dataLen mem)
    (UInt256.ofNat 10) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd4619pre := evm_run rd4611 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨260⟩ = ⟨292⟩ by native_decide] at rd4619pre
  let awCopy : UInt256 :=
    UInt256.ofNat (MachineState.M (UInt256.ofNat 10).toNat 292 dataLen.toNat)
  have rd4620 := RD.calldatacopy
    (Cₘ awCopy - Cₘ (UInt256.ofNat 10))
    (clipperTakeCallbackPayloadMem ee owe slice dataLen dataStart mem)
    awCopy rd4619pre (by clipper_runtime_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCopy,
        show (⟨292⟩ : UInt256).toNat = 292 by decide])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd4625pre := evm_run rd4620 with [
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have haddr : ((⟨292⟩ : UInt256) + dataLen).toNat = 292 + dataLen.toNat := by
    rw [uadd_toNat, show (⟨292⟩ : UInt256).toNat = 292 by decide,
      Nat.mod_eq_of_lt]
    have hsize : 292 + 4294967296 < UInt256.size := by native_decide
    omega
  let awPad : UInt256 :=
    UInt256.ofNat
      (MachineState.M awCopy.toNat (((⟨292⟩ : UInt256) + dataLen).toNat) 32)
  have rd4626 := RD.mstore
    (Cₘ awPad - Cₘ awCopy)
    (clipperTakeCallbackCalldataMem ee owe slice dataLen dataStart mem)
    awPad rd4625pre (by clipper_runtime_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awCopy, awPad])
    (by
      rw [haddr]
      rfl)
    (by rfl)
    (by evm_ov)
  have rd4636 := evm_run rd4626 with [
    raw push1 ⟨31⟩ (by clipper_runtime_decode) (by evm_ov),
    raw not (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨31⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd4643 := evm_run rd4636 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd4651 := evm_run rd4643 with [
    raw swap7 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  rw [clipperTakePaddedSizeWord dataLen hlenMax] at rd4651
  have hdataLenNat : dataLen.toNat ≠ 0 := by
    intro hz
    apply hdataLen
    apply u256_inj
    simpa using hz
  have hawCopyBound :
      MachineState.M (UInt256.ofNat 10).toNat 292 dataLen.toNat < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 by decide]
    simp only [MachineState.M, hdataLenNat, ↓reduceIte,
      show (UInt256.ofNat 10).toNat = 10 by decide]
    rw [Nat.max_def]
    split <;> omega
  have hawCopyNat : awCopy.toNat =
      MachineState.M (UInt256.ofNat 10).toNat 292 dataLen.toNat := by
    exact ulit_toNat' _ hawCopyBound
  have hawPadBound :
      MachineState.M awCopy.toNat (((⟨292⟩ : UInt256) + dataLen).toNat) 32 <
        UInt256.size := by
    rw [haddr, hawCopyNat, show UInt256.size = 2 ^ 256 by decide]
    simp only [MachineState.M, hdataLenNat, ↓reduceIte,
      show (UInt256.ofNat 10).toNat = 10 by decide]
    rw [Nat.max_def]
    split
    · omega
    · omega
  have hawPadNat : awPad.toNat =
      MachineState.M awCopy.toNat (((⟨292⟩ : UInt256) + dataLen).toNat) 32 := by
    exact ulit_toNat' _ hawPadBound
  have hawPadGe : 3 ≤ awPad.toNat := by
    rw [hawPadNat, haddr, hawCopyNat]
    simp only [MachineState.M]
    omega
  have hawPadSmall : awPad.toNat * 32 < UInt256.size := by
    rw [hawPadNat, haddr, hawCopyNat,
      show UInt256.size = 2 ^ 256 by decide]
    have hcopyDiv :
        ((292 + dataLen.toNat + 31) / 32) * 32 ≤
          292 + dataLen.toNat + 31 := Nat.div_mul_le_self _ _
    have hpadDiv :
        ((292 + dataLen.toNat + 32 + 31) / 32) * 32 ≤
          292 + dataLen.toNat + 32 + 31 := Nat.div_mul_le_self _ _
    have hsmall : 4294967296 + 355 < 2 ^ 256 := by native_decide
    simp only [MachineState.M, hdataLenNat, ↓reduceIte,
      show (UInt256.ofNat 10).toNat = 10 by decide]
    rw [Nat.max_def]
    split
    · exact lt_of_le_of_lt hpadDiv (by omega)
    · rw [Nat.max_def]
      split
      · exact lt_of_le_of_lt hcopyDiv (by omega)
      · native_decide
  have hawPadCovers :
      (clipperTakeCallbackCalldataMem ee owe slice dataLen dataStart mem).size ≤
        awPad.toNat * 32 := by
    rw [clipperTakeCallbackCalldataMem_size ee owe slice dataLen dataStart hmem
      hdataLen hpayload, hawPadNat, haddr]
    simp only [MachineState.M]
    have hceil :
        324 + dataLen.toNat ≤ ((324 + dataLen.toNat + 31) / 32) * 32 := by
      have hmod := Nat.mod_lt (324 + dataLen.toNat + 31) (by decide : 0 < 32)
      have hdiv := Nat.div_add_mod (324 + dataLen.toNat + 31) 32
      omega
    have hright : (324 + dataLen.toNat + 31) / 32 ≤
        Nat.max awCopy.toNat ((292 + dataLen.toNat + 32 + 31) / 32) := by
      convert Nat.le_max_right awCopy.toNat
        ((292 + dataLen.toNat + 32 + 31) / 32) using 1 <;> omega
    exact le_trans hceil (Nat.mul_le_mul_right 32 hright)
  have hawMload64 :
      UInt256.ofNat (MachineState.M awPad.toNat (⟨64⟩ : UInt256).toNat 32) =
        awPad := by
    apply u256_inj
    have hM : MachineState.M awPad.toNat (⟨64⟩ : UInt256).toNat 32 =
        awPad.toNat := by
      simp only [MachineState.M]
      rw [show ((⟨64⟩ : UInt256).toNat + 32 + 31) / 32 = 3 by decide]
      exact max_eq_left hawPadGe
    rw [hM]
    exact congrArg UInt256.toNat (u256_ofNat_toNat awPad)
  have hcallMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperTakeCallbackCalldataMem ee owe slice dataLen dataStart mem).size
          ∨ (⟨64⟩ : UInt256) ≥ awPad * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperTakeCallbackCalldataMem ee owe slice dataLen dataStart mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    apply mloadFreePtrValue
    · rw [clipperTakeCallbackCalldataMem_size ee owe slice dataLen dataStart hmem
        hdataLen hpayload]
      omega
    ·
      have hmul : (awPad * (⟨32⟩ : UInt256)).toNat = awPad.toNat * 32 := by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
          umul_toNat (a := awPad) (b := (⟨32⟩ : UInt256)) hawPadSmall
      intro hge
      have h64 : (⟨64⟩ : UInt256).toNat ≥
          (awPad * (⟨32⟩ : UInt256)).toNat := hge
      rw [hmul] at h64
      change 64 ≥ awPad.toNat * 32 at h64
      nlinarith
    · exact clipperTakeCallbackCalldataMem_read64 ee owe slice dataLen dataStart hmem
        hread64 hdataLen hpayload
  have rd4655pre := evm_run rd4651 with [
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4656 := rd4655pre.mload 0 ⟨128⟩ awPad
    (by clipper_runtime_decode) (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawMload64])
    hcallMload64 hawMload64 (by evm_ov)
  have rd4664pre := evm_run rd4656 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  rw [clipperTakeCallbackInputSizeWord dataLen hlenMax] at rd4664pre
  refine ⟨awPad, _, _, by simpa [u256_land_comm] using rd4664pre, ?_⟩
  exact ⟨by
    rw [clipperTakeCallbackCalldataMem_size ee owe slice dataLen dataStart hmem
      hdataLen hpayload]
    omega,
    clipperTakeCallbackCalldataMem_read64 ee owe slice dataLen dataStart hmem hread64
      hdataLen hpayload,
    hawPadCovers,
    hawPadSmall⟩

end Benchmarks.Dss.Clipper
