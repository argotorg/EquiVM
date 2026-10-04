import Reasoning.ExternalCall
import Benchmarks.Dss.Clipper.YankSuccessSource
import Benchmarks.Dss.Clipper.YankVatEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 8000000 in
theorem clipperYankBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 28)) :
    runtimeEquivalenceFor (config v) (contract v) σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 28) (by native_decide) hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some (yankTransition v) :=
    clipperDispatch_yank v hsel
  have hreachEntry := clipperReachYankBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := clipperDecode_yank_ok v (I := I) hsz36
    have hreachBody := clipperYankX_decoded
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (v := v) hpatch hsz36 hsize hreachEntry
    let locals := clipperYankStore I
    by_cases hauthEvm : clipperRelyAuthWord σ I = ⟨1⟩
    · by_cases hlockedEvm : solcSlotWord σ I ⟨13⟩ = ⟨0⟩
      · let σLocked := sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩
        obtain ⟨_, _, rd1912⟩ := hreachBody
        obtain ⟨_, _, rd1994⟩ := clipperYankX_authorized (v := v) hpatch hauthEvm rd1912
        obtain ⟨_, _, rd2071⟩ := clipperYankX_lockOpen (v := v) hpatch hlockedEvm rd1994
        obtain ⟨_, _, rd2077⟩ := clipperYankX_lockStore (v := v) hpatch hperm rd2071
        by_cases husrEvm : clipperYankSalesUsrWord σLocked I = ⟨0⟩
        · let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          have hbody :
              ExecTransitionBody (config v) (contract v) evmSolm locals
                (yankTransition v).body .reverted := by
            simpa [evmSolm, locals] using
              (clipperYankInactiveSourceReverts
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                hauthEvm hlockedEvm (by simpa [σLocked] using husrEvm))
          have hrev := clipperYankX_usrZero (v := v) hpatch
            (by simpa [σLocked] using husrEvm) (by simpa [σLocked] using rd2077)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · obtain ⟨_, _, rd2184⟩ := clipperYankX_usrNonzero (v := v) hpatch
            (by simpa [σLocked] using husrEvm) (by simpa [σLocked] using rd2077)
          obtain ⟨_, _, rd2208⟩ := clipperYankX_loadDogAndTab (v := v) hpatch
            (by simpa [clipperYankSalesHashMem] using rd2184)
          obtain ⟨_, _, rd2279⟩ := clipperYankX_dogDigsCallSetup (v := v) hpatch
            rd2208
          obtain ⟨_, _, rd2301⟩ := clipperYankX_dogDigsExtcodesizeGuard (v := v)
            hpatch rd2279
          by_cases hcodeSizeDog :
              Reasoning.Theory.extCodeSizeWord σLocked
                (clipperYankDogTarget σLocked I) = ⟨0⟩
          · let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
            have hbody :
                ExecTransitionBody (config v) (contract v) evmSolm locals
                  (yankTransition v).body .reverted := by
              simpa [evmSolm, locals, σLocked] using
                (clipperYankDogDigsNoCodeSourceReverts
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  v hwv hauthEvm hlockedEvm (by simpa [σLocked] using husrEvm)
                  (by simpa [σLocked] using hcodeSizeDog))
            have hrev := clipperYankX_dogDigsNoCode
              (v := v) (tab := clipperYankSalesTabWord σLocked I)
              (target := clipperYankDogTarget σLocked I) hpatch
              (by
                simpa [σLocked, clipperYankDogTarget, clipperYankDogWord,
                  u256_land_comm] using rd2301)
              hcodeSizeDog
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hcodeSizeDogNE :
                Reasoning.Theory.extCodeSizeWord σLocked
                  (clipperYankDogTarget σLocked I) ≠ ⟨0⟩ := hcodeSizeDog
            have hdogCodeSolm :
                0 < (UInt256.ofNat
                  (((Solm.EVM.storageStore
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    ⟨13⟩ ⟨1⟩).lookupAccount
                      (AccountAddress.ofUInt256
                        (clipperYankDogTarget σLocked I))).option
                    0 (fun acc => acc.code.size))).toNat := by
              let σLock := σLocked
              let target := clipperYankDogTarget σLocked I
              suffices hlookup :
                  0 < (UInt256.ofNat
                    ((σLock.get? (AccountAddress.ofUInt256 target)).option
                      0 (fun acc => acc.code.size))).toNat by
                simpa [σLock, target, σLocked, initState, storageStore_accountMap,
                  storageStore_executionEnv, State.lookupAccount] using hlookup
              unfold Reasoning.Theory.extCodeSizeWord at hcodeSizeDogNE
              cases hacc : σLock.get? (AccountAddress.ofUInt256 target) with
              | none =>
                  exfalso
                  exact hcodeSizeDogNE (by simp [-Std.ExtTreeMap.get?_eq_getElem?, σLock, target, hacc, Option.option])
              | some acc =>
                  have hwordNe :
                      UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
                    intro hzero
                    exact hcodeSizeDogNE (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, σLock, target, hacc] using hzero)
                  have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
                    intro hzeroNat
                    apply hwordNe
                    cases hword : UInt256.ofNat acc.code.size with
                    | mk val =>
                        cases val using Fin.cases
                        · rfl
                        · simp [UInt256.toNat, hword] at hzeroNat
                  simpa [σLock, hacc] using Nat.pos_of_ne_zero htoNatNe
            by_cases hdepthLt : I.depth.val < 1024
            · obtain ⟨σ_dog, zDog, outDog, A_dog, k2317, C2317,
                  rd2317, hcallDogEvmRaw, houtDogSize⟩ :=
                clipperYankX_dogDigsPostCall
                  (code := code)
                  (σStart := σ) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) (σ := σLocked)
                  (sel := clipperSelWord I)
                  (target := clipperYankDogTarget σLocked I)
                  (tab := clipperYankSalesTabWord σLocked I)
                  v hpatch
                  (by
                    simpa [σLocked, clipperYankDogTarget, clipperYankDogWord,
                      u256_land_comm] using rd2301)
                  hcodeSizeDogNE hdepthLt hperm
              cases zDog
              · have hcallDogEvm :
                    typedCallViaEVM (config v)
                      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σLocked }
                      (EVM.address (AccountAddress.ofUInt256
                        (clipperYankDogTarget σLocked I)))
                      "digs" 0
                      [v.ilk,
                        .int (Int.ofNat
                          (clipperYankSalesTabWord σLocked I).toNat)]
                      (false,
                        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ_dog
                          substate := A_dog
                           },
                        outDog) true := by
                  simpa using hcallDogEvmRaw
                have hrev := RD.clipperYankDogDigsCallFailure v hpatch
                  (by simpa using rd2317) houtDogSize (by simp)
                let evmDogEvm : EVM.State :=
                  { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σLocked }
                let evmDogSolmStart : EVM.State :=
                  { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σLocked }
                obtain ⟨σ_dog_solm, A_dog_solm, hcallDogSolmRaw, _hAccountsDog⟩ :=
                  Reasoning.Theory.typedCallViaEVM_sameInputs
                    (evm_solm := evmDogSolmStart) hcallDogEvm rfl
                    (by simp [evmDogSolmStart, initState])
                    (by simp [evmDogSolmStart, initState])
                let evmDogSolm : EVM.State :=
                  { evmDogSolmStart with
                    accountMap := σ_dog_solm
                    substate := A_dog_solm
                     }
                have hlockStateEq :
                    Solm.EVM.storageStore
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        ⟨13⟩ ⟨1⟩ =
                      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σLocked } := by
                  simp [-Std.ExtTreeMap.get?_eq_getElem?, σLocked, initState, Solm.EVM.storageStore, sstoreAccountMap,
                    State.lookupAccount, State.setAccount, Account.updateStorage]
                  cases σ.get? I.codeOwner <;> rfl
                have hcallDogSolm :
                    typedCallViaEVM (config v)
                      (Solm.EVM.storageStore
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        ⟨13⟩ ⟨1⟩)
                      (EVM.address (AccountAddress.ofUInt256
                        (clipperYankDogTarget σLocked I)))
                      "digs" 0
                      [v.ilk,
                        .int (Int.ofNat
                          (clipperYankSalesTabWord σLocked I).toNat)]
                      (false, evmDogSolm, outDog) true := by
                  simpa [evmDogSolm, evmDogSolmStart, evmDogEvm, hlockStateEq, σLocked,
                    storageStore_accountMap, storageStore_executionEnv] using hcallDogSolmRaw
                let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm locals
                      (yankTransition v).body .reverted := by
                  simpa [evmSolm, locals, σLocked] using
                    (clipperYankDogDigsCallFailureSourceReverts
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (evmDog := evmDogSolm) (outDog := outDog)
                      v hwv hauthEvm hlockedEvm
                      (by simpa [σLocked] using husrEvm)
                      hdogCodeSolm hcallDogSolm)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · obtain ⟨k2335, C2335, rd2335raw⟩ :=
                  RD.clipperYankDogDigsCallSuccessToFluxSetup v hpatch
                    (by simpa using rd2317)
                have rd2335 : RD code I (Sat256.ofUInt256 g)
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2335⟩
                    (⟨196⟩ :: clipperDogDigsSelectorWord ::
                      clipperYankDogTarget σLocked I :: clipperYankArgWord I ::
                      ⟨502⟩ :: [clipperSelWord I])
                    (clipperDogDigsCalldataMem v (clipperYankSalesTabWord σLocked I)
                      (clipperYankSalesHashMemRefresh I))
                    (UInt256.ofNat 7) outDog σ_dog k2335 C2335 := by
                  have hmin :
                      (min (⟨0⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat = 0 := by
                    rfl
                  have haw :
                      UInt256.ofNat
                        (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
                          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
                          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
                        UInt256.ofNat 7 := by
                    native_decide
                  simpa [hmin, byteArray_write_len_zero, haw] using rd2335raw
                obtain ⟨k2495, C2495, rd2495⟩ :=
                  RD.clipperYankVatFluxExtcodesizeGuard
                    (code := code)  (σ := σ_dog)
                    (ee := I) (g := Sat256.ofUInt256 g)
                    (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (sel := clipperSelWord I)
                    (dogTarget := clipperYankDogTarget σLocked I)
                    (tab := clipperYankSalesTabWord σLocked I)
                    (rdata := outDog) v hpatch rd2335
                have hcallDogEvm :
                    typedCallViaEVM (config v)
                      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σLocked }
                      (EVM.address (AccountAddress.ofUInt256
                        (clipperYankDogTarget σLocked I)))
                      "digs" 0
                      [v.ilk,
                        .int (Int.ofNat
                          (clipperYankSalesTabWord σLocked I).toNat)]
                      (true,
                        { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                          accountMap := σ_dog
                          substate := A_dog
                           },
                        outDog) true := by
                  simpa using hcallDogEvmRaw
                let evmDogEvm : EVM.State :=
                  { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σLocked }
                let evmDogSolmStart : EVM.State :=
                  { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σLocked }
                obtain ⟨σ_dog_solm, A_dog_solm, hcallDogSolmRaw, hAccountsDog⟩ :=
                  Reasoning.Theory.typedCallViaEVM_sameInputs
                    (evm_solm := evmDogSolmStart) hcallDogEvm rfl
                    (by simp [evmDogSolmStart, initState])
                    (by simp [evmDogSolmStart, initState])
                let evmDogSolm : EVM.State :=
                  { evmDogSolmStart with
                    accountMap := σ_dog_solm
                    substate := A_dog_solm
                     }
                have hlockStateEq :
                    Solm.EVM.storageStore
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        ⟨13⟩ ⟨1⟩ =
                      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σLocked } := by
                  simp [-Std.ExtTreeMap.get?_eq_getElem?, σLocked, initState, Solm.EVM.storageStore, sstoreAccountMap,
                    State.lookupAccount, State.setAccount, Account.updateStorage]
                  cases σ.get? I.codeOwner <;> rfl
                have hcallDogSolm :
                    typedCallViaEVM (config v)
                      (Solm.EVM.storageStore
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        ⟨13⟩ ⟨1⟩)
                      (EVM.address (AccountAddress.ofUInt256
                        (clipperYankDogTarget σLocked I)))
                      "digs" 0
                      [v.ilk,
                        .int (Int.ofNat
                          (clipperYankSalesTabWord σLocked I).toNat)]
                      (true, evmDogSolm, outDog) true := by
                  simpa [evmDogSolm, evmDogSolmStart, evmDogEvm, hlockStateEq, σLocked,
                    storageStore_accountMap, storageStore_executionEnv] using hcallDogSolmRaw
                have hLotWord :
                    clipperYankSalesLotWord σ_dog I =
                      clipperYankSalesLotWord σ_dog_solm I :=
                  congrArg (fun m => clipperYankSalesLotWord m I) hAccountsDog
                by_cases hcodeSizeVat :
                    Reasoning.Theory.extCodeSizeWord σ_dog
                      (clipperYankVatTarget v) = ⟨0⟩
                · have hcodeSizeVatSolm :
                      Reasoning.Theory.extCodeSizeWord σ_dog_solm
                        (clipperYankVatTarget v) = ⟨0⟩ := by
                    simpa only [← hAccountsDog] using hcodeSizeVat
                  have hvatNoCode :
                      (UInt256.ofNat ((evmDogSolm.lookupAccount v.vat).option 0
                        (fun acc => acc.code.size))).toNat = 0 := by
                    unfold Reasoning.Theory.extCodeSizeWord at hcodeSizeVatSolm
                    cases hacc : σ_dog_solm.get? v.vat with
                    | none =>
                        rw [show State.lookupAccount evmDogSolm v.vat = none by
                          simp [-Std.ExtTreeMap.get?_eq_getElem?, evmDogSolm, State.lookupAccount, hacc]]
                        rfl
                    | some acc =>
                        have hword : UInt256.ofNat acc.code.size = ⟨0⟩ := by
                          simpa [-Std.ExtTreeMap.get?_eq_getElem?, clipperYankVatTargetAddress v, hacc] using hcodeSizeVatSolm
                        simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmDogSolm, evmDogSolmStart, State.lookupAccount, hacc] using
                          congrArg UInt256.toNat hword
                  have hrev := clipperYankX_vatFluxNoCode
                    (v := v) (tab := clipperYankSalesTabWord σLocked I)
                    hpatch rd2495 hcodeSizeVat
                  let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
                  have hbody :
                      ExecTransitionBody (config v) (contract v) evmSolm locals
                        (yankTransition v).body .reverted := by
                    simpa [evmSolm, locals, σLocked] using
                      (clipperYankVatFluxNoCodeSourceReverts
                        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (evmDog := evmDogSolm) (outDog := outDog)
                        v hwv hauthEvm hlockedEvm
                        (by simpa [σLocked] using husrEvm)
                        hdogCodeSolm hcallDogSolm hvatNoCode)
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hcodeSizeVatNE :
                      Reasoning.Theory.extCodeSizeWord σ_dog
                        (clipperYankVatTarget v) ≠ ⟨0⟩ := hcodeSizeVat
                  have hcodeSizeVatSolmNE :
                      Reasoning.Theory.extCodeSizeWord σ_dog_solm
                        (clipperYankVatTarget v) ≠ ⟨0⟩ := by
                    simpa only [← hAccountsDog] using hcodeSizeVatNE
                  have hvatCodeSolm :
                      0 < (UInt256.ofNat ((evmDogSolm.lookupAccount v.vat).option 0
                        (fun acc => acc.code.size))).toNat := by
                    have hwordNe :
                        UInt256.ofNat ((σ_dog_solm.get? v.vat).option 0
                          (fun acc => acc.code.size)) ≠ (⟨0⟩ : UInt256) := by
                      intro hzero
                      apply hcodeSizeVatSolmNE
                      unfold Reasoning.Theory.extCodeSizeWord
                      cases hacc : σ_dog_solm.get? v.vat with
                      | none =>
                          rw [clipperYankVatTargetAddress v, hacc]
                          rfl
                      | some acc =>
                          simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperYankVatTargetAddress v, hacc] at hzero ⊢
                          exact hzero
                    have htoNatNe :
                        (UInt256.ofNat ((σ_dog_solm.get? v.vat).option 0
                          (fun acc => acc.code.size))).toNat ≠ 0 := by
                      intro hzero
                      exact hwordNe (uint256_toNat_eq_zero hzero)
                    have hpos :=
                      Nat.pos_of_ne_zero htoNatNe
                    simpa [evmDogSolm, evmDogSolmStart, State.lookupAccount] using hpos
                  obtain ⟨σ_vat, zVat, outVat, A_vat, k2511, C2511,
                      rd2511, hcallVatEvmRaw, houtVatSize⟩ :=
                    RD.clipperYankVatFluxPostCall
                      (code := code)
                      (σStart := σ) (σ₀ := σ₀)
                      (σ := σ_dog) (I := I) (g := Sat256.ofUInt256 g) (A := A)
                      (sel := clipperSelWord I)
                      (tab := clipperYankSalesTabWord σLocked I)
                      (rdata := outDog) v hpatch rd2495 hcodeSizeVatNE hdepthLt hperm
                  cases zVat
                  · have hcallVatEvm :
                        typedCallViaEVM (config v)
                          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                            accountMap := σ_dog
                             }
                          (EVM.address v.vat) "flux" 0
                          [v.ilk, .address I.codeOwner, .address I.source,
                            .int (Int.ofNat (clipperYankSalesLotWord σ_dog I).toNat)]
                          (false,
                            { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                              accountMap := σ_vat
                              substate := A_vat
                               },
                            outVat) true := by
                      simpa using hcallVatEvmRaw
                    have hrev := RD.clipperYankVatFluxCallFailure v hpatch
                      (by simpa using rd2511) houtVatSize (by simp)
                    let evmVatEvmStart : EVM.State :=
                      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ_dog
                         }
                    obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, _hAccountsVat⟩ :=
                      Reasoning.Theory.typedCallViaEVM_sameInputs
                        (evm_solm := evmDogSolm) hcallVatEvm hAccountsDog
                        (by simp [evmVatEvmStart, evmDogSolm, evmDogSolmStart, initState])
                        (by simp [evmVatEvmStart, evmDogSolm, evmDogSolmStart, initState])
                    let evmVatSolm : EVM.State :=
                      { evmDogSolm with
                        accountMap := σ_vat_solm
                        substate := A_vat_solm
                         }
                    have hlotLoadSolm :
                        Solm.EVM.storageLoad evmDogSolm evmDogSolm.executionEnv.codeOwner
                            (clipperYankSalesLotSlot I) =
                          clipperYankSalesLotWord σ_dog_solm I := by
                      simp [evmDogSolm, evmDogSolmStart, clipperYankSalesLotWord,
                        solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, initState]
                      cases σ_dog_solm.get? I.codeOwner <;> rfl
                    have hcallVatSolm :
                        typedCallViaEVM (config v) evmDogSolm (EVM.address v.vat) "flux" 0
                          [v.ilk, .address evmDogSolm.executionEnv.codeOwner,
                            .address evmDogSolm.executionEnv.source,
                            .int (Int.ofNat
                              (Solm.EVM.storageLoad evmDogSolm
                                evmDogSolm.executionEnv.codeOwner
                                (clipperYankSalesLotSlot I)).toNat)]
                          (false, evmVatSolm, outVat) true := by
                      simpa [evmVatSolm, evmVatEvmStart, evmDogSolm, evmDogSolmStart,
                        initState, hLotWord, hlotLoadSolm] using hcallVatSolmRaw
                    let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
                    have hbody :
                        ExecTransitionBody (config v) (contract v) evmSolm locals
                          (yankTransition v).body .reverted := by
                      simpa [evmSolm, locals, σLocked] using
                        (clipperYankVatFluxCallFailureSourceReverts
                          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          (evmDog := evmDogSolm) (evmVat := evmVatSolm)
                          (outDog := outDog) (outVat := outVat)
                          v hwv hauthEvm hlockedEvm
                          (by simpa [σLocked] using husrEvm)
                          hdogCodeSolm hcallDogSolm hvatCodeSolm hcallVatSolm)
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hcallVatEvm :
                        typedCallViaEVM (config v)
                          { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                            accountMap := σ_dog
                             }
                          (EVM.address v.vat) "flux" 0
                          [v.ilk, .address I.codeOwner, .address I.source,
                            .int (Int.ofNat (clipperYankSalesLotWord σ_dog I).toNat)]
                          (true,
                            { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                              accountMap := σ_vat
                              substate := A_vat
                               },
                            outVat) true := by
                      simpa using hcallVatEvmRaw
                    let evmVatEvmStart : EVM.State :=
                      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ_dog
                         }
                    obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hAccountsVatRaw⟩ :=
                      Reasoning.Theory.typedCallViaEVM_sameInputs
                        (evm_solm := evmDogSolm) hcallVatEvm hAccountsDog
                        (by simp [evmVatEvmStart, evmDogSolm, evmDogSolmStart, initState])
                        (by simp [evmVatEvmStart, evmDogSolm, evmDogSolmStart, initState])
                    let evmVatSolm : EVM.State :=
                      { evmDogSolm with
                        accountMap := σ_vat_solm
                        substate := A_vat_solm
                         }
                    have hAccountsVat : Eq σ_vat σ_vat_solm := by
                      simpa [evmVatEvmStart, evmDogSolm, evmDogSolmStart, initState] using
                        hAccountsVatRaw
                    have hlotLoadSolm :
                        Solm.EVM.storageLoad evmDogSolm evmDogSolm.executionEnv.codeOwner
                            (clipperYankSalesLotSlot I) =
                          clipperYankSalesLotWord σ_dog_solm I := by
                      simp [evmDogSolm, evmDogSolmStart, clipperYankSalesLotWord,
                        solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, initState]
                      cases σ_dog_solm.get? I.codeOwner <;> rfl
                    have hcallVatSolm :
                        typedCallViaEVM (config v) evmDogSolm (EVM.address v.vat) "flux" 0
                          [v.ilk, .address evmDogSolm.executionEnv.codeOwner,
                            .address evmDogSolm.executionEnv.source,
                            .int (Int.ofNat
                              (Solm.EVM.storageLoad evmDogSolm
                                evmDogSolm.executionEnv.codeOwner
                                (clipperYankSalesLotSlot I)).toNat)]
                          (true, evmVatSolm, outVat) true := by
                      simpa [evmVatSolm, evmVatEvmStart, evmDogSolm, evmDogSolmStart,
                        initState, hLotWord, hlotLoadSolm] using hcallVatSolmRaw
                    obtain ⟨k8274, C8274, rd8274⟩ :=
                      Benchmarks.Dss.Clipper.RD.clipperYankVatFluxCallSuccessToRemove v hpatch
                        (by simpa using rd2511)
                    by_cases hactiveLenEvm : solcSlotWord σ_vat I ⟨11⟩ = ⟨0⟩
                    · have hinv :=
                        Benchmarks.Dss.Clipper.RD.clipperYankRemoveEmptyInvalid
                          v hpatch rd8274 hactiveLenEvm
                      have hactiveLenSolmWord : solcSlotWord σ_vat_solm I ⟨11⟩ = ⟨0⟩ := by
                        simpa only [hAccountsVat] using hactiveLenEvm
                      have hactiveLenSolm :
                          Solm.EVM.storageLoad evmVatSolm evmVatSolm.executionEnv.codeOwner
                            ⟨11⟩ = ⟨0⟩ := by
                        simpa [evmVatSolm, evmDogSolm, evmDogSolmStart, initState,
                          solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount] using
                          hactiveLenSolmWord
                      let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
                      have hbody :
                          ExecTransitionBody (config v) (contract v) evmSolm locals
                            (yankTransition v).body .reverted := by
                        simpa [evmSolm, locals, σLocked] using
                          (clipperYankRemoveEmptyAfterVatSourceReverts
                            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (evmDog := evmDogSolm) (evmVat := evmVatSolm)
                            (outDog := outDog) (outVat := outVat)
                            v hwv hauthEvm hlockedEvm
                            (by simpa [σLocked] using husrEvm)
                            hdogCodeSolm hcallDogSolm hvatCodeSolm hcallVatSolm
                            hactiveLenSolm)
                      exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdecode hbody
                    · let removeMem :=
                        outVat.write 0
                          (clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ_dog I)
                            (clipperYankVatFluxBaseMem v I
                              (clipperYankSalesTabWord σLocked I)))
                          128 ((⟨0⟩ : UInt256) ⊓ UInt256.ofNat outVat.size).toNat
                      let lastIndexEvm := solcSlotWord σ_vat I ⟨11⟩ + UInt256.lnot ⟨0⟩
                      have hremoveMemSize :
                          64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) removeMem).size := by
                        have hminVat :
                            (((⟨0⟩ : UInt256) ⊓ UInt256.ofNat outVat.size).toNat) = 0 := by
                          rfl
                        have hremoveMemEq :
                            removeMem =
                              clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ_dog I)
                                (clipperYankVatFluxBaseMem v I
                                  (clipperYankSalesTabWord σLocked I)) := by
                          simp [removeMem, hminVat, byteArray_write_len_zero]
                        rw [hremoveMemEq]
                        have hcalldataSize :
                            (clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ_dog I)
                              (clipperYankVatFluxBaseMem v I
                                (clipperYankSalesTabWord σLocked I))).size = 260 :=
                          clipperVatFluxCalldataMem_size v I (clipperYankSalesLotWord σ_dog I)
                            (clipperYankVatFluxBaseMem_size v I
                              (clipperYankSalesTabWord σLocked I))
                        have hwordSize :
                            (wordAt0Mem (⟨11⟩ : UInt256)
                              (clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ_dog I)
                                (clipperYankVatFluxBaseMem v I
                                  (clipperYankSalesTabWord σLocked I)))).size =
                              max
                                (clipperVatFluxCalldataMem v I
                                  (clipperYankSalesLotWord σ_dog I)
                                  (clipperYankVatFluxBaseMem v I
                                    (clipperYankSalesTabWord σLocked I))).size (0 + 32) := by
                          simpa [wordAt0Mem, Reasoning.Theory.writeWord] using
                            (Reasoning.Theory.writeWord_size
                              (clipperVatFluxCalldataMem v I (clipperYankSalesLotWord σ_dog I)
                                (clipperYankVatFluxBaseMem v I
                                  (clipperYankSalesTabWord σLocked I)))
                              0 (⟨11⟩ : UInt256) (by
                                simpa using lt_usize 0 (by norm_num)))
                        rw [hwordSize, hcalldataSize]
                        norm_num
                      have hactiveLenEq :
                          solcSlotWord σ_vat I ⟨11⟩ = solcSlotWord σ_vat_solm I ⟨11⟩ :=
                        congrArg (fun m => solcSlotWord m I ⟨11⟩) hAccountsVat
                      have hactiveLenSolmWord :
                          solcSlotWord σ_vat_solm I ⟨11⟩ ≠ ⟨0⟩ := by
                        intro hzero
                        exact hactiveLenEvm (by simpa [hactiveLenEq, hzero])
                      have hactiveLenSolm :
                          Solm.EVM.storageLoad evmVatSolm evmVatSolm.executionEnv.codeOwner
                            ⟨11⟩ ≠ ⟨0⟩ := by
                        simpa [evmVatSolm, evmDogSolm, evmDogSolmStart, initState,
                          solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount] using
                          hactiveLenSolmWord
                      have hloadLenSolm :
                          Solm.EVM.storageLoad evmVatSolm evmVatSolm.executionEnv.codeOwner
                            ⟨11⟩ = solcSlotWord σ_vat_solm I ⟨11⟩ := by
                        simp [evmVatSolm, evmDogSolm, evmDogSolmStart, initState,
                          solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
                        cases σ_vat_solm.get? I.codeOwner <;> rfl
                      have hlastIndexEq :
                          lastIndexEvm =
                            UInt256.sub
                              (Solm.EVM.storageLoad evmVatSolm
                                evmVatSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
                        rw [show lastIndexEvm =
                            solcSlotWord σ_vat I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
                        rw [clipperYankLenAddLnotZero_eq_subOne]
                        rw [hloadLenSolm, ← hactiveLenEq]
                      have hownerVatSolm : evmVatSolm.executionEnv.codeOwner = I.codeOwner := by
                        simp [evmVatSolm, evmDogSolm, evmDogSolmStart, initState]
                      have haccVatSolmExists :
                          ∃ acc,
                            evmVatSolm.accountMap.get? evmVatSolm.executionEnv.codeOwner =
                              some acc := by
                        cases hfind :
                            evmVatSolm.accountMap.get? evmVatSolm.executionEnv.codeOwner with
                        | none =>
                            exfalso
                            have hzero :
                                Solm.EVM.storageLoad evmVatSolm
                                  evmVatSolm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
                              simp [-Std.ExtTreeMap.get?_eq_getElem?, Solm.EVM.storageLoad, State.lookupAccount, hfind,
                                Option.option]
                            exact hactiveLenSolm hzero
                        | some acc =>
                            exact ⟨acc, rfl⟩
                      obtain ⟨accVatSolm, haccVatSolm⟩ := haccVatSolmExists
                      by_cases hidEq :
                          clipperYankArgWord I =
                            solcSlotWord σ_vat I (clipperYankActiveSlot lastIndexEvm)
                      · obtain ⟨k8379, C8379, rd8379⟩ :=
                          Benchmarks.Dss.Clipper.RD.clipperYankRemoveIdEqMoveToJoin
                            v hpatch
                            (by simpa [removeMem] using rd8274)
                            hactiveLenEvm
                            (by simpa [lastIndexEvm] using hidEq)
                        have hjoinMemSize :
                            64 ≤
                              (wordAt0Mem (⟨11⟩ : UInt256)
                                (wordAt0Mem (⟨11⟩ : UInt256) removeMem)).size := by
                          have hsizeEq :
                              (wordAt0Mem (⟨11⟩ : UInt256)
                                (wordAt0Mem (⟨11⟩ : UInt256) removeMem)).size =
                                  max (wordAt0Mem (⟨11⟩ : UInt256) removeMem).size
                                    (0 + 32) := by
                            simpa [wordAt0Mem, Reasoning.Theory.writeWord] using
                              (Reasoning.Theory.writeWord_size
                                (wordAt0Mem (⟨11⟩ : UInt256) removeMem) 0
                                (⟨11⟩ : UInt256) (by
                                  simpa using lt_usize 0 (by norm_num)))
                          rw [hsizeEq]
                          exact le_trans hremoveMemSize (Nat.le_max_left _ _)
                        have hret :
                            RDret code (Sat256.ofUInt256 g)
                              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                              (clipperYankSuccessAccountMap σ_vat I lastIndexEvm)
                              ByteArray.empty := by
                          simpa [lastIndexEvm] using
                            (Benchmarks.Dss.Clipper.RD.clipperYankRemoveJoinSuccess
                              v hpatch rd8379 hactiveLenEvm hjoinMemSize hperm)
                        have hmoveEq :
                            solcSlotWord σ_vat I (clipperYankActiveSlot lastIndexEvm) =
                              solcSlotWord σ_vat_solm I
                                (clipperYankActiveSlot lastIndexEvm) :=
                          congrArg
                            (fun m => solcSlotWord m I (clipperYankActiveSlot lastIndexEvm))
                            hAccountsVat
                        have hloadMoveSolm :
                            Solm.EVM.storageLoad evmVatSolm
                              evmVatSolm.executionEnv.codeOwner
                              (clipperYankActiveSlot lastIndexEvm) =
                                solcSlotWord σ_vat_solm I
                                  (clipperYankActiveSlot lastIndexEvm) := by
                          simp [evmVatSolm, evmDogSolm, evmDogSolmStart, initState,
                            solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
                          cases σ_vat_solm.get? I.codeOwner <;> rfl
                        have hidEqSolm :
                            clipperYankArgWord I =
                              Solm.EVM.storageLoad evmVatSolm
                                evmVatSolm.executionEnv.codeOwner
                                (clipperYankActiveSlot
                                  (UInt256.sub
                                    (Solm.EVM.storageLoad evmVatSolm
                                      evmVatSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)) := by
                          rw [← hlastIndexEq, hloadMoveSolm, ← hmoveEq]
                          exact hidEq
                        have hafter :=
                          clipperYankAfterVatRemoveIdEqMoveSourceOk v evmVatSolm I
                            haccVatSolm hactiveLenSolm hidEqSolm
                        let evmSolm := initState σ σ₀
                          (Sat256.ofUInt256 g) A I
                        have hbody :
                            ExecTransitionBody (config v) (contract v) evmSolm locals
                              (yankTransition v).body
                              (.returned
                                { contract := contract v,
                                  locals := (clipperYankFluxRetStore I).insert "_removeRet" .unit }
                                (Solm.EVM.storageStore
                                  (clipperYankDeleteSaleState
                                    (clipperYankRemovePopState evmVatSolm
                                      (UInt256.sub
                                        (Solm.EVM.storageLoad evmVatSolm
                                          evmVatSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                    I)
                                  (clipperYankDeleteSaleState
                                    (clipperYankRemovePopState evmVatSolm
                                      (UInt256.sub
                                        (Solm.EVM.storageLoad evmVatSolm
                                          evmVatSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                    I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩)
                                none) := by
                          simpa [evmSolm, locals, σLocked] using
                            (clipperYankAfterVatSourceOk
                              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmDog := evmDogSolm) (evmVat := evmVatSolm)
                              (outDog := outDog) (outVat := outVat)
                              v hwv hauthEvm hlockedEvm
                              (by simpa [σLocked] using husrEvm)
                              hdogCodeSolm hcallDogSolm hvatCodeSolm hcallVatSolm
                              hafter)
                        have hAccountsFinal :
                            Eq
                              (clipperYankSuccessAccountMap σ_vat I lastIndexEvm)
                              (Solm.EVM.storageStore
                                (clipperYankDeleteSaleState
                                  (clipperYankRemovePopState evmVatSolm
                                    (UInt256.sub
                                      (Solm.EVM.storageLoad evmVatSolm
                                        evmVatSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                  I)
                                (clipperYankDeleteSaleState
                                  (clipperYankRemovePopState evmVatSolm
                                    (UInt256.sub
                                      (Solm.EVM.storageLoad evmVatSolm
                                        evmVatSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                  I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩).accountMap := by
                          have hbase :=
                            clipperYankSuccessAccountMap_state_accounts_eq
                              (σ := σ_vat) (τ := σ_vat_solm) evmVatSolm I lastIndexEvm
                              hAccountsVat (by rfl) hownerVatSolm
                          simpa [hlastIndexEq] using hbase
                        exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
                          hAccountsFinal
                          (by
                            simpa [yankTransition] using
                              (returnEquiv.fallthrough (o := ByteArray.empty) (r := none)
                                (t := []) rfl rfl (by native_decide)))
                      · let moveEvm :=
                          solcSlotWord σ_vat I (clipperYankActiveSlot lastIndexEvm)
                        let idxEvm := solcSlotWord σ_vat I (clipperYankSalesPosSlot I)
                        have hmoveEq :
                            moveEvm =
                              solcSlotWord σ_vat_solm I
                                (clipperYankActiveSlot lastIndexEvm) := by
                          simpa [moveEvm] using
                            congrArg
                              (fun m => solcSlotWord m I (clipperYankActiveSlot lastIndexEvm))
                              hAccountsVat
                        have hloadMoveSolm :
                            Solm.EVM.storageLoad evmVatSolm
                              evmVatSolm.executionEnv.codeOwner
                              (clipperYankActiveSlot lastIndexEvm) =
                                solcSlotWord σ_vat_solm I
                                  (clipperYankActiveSlot lastIndexEvm) := by
                          simp [evmVatSolm, evmDogSolm, evmDogSolmStart, initState,
                            solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
                          cases σ_vat_solm.get? I.codeOwner <;> rfl
                        have hidNeSolm :
                            clipperYankArgWord I ≠
                              Solm.EVM.storageLoad evmVatSolm
                                evmVatSolm.executionEnv.codeOwner
                                (clipperYankActiveSlot
                                  (UInt256.sub
                                    (Solm.EVM.storageLoad evmVatSolm
                                      evmVatSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)) := by
                          intro heq
                          apply hidEq
                          rw [← hlastIndexEq, hloadMoveSolm, ← hmoveEq] at heq
                          simpa [moveEvm] using heq
                        have hidxEq :
                            idxEvm =
                              solcSlotWord σ_vat_solm I (clipperYankSalesPosSlot I) := by
                          simpa [idxEvm] using
                            congrArg
                              (fun m => solcSlotWord m I (clipperYankSalesPosSlot I))
                              hAccountsVat
                        have hloadIdxSolm :
                            Solm.EVM.storageLoad evmVatSolm
                              evmVatSolm.executionEnv.codeOwner
                              (clipperYankSalesPosSlot I) =
                                solcSlotWord σ_vat_solm I
                                  (clipperYankSalesPosSlot I) := by
                          simp [evmVatSolm, evmDogSolm, evmDogSolmStart, initState,
                            solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount]
                          cases σ_vat_solm.get? I.codeOwner <;> rfl
                        by_cases hidxBound :
                            idxEvm.toNat < (solcSlotWord σ_vat I ⟨11⟩).toNat
                        · obtain ⟨k8379, C8379, rd8379, hjoinMemSize⟩ :=
                            Benchmarks.Dss.Clipper.RD.clipperYankRemoveIdNeMoveToJoin
                              v hpatch
                              (by simpa [removeMem] using rd8274)
                              hactiveLenEvm
                              (by simpa [lastIndexEvm, moveEvm] using hidEq)
                              (by simpa [removeMem] using hremoveMemSize)
                              (by simpa [idxEvm] using hidxBound)
                              (by simp)
                              hperm
                          let evmIndexSolm :=
                            Solm.EVM.storageStore evmVatSolm
                              evmVatSolm.executionEnv.codeOwner
                              (clipperYankActiveSlot idxEvm) moveEvm
                          let evmMovePosSolm :=
                            Solm.EVM.storageStore evmIndexSolm
                              evmIndexSolm.executionEnv.codeOwner
                              (clipperYankSalesMovePosSlot moveEvm) idxEvm
                          have hmoveAccounts :
                              Eq
                                (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                evmMovePosSolm.accountMap := by
                            simpa [evmIndexSolm, evmMovePosSolm] using
                              clipperYankMoveAccountMap_state_accounts_eq
                                (σ := σ_vat) (τ := σ_vat_solm) evmVatSolm I
                                idxEvm moveEvm hAccountsVat (by rfl) hownerVatSolm
                          have hownerMovePosSolm :
                              evmMovePosSolm.executionEnv.codeOwner = I.codeOwner := by
                            simp [evmMovePosSolm, evmIndexSolm, storageStore_executionEnv,
                              hownerVatSolm]
                          have hloadLenAfterSolm :
                              Solm.EVM.storageLoad evmMovePosSolm
                                evmMovePosSolm.executionEnv.codeOwner ⟨11⟩ =
                                  solcSlotWord evmMovePosSolm.accountMap I ⟨11⟩ := by
                            simp [Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
                              hownerMovePosSolm]
                            cases evmMovePosSolm.accountMap.get? I.codeOwner <;> rfl
                          have hlenAfterEq :
                              solcSlotWord
                                  (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                  I ⟨11⟩ =
                                solcSlotWord evmMovePosSolm.accountMap I ⟨11⟩ :=
                            congrArg (fun m => solcSlotWord m I ⟨11⟩) hmoveAccounts
                          have hidxBoundSolm :
                              (Solm.EVM.storageLoad evmVatSolm
                                evmVatSolm.executionEnv.codeOwner
                                (clipperYankSalesPosSlot I)).toNat <
                                (Solm.EVM.storageLoad evmVatSolm
                                  evmVatSolm.executionEnv.codeOwner ⟨11⟩).toNat := by
                            simpa [idxEvm, hloadIdxSolm, hloadLenSolm, ← hidxEq,
                              ← hactiveLenEq] using hidxBound
                          by_cases hlenAfterEvm :
                              solcSlotWord
                                  (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                  I ⟨11⟩ = ⟨0⟩
                          · have hinv :=
                              Benchmarks.Dss.Clipper.RD.clipperYankRemoveJoinEmptyInvalid
                                v hpatch rd8379 hlenAfterEvm
                            have hlenAfterSolm :
                                Solm.EVM.storageLoad evmMovePosSolm
                                  evmMovePosSolm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
                              rw [hloadLenAfterSolm, ← hlenAfterEq]
                              exact hlenAfterEvm
                            have hremoveRevert :
                                ExecFuncBody (config v)
                                  { contract := contract v, locals := clipperYankRemoveStore I }
                                  evmVatSolm removeFunction.body .reverted := by
                              simpa [evmIndexSolm, evmMovePosSolm, ← hlastIndexEq,
                                hloadMoveSolm, ← hmoveEq, hloadIdxSolm, ← hidxEq] using
                                (clipperYankRemoveIdNeMovePopEmptySourceReverts
                                  v evmVatSolm I hactiveLenSolm hidNeSolm hidxBoundSolm
                                  (by
                                    simpa [evmIndexSolm, evmMovePosSolm, ← hlastIndexEq,
                                      hloadMoveSolm, ← hmoveEq, hloadIdxSolm, ← hidxEq] using
                                      hlenAfterSolm))
                            have hafter :
                                ExecBlock (config v)
                                  { contract := contract v, locals := clipperYankFluxRetStore I }
                                  evmVatSolm
                                  [.internalCall "_remove" [.var "id"] "_removeRet",
                                    .assign .storage lockedRef (.intLit 0)]
                                  .reverted := by
                              exact ExecBlock.consRevert
                                (internalCallFunctionRevert
                                  (cfg := config v)
                                  (caller :=
                                    { contract := contract v,
                                      locals := clipperYankFluxRetStore I })
                                  (evm := evmVatSolm)
                                  (name := "_remove") (retVar := "_removeRet")
                                  (args := [.var "id"])
                                  (argVals := [clipperYankArgValue I])
                                  (callee := removeFunction)
                                  (locals := clipperYankRemoveStore I)
                                  (clipperYankFluxRetStore_removeArgs I v evmVatSolm)
                                  (clipperYankRemoveLookup v)
                                  (clipperYankRemoveBind I)
                                  hremoveRevert)
                            let evmSolm := initState σ σ₀
                              (Sat256.ofUInt256 g) A I
                            have hbody :
                                ExecTransitionBody (config v) (contract v) evmSolm locals
                                  (yankTransition v).body .reverted := by
                              simpa [evmSolm, locals, σLocked] using
                                (clipperYankAfterVatSourceReverts
                                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                  (evmDog := evmDogSolm) (evmVat := evmVatSolm)
                                  (outDog := outDog) (outVat := outVat)
                                  v hwv hauthEvm hlockedEvm
                                  (by simpa [σLocked] using husrEvm)
                                  hdogCodeSolm hcallDogSolm hvatCodeSolm hcallVatSolm
                                  hafter)
                            exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdecode hbody
                          · let lastIndexAfterEvm :=
                              solcSlotWord
                                  (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                  I ⟨11⟩ + UInt256.lnot ⟨0⟩
                            have hret :
                                RDret code (Sat256.ofUInt256 g)
                                  (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                                  (clipperYankSuccessAccountMap
                                      (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                      I lastIndexAfterEvm)
                                  ByteArray.empty := by
                              simpa [lastIndexAfterEvm] using
                                (Benchmarks.Dss.Clipper.RD.clipperYankRemoveJoinSuccess
                                  v hpatch rd8379 hlenAfterEvm hjoinMemSize hperm)
                            have hlenAfterSolm :
                                Solm.EVM.storageLoad evmMovePosSolm
                                  evmMovePosSolm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
                              intro hzero
                              exact hlenAfterEvm (by
                                rw [hloadLenAfterSolm, ← hlenAfterEq] at hzero
                                exact hzero)
                            have hlastAfterEq :
                                lastIndexAfterEvm =
                                  UInt256.sub
                                    (Solm.EVM.storageLoad evmMovePosSolm
                                      evmMovePosSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
                              rw [show lastIndexAfterEvm =
                                  solcSlotWord
                                    (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                    I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
                              rw [clipperYankLenAddLnotZero_eq_subOne]
                              rw [hloadLenAfterSolm, ← hlenAfterEq]
                            have hafter :
                                ExecBlock (config v)
                                  { contract := contract v, locals := clipperYankFluxRetStore I }
                                  evmVatSolm
                                  [.internalCall "_remove" [.var "id"] "_removeRet",
                                    .assign .storage lockedRef (.intLit 0)]
                                  (.ok
                                    { contract := contract v,
                                      locals := (clipperYankFluxRetStore I).insert
                                        "_removeRet" .unit }
                                    (Solm.EVM.storageStore
                                      (clipperYankDeleteSaleState
                                        (clipperYankRemovePopState evmMovePosSolm
                                          (UInt256.sub
                                            (Solm.EVM.storageLoad evmMovePosSolm
                                              evmMovePosSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                        I)
                                      (clipperYankDeleteSaleState
                                        (clipperYankRemovePopState evmMovePosSolm
                                          (UInt256.sub
                                            (Solm.EVM.storageLoad evmMovePosSolm
                                              evmMovePosSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                        I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
                              simpa [evmIndexSolm, evmMovePosSolm, ← hlastIndexEq,
                                hloadMoveSolm, ← hmoveEq, hloadIdxSolm, ← hidxEq] using
                                (clipperYankAfterVatRemoveIdNeMoveSourceOk
                                  v evmVatSolm I haccVatSolm hactiveLenSolm hidNeSolm
                                  hidxBoundSolm
                                  (by
                                    simpa [evmIndexSolm, evmMovePosSolm, ← hlastIndexEq,
                                      hloadMoveSolm, ← hmoveEq, hloadIdxSolm, ← hidxEq] using
                                      hlenAfterSolm))
                            let evmSolm := initState σ σ₀
                              (Sat256.ofUInt256 g) A I
                            have hbody :
                                ExecTransitionBody (config v) (contract v) evmSolm locals
                                  (yankTransition v).body
                                  (.returned
                                    { contract := contract v,
                                      locals := (clipperYankFluxRetStore I).insert
                                        "_removeRet" .unit }
                                    (Solm.EVM.storageStore
                                      (clipperYankDeleteSaleState
                                        (clipperYankRemovePopState evmMovePosSolm
                                          (UInt256.sub
                                            (Solm.EVM.storageLoad evmMovePosSolm
                                              evmMovePosSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                        I)
                                      (clipperYankDeleteSaleState
                                        (clipperYankRemovePopState evmMovePosSolm
                                          (UInt256.sub
                                            (Solm.EVM.storageLoad evmMovePosSolm
                                              evmMovePosSolm.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                        I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩)
                                    none) := by
                              simpa [evmSolm, locals, σLocked] using
                                (clipperYankAfterVatSourceOk
                                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                  (evmDog := evmDogSolm) (evmVat := evmVatSolm)
                                  (outDog := outDog) (outVat := outVat)
                                  v hwv hauthEvm hlockedEvm
                                  (by simpa [σLocked] using husrEvm)
                                  hdogCodeSolm hcallDogSolm hvatCodeSolm hcallVatSolm
                                  hafter)
                            have hAccountsFinal :
                                Eq
                                  (clipperYankSuccessAccountMap
                                    (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                    I lastIndexAfterEvm)
                                  (Solm.EVM.storageStore
                                    (clipperYankDeleteSaleState
                                      (clipperYankRemovePopState evmMovePosSolm
                                        (UInt256.sub
                                          (Solm.EVM.storageLoad evmMovePosSolm
                                            evmMovePosSolm.executionEnv.codeOwner ⟨11⟩)
                                          ⟨1⟩))
                                      I)
                                    (clipperYankDeleteSaleState
                                      (clipperYankRemovePopState evmMovePosSolm
                                        (UInt256.sub
                                          (Solm.EVM.storageLoad evmMovePosSolm
                                            evmMovePosSolm.executionEnv.codeOwner ⟨11⟩)
                                          ⟨1⟩))
                                      I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩).accountMap := by
                              have hbase :=
                                clipperYankSuccessAccountMap_state_accounts_eq
                                  (σ := clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                  (τ := evmMovePosSolm.accountMap)
                                  evmMovePosSolm I lastIndexAfterEvm
                                  hmoveAccounts (by rfl) hownerMovePosSolm
                              simpa [hlastAfterEq] using hbase
                            exact hret.reEquivExecutionGen hcode hdispatch hdecode
                              hbody hAccountsFinal
                              (by
                                simpa [yankTransition] using
                                  (returnEquiv.fallthrough (o := ByteArray.empty) (r := none)
                                    (t := []) rfl rfl (by native_decide)))
                        · have hidxBoundEvm :
                              (solcSlotWord σ_vat I ⟨11⟩).toNat ≤ idxEvm.toNat :=
                            Nat.le_of_not_gt hidxBound
                          have hinv :=
                            Benchmarks.Dss.Clipper.RD.clipperYankRemoveIdNeMoveIndexOobInvalid
                              v hpatch
                              (by simpa [removeMem] using rd8274)
                              hactiveLenEvm
                              (by simpa [lastIndexEvm, moveEvm] using hidEq)
                              (by simpa [removeMem] using hremoveMemSize)
                              (by simpa [idxEvm] using hidxBoundEvm)
                          have hidxBoundSolm :
                              (Solm.EVM.storageLoad evmVatSolm
                                evmVatSolm.executionEnv.codeOwner ⟨11⟩).toNat ≤
                                (Solm.EVM.storageLoad evmVatSolm
                                  evmVatSolm.executionEnv.codeOwner
                                  (clipperYankSalesPosSlot I)).toNat := by
                            simpa [idxEvm, hloadIdxSolm, hloadLenSolm, ← hidxEq,
                              ← hactiveLenEq] using hidxBoundEvm
                          have hremoveRevert :
                              ExecFuncBody (config v)
                                { contract := contract v, locals := clipperYankRemoveStore I }
                                evmVatSolm removeFunction.body .reverted :=
                            clipperYankRemoveIdNeMoveIndexOobSourceReverts
                              v evmVatSolm I hactiveLenSolm hidNeSolm hidxBoundSolm
                          have hafter :
                              ExecBlock (config v)
                                { contract := contract v, locals := clipperYankFluxRetStore I }
                                evmVatSolm
                                [.internalCall "_remove" [.var "id"] "_removeRet",
                                  .assign .storage lockedRef (.intLit 0)]
                                .reverted := by
                            exact ExecBlock.consRevert
                              (internalCallFunctionRevert
                                (cfg := config v)
                                (caller :=
                                  { contract := contract v, locals := clipperYankFluxRetStore I })
                                (evm := evmVatSolm)
                                (name := "_remove") (retVar := "_removeRet")
                                (args := [.var "id"])
                                (argVals := [clipperYankArgValue I])
                                (callee := removeFunction)
                                (locals := clipperYankRemoveStore I)
                                (clipperYankFluxRetStore_removeArgs I v evmVatSolm)
                                (clipperYankRemoveLookup v)
                                (clipperYankRemoveBind I)
                                hremoveRevert)
                          let evmSolm := initState σ σ₀
                            (Sat256.ofUInt256 g) A I
                          have hbody :
                              ExecTransitionBody (config v) (contract v) evmSolm locals
                                (yankTransition v).body .reverted := by
                            simpa [evmSolm, locals, σLocked] using
                              (clipperYankAfterVatSourceReverts
                                (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (evmDog := evmDogSolm) (evmVat := evmVatSolm)
                                (outDog := outDog) (outVat := outVat)
                                v hwv hauthEvm hlockedEvm
                                (by simpa [σLocked] using husrEvm)
                                hdogCodeSolm hcallDogSolm hvatCodeSolm hcallVatSolm
                                hafter)
                          exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdecode hbody
            · have hdepthEq : I.depth = 1024 := by
                have hval : I.depth.val = 1024 := by
                  have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
                  omega
                apply Fin.ext
                simpa using hval
              obtain ⟨k2317, C2317, rd2317⟩ :=
                RD.clipperYankDogDigsCallDepthLimit
                  (code := code)
                  (σStart := σ) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) (σ := σLocked)
                  (sel := clipperSelWord I)
                  (target := clipperYankDogTarget σLocked I)
                  (tab := clipperYankSalesTabWord σLocked I)
                  v hpatch
                  (by
                    simpa [σLocked, clipperYankDogTarget, clipperYankDogWord,
                      u256_land_comm] using rd2301)
                  hcodeSizeDogNE hdepthEq
              have hrev := RD.clipperYankDogDigsCallFailure v hpatch
                (by simpa using rd2317) (by native_decide) (by simp)
              let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
              let evmSolmLock :=
                Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
              let A_dog :=
                (evmSolmLock.addAccessedAccount
                  (EVM.address (AccountAddress.ofUInt256
                    (clipperYankDogTarget σLocked I)))).substate
              let evmDogSolm : EVM.State := { evmSolmLock with substate := A_dog }
              have hdepthLock : evmSolmLock.executionEnv.depth = 1024 := by
                simpa [evmSolmLock, evmSolm, initState, storageStore_executionEnv]
                  using hdepthEq
              have hcallDogSolm :
                  typedCallViaEVM (config v)
                    (Solm.EVM.storageStore
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                      ⟨13⟩ ⟨1⟩)
                    (EVM.address (AccountAddress.ofUInt256
                      (clipperYankDogTarget σLocked I)))
                    "digs" 0
                    [v.ilk,
                      .int (Int.ofNat
                        (clipperYankSalesTabWord σLocked I).toNat)]
                    (false, evmDogSolm, ByteArray.empty) true := by
                simpa [evmDogSolm, A_dog, evmSolmLock, evmSolm, σLocked, initState,
                  storageStore_accountMap, storageStore_executionEnv] using
                  (callNotMade_depthLimit (cfg := config v) (evm := evmSolmLock)
                    (tgt := EVM.address (AccountAddress.ofUInt256
                      (clipperYankDogTarget σLocked I)))
                    (name := "digs")
                    (args := [v.ilk,
                      .int (Int.ofNat
                        (clipperYankSalesTabWord σLocked I).toNat)])
                    (callPerm := true)
                    (calldata :=
                      (clipperDogDigsCalldataMem v
                        (clipperYankSalesTabWord σLocked I)
                        (clipperYankSalesHashMemRefresh I)).readWithPadding 128 68)
                    (by
                      simpa [clipperYankSalesHashMemRefresh_size I] using
                        clipperDogDigsEncode_eq v
                          (clipperYankSalesTabWord σLocked I)
                          (clipperYankSalesHashMemRefresh_size I))
                    hdepthLock)
              have hbody :
                  ExecTransitionBody (config v) (contract v) evmSolm locals
                    (yankTransition v).body .reverted := by
                simpa [evmSolm, locals, σLocked] using
                  (clipperYankDogDigsCallFailureSourceReverts
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmDog := evmDogSolm) (outDog := ByteArray.empty)
                    v hwv hauthEvm hlockedEvm
                    (by simpa [σLocked] using husrEvm)
                    hdogCodeSolm hcallDogSolm)
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody (config v) (contract v) evmSolm locals
              (yankTransition v).body .reverted := by
          simpa [evmSolm, locals] using
            (clipperYankLockedSourceReverts
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
              hauthEvm hlockedEvm)
        obtain ⟨_, _, rd1912⟩ := hreachBody
        obtain ⟨_, _, rd1994⟩ := clipperYankX_authorized (v := v) hpatch hauthEvm rd1912
        have hrev := clipperYankX_locked (v := v) hpatch hlockedEvm rd1994
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evmSolm locals
            (yankTransition v).body .reverted := by
        simpa [evmSolm, locals] using
          (clipperYankAuthSourceReverts
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv hauthEvm)
      obtain ⟨_, _, rd1912⟩ := hreachBody
      have hrev := clipperYankX_unauthorized (v := v) hpatch hauthEvm rd1912
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hrev := clipperYankX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4
      hsize hshort hreachEntry
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (clipperDecode_yank_none_short v hsz4 hshort)

end Benchmarks.Dss.Clipper
