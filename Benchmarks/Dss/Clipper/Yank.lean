import Reasoning.ExternalCall
import Benchmarks.Dss.Clipper.YankSuccessSource
import Benchmarks.Dss.Clipper.YankVatEVM

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 8000000 in
theorem clipperYankBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 28)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 28) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some yankTransition :=
    clipperDispatch_yank hsel
  have hreachEntry := clipperReachYankBody (fork := fork)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := clipperDecode_yank_ok (I := I) hsz36
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
        have hfirstWrite := clipperYankX_lockStoreSplit (v := v) hpatch rd2071
        rcases hfirstWrite with ⟨hperm, _, _, rd2077⟩ | ⟨hperm, hstatic⟩
        swap
        · exact hstatic.reEquivStaticHalt hcode hdispatch hdecode
            ((clipperYankInactiveSourceRevertsSplit v hwv hauthEvm hlockedEvm).2 hperm)
        by_cases husrEvm : clipperYankSalesUsrWord σLocked I = ⟨0⟩
        · let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
          have hbody :
              ExecTransitionBody fork config contract evmStele locals
                yankTransition.body .reverted (immStore v) := by
            simpa [evmStele, locals] using
              (clipperYankInactiveSourceReverts (fork := fork) (hperm := by assumption)
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
          · let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
            have hbody :
                ExecTransitionBody fork config contract evmStele locals
                  yankTransition.body .reverted (immStore v) := by
              simpa [evmStele, locals, σLocked] using
                (clipperYankDogDigsNoCodeSourceReverts (fork := fork) (hperm := by assumption)
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
            have hdogCodeStele :
                0 < (UInt256.ofNat
                  (((Stele.EVM.storageStore
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
                    typedCallViaEVM fork config
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
                let evmDogSteleStart : EVM.State :=
                  { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σLocked }
                obtain ⟨σ_dog_stele, A_dog_stele, hcallDogSteleRaw, _hAccountsDog⟩ :=
                  Reasoning.Theory.typedCallViaEVM_sameInputs
                    (evm_stele := evmDogSteleStart) hcallDogEvm rfl
                    (by simp [evmDogSteleStart, initState])
                    (by simp [evmDogSteleStart, initState])
                let evmDogStele : EVM.State :=
                  { evmDogSteleStart with
                    accountMap := σ_dog_stele
                    substate := A_dog_stele
                     }
                have hlockStateEq :
                    Stele.EVM.storageStore
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        ⟨13⟩ ⟨1⟩ =
                      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σLocked } := by
                  simp [-Std.ExtTreeMap.get?_eq_getElem?, σLocked, initState, Stele.EVM.storageStore, sstoreAccountMap,
                    State.lookupAccount, State.setAccount, Account.updateStorage]
                  cases σ.get? I.codeOwner <;> rfl
                have hcallDogStele :
                    typedCallViaEVM fork config
                      (Stele.EVM.storageStore
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        ⟨13⟩ ⟨1⟩)
                      (EVM.address (AccountAddress.ofUInt256
                        (clipperYankDogTarget σLocked I)))
                      "digs" 0
                      [v.ilk,
                        .int (Int.ofNat
                          (clipperYankSalesTabWord σLocked I).toNat)]
                      (false, evmDogStele, outDog) true := by
                  simpa [evmDogStele, evmDogSteleStart, evmDogEvm, hlockStateEq, σLocked,
                    storageStore_accountMap, storageStore_executionEnv] using hcallDogSteleRaw
                let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
                have hbody :
                    ExecTransitionBody fork config contract evmStele locals
                      yankTransition.body .reverted (immStore v) := by
                  simpa [evmStele, locals, σLocked] using
                    (clipperYankDogDigsCallFailureSourceReverts (fork := fork) (hperm := by assumption)
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (evmDog := evmDogStele) (outDog := outDog)
                      v hwv hauthEvm hlockedEvm
                      (by simpa [σLocked] using husrEvm)
                      hdogCodeStele hcallDogStele)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · obtain ⟨k2335, C2335, rd2335raw⟩ :=
                  RD.clipperYankDogDigsCallSuccessToFluxSetup v hpatch
                    (by simpa using rd2317)
                have rd2335 : RD fork code I (Sat256.ofUInt256 g)
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
                    typedCallViaEVM fork config
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
                let evmDogSteleStart : EVM.State :=
                  { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σLocked }
                obtain ⟨σ_dog_stele, A_dog_stele, hcallDogSteleRaw, hAccountsDog⟩ :=
                  Reasoning.Theory.typedCallViaEVM_sameInputs
                    (evm_stele := evmDogSteleStart) hcallDogEvm rfl
                    (by simp [evmDogSteleStart, initState])
                    (by simp [evmDogSteleStart, initState])
                let evmDogStele : EVM.State :=
                  { evmDogSteleStart with
                    accountMap := σ_dog_stele
                    substate := A_dog_stele
                     }
                have hlockStateEq :
                    Stele.EVM.storageStore
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        ⟨13⟩ ⟨1⟩ =
                      { initState σ σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σLocked } := by
                  simp [-Std.ExtTreeMap.get?_eq_getElem?, σLocked, initState, Stele.EVM.storageStore, sstoreAccountMap,
                    State.lookupAccount, State.setAccount, Account.updateStorage]
                  cases σ.get? I.codeOwner <;> rfl
                have hcallDogStele :
                    typedCallViaEVM fork config
                      (Stele.EVM.storageStore
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                        ⟨13⟩ ⟨1⟩)
                      (EVM.address (AccountAddress.ofUInt256
                        (clipperYankDogTarget σLocked I)))
                      "digs" 0
                      [v.ilk,
                        .int (Int.ofNat
                          (clipperYankSalesTabWord σLocked I).toNat)]
                      (true, evmDogStele, outDog) true := by
                  simpa [evmDogStele, evmDogSteleStart, evmDogEvm, hlockStateEq, σLocked,
                    storageStore_accountMap, storageStore_executionEnv] using hcallDogSteleRaw
                have hLotWord :
                    clipperYankSalesLotWord σ_dog I =
                      clipperYankSalesLotWord σ_dog_stele I :=
                  congrArg (fun m => clipperYankSalesLotWord m I) hAccountsDog
                by_cases hcodeSizeVat :
                    Reasoning.Theory.extCodeSizeWord σ_dog
                      (clipperYankVatTarget v) = ⟨0⟩
                · have hcodeSizeVatStele :
                      Reasoning.Theory.extCodeSizeWord σ_dog_stele
                        (clipperYankVatTarget v) = ⟨0⟩ := by
                    simpa only [← hAccountsDog] using hcodeSizeVat
                  have hvatNoCode :
                      (UInt256.ofNat ((evmDogStele.lookupAccount v.vat).option 0
                        (fun acc => acc.code.size))).toNat = 0 := by
                    unfold Reasoning.Theory.extCodeSizeWord at hcodeSizeVatStele
                    cases hacc : σ_dog_stele.get? v.vat with
                    | none =>
                        rw [show State.lookupAccount evmDogStele v.vat = none by
                          simp [-Std.ExtTreeMap.get?_eq_getElem?, evmDogStele, State.lookupAccount, hacc]]
                        rfl
                    | some acc =>
                        have hword : UInt256.ofNat acc.code.size = ⟨0⟩ := by
                          simpa [-Std.ExtTreeMap.get?_eq_getElem?, clipperYankVatTargetAddress v, hacc] using hcodeSizeVatStele
                        simpa [-Std.ExtTreeMap.get?_eq_getElem?, evmDogStele, evmDogSteleStart, State.lookupAccount, hacc] using
                          congrArg UInt256.toNat hword
                  have hrev := clipperYankX_vatFluxNoCode
                    (v := v) (tab := clipperYankSalesTabWord σLocked I)
                    hpatch rd2495 hcodeSizeVat
                  let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
                  have hbody :
                      ExecTransitionBody fork config contract evmStele locals
                        yankTransition.body .reverted (immStore v) := by
                    simpa [evmStele, locals, σLocked] using
                      (clipperYankVatFluxNoCodeSourceReverts (fork := fork) (hperm := by assumption)
                        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (evmDog := evmDogStele) (outDog := outDog)
                        v hwv hauthEvm hlockedEvm
                        (by simpa [σLocked] using husrEvm)
                        hdogCodeStele hcallDogStele hvatNoCode)
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hcodeSizeVatNE :
                      Reasoning.Theory.extCodeSizeWord σ_dog
                        (clipperYankVatTarget v) ≠ ⟨0⟩ := hcodeSizeVat
                  have hcodeSizeVatSteleNE :
                      Reasoning.Theory.extCodeSizeWord σ_dog_stele
                        (clipperYankVatTarget v) ≠ ⟨0⟩ := by
                    simpa only [← hAccountsDog] using hcodeSizeVatNE
                  have hvatCodeStele :
                      0 < (UInt256.ofNat ((evmDogStele.lookupAccount v.vat).option 0
                        (fun acc => acc.code.size))).toNat := by
                    have hwordNe :
                        UInt256.ofNat ((σ_dog_stele.get? v.vat).option 0
                          (fun acc => acc.code.size)) ≠ (⟨0⟩ : UInt256) := by
                      intro hzero
                      apply hcodeSizeVatSteleNE
                      unfold Reasoning.Theory.extCodeSizeWord
                      cases hacc : σ_dog_stele.get? v.vat with
                      | none =>
                          rw [clipperYankVatTargetAddress v, hacc]
                          rfl
                      | some acc =>
                          simp [-Std.ExtTreeMap.get?_eq_getElem?, clipperYankVatTargetAddress v, hacc] at hzero ⊢
                          exact hzero
                    have htoNatNe :
                        (UInt256.ofNat ((σ_dog_stele.get? v.vat).option 0
                          (fun acc => acc.code.size))).toNat ≠ 0 := by
                      intro hzero
                      exact hwordNe (uint256_toNat_eq_zero hzero)
                    have hpos :=
                      Nat.pos_of_ne_zero htoNatNe
                    simpa [evmDogStele, evmDogSteleStart, State.lookupAccount] using hpos
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
                        typedCallViaEVM fork config
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
                    obtain ⟨σ_vat_stele, A_vat_stele, hcallVatSteleRaw, _hAccountsVat⟩ :=
                      Reasoning.Theory.typedCallViaEVM_sameInputs
                        (evm_stele := evmDogStele) hcallVatEvm hAccountsDog
                        (by simp [evmVatEvmStart, evmDogStele, evmDogSteleStart, initState])
                        (by simp [evmVatEvmStart, evmDogStele, evmDogSteleStart, initState])
                    let evmVatStele : EVM.State :=
                      { evmDogStele with
                        accountMap := σ_vat_stele
                        substate := A_vat_stele
                         }
                    have hlotLoadStele :
                        Stele.EVM.storageLoad evmDogStele evmDogStele.executionEnv.codeOwner
                            (clipperYankSalesLotSlot I) =
                          clipperYankSalesLotWord σ_dog_stele I := by
                      simp [evmDogStele, evmDogSteleStart, clipperYankSalesLotWord,
                        solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount, initState]
                      cases σ_dog_stele.get? I.codeOwner <;> rfl
                    have hcallVatStele :
                        typedCallViaEVM fork config evmDogStele (EVM.address v.vat) "flux" 0
                          [v.ilk, .address evmDogStele.executionEnv.codeOwner,
                            .address evmDogStele.executionEnv.source,
                            .int (Int.ofNat
                              (Stele.EVM.storageLoad evmDogStele
                                evmDogStele.executionEnv.codeOwner
                                (clipperYankSalesLotSlot I)).toNat)]
                          (false, evmVatStele, outVat) true := by
                      simpa [evmVatStele, evmVatEvmStart, evmDogStele, evmDogSteleStart,
                        initState, hLotWord, hlotLoadStele] using hcallVatSteleRaw
                    let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
                    have hbody :
                        ExecTransitionBody fork config contract evmStele locals
                          yankTransition.body .reverted (immStore v) := by
                      simpa [evmStele, locals, σLocked] using
                        (clipperYankVatFluxCallFailureSourceReverts (fork := fork) (hperm := by assumption)
                          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          (evmDog := evmDogStele) (evmVat := evmVatStele)
                          (outDog := outDog) (outVat := outVat)
                          v hwv hauthEvm hlockedEvm
                          (by simpa [σLocked] using husrEvm)
                          hdogCodeStele hcallDogStele hvatCodeStele hcallVatStele)
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hcallVatEvm :
                        typedCallViaEVM fork config
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
                    obtain ⟨σ_vat_stele, A_vat_stele, hcallVatSteleRaw, hAccountsVatRaw⟩ :=
                      Reasoning.Theory.typedCallViaEVM_sameInputs
                        (evm_stele := evmDogStele) hcallVatEvm hAccountsDog
                        (by simp [evmVatEvmStart, evmDogStele, evmDogSteleStart, initState])
                        (by simp [evmVatEvmStart, evmDogStele, evmDogSteleStart, initState])
                    let evmVatStele : EVM.State :=
                      { evmDogStele with
                        accountMap := σ_vat_stele
                        substate := A_vat_stele
                         }
                    have hAccountsVat : Eq σ_vat σ_vat_stele := by
                      simpa [evmVatEvmStart, evmDogStele, evmDogSteleStart, initState] using
                        hAccountsVatRaw
                    have hlotLoadStele :
                        Stele.EVM.storageLoad evmDogStele evmDogStele.executionEnv.codeOwner
                            (clipperYankSalesLotSlot I) =
                          clipperYankSalesLotWord σ_dog_stele I := by
                      simp [evmDogStele, evmDogSteleStart, clipperYankSalesLotWord,
                        solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount, initState]
                      cases σ_dog_stele.get? I.codeOwner <;> rfl
                    have hcallVatStele :
                        typedCallViaEVM fork config evmDogStele (EVM.address v.vat) "flux" 0
                          [v.ilk, .address evmDogStele.executionEnv.codeOwner,
                            .address evmDogStele.executionEnv.source,
                            .int (Int.ofNat
                              (Stele.EVM.storageLoad evmDogStele
                                evmDogStele.executionEnv.codeOwner
                                (clipperYankSalesLotSlot I)).toNat)]
                          (true, evmVatStele, outVat) true := by
                      simpa [evmVatStele, evmVatEvmStart, evmDogStele, evmDogSteleStart,
                        initState, hLotWord, hlotLoadStele] using hcallVatSteleRaw
                    obtain ⟨k8274, C8274, rd8274⟩ :=
                      Benchmarks.Dss.Clipper.RD.clipperYankVatFluxCallSuccessToRemove v hpatch
                        (by simpa using rd2511)
                    by_cases hactiveLenEvm : solcSlotWord σ_vat I ⟨11⟩ = ⟨0⟩
                    · have hinv :=
                        Benchmarks.Dss.Clipper.RD.clipperYankRemoveEmptyInvalid
                          v hpatch rd8274 hactiveLenEvm
                      have hactiveLenSteleWord : solcSlotWord σ_vat_stele I ⟨11⟩ = ⟨0⟩ := by
                        simpa only [hAccountsVat] using hactiveLenEvm
                      have hactiveLenStele :
                          Stele.EVM.storageLoad evmVatStele evmVatStele.executionEnv.codeOwner
                            ⟨11⟩ = ⟨0⟩ := by
                        simpa [evmVatStele, evmDogStele, evmDogSteleStart, initState,
                          solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount] using
                          hactiveLenSteleWord
                      let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
                      have hbody :
                          ExecTransitionBody fork config contract evmStele locals
                            yankTransition.body .reverted (immStore v) := by
                        simpa [evmStele, locals, σLocked] using
                          (clipperYankRemoveEmptyAfterVatSourceReverts (fork := fork) (hperm := by assumption)
                            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (evmDog := evmDogStele) (evmVat := evmVatStele)
                            (outDog := outDog) (outVat := outVat)
                            v hwv hauthEvm hlockedEvm
                            (by simpa [σLocked] using husrEvm)
                            hdogCodeStele hcallDogStele hvatCodeStele hcallVatStele
                            hactiveLenStele)
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
                          solcSlotWord σ_vat I ⟨11⟩ = solcSlotWord σ_vat_stele I ⟨11⟩ :=
                        congrArg (fun m => solcSlotWord m I ⟨11⟩) hAccountsVat
                      have hactiveLenSteleWord :
                          solcSlotWord σ_vat_stele I ⟨11⟩ ≠ ⟨0⟩ := by
                        intro hzero
                        exact hactiveLenEvm (by simpa [hactiveLenEq, hzero])
                      have hactiveLenStele :
                          Stele.EVM.storageLoad evmVatStele evmVatStele.executionEnv.codeOwner
                            ⟨11⟩ ≠ ⟨0⟩ := by
                        simpa [evmVatStele, evmDogStele, evmDogSteleStart, initState,
                          solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount] using
                          hactiveLenSteleWord
                      have hloadLenStele :
                          Stele.EVM.storageLoad evmVatStele evmVatStele.executionEnv.codeOwner
                            ⟨11⟩ = solcSlotWord σ_vat_stele I ⟨11⟩ := by
                        simp [evmVatStele, evmDogStele, evmDogSteleStart, initState,
                          solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount]
                        cases σ_vat_stele.get? I.codeOwner <;> rfl
                      have hlastIndexEq :
                          lastIndexEvm =
                            UInt256.sub
                              (Stele.EVM.storageLoad evmVatStele
                                evmVatStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
                        rw [show lastIndexEvm =
                            solcSlotWord σ_vat I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
                        rw [u256_add_lnot_zero_eq_sub_one]
                        rw [hloadLenStele, ← hactiveLenEq]
                      have hownerVatStele : evmVatStele.executionEnv.codeOwner = I.codeOwner := by
                        simp [evmVatStele, evmDogStele, evmDogSteleStart, initState]
                      have haccVatSteleExists :
                          ∃ acc,
                            evmVatStele.accountMap.get? evmVatStele.executionEnv.codeOwner =
                              some acc := by
                        cases hfind :
                            evmVatStele.accountMap.get? evmVatStele.executionEnv.codeOwner with
                        | none =>
                            exfalso
                            have hzero :
                                Stele.EVM.storageLoad evmVatStele
                                  evmVatStele.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
                              simp [-Std.ExtTreeMap.get?_eq_getElem?, Stele.EVM.storageLoad, State.lookupAccount, hfind,
                                Option.option]
                            exact hactiveLenStele hzero
                        | some acc =>
                            exact ⟨acc, rfl⟩
                      obtain ⟨accVatStele, haccVatStele⟩ := haccVatSteleExists
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
                            RDret fork code (Sat256.ofUInt256 g)
                              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                              (clipperYankSuccessAccountMap σ_vat I lastIndexEvm)
                              ByteArray.empty := by
                          simpa [lastIndexEvm] using
                            (Benchmarks.Dss.Clipper.RD.clipperYankRemoveJoinSuccess
                              v hpatch rd8379 hactiveLenEvm hjoinMemSize hperm)
                        have hmoveEq :
                            solcSlotWord σ_vat I (clipperYankActiveSlot lastIndexEvm) =
                              solcSlotWord σ_vat_stele I
                                (clipperYankActiveSlot lastIndexEvm) :=
                          congrArg
                            (fun m => solcSlotWord m I (clipperYankActiveSlot lastIndexEvm))
                            hAccountsVat
                        have hloadMoveStele :
                            Stele.EVM.storageLoad evmVatStele
                              evmVatStele.executionEnv.codeOwner
                              (clipperYankActiveSlot lastIndexEvm) =
                                solcSlotWord σ_vat_stele I
                                  (clipperYankActiveSlot lastIndexEvm) := by
                          simp [evmVatStele, evmDogStele, evmDogSteleStart, initState,
                            solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount]
                          cases σ_vat_stele.get? I.codeOwner <;> rfl
                        have hidEqStele :
                            clipperYankArgWord I =
                              Stele.EVM.storageLoad evmVatStele
                                evmVatStele.executionEnv.codeOwner
                                (clipperYankActiveSlot
                                  (UInt256.sub
                                    (Stele.EVM.storageLoad evmVatStele
                                      evmVatStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)) := by
                          rw [← hlastIndexEq, hloadMoveStele, ← hmoveEq]
                          exact hidEq
                        have hafter :=
                          clipperYankAfterVatRemoveIdEqMoveSourceOk (fork := fork) (hperm := by assumption) v evmVatStele I
                            haccVatStele hactiveLenStele hidEqStele
                        let evmStele := initState σ σ₀
                          (Sat256.ofUInt256 g) A I
                        have hbody :
                            ExecTransitionBody fork config contract evmStele locals
                              yankTransition.body
                              (.returned
                                { contract := contract,
                                  locals := (clipperYankFluxRetStore I).insert "_removeRet" .unit, immutables := immStore v }
                                (Stele.EVM.storageStore
                                  (clipperYankDeleteSaleState
                                    (clipperYankRemovePopState evmVatStele
                                      (UInt256.sub
                                        (Stele.EVM.storageLoad evmVatStele
                                          evmVatStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                    I)
                                  (clipperYankDeleteSaleState
                                    (clipperYankRemovePopState evmVatStele
                                      (UInt256.sub
                                        (Stele.EVM.storageLoad evmVatStele
                                          evmVatStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                    I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩)
                                none) (immStore v) := by
                          simpa [evmStele, locals, σLocked] using
                            (clipperYankAfterVatSourceOk (fork := fork) (hperm := by assumption)
                              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmDog := evmDogStele) (evmVat := evmVatStele)
                              (outDog := outDog) (outVat := outVat)
                              v hwv hauthEvm hlockedEvm
                              (by simpa [σLocked] using husrEvm)
                              hdogCodeStele hcallDogStele hvatCodeStele hcallVatStele
                              hafter)
                        have hAccountsFinal :
                            Eq
                              (clipperYankSuccessAccountMap σ_vat I lastIndexEvm)
                              (Stele.EVM.storageStore
                                (clipperYankDeleteSaleState
                                  (clipperYankRemovePopState evmVatStele
                                    (UInt256.sub
                                      (Stele.EVM.storageLoad evmVatStele
                                        evmVatStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                  I)
                                (clipperYankDeleteSaleState
                                  (clipperYankRemovePopState evmVatStele
                                    (UInt256.sub
                                      (Stele.EVM.storageLoad evmVatStele
                                        evmVatStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                  I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩).accountMap := by
                          have hbase :=
                            clipperYankSuccessAccountMap_state_accounts_eq
                              (σ := σ_vat) (τ := σ_vat_stele) evmVatStele I lastIndexEvm
                              hAccountsVat (by rfl) hownerVatStele
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
                              solcSlotWord σ_vat_stele I
                                (clipperYankActiveSlot lastIndexEvm) := by
                          simpa [moveEvm] using
                            congrArg
                              (fun m => solcSlotWord m I (clipperYankActiveSlot lastIndexEvm))
                              hAccountsVat
                        have hloadMoveStele :
                            Stele.EVM.storageLoad evmVatStele
                              evmVatStele.executionEnv.codeOwner
                              (clipperYankActiveSlot lastIndexEvm) =
                                solcSlotWord σ_vat_stele I
                                  (clipperYankActiveSlot lastIndexEvm) := by
                          simp [evmVatStele, evmDogStele, evmDogSteleStart, initState,
                            solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount]
                          cases σ_vat_stele.get? I.codeOwner <;> rfl
                        have hidNeStele :
                            clipperYankArgWord I ≠
                              Stele.EVM.storageLoad evmVatStele
                                evmVatStele.executionEnv.codeOwner
                                (clipperYankActiveSlot
                                  (UInt256.sub
                                    (Stele.EVM.storageLoad evmVatStele
                                      evmVatStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩)) := by
                          intro heq
                          apply hidEq
                          rw [← hlastIndexEq, hloadMoveStele, ← hmoveEq] at heq
                          simpa [moveEvm] using heq
                        have hidxEq :
                            idxEvm =
                              solcSlotWord σ_vat_stele I (clipperYankSalesPosSlot I) := by
                          simpa [idxEvm] using
                            congrArg
                              (fun m => solcSlotWord m I (clipperYankSalesPosSlot I))
                              hAccountsVat
                        have hloadIdxStele :
                            Stele.EVM.storageLoad evmVatStele
                              evmVatStele.executionEnv.codeOwner
                              (clipperYankSalesPosSlot I) =
                                solcSlotWord σ_vat_stele I
                                  (clipperYankSalesPosSlot I) := by
                          simp [evmVatStele, evmDogStele, evmDogSteleStart, initState,
                            solcSlotWord, Stele.EVM.storageLoad, State.lookupAccount]
                          cases σ_vat_stele.get? I.codeOwner <;> rfl
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
                          let evmIndexStele :=
                            Stele.EVM.storageStore evmVatStele
                              evmVatStele.executionEnv.codeOwner
                              (clipperYankActiveSlot idxEvm) moveEvm
                          let evmMovePosStele :=
                            Stele.EVM.storageStore evmIndexStele
                              evmIndexStele.executionEnv.codeOwner
                              (clipperYankSalesMovePosSlot moveEvm) idxEvm
                          have hmoveAccounts :
                              Eq
                                (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                evmMovePosStele.accountMap := by
                            simpa [evmIndexStele, evmMovePosStele] using
                              clipperYankMoveAccountMap_state_accounts_eq
                                (σ := σ_vat) (τ := σ_vat_stele) evmVatStele I
                                idxEvm moveEvm hAccountsVat (by rfl) hownerVatStele
                          have hownerMovePosStele :
                              evmMovePosStele.executionEnv.codeOwner = I.codeOwner := by
                            simp [evmMovePosStele, evmIndexStele, storageStore_executionEnv,
                              hownerVatStele]
                          have hloadLenAfterStele :
                              Stele.EVM.storageLoad evmMovePosStele
                                evmMovePosStele.executionEnv.codeOwner ⟨11⟩ =
                                  solcSlotWord evmMovePosStele.accountMap I ⟨11⟩ := by
                            simp [Stele.EVM.storageLoad, State.lookupAccount, solcSlotWord,
                              hownerMovePosStele]
                            cases evmMovePosStele.accountMap.get? I.codeOwner <;> rfl
                          have hlenAfterEq :
                              solcSlotWord
                                  (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                  I ⟨11⟩ =
                                solcSlotWord evmMovePosStele.accountMap I ⟨11⟩ :=
                            congrArg (fun m => solcSlotWord m I ⟨11⟩) hmoveAccounts
                          have hidxBoundStele :
                              (Stele.EVM.storageLoad evmVatStele
                                evmVatStele.executionEnv.codeOwner
                                (clipperYankSalesPosSlot I)).toNat <
                                (Stele.EVM.storageLoad evmVatStele
                                  evmVatStele.executionEnv.codeOwner ⟨11⟩).toNat := by
                            simpa [idxEvm, hloadIdxStele, hloadLenStele, ← hidxEq,
                              ← hactiveLenEq] using hidxBound
                          by_cases hlenAfterEvm :
                              solcSlotWord
                                  (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                  I ⟨11⟩ = ⟨0⟩
                          · have hinv :=
                              Benchmarks.Dss.Clipper.RD.clipperYankRemoveJoinEmptyInvalid
                                v hpatch rd8379 hlenAfterEvm
                            have hlenAfterStele :
                                Stele.EVM.storageLoad evmMovePosStele
                                  evmMovePosStele.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩ := by
                              rw [hloadLenAfterStele, ← hlenAfterEq]
                              exact hlenAfterEvm
                            have hremoveRevert :
                                ExecFuncBody fork config
                                  { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
                                  evmVatStele removeFunction.body .reverted := by
                              simpa [evmIndexStele, evmMovePosStele, ← hlastIndexEq,
                                hloadMoveStele, ← hmoveEq, hloadIdxStele, ← hidxEq] using
                                (clipperYankRemoveIdNeMovePopEmptySourceReverts (fork := fork) (hperm := by assumption)
                                  v evmVatStele I hactiveLenStele hidNeStele hidxBoundStele
                                  (by
                                    simpa [evmIndexStele, evmMovePosStele, ← hlastIndexEq,
                                      hloadMoveStele, ← hmoveEq, hloadIdxStele, ← hidxEq] using
                                      hlenAfterStele))
                            have hafter :
                                ExecBlock fork config
                                  { contract := contract, locals := clipperYankFluxRetStore I, immutables := immStore v }
                                  evmVatStele
                                  [.internalCall "_remove" [.var "id"] "_removeRet",
                                    .assign .storage lockedRef (.intLit 0)]
                                  .reverted := by
                              exact ExecBlock.consRevert
                                (internalCallFunctionRevert
                                  (cfg := config)
                                  (caller :=
                                    { contract := contract,
                                      locals := clipperYankFluxRetStore I, immutables := immStore v })
                                  (evm := evmVatStele)
                                  (name := "_remove") (retVar := "_removeRet")
                                  (args := [.var "id"])
                                  (argVals := [clipperYankArgValue I])
                                  (callee := removeFunction)
                                  (locals := clipperYankRemoveStore I)
                                  (clipperYankFluxRetStore_removeArgs I v evmVatStele)
                                  (clipperYankRemoveLookup)
                                  (clipperYankRemoveBind I)
                                  hremoveRevert)
                            let evmStele := initState σ σ₀
                              (Sat256.ofUInt256 g) A I
                            have hbody :
                                ExecTransitionBody fork config contract evmStele locals
                                  yankTransition.body .reverted (immStore v) := by
                              simpa [evmStele, locals, σLocked] using
                                (clipperYankAfterVatSourceReverts (fork := fork) (hperm := by assumption)
                                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                  (evmDog := evmDogStele) (evmVat := evmVatStele)
                                  (outDog := outDog) (outVat := outVat)
                                  v hwv hauthEvm hlockedEvm
                                  (by simpa [σLocked] using husrEvm)
                                  hdogCodeStele hcallDogStele hvatCodeStele hcallVatStele
                                  hafter)
                            exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdecode hbody
                          · let lastIndexAfterEvm :=
                              solcSlotWord
                                  (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                  I ⟨11⟩ + UInt256.lnot ⟨0⟩
                            have hret :
                                RDret fork code (Sat256.ofUInt256 g)
                                  (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                                  (clipperYankSuccessAccountMap
                                      (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                      I lastIndexAfterEvm)
                                  ByteArray.empty := by
                              simpa [lastIndexAfterEvm] using
                                (Benchmarks.Dss.Clipper.RD.clipperYankRemoveJoinSuccess
                                  v hpatch rd8379 hlenAfterEvm hjoinMemSize hperm)
                            have hlenAfterStele :
                                Stele.EVM.storageLoad evmMovePosStele
                                  evmMovePosStele.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
                              intro hzero
                              exact hlenAfterEvm (by
                                rw [hloadLenAfterStele, ← hlenAfterEq] at hzero
                                exact hzero)
                            have hlastAfterEq :
                                lastIndexAfterEvm =
                                  UInt256.sub
                                    (Stele.EVM.storageLoad evmMovePosStele
                                      evmMovePosStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩ := by
                              rw [show lastIndexAfterEvm =
                                  solcSlotWord
                                    (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                    I ⟨11⟩ + UInt256.lnot ⟨0⟩ from rfl]
                              rw [u256_add_lnot_zero_eq_sub_one]
                              rw [hloadLenAfterStele, ← hlenAfterEq]
                            have hafter :
                                ExecBlock fork config
                                  { contract := contract, locals := clipperYankFluxRetStore I, immutables := immStore v }
                                  evmVatStele
                                  [.internalCall "_remove" [.var "id"] "_removeRet",
                                    .assign .storage lockedRef (.intLit 0)]
                                  (.ok
                                    { contract := contract,
                                      locals := (clipperYankFluxRetStore I).insert
                                        "_removeRet" .unit, immutables := immStore v }
                                    (Stele.EVM.storageStore
                                      (clipperYankDeleteSaleState
                                        (clipperYankRemovePopState evmMovePosStele
                                          (UInt256.sub
                                            (Stele.EVM.storageLoad evmMovePosStele
                                              evmMovePosStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                        I)
                                      (clipperYankDeleteSaleState
                                        (clipperYankRemovePopState evmMovePosStele
                                          (UInt256.sub
                                            (Stele.EVM.storageLoad evmMovePosStele
                                              evmMovePosStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                        I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
                              simpa [evmIndexStele, evmMovePosStele, ← hlastIndexEq,
                                hloadMoveStele, ← hmoveEq, hloadIdxStele, ← hidxEq] using
                                (clipperYankAfterVatRemoveIdNeMoveSourceOk (fork := fork) (hperm := by assumption)
                                  v evmVatStele I haccVatStele hactiveLenStele hidNeStele
                                  hidxBoundStele
                                  (by
                                    simpa [evmIndexStele, evmMovePosStele, ← hlastIndexEq,
                                      hloadMoveStele, ← hmoveEq, hloadIdxStele, ← hidxEq] using
                                      hlenAfterStele))
                            let evmStele := initState σ σ₀
                              (Sat256.ofUInt256 g) A I
                            have hbody :
                                ExecTransitionBody fork config contract evmStele locals
                                  yankTransition.body
                                  (.returned
                                    { contract := contract,
                                      locals := (clipperYankFluxRetStore I).insert
                                        "_removeRet" .unit, immutables := immStore v }
                                    (Stele.EVM.storageStore
                                      (clipperYankDeleteSaleState
                                        (clipperYankRemovePopState evmMovePosStele
                                          (UInt256.sub
                                            (Stele.EVM.storageLoad evmMovePosStele
                                              evmMovePosStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                        I)
                                      (clipperYankDeleteSaleState
                                        (clipperYankRemovePopState evmMovePosStele
                                          (UInt256.sub
                                            (Stele.EVM.storageLoad evmMovePosStele
                                              evmMovePosStele.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))
                                        I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩)
                                    none) (immStore v) := by
                              simpa [evmStele, locals, σLocked] using
                                (clipperYankAfterVatSourceOk (fork := fork) (hperm := by assumption)
                                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                  (evmDog := evmDogStele) (evmVat := evmVatStele)
                                  (outDog := outDog) (outVat := outVat)
                                  v hwv hauthEvm hlockedEvm
                                  (by simpa [σLocked] using husrEvm)
                                  hdogCodeStele hcallDogStele hvatCodeStele hcallVatStele
                                  hafter)
                            have hAccountsFinal :
                                Eq
                                  (clipperYankSuccessAccountMap
                                    (clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                    I lastIndexAfterEvm)
                                  (Stele.EVM.storageStore
                                    (clipperYankDeleteSaleState
                                      (clipperYankRemovePopState evmMovePosStele
                                        (UInt256.sub
                                          (Stele.EVM.storageLoad evmMovePosStele
                                            evmMovePosStele.executionEnv.codeOwner ⟨11⟩)
                                          ⟨1⟩))
                                      I)
                                    (clipperYankDeleteSaleState
                                      (clipperYankRemovePopState evmMovePosStele
                                        (UInt256.sub
                                          (Stele.EVM.storageLoad evmMovePosStele
                                            evmMovePosStele.executionEnv.codeOwner ⟨11⟩)
                                          ⟨1⟩))
                                      I).executionEnv.codeOwner ⟨13⟩ ⟨0⟩).accountMap := by
                              have hbase :=
                                clipperYankSuccessAccountMap_state_accounts_eq
                                  (σ := clipperYankMoveAccountMap σ_vat I idxEvm moveEvm)
                                  (τ := evmMovePosStele.accountMap)
                                  evmMovePosStele I lastIndexAfterEvm
                                  hmoveAccounts (by rfl) hownerMovePosStele
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
                          have hidxBoundStele :
                              (Stele.EVM.storageLoad evmVatStele
                                evmVatStele.executionEnv.codeOwner ⟨11⟩).toNat ≤
                                (Stele.EVM.storageLoad evmVatStele
                                  evmVatStele.executionEnv.codeOwner
                                  (clipperYankSalesPosSlot I)).toNat := by
                            simpa [idxEvm, hloadIdxStele, hloadLenStele, ← hidxEq,
                              ← hactiveLenEq] using hidxBoundEvm
                          have hremoveRevert :
                              ExecFuncBody fork config
                                { contract := contract, locals := clipperYankRemoveStore I, immutables := immStore v }
                                evmVatStele removeFunction.body .reverted :=
                            clipperYankRemoveIdNeMoveIndexOobSourceReverts
                              v evmVatStele I hactiveLenStele hidNeStele hidxBoundStele
                          have hafter :
                              ExecBlock fork config
                                { contract := contract, locals := clipperYankFluxRetStore I, immutables := immStore v }
                                evmVatStele
                                [.internalCall "_remove" [.var "id"] "_removeRet",
                                  .assign .storage lockedRef (.intLit 0)]
                                .reverted := by
                            exact ExecBlock.consRevert
                              (internalCallFunctionRevert
                                (cfg := config)
                                (caller :=
                                  { contract := contract, locals := clipperYankFluxRetStore I, immutables := immStore v })
                                (evm := evmVatStele)
                                (name := "_remove") (retVar := "_removeRet")
                                (args := [.var "id"])
                                (argVals := [clipperYankArgValue I])
                                (callee := removeFunction)
                                (locals := clipperYankRemoveStore I)
                                (clipperYankFluxRetStore_removeArgs I v evmVatStele)
                                (clipperYankRemoveLookup)
                                (clipperYankRemoveBind I)
                                hremoveRevert)
                          let evmStele := initState σ σ₀
                            (Sat256.ofUInt256 g) A I
                          have hbody :
                              ExecTransitionBody fork config contract evmStele locals
                                yankTransition.body .reverted (immStore v) := by
                            simpa [evmStele, locals, σLocked] using
                              (clipperYankAfterVatSourceReverts (fork := fork) (hperm := by assumption)
                                (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                (evmDog := evmDogStele) (evmVat := evmVatStele)
                                (outDog := outDog) (outVat := outVat)
                                v hwv hauthEvm hlockedEvm
                                (by simpa [σLocked] using husrEvm)
                                hdogCodeStele hcallDogStele hvatCodeStele hcallVatStele
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
              let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
              let evmSteleLock :=
                Stele.EVM.storageStore evmStele evmStele.executionEnv.codeOwner ⟨13⟩ ⟨1⟩
              let A_dog :=
                (Ethereum.EVM.callSubstate fork evmSteleLock.accountMap
                  (EVM.address (AccountAddress.ofUInt256
                    (clipperYankDogTarget σLocked I))) evmSteleLock.substate)
              let evmDogStele : EVM.State := { evmSteleLock with substate := A_dog }
              have hdepthLock : evmSteleLock.executionEnv.depth = 1024 := by
                simpa [evmSteleLock, evmStele, initState, storageStore_executionEnv]
                  using hdepthEq
              have hcallDogStele :
                  typedCallViaEVM fork config
                    (Stele.EVM.storageStore
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                      ⟨13⟩ ⟨1⟩)
                    (EVM.address (AccountAddress.ofUInt256
                      (clipperYankDogTarget σLocked I)))
                    "digs" 0
                    [v.ilk,
                      .int (Int.ofNat
                        (clipperYankSalesTabWord σLocked I).toNat)]
                    (false, evmDogStele, ByteArray.empty) true := by
                simpa [evmDogStele, A_dog, evmSteleLock, evmStele, σLocked, initState,
                  storageStore_accountMap, storageStore_executionEnv] using
                  (callNotMade_depthLimit (cfg := config) (evm := evmSteleLock)
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
                  ExecTransitionBody fork config contract evmStele locals
                    yankTransition.body .reverted (immStore v) := by
                simpa [evmStele, locals, σLocked] using
                  (clipperYankDogDigsCallFailureSourceReverts (fork := fork) (hperm := by assumption)
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (evmDog := evmDogStele) (outDog := ByteArray.empty)
                    v hwv hauthEvm hlockedEvm
                    (by simpa [σLocked] using husrEvm)
                    hdogCodeStele hcallDogStele)
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody fork config contract evmStele locals
              yankTransition.body .reverted (immStore v) := by
          simpa [evmStele, locals] using
            (clipperYankLockedSourceReverts
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
              hauthEvm hlockedEvm)
        obtain ⟨_, _, rd1912⟩ := hreachBody
        obtain ⟨_, _, rd1994⟩ := clipperYankX_authorized (v := v) hpatch hauthEvm rd1912
        have hrev := clipperYankX_locked (v := v) hpatch hlockedEvm rd1994
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody fork config contract evmStele locals
            yankTransition.body .reverted (immStore v) := by
        simpa [evmStele, locals] using
          (clipperYankAuthSourceReverts
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv hauthEvm)
      obtain ⟨_, _, rd1912⟩ := hreachBody
      have hrev := clipperYankX_unauthorized (v := v) hpatch hauthEvm rd1912
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hrev := clipperYankX_shortarg (v := v) (g := Sat256.ofUInt256 g) hpatch hsz4
      hsize hshort hreachEntry
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (clipperDecode_yank_none_short hsz4 hshort)

end Benchmarks.Dss.Clipper
