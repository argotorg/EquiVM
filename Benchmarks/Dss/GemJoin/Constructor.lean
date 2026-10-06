import Benchmarks.Dss.GemJoin.ConstructorSource
import Benchmarks.Dss.GemJoin.ConstructorTrace

/-!
# MakerDAO/Sky DSS GemJoin constructor correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.GemJoin

set_option maxRecDepth 2000000

private theorem ctorExtCodeSize_ne_zero_lookup_code_pos {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.get? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.get? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using Nat.pos_of_ne_zero htoNatNe

private theorem ctorExtCodeSize_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.get? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.get? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hword

private theorem storageStore_substate_ctor (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_sigma0_ctor (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

private theorem evmAddress_accountAddress_ctor (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow, AccountAddress.size] using a.isLt)

private theorem RDret.xiResultAcc {σ σ' σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {code o : ByteArray}
    (hcode : I.code = code)
    (h : RDret code g (initState σ σ₀ g A I) σ' o) :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ σ σ₀ g.toUInt256 A I =
          .ok (.success (σ', g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hσ : s.accountMap = σ' := hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

theorem gemJoinCtorPrefixStateEquiv
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) :
    let evm0e := initState σ σ₀ g A I
    let evm0s := initState σ σ₀ g A I
    let evm1e := gemJoinCtorAfterWardsState evm0e
    let evm1s := gemJoinCtorAfterWardsState evm0s
    let evm2e := gemJoinCtorAfterLiveState evm1e
    let evm2s := gemJoinCtorAfterLiveState evm1s
    let evm3e := gemJoinCtorAfterVatState evm2e vat
    let evm3s := gemJoinCtorAfterVatState evm2s vat
    let evm4e := gemJoinCtorAfterIlkState evm3e ilk
    let evm4s := gemJoinCtorAfterIlkState evm3s ilk
    let evm5e := gemJoinCtorAfterGemState evm4e gem
    let evm5s := gemJoinCtorAfterGemState evm4s gem
    evm5e.accountMap = evm5s.accountMap := by
  intro evm0e evm0s evm1e evm1s evm2e evm2s evm3e evm3s evm4e evm4s evm5e evm5s
  rfl

theorem gemJoinCtorPrefixAccountMapEquiv
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress) :
    let σWards := sstoreAccountMap I.codeOwner σ (gemJoinCtorCallerWardsSlot I) ⟨1⟩
    let σLive := sstoreAccountMap I.codeOwner σWards ⟨5⟩ ⟨1⟩
    let vatStored := gemJoinCtorVatStored σLive I vat
    let σVat := sstoreAccountMap I.codeOwner σLive ⟨1⟩ vatStored
    let σIlk := sstoreAccountMap I.codeOwner σVat ⟨2⟩ ilk
    let gemStored := gemJoinCtorGemStored σIlk I gem
    let σGem := sstoreAccountMap I.codeOwner σIlk ⟨3⟩ gemStored
    let evm0s :=
      initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1s := gemJoinCtorAfterWardsState evm0s
    let evm2s := gemJoinCtorAfterLiveState evm1s
    let evm3s := gemJoinCtorAfterVatState evm2s vat
    let evm4s := gemJoinCtorAfterIlkState evm3s ilk
    let evm5s := gemJoinCtorAfterGemState evm4s gem
    σGem = evm5s.accountMap := by
  intro σWards σLive vatStored σVat σIlk gemStored σGem evm0s evm1s evm2s evm3s evm4s evm5s
  let evm0e :=
    initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1e := gemJoinCtorAfterWardsState evm0e
  let evm2e := gemJoinCtorAfterLiveState evm1e
  let evm3e := gemJoinCtorAfterVatState evm2e vat
  let evm4e := gemJoinCtorAfterIlkState evm3e ilk
  let evm5e := gemJoinCtorAfterGemState evm4e gem
  have hprefix := gemJoinCtorPrefixStateEquiv
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    vat ilk gem
  have hslot : wardsSlot (.address I.source) = gemJoinCtorCallerWardsSlot I :=
    gemJoinCtorCallerWardsSlot_eq I
  have hmap : evm5e.accountMap = evm5s.accountMap := by
    simpa [evm0e, evm1e, evm2e, evm3e, evm4e, evm5e, evm0s, evm1s, evm2s,
      evm3s, evm4s, evm5s] using hprefix
  simpa [evm5e, evm4e, evm3e, evm2e, evm1e, evm0e, σGem, gemStored, σIlk,
    σVat, vatStored, σLive, σWards, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
    gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, solcSlotWord, gemJoinCtorGemStored,
    gemJoinCtorVatStored, hslot] using hmap

theorem gemJoinConstructorCorrect :
    constructorEquivalence config gemJoinCreationBytecode contract gemJoinBytecode := by
  refine constructorEquivalence.intro ?_
  intro σ σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm
  rcases gemJoinCtorDeployment_shape hdeploy with ⟨vat, ilk, gem, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = gemJoinCtorCode vat ilk gem := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · obtain ⟨_, _, rd68⟩ := gemJoinCtorArgsReach
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g0 := Sat256.ofUInt256 g) vat ilk gem hcodeCtor hwv
    obtain ⟨_, _, rd85⟩ := gemJoinCtorWardsStoreReach vat ilk gem hperm rd68
    let σWards := sstoreAccountMap I.codeOwner σ (gemJoinCtorCallerWardsSlot I) ⟨1⟩
    have rd85' := by simpa [σWards] using rd85
    obtain ⟨_, _, rd90⟩ := gemJoinCtorLiveStoreReach vat ilk gem hperm rd85'
    let σLive := sstoreAccountMap I.codeOwner σWards ⟨5⟩ ⟨1⟩
    have rd90' := by simpa [σLive, σWards] using rd90
    obtain ⟨_, _, rd119⟩ := gemJoinCtorVatStoreReach vat ilk gem hperm rd90'
    let vatStored := gemJoinCtorVatStored σLive I vat
    let σVat := sstoreAccountMap I.codeOwner σLive ⟨1⟩ vatStored
    have rd119' := by simpa [σVat, vatStored, σLive] using rd119
    obtain ⟨_, _, rd124⟩ := gemJoinCtorIlkStoreReach vat ilk gem hperm rd119'
    let σIlk := sstoreAccountMap I.codeOwner σVat ⟨2⟩ ilk
    have rd124' := by simpa [σIlk, σVat] using rd124
    obtain ⟨_, _, rd141⟩ := gemJoinCtorGemStoreReach vat ilk gem hperm rd124'
    let gemStored := gemJoinCtorGemStored σIlk I gem
    let σGem := sstoreAccountMap I.codeOwner σIlk ⟨3⟩ gemStored
    have rd141' := by simpa [σGem, gemStored, σIlk] using rd141
    obtain ⟨_, _, rd184raw⟩ := gemJoinCtorDecimalsSetupReach vat ilk gem rd141'
    let gemTarget := gemJoinCtorGemTargetOfStored gemStored
    have rd184 := by simpa [gemTarget, gemStored] using rd184raw
    let evm0s :=
      initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1s := gemJoinCtorAfterWardsState evm0s
    let evm2s := gemJoinCtorAfterLiveState evm1s
    let evm3s := gemJoinCtorAfterVatState evm2s vat
    let evm4s := gemJoinCtorAfterIlkState evm3s ilk
    let evm5s := gemJoinCtorAfterGemState evm4s gem
    have hAccounts5 : σGem = evm5s.accountMap := by
      simpa [σWards, σLive, vatStored, σVat, σIlk, gemStored, σGem,
        evm0s, evm1s, evm2s, evm3s, evm4s, evm5s] using
        gemJoinCtorPrefixAccountMapEquiv
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          vat ilk gem
    have htargetAddr : gem = AccountAddress.ofUInt256 gemTarget := by
      simpa [gemTarget, gemStored, gemJoinCtorGemTargetOfStored] using
        (gemJoinCtorGemTargetAddress_eq σIlk I gem).symm
    by_cases hcodeSize : Reasoning.Theory.extCodeSizeWord σGem gemTarget = ⟨0⟩
    · have hrev := gemJoinCtorDecimalsNoCodeReverts vat ilk gem gemTarget hcodeSize rd184
      rcases hrev.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
      · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
      · have hcodeSizeSolm : extCodeSizeWord evm5s.accountMap gemTarget = ⟨0⟩ := by
          simpa [hAccounts5] using hcodeSize
        have hgemNoCode :
            (UInt256.ofNat ((evm5s.lookupAccount gem).option 0 (fun acc => acc.code.size))).toNat =
              0 := by
          simpa [evm5s, State.lookupAccount] using
            ctorExtCodeSize_zero_lookup_code_zero (σ := evm5s.accountMap)
              (target := gemTarget) (addr := gem) htargetAddr hcodeSizeSolm
        refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
          (gemJoinSolmCtorExecReverts_noCode
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            vat ilk gem hwv
            (by
              simpa [gemJoinCtorAfterInitStores, evmAddress_accountAddress_ctor, evm0s, evm1s,
                evm2s, evm3s, evm4s, evm5s] using hgemNoCode))
          ?_
        exact ctorResultEquiv.revert rfl rfl
    · have hcodeSizeSolmNe : extCodeSizeWord evm5s.accountMap gemTarget ≠ ⟨0⟩ := by
        intro hzero
        have hzero' : extCodeSizeWord σGem gemTarget = ⟨0⟩ := by
          simpa [hAccounts5] using hzero
        exact hcodeSize hzero'
      have hgemCode :
          0 < (UInt256.ofNat ((evm5s.lookupAccount gem).option 0
            (fun acc => acc.code.size))).toNat := by
        simpa [evm5s, State.lookupAccount] using
          ctorExtCodeSize_ne_zero_lookup_code_pos (σ := evm5s.accountMap)
            (target := gemTarget) (addr := gem) htargetAddr hcodeSizeSolmNe
      by_cases hdepth : I.depth.val < 1024
      · obtain ⟨σCall, z, out, Ain, callGas, _, _, hΘ, rd200, hout⟩ :=
          gemJoinCtorDecimalsStaticcallReach vat ilk gem gemTarget hcodeSize hdepth rd184
        let evm0e :=
          initState σ σ₀ (Sat256.ofUInt256 g) A I
        let evm1e := gemJoinCtorAfterWardsState evm0e
        let evm2e := gemJoinCtorAfterLiveState evm1e
        let evm3e := gemJoinCtorAfterVatState evm2e vat
        let evm4e := gemJoinCtorAfterIlkState evm3e ilk
        let evm5e := gemJoinCtorAfterGemState evm4e gem
        have hAccounts5e : evm5e.accountMap = evm5s.accountMap := by
          simpa [evm0e, evm1e, evm2e, evm3e, evm4e, evm5e, evm0s, evm1s, evm2s,
            evm3s, evm4s, evm5s] using
            (gemJoinCtorPrefixStateEquiv
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) vat ilk gem)
        have htgt : EVM.address gem = AccountAddress.ofUInt256 gemTarget := by
          rw [evmAddress_accountAddress_ctor, htargetAddr]
        have hslot : wardsSlot (.address I.source) = gemJoinCtorCallerWardsSlot I :=
          gemJoinCtorCallerWardsSlot_eq I
        obtain ⟨gTheta, ATheta, hTheta⟩ := hΘ
        have hdepthNe : evm5e.executionEnv.depth ≠ 1024 := by
          intro hEq
          have hEqI : I.depth = 1024 := by
            simpa [evm5e, evm4e, evm3e, evm2e, evm1e, evm0e,
              gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState, gemJoinCtorAfterVatState,
              gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState, storageStore_executionEnv,
              initState] using hEq
          have hnot : ¬ I.depth.val < 1024 := by
            rw [hEqI]
            decide
          exact hnot hdepth
        let evmCallEvm : EVM.State :=
          { evm5e with
            accountMap := σCall
            substate := ATheta }
        have hcallEvm :
            typedCallViaEVM config evm5e (EVM.address gem) "decimals" 0 []
              (z, evmCallEvm, out) false := by
          refine callCoincides (A_in := Ain) (g'' := gTheta) (callGas := callGas)
            (callPerm := false) (targetWord := gemTarget)
            (mem := gemJoinCtorDecimalsCalldataMem I vat ilk gem)
            (inOff := ⟨224⟩) (inSize := ⟨4⟩)
            hdepthNe htgt ?_ ?_
          · exact gemJoinCtorDecimalsCalldataMem_encode I vat ilk gem
          · simpa [evm5e, evm4e, evm3e, evm2e, evm1e, evm0e, σGem, gemStored, σIlk,
              σVat, vatStored, σLive, σWards, gemTarget, evmCallEvm,
              gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState, gemJoinCtorAfterVatState,
              gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState, storageStore_accountMap,
              storageStore_executionEnv,
              storageStore_sigma0_ctor, initState, Solm.EVM.storageLoad,
              State.lookupAccount, Account.lookupStorage, solcSlotWord,
              gemJoinCtorGemStored, gemJoinCtorVatStored, hslot, hperm] using hTheta
        have hstate : evm5e = evm5s := by
          simp [evm5e, evm5s, evm4e, evm4s, evm3e, evm3s, evm2e, evm2s,
            evm1e, evm1s, evm0e, evm0s, gemJoinCtorAfterGemState,
            gemJoinCtorAfterIlkState, gemJoinCtorAfterVatState,
            gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState,
            storageStore_sigma0_ctor, storageStore_accountMap,
            storageStore_executionEnv, initState]
        have hcallSolm :
            typedCallViaEVM config evm5s (EVM.address gem) "decimals" 0 []
              (z, evmCallEvm, out) false := by
          simpa [hstate] using hcallEvm
        let evmDecimalsSolm := evmCallEvm
        cases hz : z
        · have hrev := gemJoinCtorDecimalsStatusFailReverts vat ilk gem gemTarget hz hout rd200
          rcases hrev.xiResult hcodeCtor with hOOG | ⟨g', outRev, hRev⟩
          · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
          · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
              (gemJoinSolmCtorExecReverts_decimalsFailure
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (evmDecimals := evmDecimalsSolm) (outDecimals := out)
                vat ilk gem hwv
                (by
                  simpa [gemJoinCtorAfterInitStores, evmAddress_accountAddress_ctor, evm0s, evm1s,
                    evm2s, evm3s, evm4s, evm5s] using hgemCode)
                (by
                  simpa [hz, gemJoinCtorAfterInitStores, evm0s, evm1s, evm2s, evm3s, evm4s,
                    evm5s, evmDecimalsSolm] using hcallSolm))
              ?_
            exact ctorResultEquiv.revert rfl rfl
        · obtain ⟨_, _, rd218⟩ := gemJoinCtorDecimalsStatusOkReach vat ilk gem gemTarget hz rd200
          by_cases hlo : 32 ≤ out.size
          ·
            -- success path continues through ABI decode and runtime return
            have hhi := hout
            let retWord := gemJoinCtorDecimalsReturnWord out
            have hL : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 :=
              gemJoinCtorMin32_toNat_of_ge hlo hhi
            let memRet := out.write 0 (gemJoinCtorDecimalsCalldataMem I vat ilk gem) 224 32
            have hmemRetSize : memRet.size = 256 := by
              simpa [memRet] using
                gemJoinCtorDecimalsReturnWrite_size 32
                  (by rw [gemJoinCtorDecimalsCalldataMem_size])
                  (by decide) hlo
            have hread64 :
                memRet.readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩ := by
              simpa [memRet] using
                gemJoinCtorDecimalsReturnWrite_read64 32
                  (by rw [gemJoinCtorDecimalsCalldataMem_size])
                  (gemJoinCtorDecimalsCalldataMem_read64 I vat ilk gem)
                  (by decide) hlo
            have hmload64 :
                (if (⟨64⟩ : UInt256).toNat ≥ memRet.size
 then ⟨0⟩
                 else UInt256.ofNat
                   (fromByteArrayBigEndian (memRet.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
                  ⟨224⟩ := by
              exact mloadWordValue_of_readWithPadding
                (mem := memRet)
                (off := ⟨64⟩) (v := ⟨224⟩)
                (by rw [hmemRetSize]; decide) hread64
            have hread224 :
                memRet.readWithPadding 224 32 = out.extract 0 32 := by
              simpa [memRet] using
                gemJoinCtorDecimalsReturnWrite_read224_32
                  (by rw [gemJoinCtorDecimalsCalldataMem_size]) hlo
            have hretWordBytes : UInt256.toByteArray retWord = out.extract 0 32 := by
              dsimp only [retWord, gemJoinCtorDecimalsReturnWord]
              rw [← uInt256OfByteArray_eq (out.extract 0 32)]
              exact toByteArray_uInt256OfByteArray_of_size_gemJoin
                (by rw [ByteArray.size_extract]; omega)
            have hmload224 :
                (if (⟨224⟩ : UInt256).toNat ≥ memRet.size
 then ⟨0⟩
                 else UInt256.ofNat
                   (fromByteArrayBigEndian (memRet.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
                  retWord := by
              exact mloadWordValue_of_readWithPadding
                (mem := memRet)
                (off := ⟨224⟩) (v := retWord)
                (by rw [hmemRetSize]; decide)
                (by rw [hretWordBytes]; exact hread224)
            obtain ⟨_, _, rd241⟩ := gemJoinCtorDecimalsReturnDecodeOkReach (aw := ⟨8⟩)
              vat ilk gem gemTarget retWord hlo hhi
              (by native_decide)
              (by native_decide) hmload64 hmload224
              (by native_decide)
              (by native_decide)
              (by simpa [memRet, hL] using rd218)
            have hret := gemJoinCtorReturnTrace vat ilk retWord gem hperm hmload64
              (by simpa [memRet] using rd241)
            rcases RDret.xiResultAcc hcodeCtor hret with hOOG | ⟨g', A', hSuccess⟩
            · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
            · have hdec :
                  config.externalABI.decode? "decimals" out =
                    some [.int (Int.ofNat retWord.toNat)] := by
                simp [config, externalABI, decodeReturn?]
                simpa [retWord, gemJoinCtorDecimalsReturnWord,
                  UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)]
                  using decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) hlo
              have hAccountsDec :
                  (sstoreAccountMap I.codeOwner σCall ⟨4⟩ retWord) =
                    (gemJoinCtorAfterDecState evmDecimalsSolm retWord).accountMap := by
                simp only [evmDecimalsSolm, gemJoinCtorAfterDecState,
                  storageStore_accountMap, evmCallEvm]
                have howner : evm5e.executionEnv.codeOwner = I.codeOwner := by
                  simp [evm5e, evm4e, evm3e, evm2e, evm1e, evm0e,
                    gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
                    gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState,
                    gemJoinCtorAfterWardsState, storageStore_executionEnv,
                    initState]
                rw [howner]
              refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hSuccess)
                (gemJoinSolmCtorExecSuccess
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (evmDecimals := evmDecimalsSolm) (outDecimals := out) (dec := retWord)
                  vat ilk gem hwv
                  (by
                    simpa [gemJoinCtorAfterInitStores, evmAddress_accountAddress_ctor, evm0s,
                      evm1s, evm2s, evm3s, evm4s, evm5s] using hgemCode)
                  (by
                    simpa [hz, gemJoinCtorAfterInitStores, evm0s, evm1s, evm2s, evm3s,
                      evm4s, evm5s, evmDecimalsSolm] using hcallSolm)
                  hdec)
                ?_
              exact ctorResultEquiv.success rfl rfl hAccountsDec rfl
          ·
            have hshort : out.size < 32 := by omega
            have hrev := gemJoinCtorDecimalsReturnDecodeShortReverts vat ilk gem gemTarget hshort hout
              (by native_decide)
              (by native_decide)
              (by
                have hLle : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ 32 := by
                  rw [gemJoinCtorMin32_toNat_of_lt hshort]
                  omega
                let memRet := out.write 0 (gemJoinCtorDecimalsCalldataMem I vat ilk gem) 224
                  (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
                have hmemRetSize : memRet.size = 256 := by
                  simpa [memRet] using
                    gemJoinCtorDecimalsReturnWrite_size
                      ((min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
                      (by rw [gemJoinCtorDecimalsCalldataMem_size])
                      hLle (by rw [gemJoinCtorMin32_toNat_of_lt hshort])
                have hread64 :
                    memRet.readWithPadding 64 32 = UInt256.toByteArray ⟨224⟩ := by
                  simpa [memRet] using
                    gemJoinCtorDecimalsReturnWrite_read64
                      ((min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
                      (by rw [gemJoinCtorDecimalsCalldataMem_size])
                      (gemJoinCtorDecimalsCalldataMem_read64 I vat ilk gem)
                      hLle (by rw [gemJoinCtorMin32_toNat_of_lt hshort])
                exact mloadWordValue_of_readWithPadding
                  (mem := memRet)
                  (off := ⟨64⟩) (v := ⟨224⟩)
                  (by rw [hmemRetSize]; decide) hread64)
              rd218
            rcases hrev.xiResult hcodeCtor with hOOG | ⟨g', outRev, hRev⟩
            · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
            · have hdec : config.externalABI.decode? "decimals" out = none := by
                simp [config, externalABI, decodeReturn?]
                exact decodeReturnValueWithMode_legacy_uint256_none_short hshort
              refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
                (gemJoinSolmCtorExecReverts_decimalsDecode
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (evmDecimals := evmDecimalsSolm) (outDecimals := out)
                  vat ilk gem hwv
                  (by
                    simpa [gemJoinCtorAfterInitStores, evmAddress_accountAddress_ctor, evm0s,
                      evm1s, evm2s, evm3s, evm4s, evm5s] using hgemCode)
                  (by
                    simpa [hz, gemJoinCtorAfterInitStores, evm0s, evm1s, evm2s, evm3s,
                      evm4s, evm5s, evmDecimalsSolm] using hcallSolm)
                  hdec)
                ?_
              exact ctorResultEquiv.revert rfl rfl
      · have hdepthEq : I.depth = 1024 := by
          apply Fin.ext
          have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
          omega
        obtain ⟨_, _, rd200⟩ :=
          gemJoinCtorDecimalsStaticcallDepthLimitReach vat ilk gem gemTarget hcodeSize hdepthEq rd184
        have houtEmpty : ByteArray.empty.size < UInt256.size := by native_decide
        have hrev := gemJoinCtorDecimalsStatusFailReverts vat ilk gem gemTarget
          (z := false) rfl houtEmpty rd200
        rcases hrev.xiResult hcodeCtor with hOOG | ⟨g', outRev, hRev⟩
        · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
        · let A_dec := (evm5s.addAccessedAccount (EVM.address gem)).substate
          have hcallDepth :
              typedCallViaEVM config evm5s (EVM.address gem) "decimals" 0 []
                (false, { evm5s with substate := A_dec }, ByteArray.empty) false := by
            simpa [A_dec, evm5s, evm4s, evm3s, evm2s, evm1s, evm0s, storageStore_executionEnv,
              gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState, gemJoinCtorAfterVatState,
              gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState, initState] using
              (callNotMade_depthLimit (cfg := config) (evm := evm5s)
                (tgt := EVM.address gem) (name := "decimals") (args := [])
                (callPerm := false)
                (calldata := (gemJoinCtorDecimalsCalldataMem I vat ilk gem).readWithPadding 224 4)
                (gemJoinCtorDecimalsCalldataMem_encode I vat ilk gem)
                (by
                  simpa [evm5s, evm4s, evm3s, evm2s, evm1s, evm0s, storageStore_executionEnv,
                    gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState, gemJoinCtorAfterVatState,
                    gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState, initState] using hdepthEq))
          refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
            (gemJoinSolmCtorExecReverts_decimalsFailure
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmDecimals := { evm5s with substate := A_dec }) (outDecimals := ByteArray.empty)
              vat ilk gem hwv
              (by
                simpa [gemJoinCtorAfterInitStores, evmAddress_accountAddress_ctor, evm0s, evm1s,
                  evm2s, evm3s, evm4s, evm5s] using hgemCode)
              (by
                simpa [gemJoinCtorAfterInitStores, evm0s, evm1s, evm2s, evm3s, evm4s,
                  evm5s] using hcallDepth))
            ?_
          exact ctorResultEquiv.revert rfl rfl
  · have hrd := gemJoinInitcodeNonpayableRevert
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat ilk gem hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (gemJoinSolmCtorExecReverts_nonpayable
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          vat ilk gem hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.GemJoin
