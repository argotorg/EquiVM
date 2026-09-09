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
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

private theorem ctorExtCodeSize_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by decide +native)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

private theorem storageStore_substate_ctor (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_sigma0_ctor (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_blocks_ctor (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem storageStore_genesisBlockHeader_ctor (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem evmAddress_accountAddress_ctor (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow, AccountAddress.size] using a.isLt)

private theorem RDret.xiResultAcc {cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) acc o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I =
          .ok (.success (acc.1, acc.2, g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hcA : s.createdAccounts = acc.1 := congrArg Prod.fst hacc
    have hσ : s.accountMap = acc.2 := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

theorem gemJoinCtorPrefixStateEquiv
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let evm0e := initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I
    let evm0s := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
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
    EVMStateEquiv evm5e evm5s := by
  intro evm0e evm0s evm1e evm1s evm2e evm2s evm3e evm3s evm4e evm4s evm5e evm5s
  have h0 : EVMStateEquiv evm0e evm0s := by
    simpa [evm0e, evm0s] using EVMStateEquiv.initState (g := g) hAccounts
  have h1 : EVMStateEquiv evm1e evm1s := by
    have hslot : wardsSlot (.address I.source) = gemJoinCtorCallerWardsSlot I :=
      gemJoinCtorCallerWardsSlot_eq I
    simpa [evm1e, evm1s, evm0e, evm0s, gemJoinCtorAfterWardsState, initState, hslot]
      using h0.storageStore_codeOwner (gemJoinCtorCallerWardsSlot I)
        (show (⟨1⟩ : UInt256) = ⟨1⟩ by rfl)
  have h2 : EVMStateEquiv evm2e evm2s := by
    simpa [evm2e, evm2s, gemJoinCtorAfterLiveState] using
      h1.storageStore_codeOwner ⟨5⟩ (show (⟨1⟩ : UInt256) = ⟨1⟩ by rfl)
  have h3 : EVMStateEquiv evm3e evm3s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm2e evm2e.executionEnv.codeOwner ⟨1⟩)
            (EVM.word vat.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨1⟩)
            (EVM.word vat.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word vat.val))
        (h2.storageLoad_codeOwner ⟨1⟩)
    simpa [evm3e, evm3s, gemJoinCtorAfterVatState] using h2.storageStore_codeOwner ⟨1⟩ hval
  have h4 : EVMStateEquiv evm4e evm4s := by
    simpa [evm4e, evm4s, gemJoinCtorAfterIlkState] using
      h3.storageStore_codeOwner ⟨2⟩ (show ilk = ilk by rfl)
  have h5 : EVMStateEquiv evm5e evm5s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm4e evm4e.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm4s evm4s.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word gem.val))
        (h4.storageLoad_codeOwner ⟨3⟩)
    simpa [evm5e, evm5s, gemJoinCtorAfterGemState] using h4.storageStore_codeOwner ⟨3⟩ hval
  exact h5

theorem gemJoinCtorPrefixAccountMapEquiv
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (vat : AccountAddress) (ilk : UInt256) (gem : AccountAddress)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let σWards := sstoreAccountMap I.codeOwner σ_evm (gemJoinCtorCallerWardsSlot I) ⟨1⟩
    let σLive := sstoreAccountMap I.codeOwner σWards ⟨5⟩ ⟨1⟩
    let vatStored := gemJoinCtorVatStored σLive I vat
    let σVat := sstoreAccountMap I.codeOwner σLive ⟨1⟩ vatStored
    let σIlk := sstoreAccountMap I.codeOwner σVat ⟨2⟩ ilk
    let gemStored := gemJoinCtorGemStored σIlk I gem
    let σGem := sstoreAccountMap I.codeOwner σIlk ⟨3⟩ gemStored
    let evm0s :=
      initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1s := gemJoinCtorAfterWardsState evm0s
    let evm2s := gemJoinCtorAfterLiveState evm1s
    let evm3s := gemJoinCtorAfterVatState evm2s vat
    let evm4s := gemJoinCtorAfterIlkState evm3s ilk
    let evm5s := gemJoinCtorAfterGemState evm4s gem
    accountMapEquiv σGem evm5s.accountMap := by
  intro σWards σLive vatStored σVat σIlk gemStored σGem evm0s evm1s evm2s evm3s evm4s evm5s
  let evm0e :=
    initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evm1e := gemJoinCtorAfterWardsState evm0e
  let evm2e := gemJoinCtorAfterLiveState evm1e
  let evm3e := gemJoinCtorAfterVatState evm2e vat
  let evm4e := gemJoinCtorAfterIlkState evm3e ilk
  let evm5e := gemJoinCtorAfterGemState evm4e gem
  have hprefix := gemJoinCtorPrefixStateEquiv (createdAccounts := createdAccounts)
    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ_evm := σ_evm)
    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    vat ilk gem hAccounts
  have hslot : wardsSlot (.address I.source) = gemJoinCtorCallerWardsSlot I :=
    gemJoinCtorCallerWardsSlot_eq I
  have hmap : accountMapEquiv evm5e.accountMap evm5s.accountMap := by
    simpa [evm0e, evm1e, evm2e, evm3e, evm4e, evm5e, evm0s, evm1s, evm2s,
      evm3s, evm4s, evm5s] using hprefix.accountMap
  simpa [evm5e, evm4e, evm3e, evm2e, evm1e, evm0e, σGem, gemStored, σIlk,
    σVat, vatStored, σLive, σWards, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
    gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, solcSlotWord, gemJoinCtorGemStored,
    gemJoinCtorVatStored, hslot] using hmap

theorem gemJoinConstructorCorrect :
    constructorEquivalence config gemJoinCreationBytecode contract gemJoinBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases gemJoinCtorDeployment_shape hdeploy with ⟨vat, ilk, gem, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = gemJoinCtorCode vat ilk gem := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · obtain ⟨_, _, rd68⟩ := gemJoinCtorArgsReach
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g0 := Sat256.ofUInt256 g) vat ilk gem hcodeCtor hwv
    obtain ⟨_, _, rd85⟩ := gemJoinCtorWardsStoreReach vat ilk gem hperm rd68
    let σWards := sstoreAccountMap I.codeOwner σ_evm (gemJoinCtorCallerWardsSlot I) ⟨1⟩
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
      initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evm1s := gemJoinCtorAfterWardsState evm0s
    let evm2s := gemJoinCtorAfterLiveState evm1s
    let evm3s := gemJoinCtorAfterVatState evm2s vat
    let evm4s := gemJoinCtorAfterIlkState evm3s ilk
    let evm5s := gemJoinCtorAfterGemState evm4s gem
    have hAccounts5 : accountMapEquiv σGem evm5s.accountMap := by
      simpa [σWards, σLive, vatStored, σVat, σIlk, gemStored, σGem,
        evm0s, evm1s, evm2s, evm3s, evm4s, evm5s] using
        gemJoinCtorPrefixAccountMapEquiv (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ_evm := σ_evm)
          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          vat ilk gem hAccounts
    have htargetAddr : gem = AccountAddress.ofUInt256 gemTarget := by
      simpa [gemTarget, gemStored, gemJoinCtorGemTargetOfStored] using
        (gemJoinCtorGemTargetAddress_eq σIlk I gem).symm
    by_cases hcodeSize : Reasoning.Theory.extCodeSizeWord σGem gemTarget = ⟨0⟩
    · have hrev := gemJoinCtorDecimalsNoCodeReverts vat ilk gem gemTarget hcodeSize rd184
      rcases hrev.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
      · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
      · have hcodeSizeSolm : extCodeSizeWord evm5s.accountMap gemTarget = ⟨0⟩ := by
          have hEq := extCodeSizeWord_accountMapEquiv hAccounts5 gemTarget
          exact hEq ▸ hcodeSize
        have hgemNoCode :
            (UInt256.ofNat ((evm5s.lookupAccount gem).option 0 (fun acc => acc.code.size))).toNat =
              0 := by
          simpa [evm5s, State.lookupAccount] using
            ctorExtCodeSize_zero_lookup_code_zero (σ := evm5s.accountMap)
              (target := gemTarget) (addr := gem) htargetAddr hcodeSizeSolm
        refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
          (gemJoinSolmCtorExecReverts_noCode
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            vat ilk gem hwv
            (by
              simpa [gemJoinCtorAfterInitStores, evmAddress_accountAddress_ctor, evm0s, evm1s,
                evm2s, evm3s, evm4s, evm5s] using hgemNoCode))
          ?_
        exact ctorResultEquiv.revert rfl rfl
    · have hcodeSizeSolmNe : extCodeSizeWord evm5s.accountMap gemTarget ≠ ⟨0⟩ := by
        intro hzero
        have hEq := extCodeSizeWord_accountMapEquiv hAccounts5 gemTarget
        exact hcodeSize (hEq.trans hzero)
      have hgemCode :
          0 < (UInt256.ofNat ((evm5s.lookupAccount gem).option 0
            (fun acc => acc.code.size))).toNat := by
        simpa [evm5s, State.lookupAccount] using
          ctorExtCodeSize_ne_zero_lookup_code_pos (σ := evm5s.accountMap)
            (target := gemTarget) (addr := gem) htargetAddr hcodeSizeSolmNe
      by_cases hdepth : I.depth.val < 1024
      · obtain ⟨createdAccountsCall, σCall, z, out, Ain, callGas, _, _, hΘ, rd200, hout⟩ :=
          gemJoinCtorDecimalsStaticcallReach vat ilk gem gemTarget hcodeSize hdepth rd184
        let evm0e :=
          initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evm1e := gemJoinCtorAfterWardsState evm0e
        let evm2e := gemJoinCtorAfterLiveState evm1e
        let evm3e := gemJoinCtorAfterVatState evm2e vat
        let evm4e := gemJoinCtorAfterIlkState evm3e ilk
        let evm5e := gemJoinCtorAfterGemState evm4e gem
        have hAccounts5e : accountMapEquiv evm5e.accountMap evm5s.accountMap := by
          simpa [evm0e, evm1e, evm2e, evm3e, evm4e, evm5e, evm0s, evm1s, evm2s,
            evm3s, evm4s, evm5s] using
            (gemJoinCtorPrefixStateEquiv (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := Sat256.ofUInt256 g) vat ilk gem hAccounts).accountMap
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
            substate := ATheta
            createdAccounts := createdAccountsCall }
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
              storageStore_executionEnv, storageStore_createdAccounts,
              storageStore_sigma0_ctor, storageStore_blocks_ctor,
              storageStore_genesisBlockHeader_ctor, initState, Solm.EVM.storageLoad,
              State.lookupAccount, Account.lookupStorage, solcSlotWord,
              gemJoinCtorGemStored, gemJoinCtorVatStored, hslot, hperm] using hTheta
        obtain ⟨σSolmCall, ASolmCall, hcallSolm, hPostAccounts⟩ :=
          typedCallViaEVM_accountMapEquiv (evm_solm := evm5s) hcallEvm hAccounts5e
            (by simp [evm5e, evm5s, evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
              gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState,
              storageStore_sigma0_ctor, initState])
            (by simp [evm5e, evm5s, evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
              gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState,
              storageStore_createdAccounts, initState])
            (by simp [evm5e, evm5s, evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
              gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState,
              storageStore_genesisBlockHeader_ctor, initState])
            (by simp [evm5e, evm5s, evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
              gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState,
              storageStore_blocks_ctor, initState])
            (by simp [evm5e, evm5s, evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
              gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState,
              storageStore_substate_ctor, initState])
            (by simp [evm5e, evm5s, evm4e, evm4s, evm3e, evm3s, evm2e, evm2s, evm1e, evm1s,
              evm0e, evm0s, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
              gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState,
              storageStore_executionEnv, initState])
        let evmDecimalsSolm : EVM.State :=
          { evm5s with
            accountMap := σSolmCall
            substate := ASolmCall
            createdAccounts := createdAccountsCall }
        cases hz : z
        · have hrev := gemJoinCtorDecimalsStatusFailReverts vat ilk gem gemTarget hz hout rd200
          rcases hrev.xiResult hcodeCtor with hOOG | ⟨g', outRev, hRev⟩
          · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
          · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
              (gemJoinSolmCtorExecReverts_decimalsFailure
                (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
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
                    ∨ (⟨64⟩ : UInt256) ≥
                      UInt256.ofNat
                        (MachineState.M
                          (MachineState.M (UInt256.ofNat 8).toNat 224 4)
                          224 32) * ⟨32⟩ then ⟨0⟩
                 else UInt256.ofNat
                   (fromByteArrayBigEndian (memRet.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
                  ⟨224⟩ := by
              exact mloadWordValue_of_readWithPadding
                (mem := memRet)
                (aw := UInt256.ofNat
                  (MachineState.M
                    (MachineState.M (UInt256.ofNat 8).toNat 224 4)
                    224 32))
                (off := ⟨64⟩) (v := ⟨224⟩)
                (by rw [hmemRetSize]; decide)
                (by decide +native) hread64
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
                    ∨ (⟨224⟩ : UInt256) ≥
                      UInt256.ofNat
                        (MachineState.M
                          (MachineState.M (UInt256.ofNat 8).toNat 224 4)
                          224 32) * ⟨32⟩ then ⟨0⟩
                 else UInt256.ofNat
                   (fromByteArrayBigEndian (memRet.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
                  retWord := by
              exact mloadWordValue_of_readWithPadding
                (mem := memRet)
                (aw := UInt256.ofNat
                  (MachineState.M
                    (MachineState.M (UInt256.ofNat 8).toNat 224 4)
                    224 32))
                (off := ⟨224⟩) (v := retWord)
                (by rw [hmemRetSize]; decide)
                (by decide +native)
                (by rw [hretWordBytes]; exact hread224)
            obtain ⟨_, _, rd241⟩ := gemJoinCtorDecimalsReturnDecodeOkReach
              vat ilk gem gemTarget retWord hlo hhi
              (by
                intro s hs hstk
                simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hstk]
                decide +native)
              (by decide +native) hmload64 hmload224
              (by
                intro s hs hstk
                simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hstk]
                decide +native)
              (by decide +native)
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
              have hcreated :
                  createdAccountsCall =
                    (gemJoinCtorAfterDecState evmDecimalsSolm retWord).createdAccounts := by
                simp [evmDecimalsSolm, gemJoinCtorAfterDecState, storageStore_createdAccounts]
              have hAccountsDec :
                  accountMapEquiv (sstoreAccountMap I.codeOwner σCall ⟨4⟩ retWord)
                    (gemJoinCtorAfterDecState evmDecimalsSolm retWord).accountMap := by
                have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩ retWord hPostAccounts
                simpa [evmDecimalsSolm, gemJoinCtorAfterDecState, storageStore_accountMap,
                  storageStore_executionEnv, evmCallEvm, evm5s, evm4s, evm3s, evm2s, evm1s,
                  evm0s, gemJoinCtorAfterGemState, gemJoinCtorAfterIlkState,
                  gemJoinCtorAfterVatState, gemJoinCtorAfterLiveState, gemJoinCtorAfterWardsState,
                  initState] using hbase
              refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hSuccess)
                (gemJoinSolmCtorExecSuccess
                  (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
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
              exact ctorResultEquiv.success rfl rfl hcreated hAccountsDec rfl
          ·
            have hshort : out.size < 32 := by omega
            have hrev := gemJoinCtorDecimalsReturnDecodeShortReverts vat ilk gem gemTarget hshort hout
              (by
                intro s hs hstk
                simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hstk]
                decide +native)
              (by decide +native)
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
                  (aw := UInt256.ofNat
                    (MachineState.M
                      (MachineState.M (UInt256.ofNat 8).toNat 224 4)
                      224 32))
                  (off := ⟨64⟩) (v := ⟨224⟩)
                  (by rw [hmemRetSize]; decide)
                  (by decide +native) hread64)
              rd218
            rcases hrev.xiResult hcodeCtor with hOOG | ⟨g', outRev, hRev⟩
            · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
            · have hdec : config.externalABI.decode? "decimals" out = none := by
                simp [config, externalABI, decodeReturn?]
                exact decodeReturnValueWithMode_legacy_uint256_none_short hshort
              refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
                (gemJoinSolmCtorExecReverts_decimalsDecode
                  (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
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
        have houtEmpty : ByteArray.empty.size < UInt256.size := by decide +native
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
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
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
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat ilk gem hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (gemJoinSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          vat ilk gem hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.GemJoin
