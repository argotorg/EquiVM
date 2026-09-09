import Benchmarks.Auction.SettleAuctionCallPaths

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionStorageStore_σ₀ (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem auctionStorageStore_genesisBlockHeader
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem auctionStorageStore_blocks (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem auctionStorageStore_substate (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

private theorem auctionAccountMapExtensionalEq_of_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

private theorem auctionAccountMapEquiv_of_accountMapExtensionalEq {σ τ : AccountMap}
    (hστ : accountMapExtensionalEq σ τ) : accountMapEquiv σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

theorem auctionSettleAuctionEnterState_executionEnv (evm : EVM.State) :
    (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
  simpa [auctionSettleAuctionEnterState] using
    storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩

theorem auctionSettleAuctionEnterState_storageLoad_ne
    (evm : EVM.State) {slot : UInt256} (hne : slot ≠ ⟨101⟩) :
    Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm) evm.executionEnv.codeOwner slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
  simpa [auctionSettleAuctionEnterState] using
    storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
      (readSlot := slot) (writeSlot := ⟨101⟩) (val := ⟨2⟩) hne

theorem auctionCallViaEVM_callMade_accountMapEquiv_perm {storage : StorageLayout}
    {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {value : ℤ} {calldata : ByteArray} {out : ByteArray}
    {callPerm : Bool}
    (hcall : callViaEVM evm_evm tgt value calldata (true, evm'_evm, out) callPerm)
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      callViaEVM evm_solm tgt value calldata
        (true,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) callPerm ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm := by
  have h_ext_eq : accountMapExtensionalEq evm_evm.accountMap evm_solm.accountMap :=
    auctionAccountMapExtensionalEq_of_accountMapEquiv hAccounts
  cases hcall with
  | callMade hvalue hTheta hevm' hvalue' hdepth =>
    obtain ⟨callGas, A_in, hTheta⟩ := hTheta
    rename_i valueWord cA' σ' g' A'
    generalize htheta_solm :
      Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
        evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
        evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
        (toExecute evm_solm.accountMap tgt) callGas
        (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
        (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header callPerm = thetaRes
    have hcode_equiv :
        toExecute evm_evm.accountMap tgt = toExecute evm_solm.accountMap tgt :=
      accountMapExtensionalEq_toExecute h_ext_eq tgt
    have htheta_solm' :
        Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
          evm_evm.genesisBlockHeader evm_evm.blocks evm_solm.accountMap evm_evm.σ₀ A_in
          evm_evm.executionEnv.codeOwner evm_evm.executionEnv.sender tgt
          (toExecute evm_evm.accountMap tgt) callGas
          (UInt256.ofNat evm_evm.executionEnv.gasPrice) valueWord valueWord calldata
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header callPerm =
          (thetaRes.1, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
            thetaRes.2.2.2.2.1, thetaRes.2.2.2.2.2) := by
      rw [← htheta_solm]
      rw [hCreated, ← hOriginalAccounts, hGenesis, hBlocks, hEnv, hcode_equiv]
    let a1 : AccountAddress := ⟨0, by simp [AccountAddress.size]⟩
    have hTheta_rel :=
      (accountMap_extensionality_of_Theta_and_Lambda
      (blobVersionedHashes := evm_evm.executionEnv.blobVersionedHashes)
      (createdAccounts := evm_evm.createdAccounts)
      (genesisBlockHeader := evm_evm.genesisBlockHeader)
      (blocks := evm_evm.blocks)
      (σ₁ := evm_evm.accountMap)
      (σ₂ := evm_solm.accountMap)
      (σ₀ := evm_evm.σ₀)
      (A := A_in)
      (s := evm_evm.executionEnv.codeOwner)
      (o := evm_evm.executionEnv.sender)
      (r := tgt)
      (g := callGas)
      (p := UInt256.ofNat evm_evm.executionEnv.gasPrice)
      (v := valueWord)
      (v' := valueWord)
      (d := calldata)
      (i := ByteArray.empty)
      (ζ := none)
      (H := evm_evm.executionEnv.header)
      (w := callPerm)
      a1 a1
      (toExecute evm_evm.accountMap tgt)
      cA' thetaRes.1
      σ' thetaRes.2.1
      g' thetaRes.2.2.1
      A' thetaRes.2.2.2.1
      true thetaRes.2.2.2.2.1
      out thetaRes.2.2.2.2.2
      (evm_evm.executionEnv.depth + 1)
      h_ext_eq).1 hTheta.symm htheta_solm'
    have hCreated' : evm'_evm.createdAccounts = thetaRes.1 := by
      simp [hevm', hTheta_rel.1]
    have hTheta_s :
        (evm'_evm.createdAccounts, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
            true, out) =
          Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
            evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
            evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
            (toExecute evm_solm.accountMap tgt) callGas
            (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
            (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header callPerm := by
      rw [hTheta_rel.2.2.2.1, hTheta_rel.2.2.2.2.1]
      rw [hCreated']
      exact htheta_solm.symm
    use thetaRes.2.1
    use thetaRes.2.2.2.1
    constructor
    · exact callViaEVM.callMade (perm := callPerm) hvalue
        ⟨callGas, A_in, hTheta_s⟩ rfl (by
          rw [hEnv]
          rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
          exact hvalue') (by
          rw [hEnv]
          exact hdepth)
    · have hσext : accountMapExtensionalEq σ' thetaRes.2.1 := hTheta_rel.2.2.2.2.2
      simpa [hevm'] using auctionAccountMapEquiv_of_accountMapExtensionalEq hσext

-- LIBRARY CANDIDATE: value-parametric call-made transport without a substate equality premise.
theorem auctionCallViaEVM_callMadeTheta_accountMapEquiv_perm
    {evm_evm evm_solm : EVM.State}
    {tgt : EVM.Address} {value : ℤ} {calldata out : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {g'' callGas valueWord : UInt256} {callPerm : Bool}
    (hvalue : valueWord = EVM.wordOfInt value)
    (hTheta : (cA', σ', g'', A', z, out) =
        Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
          evm_evm.genesisBlockHeader evm_evm.blocks evm_evm.accountMap evm_evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm_evm.executionEnv.codeOwner))
          evm_evm.executionEnv.sender tgt (toExecute evm_evm.accountMap tgt)
          callGas (UInt256.ofNat evm_evm.executionEnv.gasPrice) valueWord valueWord calldata
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header callPerm)
    (hbalance : valueWord ≤ (evm_evm.accountMap.find? evm_evm.executionEnv.codeOwner
      |>.elim ⟨0⟩ (·.balance)))
    (hdepth : evm_evm.executionEnv.depth ≠ 1024)
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      callViaEVM evm_solm tgt value calldata
        (z,
          { evm_solm with
              accountMap := σ'_solm,
              substate := A'_solm,
              createdAccounts := cA' },
          out) callPerm ∧
      accountMapEquiv σ' σ'_solm := by
  have h_ext_eq : accountMapExtensionalEq evm_evm.accountMap evm_solm.accountMap :=
    auctionAccountMapExtensionalEq_of_accountMapEquiv hAccounts
  have hThetaEvm := hTheta
  rw [accountAddress_roundtrip] at hThetaEvm
  generalize htheta_solm :
    Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
      evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
      evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
      (toExecute evm_solm.accountMap tgt) callGas
      (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
      (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header callPerm = thetaRes
  have hcode_equiv :
      toExecute evm_evm.accountMap tgt = toExecute evm_solm.accountMap tgt :=
    accountMapExtensionalEq_toExecute h_ext_eq tgt
  have htheta_solm' :
      Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
        evm_evm.genesisBlockHeader evm_evm.blocks evm_solm.accountMap evm_evm.σ₀ A_in
        evm_evm.executionEnv.codeOwner evm_evm.executionEnv.sender tgt
        (toExecute evm_evm.accountMap tgt) callGas
        (UInt256.ofNat evm_evm.executionEnv.gasPrice) valueWord valueWord calldata
        (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header callPerm =
        (thetaRes.1, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
          thetaRes.2.2.2.2.1, thetaRes.2.2.2.2.2) := by
    rw [← htheta_solm]
    rw [hCreated, ← hOriginalAccounts, hGenesis, hBlocks, hEnv, hcode_equiv]
  let a1 : AccountAddress := ⟨0, by simp [AccountAddress.size]⟩
  have hTheta_rel :=
    (accountMap_extensionality_of_Theta_and_Lambda
      (blobVersionedHashes := evm_evm.executionEnv.blobVersionedHashes)
      (createdAccounts := evm_evm.createdAccounts)
      (genesisBlockHeader := evm_evm.genesisBlockHeader)
      (blocks := evm_evm.blocks)
      (σ₁ := evm_evm.accountMap)
      (σ₂ := evm_solm.accountMap)
      (σ₀ := evm_evm.σ₀)
      (A := A_in)
      (s := evm_evm.executionEnv.codeOwner)
      (o := evm_evm.executionEnv.sender)
      (r := tgt)
      (g := callGas)
      (p := UInt256.ofNat evm_evm.executionEnv.gasPrice)
      (v := valueWord)
      (v' := valueWord)
      (d := calldata)
      (i := ByteArray.empty)
      (ζ := none)
      (H := evm_evm.executionEnv.header)
      (w := callPerm)
      a1 a1
      (toExecute evm_evm.accountMap tgt)
      cA' thetaRes.1
      σ' thetaRes.2.1
      g'' thetaRes.2.2.1
      A' thetaRes.2.2.2.1
      z thetaRes.2.2.2.2.1
      out thetaRes.2.2.2.2.2
      (evm_evm.executionEnv.depth + 1)
      h_ext_eq).1 hThetaEvm.symm htheta_solm'
  have hTheta_s :
      (cA', thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1, z, out) =
        Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
          evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
          evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
          (toExecute evm_solm.accountMap tgt) callGas
          (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
          (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header callPerm := by
    rw [hTheta_rel.2.2.2.1, hTheta_rel.2.2.2.2.1]
    rw [hTheta_rel.1]
    exact htheta_solm.symm
  use thetaRes.2.1
  use thetaRes.2.2.2.1
  constructor
  · exact callViaEVM.callMade (perm := callPerm) hvalue
      ⟨callGas, A_in, hTheta_s⟩ rfl (by
        rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
        exact hbalance) (by
        rw [hEnv]
        exact hdepth)
  · have hσext : accountMapExtensionalEq σ' thetaRes.2.1 := hTheta_rel.2.2.2.2.2
    exact auctionAccountMapEquiv_of_accountMapExtensionalEq hσext

theorem auctionSettleAuctionBurnCall_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {A' : Substate} {z : Bool} {out : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let noun := auctionAuctionNounWord σ1 I
      let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
      let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
      let target := UInt256.land nounsWord solcAddrMask
      typedCallViaEVM auctionConfig
        { initState cA gh bl σ_evm σ₀ g A I with accountMap := σ2 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "burn" 0
        [.int (Int.ofNat noun.toNat)]
        (z,
          { { initState cA gh bl σ_evm σ₀ g A I with accountMap := σ2 } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true) :
    let evmS := initState cA gh bl σ_solm σ₀ g A I
    let evmEnter := auctionSettleAuctionEnterState evmS
    let evmMark := auctionSettleAuctionMarkSettledState evmEnter
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM auctionConfig evmMark
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "burn" 0
        [.int (Int.ofNat
          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩).toNat)]
        (z,
          { evmMark with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true ∧
      accountMapEquiv σ' σ'_solm := by
  let σ1Evm := auctionSettleAuctionEnterMap σ_evm I
  let σ1Solm := auctionSettleAuctionEnterMap σ_solm I
  let σ2Evm := auctionSettleAuctionMarkSettledMap σ1Evm I
  let σ2Solm := auctionSettleAuctionMarkSettledMap σ1Solm I
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  have henterEquiv : accountMapEquiv σ1Evm σ1Solm := by
    dsimp [σ1Evm, σ1Solm]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ hAccounts
  have hmarkValEq :
      auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Evm I) =
        auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Solm I) := by
    have hslot :=
      accountMapEquiv_storage_findD henterEquiv I.codeOwner ⟨211⟩
        (default : UInt256)
    simpa [auctionSlotWord] using congrArg auctionSetBoolOffset20TrueWord hslot
  have hpostEquiv : accountMapEquiv σ2Evm σ2Solm := by
    dsimp [σ2Evm, σ2Solm, auctionSettleAuctionMarkSettledMap]
    rw [hmarkValEq]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Solm I)) henterEquiv
  have henterMapState : accountMapEquiv σ1Solm evmEnter.accountMap := by
    simpa [σ1Solm, evmEnter, evmS] using
      (auctionSettleAuctionEnterMap_accountMap
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g))
  have henterOwner : evmEnter.executionEnv.codeOwner = I.codeOwner := by
    simp [evmEnter, evmS, auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  have hmarkOwner : evmMark.executionEnv.codeOwner = I.codeOwner := by
    simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  have hslotEnterPackedI :
      auctionSlotWord ⟨211⟩ σ1Solm I =
        Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩ := by
    have hslot :=
      accountMapEquiv_storage_findD henterMapState I.codeOwner ⟨211⟩
        (⟨0⟩ : UInt256)
    simpa [henterOwner, auctionSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hslot
  have hpostMapState : accountMapEquiv σ2Solm evmMark.accountMap := by
    dsimp [evmMark, auctionSettleAuctionMarkSettledState]
    rw [henterOwner]
    simp only [storageStore_accountMap]
    dsimp [σ2Solm, auctionSettleAuctionMarkSettledMap]
    rw [hslotEnterPackedI]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (auctionSetBoolOffset20TrueWord
        (Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩)) henterMapState
  have hpostToMark : accountMapEquiv σ2Evm evmMark.accountMap :=
    accountMapEquiv.trans hpostEquiv hpostMapState
  have htarget :
      UInt256.land (auctionSlotWord ⟨201⟩ σ2Evm I) solcAddrMask =
        UInt256.land
          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask := by
    have hslotTarget :
        auctionSlotWord ⟨201⟩ σ2Evm I =
          Solm.EVM.storageLoad evmMark evmMark.executionEnv.codeOwner ⟨201⟩ := by
      have hslot :=
        accountMapEquiv_storage_findD hpostToMark I.codeOwner ⟨201⟩
          (⟨0⟩ : UInt256)
      simpa [hmarkOwner, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage] using hslot
    have hslotMark := auctionSettleAuctionMarkSettledState_storageLoad_nouns evmEnter
    simpa [evmMark] using congrArg (fun w => UInt256.land w solcAddrMask)
      (hslotTarget.trans hslotMark)
  have hnoun :
      auctionAuctionNounWord σ1Evm I =
        Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩ := by
    have hslotEnter :
        auctionSlotWord ⟨207⟩ σ1Evm I =
          auctionSlotWord ⟨207⟩ σ1Solm I := by
      have hslot :=
        accountMapEquiv_storage_findD henterEquiv I.codeOwner ⟨207⟩
          (⟨0⟩ : UInt256)
      simpa [auctionSlotWord] using hslot
    have hslotState :
        auctionSlotWord ⟨207⟩ σ1Solm I =
          Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩ := by
      have hslot :=
        accountMapEquiv_storage_findD henterMapState I.codeOwner ⟨207⟩
          (⟨0⟩ : UInt256)
      simpa [henterOwner, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage] using hslot
    simpa [auctionAuctionNounWord] using hslotEnter.trans hslotState
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hpost⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evmMark) hcall hpostToMark
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, auctionStorageStore_σ₀])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, storageStore_createdAccounts])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, auctionStorageStore_genesisBlockHeader])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, auctionStorageStore_blocks])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, auctionStorageStore_substate])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, storageStore_executionEnv])
  refine ⟨σ'_solm, A'_solm, ?_, hpost⟩
  simpa [σ1Evm, σ2Evm, evmS, evmEnter, evmMark, htarget, hnoun] using hcallSolm

theorem auctionSettleAuctionTransferFromCall_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {A' : Substate} {z : Bool} {out : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let noun := auctionAuctionNounWord σ1 I
      let packed := auctionAuctionPackedWord σ1 I
      let bidder := auctionPackedBidderWord packed
      let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
      let nounsWord := auctionSlotWord ⟨201⟩ σ2 I
      let target := UInt256.land nounsWord solcAddrMask
      typedCallViaEVM auctionConfig
        { initState cA gh bl σ_evm σ₀ g A I with accountMap := σ2 }
        (EVM.address (AccountAddress.ofNat target.toNat)) "transferFrom" 0
        [.address I.codeOwner, .address (AccountAddress.ofNat bidder.toNat),
          .int (Int.ofNat noun.toNat)]
        (z,
          { { initState cA gh bl σ_evm σ₀ g A I with accountMap := σ2 } with
              accountMap := σ', substate := A', createdAccounts := cA' },
          out) true) :
    let evmS := initState cA gh bl σ_solm σ₀ g A I
    let evmEnter := auctionSettleAuctionEnterState evmS
    let evmMark := auctionSettleAuctionMarkSettledState evmEnter
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM auctionConfig evmMark
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "transferFrom" 0
        [.address evmEnter.executionEnv.codeOwner,
          .address (AccountAddress.ofNat
            (auctionPackedBidderWord
              (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩)).toNat),
          .int (Int.ofNat
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩).toNat)]
        (z,
          { evmMark with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true ∧
      accountMapEquiv σ' σ'_solm := by
  let σ1Evm := auctionSettleAuctionEnterMap σ_evm I
  let σ1Solm := auctionSettleAuctionEnterMap σ_solm I
  let σ2Evm := auctionSettleAuctionMarkSettledMap σ1Evm I
  let σ2Solm := auctionSettleAuctionMarkSettledMap σ1Solm I
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  have henterEquiv : accountMapEquiv σ1Evm σ1Solm := by
    dsimp [σ1Evm, σ1Solm]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ hAccounts
  have hmarkValEq :
      auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Evm I) =
        auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Solm I) := by
    have hslot :=
      accountMapEquiv_storage_findD henterEquiv I.codeOwner ⟨211⟩
        (default : UInt256)
    simpa [auctionSlotWord] using congrArg auctionSetBoolOffset20TrueWord hslot
  have hpostEquiv : accountMapEquiv σ2Evm σ2Solm := by
    dsimp [σ2Evm, σ2Solm, auctionSettleAuctionMarkSettledMap]
    rw [hmarkValEq]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Solm I)) henterEquiv
  have henterMapState : accountMapEquiv σ1Solm evmEnter.accountMap := by
    simpa [σ1Solm, evmEnter, evmS] using
      (auctionSettleAuctionEnterMap_accountMap
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g))
  have henterOwner : evmEnter.executionEnv.codeOwner = I.codeOwner := by
    simp [evmEnter, evmS, auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  have hmarkOwner : evmMark.executionEnv.codeOwner = I.codeOwner := by
    simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  have hslotEnterPackedI :
      auctionSlotWord ⟨211⟩ σ1Solm I =
        Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩ := by
    have hslot :=
      accountMapEquiv_storage_findD henterMapState I.codeOwner ⟨211⟩
        (⟨0⟩ : UInt256)
    simpa [henterOwner, auctionSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hslot
  have hpostMapState : accountMapEquiv σ2Solm evmMark.accountMap := by
    dsimp [evmMark, auctionSettleAuctionMarkSettledState]
    rw [henterOwner]
    simp only [storageStore_accountMap]
    dsimp [σ2Solm, auctionSettleAuctionMarkSettledMap]
    rw [hslotEnterPackedI]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (auctionSetBoolOffset20TrueWord
        (Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩)) henterMapState
  have hpostToMark : accountMapEquiv σ2Evm evmMark.accountMap :=
    accountMapEquiv.trans hpostEquiv hpostMapState
  have htarget :
      UInt256.land (auctionSlotWord ⟨201⟩ σ2Evm I) solcAddrMask =
        UInt256.land
          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask := by
    have hslotTarget :
        auctionSlotWord ⟨201⟩ σ2Evm I =
          Solm.EVM.storageLoad evmMark evmMark.executionEnv.codeOwner ⟨201⟩ := by
      have hslot :=
        accountMapEquiv_storage_findD hpostToMark I.codeOwner ⟨201⟩
          (⟨0⟩ : UInt256)
      simpa [hmarkOwner, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage] using hslot
    have hslotMark := auctionSettleAuctionMarkSettledState_storageLoad_nouns evmEnter
    simpa [evmMark] using congrArg (fun w => UInt256.land w solcAddrMask)
      (hslotTarget.trans hslotMark)
  have hnoun :
      auctionAuctionNounWord σ1Evm I =
        Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩ := by
    have hslotEnter :
        auctionSlotWord ⟨207⟩ σ1Evm I =
          auctionSlotWord ⟨207⟩ σ1Solm I := by
      have hslot :=
        accountMapEquiv_storage_findD henterEquiv I.codeOwner ⟨207⟩
          (⟨0⟩ : UInt256)
      simpa [auctionSlotWord] using hslot
    have hslotState :
        auctionSlotWord ⟨207⟩ σ1Solm I =
          Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨207⟩ := by
      have hslot :=
        accountMapEquiv_storage_findD henterMapState I.codeOwner ⟨207⟩
          (⟨0⟩ : UInt256)
      simpa [henterOwner, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage] using hslot
    simpa [auctionAuctionNounWord] using hslotEnter.trans hslotState
  have hbidder :
      auctionPackedBidderWord (auctionAuctionPackedWord σ1Evm I) =
        auctionPackedBidderWord
          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩) := by
    have hslotEnter :
        auctionSlotWord ⟨211⟩ σ1Evm I =
          auctionSlotWord ⟨211⟩ σ1Solm I := by
      have hslot :=
        accountMapEquiv_storage_findD henterEquiv I.codeOwner ⟨211⟩
          (⟨0⟩ : UInt256)
      simpa [auctionSlotWord] using hslot
    have hslotState :
        auctionSlotWord ⟨211⟩ σ1Solm I =
          Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨211⟩ := by
      simpa [henterOwner] using hslotEnterPackedI
    simpa [auctionAuctionPackedWord] using
      congrArg auctionPackedBidderWord (hslotEnter.trans hslotState)
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hpost⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evmMark) hcall hpostToMark
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, auctionStorageStore_σ₀])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, storageStore_createdAccounts])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, auctionStorageStore_genesisBlockHeader])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, auctionStorageStore_blocks])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, auctionStorageStore_substate])
      (by simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
        auctionSettleAuctionEnterState, initState, storageStore_executionEnv])
  refine ⟨σ'_solm, A'_solm, ?_, hpost⟩
  simpa [σ1Evm, σ2Evm, evmS, evmEnter, evmMark, htarget, hnoun, hbidder,
    henterOwner] using hcallSolm

theorem evalExpr_settleAuction_nounsCode_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hnounsCode :
      let σ1 := auctionSettleAuctionEnterMap σ_evm I
      let σ2 := auctionSettleAuctionMarkSettledMap σ1 I
      Reasoning.Theory.uniswapExtCodeSizeWord σ2
          (UInt256.land (auctionSlotWord ⟨201⟩ σ2 I) solcAddrMask) ≠
        ⟨0⟩) :
    let evmS := initState cA gh bl σ_solm σ₀ g A I
    let evmEnter := auctionSettleAuctionEnterState evmS
    evalExpr? auctionConfig
        { contract := auctionContract,
          locals := auctionSettleAuctionSnapshotStore evmEnter }
        (auctionSettleAuctionMarkSettledState evmEnter)
        (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
      .ok (.bool true) := by
  let σ1Evm := auctionSettleAuctionEnterMap σ_evm I
  let σ1Solm := auctionSettleAuctionEnterMap σ_solm I
  let σ2Evm := auctionSettleAuctionMarkSettledMap σ1Evm I
  let σ2Solm := auctionSettleAuctionMarkSettledMap σ1Solm I
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmEnter := auctionSettleAuctionEnterState evmS
  let evmMark := auctionSettleAuctionMarkSettledState evmEnter
  have henterEquiv : accountMapEquiv σ1Evm σ1Solm := by
    dsimp [σ1Evm, σ1Solm]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨2⟩ hAccounts
  have hmarkValEq :
      auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Evm I) =
        auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Solm I) := by
    have hslot :=
      accountMapEquiv_storage_findD henterEquiv I.codeOwner ⟨211⟩
        (default : UInt256)
    simpa [auctionSlotWord] using congrArg auctionSetBoolOffset20TrueWord hslot
  have hpostEquiv : accountMapEquiv σ2Evm σ2Solm := by
    dsimp [σ2Evm, σ2Solm, auctionSettleAuctionMarkSettledMap]
    rw [hmarkValEq]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (auctionSetBoolOffset20TrueWord (auctionSlotWord ⟨211⟩ σ1Solm I)) henterEquiv
  have henterMapState : accountMapEquiv σ1Solm evmEnter.accountMap := by
    simpa [σ1Solm, evmEnter, evmS] using
      (auctionSettleAuctionEnterMap_accountMap
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g))
  have henterOwner : evmEnter.executionEnv.codeOwner = I.codeOwner := by
    simp [evmEnter, evmS, auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  have hmarkOwner : evmMark.executionEnv.codeOwner = I.codeOwner := by
    simp [evmMark, evmEnter, evmS, auctionSettleAuctionMarkSettledState,
      auctionSettleAuctionEnterState, initState, storageStore_executionEnv]
  have hslotEnterPackedI :
      auctionSlotWord ⟨211⟩ σ1Solm I =
        Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩ := by
    have hslot :=
      accountMapEquiv_storage_findD henterMapState I.codeOwner ⟨211⟩
        (⟨0⟩ : UInt256)
    simpa [henterOwner, auctionSlotWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage] using hslot
  have hpostMapState : accountMapEquiv σ2Solm evmMark.accountMap := by
    dsimp [evmMark, auctionSettleAuctionMarkSettledState]
    rw [henterOwner]
    simp only [storageStore_accountMap]
    dsimp [σ2Solm, auctionSettleAuctionMarkSettledMap]
    rw [hslotEnterPackedI]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨211⟩
      (auctionSetBoolOffset20TrueWord
        (Solm.EVM.storageLoad evmEnter I.codeOwner ⟨211⟩)) henterMapState
  have hpostToMark : accountMapEquiv σ2Evm evmMark.accountMap :=
    accountMapEquiv.trans hpostEquiv hpostMapState
  have htarget :
      UInt256.land (auctionSlotWord ⟨201⟩ σ2Evm I) solcAddrMask =
        UInt256.land
          (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask := by
    have hslotTarget :
        auctionSlotWord ⟨201⟩ σ2Evm I =
          Solm.EVM.storageLoad evmMark evmMark.executionEnv.codeOwner ⟨201⟩ := by
      have hslot :=
        accountMapEquiv_storage_findD hpostToMark I.codeOwner ⟨201⟩
          (⟨0⟩ : UInt256)
      simpa [hmarkOwner, auctionSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage] using hslot
    have hslotMark := auctionSettleAuctionMarkSettledState_storageLoad_nouns evmEnter
    simpa [evmMark] using congrArg (fun w => UInt256.land w solcAddrMask)
      (hslotTarget.trans hslotMark)
  have hnounsCodeState :
      Reasoning.Theory.uniswapExtCodeSizeWord evmMark.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask) ≠
        ⟨0⟩ := by
    intro hzero
    have htmp :
        Reasoning.Theory.uniswapExtCodeSizeWord evmMark.accountMap
            (UInt256.land (auctionSlotWord ⟨201⟩ σ2Evm I) solcAddrMask) =
          ⟨0⟩ := by
      simpa [htarget] using hzero
    have hback :
        Reasoning.Theory.uniswapExtCodeSizeWord σ2Evm
            (UInt256.land (auctionSlotWord ⟨201⟩ σ2Evm I) solcAddrMask) =
          ⟨0⟩ := by
      rw [uniswapExtCodeSizeWord_accountMapEquiv hpostToMark
        (UInt256.land (auctionSlotWord ⟨201⟩ σ2Evm I) solcAddrMask)]
      exact htmp
    exact hnounsCode hback
  have hlookupPos :
      0 <
        (UInt256.ofNat
          (((auctionSettleAuctionMarkSettledState evmEnter).lookupAccount
            (AccountAddress.ofNat
              ((UInt256.land
                (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
                solcAddrMask).toNat))).option 0 (fun acc => acc.code.size))).toNat := by
    let targetSource :=
      UInt256.land
        (Solm.EVM.storageLoad evmEnter evmEnter.executionEnv.codeOwner ⟨201⟩)
        solcAddrMask
    simpa [evmMark, targetSource, State.lookupAccount] using
      auctionUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evmMark.accountMap) (target := targetSource)
        (addr := AccountAddress.ofNat targetSource.toNat)
        (by simp [accountAddress_ofUInt256_eq_ofNat_toNat])
        (by simpa [targetSource] using hnounsCodeState)
  simpa [evmS, evmEnter] using
    evalExpr_settleAuction_nounsCode_after_markSettled evmEnter hlookupPos

theorem auctionSettleAuctionTransitionReverts_burnCallFailure
    (evm evmBurn : EVM.State) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (false, evmBurn, out) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_burnCallFailure (auctionSettleAuctionEnterState evm)
      evmBurn
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨209⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        intro hzero
        exact hstart (by simpa [henv, hload] using hzero))
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hsettled)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨210⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using htime)
      (by
        have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            evm.executionEnv.codeOwner ⟨211⟩ =
              Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
          simpa [auctionSettleAuctionEnterState] using
            storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
              (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
        have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
          simpa [auctionSettleAuctionEnterState] using
            storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
        simpa [henv, hload] using hbidder)
      hnounsCode hcall))

theorem auctionSettleAuctionTransitionReturns_burnNoPayout
    (evm evmBurn : EVM.State) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨208⟩ =
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
        (auctionSettleAuctionExitState evmBurn) none) := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (calleeEvm := evmBurn)
      (name := "_settleAuction") (args := []) (retVar := "_s") (argVals := [])
      (callee := settleAuctionFn) (locals := ∅)
      (calleeSolm :=
        ({ contract := auctionContract,
           locals := (auctionSettleAuctionSnapshotStore
             (auctionSettleAuctionEnterState evm)).insert "_burn" .unit } : Frame))
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReturns_burnNoPayout (auctionSettleAuctionEnterState evm)
        evmBurn
        (by
          have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨209⟩ =
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
            simpa [auctionSettleAuctionEnterState] using
              storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
          intro hzero
          exact hstart (by simpa [henv, hload] using hzero))
        (by
          have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨211⟩ =
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
            simpa [auctionSettleAuctionEnterState] using
              storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
          simpa [henv, hload] using hsettled)
        (by
          have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
            simpa [auctionSettleAuctionEnterState] using
              storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
          simpa [henv, hload] using htime)
        (by
          have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨211⟩ =
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
            simpa [auctionSettleAuctionEnterState] using
              storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
          simpa [henv, hload] using hbidder)
        hnounsCode hcall hamount)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_settleAuction_notEntered evmBurn
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals)
      (auctionSettleAuctionAssignStatusNotEntered evmBurn
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals
        (by simp [resumeAfterInternalCall]))) ExecBlock.nil

theorem auctionSettleAuctionTransitionReturns_burnPayoutLowLevelSuccess
    (evm evmBurn evmPay : EVM.State) {out outPay : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (true, evmPay, outPay) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
        (auctionSettleAuctionExitState evmPay) none) := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (calleeEvm := evmPay)
      (name := "_settleAuction") (args := []) (retVar := "_s") (argVals := [])
      (callee := settleAuctionFn) (locals := ∅)
      (calleeSolm :=
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore
              (auctionSettleAuctionEnterState evm)).insert "_burn" .unit }
          "_pay" none))
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReturns_burnPayoutLowLevelSuccess
        (auctionSettleAuctionEnterState evm) evmBurn evmPay
        (by
          have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨209⟩ =
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨209⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
            simpa [auctionSettleAuctionEnterState] using
              storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
          intro hzero
          exact hstart (by simpa [henv, hload] using hzero))
        (by
          have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨211⟩ =
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
            simpa [auctionSettleAuctionEnterState] using
              storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
          simpa [henv, hload] using hsettled)
        (by
          have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨210⟩ =
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨210⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
            simpa [auctionSettleAuctionEnterState] using
              storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
          simpa [henv, hload] using htime)
        (by
          have hload : Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              evm.executionEnv.codeOwner ⟨211⟩ =
                Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩ := by
            simpa [auctionSettleAuctionEnterState] using
              storageLoad_storageStore_ne evm evm.executionEnv.codeOwner
                (readSlot := ⟨211⟩) (writeSlot := ⟨101⟩) (val := ⟨2⟩) (by decide)
          have henv : (auctionSettleAuctionEnterState evm).executionEnv = evm.executionEnv := by
            simpa [auctionSettleAuctionEnterState] using
              storageStore_executionEnv evm evm.executionEnv.codeOwner ⟨101⟩ ⟨2⟩
          simpa [henv, hload] using hbidder)
        hnounsCode hcall hamount hpayCall)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_settleAuction_notEntered evmPay
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals)
      (auctionSettleAuctionAssignStatusNotEntered evmPay
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals
        (by simp [resumeAfterInternalCall]))) ExecBlock.nil

theorem auctionSettleAuctionTransitionReturns_burnPayoutLowLevelFailureWethSuccess
    (evm evmBurn evmPay evmDeposit evmTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray} {transferOk : Bool}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat =
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "burn" 0
      [.int (Int.ofNat
        (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmBurn, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmBurn (EVM.address (auctionOwnerAddressAt evmBurn))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmBurn),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (true, evmTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer =
      some [.bool transferOk]) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
        (auctionSettleAuctionExitState evmTransfer) none) := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (calleeEvm := evmTransfer)
      (name := "_settleAuction") (args := []) (retVar := "_s") (argVals := [])
      (callee := settleAuctionFn) (locals := ∅)
      (calleeSolm :=
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore
              (auctionSettleAuctionEnterState evm)).insert "_burn" .unit }
          "_pay" none))
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReturns_burnPayoutLowLevelFailureWethSuccess
        (auctionSettleAuctionEnterState evm) evmBurn evmPay evmDeposit evmTransfer
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨209⟩) (by decide)]
            using hstart)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
            using hsettled)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨210⟩) (by decide)]
            using htime)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
            using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer htransferDec)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_settleAuction_notEntered evmTransfer
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals)
      (auctionSettleAuctionAssignStatusNotEntered evmTransfer
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals
        (by simp [resumeAfterInternalCall]))) ExecBlock.nil

theorem auctionSettleAuctionTransitionReverts_transferFromNoCode
    (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsNoCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool false)) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_transferFromNoCode (auctionSettleAuctionEnterState evm)
      (by
        simpa [auctionSettleAuctionEnterState_executionEnv evm,
          auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨209⟩) (by decide)]
          using hstart)
      (by
        simpa [auctionSettleAuctionEnterState_executionEnv evm,
          auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
          using hsettled)
      (by
        simpa [auctionSettleAuctionEnterState_executionEnv evm,
          auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨210⟩) (by decide)]
          using htime)
      (by
        simpa [auctionSettleAuctionEnterState_executionEnv evm,
          auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
          using hbidder)
      hnounsNoCode))

theorem auctionSettleAuctionTransitionReverts_transferFromCallFailure
    (evm evmTransfer : EVM.State) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (false, evmTransfer, out) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body .reverted := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  exact ExecBlock.consRevert (internalCallFunctionRevert
    (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
    (evm := auctionSettleAuctionEnterState evm) (name := "_settleAuction") (args := [])
    (retVar := "_s") (argVals := []) (callee := settleAuctionFn) (locals := ∅)
    (by rfl) (by rfl) (by rfl)
    (auctionSettleAuctionBodyReverts_transferFromCallFailure
      (auctionSettleAuctionEnterState evm) evmTransfer
      (by
        simpa [auctionSettleAuctionEnterState_executionEnv evm,
          auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨209⟩) (by decide)]
          using hstart)
      (by
        simpa [auctionSettleAuctionEnterState_executionEnv evm,
          auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
          using hsettled)
      (by
        simpa [auctionSettleAuctionEnterState_executionEnv evm,
          auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨210⟩) (by decide)]
          using htime)
      (by
        simpa [auctionSettleAuctionEnterState_executionEnv evm,
          auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
          using hbidder)
      hnounsCode hcall))

theorem auctionSettleAuctionTransitionReturns_transferFromNoPayout
    (evm evmTransfer : EVM.State) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
          (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨208⟩ =
        ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
        (auctionSettleAuctionExitState evmTransfer) none) := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (calleeEvm := evmTransfer)
      (name := "_settleAuction") (args := []) (retVar := "_s") (argVals := [])
      (callee := settleAuctionFn) (locals := ∅)
      (calleeSolm :=
        ({ contract := auctionContract,
           locals := (auctionSettleAuctionSnapshotStore
             (auctionSettleAuctionEnterState evm)).insert "_tf" .unit } : Frame))
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReturns_transferFromNoPayout
        (auctionSettleAuctionEnterState evm) evmTransfer
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨209⟩) (by decide)]
            using hstart)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
            using hsettled)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨210⟩) (by decide)]
            using htime)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
            using hbidder)
        hnounsCode hcall hamount)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_settleAuction_notEntered evmTransfer
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals)
      (auctionSettleAuctionAssignStatusNotEntered evmTransfer
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals
        (by simp [resumeAfterInternalCall]))) ExecBlock.nil

theorem auctionSettleAuctionTransitionReturns_transferFromPayoutLowLevelSuccess
    (evm evmTransfer evmPay : EVM.State) {out outPay : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (true, evmPay, outPay) true) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
        (auctionSettleAuctionExitState evmPay) none) := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (calleeEvm := evmPay)
      (name := "_settleAuction") (args := []) (retVar := "_s") (argVals := [])
      (callee := settleAuctionFn) (locals := ∅)
      (calleeSolm :=
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore
              (auctionSettleAuctionEnterState evm)).insert "_tf" .unit }
          "_pay" none))
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReturns_transferFromPayoutLowLevelSuccess
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨209⟩) (by decide)]
            using hstart)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
            using hsettled)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨210⟩) (by decide)]
            using htime)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
            using hbidder)
        hnounsCode hcall hamount hpayCall)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_settleAuction_notEntered evmPay
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals)
      (auctionSettleAuctionAssignStatusNotEntered evmPay
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals
        (by simp [resumeAfterInternalCall]))) ExecBlock.nil

theorem auctionSettleAuctionTransitionReturns_transferFromPayoutLowLevelFailureWethSuccess
    (evm evmTransfer evmPay evmDeposit evmWethTransfer : EVM.State)
    {out outPay outDeposit outTransfer : ByteArray} {transferOk : Bool}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpaused :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩) ⟨255⟩ ≠
        ⟨0⟩)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hstart : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩ ≠ ⟨0⟩)
    (hsettled :
      auctionPackedSettledWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩) =
        ⟨0⟩)
    (htime : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (hnounsCode :
      evalExpr? auctionConfig
          { contract := auctionContract,
            locals := auctionSettleAuctionSnapshotStore (auctionSettleAuctionEnterState evm) }
          (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
          (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM auctionConfig
      (auctionSettleAuctionMarkSettledState (auctionSettleAuctionEnterState evm))
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "transferFrom" 0
      [.address (auctionSettleAuctionEnterState evm).executionEnv.codeOwner,
        .address (AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
              (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat),
        .int (Int.ofNat
          (Solm.EVM.storageLoad (auctionSettleAuctionEnterState evm)
            (auctionSettleAuctionEnterState evm).executionEnv.codeOwner ⟨207⟩).toNat)]
      (true, evmTransfer, out) true)
    (hamount :
      0 <
        (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
    (hpayCall : callViaEVM evmTransfer (EVM.address (auctionOwnerAddressAt evmTransfer))
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)
      ByteArray.empty (false, evmPay, outPay) true)
    (hwethCode :
      0 < (UInt256.ofNat (((evmPay.lookupAccount
        (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
            solcAddrMask).toNat))).option 0 (fun acc => acc.code.size)))).toNat)
    (hdeposit : typedCallViaEVM auctionConfig evmPay
      (EVM.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evmPay evmPay.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "deposit"
      (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat) []
      (true, evmDeposit, outDeposit) true)
    (htransfer : typedCallViaEVM auctionConfig evmDeposit
      (EVM.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evmDeposit evmDeposit.executionEnv.codeOwner ⟨202⟩)
          solcAddrMask).toNat)) "transfer" 0
      [.address (auctionOwnerAddressAt evmTransfer),
        .int (Int.ofNat (auctionSettleAuctionAmount (auctionSettleAuctionEnterState evm)).toNat)]
      (true, evmWethTransfer, outTransfer) true)
    (htransferDec : auctionConfig.externalABI.decode? "transfer" outTransfer =
      some [.bool transferOk]) :
    ExecTransitionBody auctionConfig auctionContract evm ∅
      settleAuctionTransition.body
      (.returned (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none)
        (auctionSettleAuctionExitState evmWethTransfer) none) := by
  dsimp [settleAuctionTransition, nonpayable]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_pause_paused_true evm hpaused)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_settleAuction_status_ne_entered_true evm hstatus)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_settleAuction_entered evm ∅)
      (auctionSettleAuctionAssignStatusEntered evm ∅ (by simp))) ?_
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := auctionConfig) (caller := { contract := auctionContract, locals := ∅ })
      (evm := auctionSettleAuctionEnterState evm) (calleeEvm := evmWethTransfer)
      (name := "_settleAuction") (args := []) (retVar := "_s") (argVals := [])
      (callee := settleAuctionFn) (locals := ∅)
      (calleeSolm :=
        (resumeAfterInternalCall
          { contract := auctionContract,
            locals := (auctionSettleAuctionSnapshotStore
              (auctionSettleAuctionEnterState evm)).insert "_tf" .unit }
          "_pay" none))
      (value := none) (by rfl) (by rfl) (by rfl)
      (auctionSettleAuctionBodyReturns_transferFromPayoutLowLevelFailureWethSuccess
        (auctionSettleAuctionEnterState evm) evmTransfer evmPay evmDeposit evmWethTransfer
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨209⟩) (by decide)]
            using hstart)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
            using hsettled)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨210⟩) (by decide)]
            using htime)
        (by
          simpa [auctionSettleAuctionEnterState_executionEnv evm,
            auctionSettleAuctionEnterState_storageLoad_ne evm (slot := ⟨211⟩) (by decide)]
            using hbidder)
        hnounsCode hcall hamount hpayCall hwethCode hdeposit htransfer htransferDec)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_settleAuction_notEntered evmWethTransfer
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals)
      (auctionSettleAuctionAssignStatusNotEntered evmWethTransfer
        (resumeAfterInternalCall { contract := auctionContract, locals := ∅ } "_s" none).locals
        (by simp [resumeAfterInternalCall]))) ExecBlock.nil

end Auction
