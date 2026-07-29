import Benchmarks.Dss.End.FileAddress

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

attribute [local simp]
  wardsSelectorBytes vatSelectorBytes catSelectorBytes dogSelectorBytes vowSelectorBytes
  potSelectorBytes spotSelectorBytes cureSelectorBytes liveSelectorBytes whenSelectorBytes
  waitSelectorBytes debtSelectorBytes tagSelectorBytes gapSelectorBytes ArtSelectorBytes
  fixSelectorBytes bagSelectorBytes outSelectorBytes relySelectorBytes denySelectorBytes
  fileAddressSelectorBytes fileUintSelectorBytes cageSelectorBytes cageIlkSelectorBytes
  snipSelectorBytes skipSelectorBytes skimSelectorBytes freeSelectorBytes thawSelectorBytes
  flowSelectorBytes packSelectorBytes cashSelectorBytes

theorem endFileAddressSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_false evm0 I (by simp [evm0, initState]) hauth
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem endFileAddressSourceBodyNotLiveReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I ≠ ⟨1⟩) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_false evm0 I hlive
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hliveGuard)

theorem endFileAddressSourceBodyUnrecognizedReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (hnotVat : fileAddressWhat I ≠ fileAddressVatBytes)
    (hnotCat : fileAddressWhat I ≠ fileAddressCatBytes)
    (hnotDog : fileAddressWhat I ≠ fileAddressDogBytes)
    (hnotVow : fileAddressWhat I ≠ fileAddressVowBytes)
    (hnotPot : fileAddressWhat I ≠ fileAddressPotBytes)
    (hnotSpot : fileAddressWhat I ≠ fileAddressSpotBytes)
    (hnotCure : fileAddressWhat I ≠ fileAddressCureBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, fileAddressVatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, fileAddressCatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, fileAddressDogBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressDogBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool false) := by
    simpa [vowLit, fileAddressVowBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVow)
  have hpot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") potLit) = .ok (.bool false) := by
    simpa [potLit, fileAddressPotBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressPotBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotPot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") spotLit) = .ok (.bool false) := by
    simpa [spotLit, fileAddressSpotBytes, strLit4, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressSpotBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotSpot)
  have hcure :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") cureLit) = .ok (.bool false) := by
    simpa [cureLit, fileAddressCureBytes, strLit4, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCureBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotCure)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hunrec :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hcureBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcure hunrec)
  have hspotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hspot hcureBlock)
  have hpotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hpot hspotBlock)
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hvow hpotBlock)
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hdog hvowBlock)
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") catLit) [.assign .storage catRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ] ]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcat hdogBlock)
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
  exact ExecBlock.consRevert (ExecStmt.iteFalse hvat hcatBlock)

theorem endFileAddressSourceBodySpotOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (hnotVat : fileAddressWhat I ≠ fileAddressVatBytes)
    (hnotCat : fileAddressWhat I ≠ fileAddressCatBytes)
    (hnotDog : fileAddressWhat I ≠ fileAddressDogBytes)
    (hnotVow : fileAddressWhat I ≠ fileAddressVowBytes)
    (hnotPot : fileAddressWhat I ≠ fileAddressPotBytes)
    (hwhat : fileAddressWhat I = fileAddressSpotBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileAddressPostState evm0 ⟨6⟩ I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, fileAddressVatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, fileAddressCatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, fileAddressDogBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressDogBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool false) := by
    simpa [vowLit, fileAddressVowBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVow)
  have hpot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") potLit) = .ok (.bool false) := by
    simpa [potLit, fileAddressPotBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressPotBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotPot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") spotLit) = .ok (.bool true) := by
    simpa [spotLit, fileAddressSpotBytes, strLit4, locals] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressSpotBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage spotRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, spotRef] using
      assign_fileAddressStorage evm0 I "spot" spotRef ⟨6⟩
        (by simp [fileAddressLocals])
        rfl
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by
          funext evm
          simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, addrLoc])
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage spotRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hspotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hspot hthen) ExecBlock.nil
  have hpotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hpot hspotBlock) ExecBlock.nil
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvow hpotBlock) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdog hvowBlock) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") catLit) [.assign .storage catRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceBodyCureOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (hnotVat : fileAddressWhat I ≠ fileAddressVatBytes)
    (hnotCat : fileAddressWhat I ≠ fileAddressCatBytes)
    (hnotDog : fileAddressWhat I ≠ fileAddressDogBytes)
    (hnotVow : fileAddressWhat I ≠ fileAddressVowBytes)
    (hnotPot : fileAddressWhat I ≠ fileAddressPotBytes)
    (hnotSpot : fileAddressWhat I ≠ fileAddressSpotBytes)
    (hwhat : fileAddressWhat I = fileAddressCureBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileAddressPostState evm0 ⟨7⟩ I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, fileAddressVatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, fileAddressCatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, fileAddressDogBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressDogBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool false) := by
    simpa [vowLit, fileAddressVowBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVow)
  have hpot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") potLit) = .ok (.bool false) := by
    simpa [potLit, fileAddressPotBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressPotBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotPot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") spotLit) = .ok (.bool false) := by
    simpa [spotLit, fileAddressSpotBytes, strLit4, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressSpotBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotSpot)
  have hcure :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") cureLit) = .ok (.bool true) := by
    simpa [cureLit, fileAddressCureBytes, strLit4, locals] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCureBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage cureRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, cureRef] using
      assign_fileAddressStorage evm0 I "cure" cureRef ⟨7⟩
        (by simp [fileAddressLocals])
        rfl
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by
          funext evm
          simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, addrLoc])
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage cureRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hcureBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcure hthen) ExecBlock.nil
  have hspotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hspot hcureBlock) ExecBlock.nil
  have hpotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hpot hspotBlock) ExecBlock.nil
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvow hpotBlock) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdog hvowBlock) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") catLit) [.assign .storage catRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 3000000 in
theorem endFileAddressX_spot_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressSpotBytes)
    (h : RD endBytecode I g s0 ⟨8657⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩
        (setAddressOffset0Word (endSlotWord ⟨6⟩ σ I) (fileAddressDataKey I)))
      ByteArray.empty := by
  have rd8659pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8664 := rd8659pre.pushConst (⟨0x1cdc1bdd⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd8669pre := evm_run rd8664 with [
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hspotWord :
      ABI.bytesToWord fileAddressSpotBytes =
        UInt256.shiftLeft (⟨0x1cdc1bdd⟩ : UInt256) ⟨226⟩ :=
    fileAddressConstWords.2.2.2.2.2.1
  rw [hwhatWord, hspotWord, u256_eq_refl] at rd8669pre
  have rd8673pre := evm_run rd8669pre with [
    raw push2 ⟨8704⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd8676pre := evm_run rd8673pre with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k8677, C8677, rd8677raw⟩ := rd8676pre.sload (by native_decide) (by evm_ov)
  have rd8677 : RD endBytecode I g s0 ⟨8677⟩
      (endSlotWord ⟨6⟩ σ I :: ⟨6⟩ :: fileAddressDataKey I ::
        UInt256.shiftLeft (⟨0x1cdc1bdd⟩ : UInt256) ⟨226⟩ :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8677 C8677 := by
    simpa [endSlotWord] using rd8677raw
  have rd8699pre := evm_run rd8677 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreWord :
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨6⟩ σ I)) =
        setAddressOffset0Word (endSlotWord ⟨6⟩ σ I) (fileAddressDataKey I) := by
    calc
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨6⟩ σ I)) =
          UInt256.lor (UInt256.land (endSlotWord ⟨6⟩ σ I) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileAddressDataKey I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (endSlotWord ⟨6⟩ σ I)]
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (endSlotWord ⟨6⟩ σ I) (fileAddressDataKey I) := by
            rfl
  obtain ⟨k8700, C8700, rd8700raw⟩ := rd8699pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc8700 :
      (⟨8677⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨8700⟩ := by
    native_decide
  rw [hpc8700] at rd8700raw
  simp only [
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8700raw
  rw [hstoreWord] at rd8700raw
  have rd8700 : RD endBytecode I g s0 ⟨8700⟩
      [fileAddressDataKey I, UInt256.shiftLeft (⟨0x1cdc1bdd⟩ : UInt256) ⟨226⟩, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩
        (setAddressOffset0Word (endSlotWord ⟨6⟩ σ I) (fileAddressDataKey I))) k8700 C8700 := by
    simpa [endSlotWord] using rd8700raw
  have rd8747 := evm_run rd8700 with [
    raw push2 ⟨8747⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact endFileAddressX_logReturn hperm rd8747

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_skip_spot {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotSpotWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressSpotBytes)
    (h : RD endBytecode I g s0 ⟨8657⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8704⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd8659pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8664 := rd8659pre.pushConst (⟨0x1cdc1bdd⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd8668pre := evm_run rd8664 with [
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hspotWord :
      ABI.bytesToWord fileAddressSpotBytes =
        UInt256.shiftLeft (⟨0x1cdc1bdd⟩ : UInt256) ⟨226⟩ :=
    fileAddressConstWords.2.2.2.2.2.1
  have hspotEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x1cdc1bdd⟩ : UInt256) ⟨226⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← hspotWord]
    exact u256_eq_of_ne (by intro hbad; exact hnotSpotWord hbad.symm)
  rw [hspotEq] at rd8668pre
  have rd8704 := evm_run rd8668pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨8704⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd8704⟩

set_option maxHeartbeats 3000000 in
theorem endFileAddressX_cure_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressCureBytes)
    (h : RD endBytecode I g s0 ⟨8704⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨7⟩
        (setAddressOffset0Word (endSlotWord ⟨7⟩ σ I) (fileAddressDataKey I)))
      ByteArray.empty := by
  have rd8706pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8711 := rd8706pre.pushConst (⟨0x63757265⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd8716pre := evm_run rd8711 with [
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hcureWord :
      ABI.bytesToWord fileAddressCureBytes =
        UInt256.shiftLeft (⟨0x63757265⟩ : UInt256) ⟨224⟩ :=
    fileAddressConstWords.2.2.2.2.2.2
  rw [hwhatWord, hcureWord, u256_eq_refl] at rd8716pre
  have rd8720pre := evm_run rd8716pre with [
    raw push2 ⟨1499⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd8723pre := evm_run rd8720pre with [
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k8724, C8724, rd8724raw⟩ := rd8723pre.sload (by native_decide) (by evm_ov)
  have rd8724 : RD endBytecode I g s0 ⟨8724⟩
      (endSlotWord ⟨7⟩ σ I :: ⟨7⟩ :: fileAddressDataKey I ::
        UInt256.shiftLeft (⟨0x63757265⟩ : UInt256) ⟨224⟩ :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8724 C8724 := by
    simpa [endSlotWord] using rd8724raw
  have rd8746pre := evm_run rd8724 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreWord :
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨7⟩ σ I)) =
        setAddressOffset0Word (endSlotWord ⟨7⟩ σ I) (fileAddressDataKey I) := by
    calc
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨7⟩ σ I)) =
          UInt256.lor (UInt256.land (endSlotWord ⟨7⟩ σ I) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileAddressDataKey I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (endSlotWord ⟨7⟩ σ I)]
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (endSlotWord ⟨7⟩ σ I) (fileAddressDataKey I) := by
            rfl
  obtain ⟨k8747, C8747, rd8747raw⟩ := rd8746pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc8747 :
      (⟨8724⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨8747⟩ := by
    native_decide
  rw [hpc8747] at rd8747raw
  simp only [
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8747raw
  rw [hstoreWord] at rd8747raw
  have rd8747 : RD endBytecode I g s0 ⟨8747⟩
      [fileAddressDataKey I, UInt256.shiftLeft (⟨0x63757265⟩ : UInt256) ⟨224⟩, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨7⟩
        (setAddressOffset0Word (endSlotWord ⟨7⟩ σ I) (fileAddressDataKey I))) k8747 C8747 := by
    simpa [endSlotWord] using rd8747raw
  exact endFileAddressX_logReturn hperm rd8747

set_option maxHeartbeats 3000000 in
theorem endFileAddressX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotCureWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressCureBytes)
    (h : RD endBytecode I g s0 ⟨8704⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd8706pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8711 := rd8706pre.pushConst (⟨0x63757265⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd8715pre := evm_run rd8711 with [
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hcureWord :
      ABI.bytesToWord fileAddressCureBytes =
        UInt256.shiftLeft (⟨0x63757265⟩ : UInt256) ⟨224⟩ :=
    fileAddressConstWords.2.2.2.2.2.2
  have hcureEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x63757265⟩ : UInt256) ⟨224⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← hcureWord]
    exact u256_eq_of_ne (by intro hbad; exact hnotCureWord hbad.symm)
  rw [hcureEq] at rd8715pre
  have rd1499 := evm_run rd8715pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1499⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact RD.endFileUintUnrecognizedRevert rd1499
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFileAddressBodyCore : endBodyObligation 20 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 20) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition :=
    endDispatchFileAddressLocal hsel
  have hreach := endReachFileAddressBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_fileAddress_ok (I := I) hsz68
    obtain ⟨_, _, rd8268⟩ :=
      endFileAddressX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hauthCouple : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    have hliveCouple : fileAddressLiveWord σ_evm I = fileAddressLiveWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
        rw [← hauthCouple]
        exact hauth
      obtain ⟨_, _, rd8357⟩ := endFileAddressX_authorized (I := I) hauth rd8268
      by_cases hlive : fileAddressLiveWord σ_evm I = ⟨1⟩
      · have hliveSolm : fileAddressLiveWord σ_solm I = ⟨1⟩ := by
          rw [← hliveCouple]
          exact hlive
        obtain ⟨_, _, rd8427⟩ := endFileAddressX_live (I := I) hlive rd8357
        by_cases hvat : fileAddressWhat I = fileAddressVatBytes
        · have hvatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressVatBytes :=
            fileAddressWhatWord_eq_of_bytes_eq hvat
          have hslotCouple : endSlotWord ⟨1⟩ σ_evm I = endSlotWord ⟨1⟩ σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
          have hbody :
              ExecTransitionBody config contract evmSolm (fileAddressLocals I)
                fileAddressTransition.body
                (.returned { contract := contract, locals := fileAddressLocals I }
                  (fileAddressPostState evmSolm ⟨1⟩ I) none) := by
            simpa [evmSolm] using
              endFileAddressSourceBodyVatOk (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hvat
          exact (endFileAddressX_vat_ok hperm hvatWord rd8427)
            |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              (by simp [fileAddressPostState, evmSolm, initState, storageStore_createdAccounts])
              (by
                rw [hslotCouple]
                simpa [fileAddressPostState, evmSolm, initState, storageStore_accountMap] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩
                    (setAddressOffset0Word (endSlotWord ⟨1⟩ σ_solm I)
                      (fileAddressDataKey I)) hAccounts)
              (by
                simpa [fileAddressTransition] using
                  (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                    (dvs := []) rfl (by native_decide) (by native_decide)))
        · have hnotVatWord :
              calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressVatBytes :=
            fileAddressWhatWord_ne_of_bytes_ne hvat fileAddressBytes_lengths.1
          obtain ⟨_, _, rd8473⟩ := endFileAddressX_skip_vat hnotVatWord rd8427
          by_cases hcat : fileAddressWhat I = fileAddressCatBytes
          · have hcatWord :
                calldataWord I.calldata 4 = ABI.bytesToWord fileAddressCatBytes :=
              fileAddressWhatWord_eq_of_bytes_eq hcat
            have hslotCouple : endSlotWord ⟨2⟩ σ_evm I = endSlotWord ⟨2⟩ σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
            have hbody :
                ExecTransitionBody config contract evmSolm (fileAddressLocals I)
                  fileAddressTransition.body
                  (.returned { contract := contract, locals := fileAddressLocals I }
                    (fileAddressPostState evmSolm ⟨2⟩ I) none) := by
              simpa [evmSolm] using
                endFileAddressSourceBodyCatOk (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hauthSolm hliveSolm hvat hcat
            exact (endFileAddressX_cat_ok hperm hcatWord rd8473)
              |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                (by simp [fileAddressPostState, evmSolm, initState, storageStore_createdAccounts])
                (by
                  rw [hslotCouple]
                  simpa [fileAddressPostState, evmSolm, initState, storageStore_accountMap] using
                    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
                      (setAddressOffset0Word (endSlotWord ⟨2⟩ σ_solm I)
                        (fileAddressDataKey I)) hAccounts)
                (by
                  simpa [fileAddressTransition] using
                    (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                      (dvs := []) rfl (by native_decide) (by native_decide)))
          · have hnotCatWord :
                calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressCatBytes :=
              fileAddressWhatWord_ne_of_bytes_ne hcat fileAddressBytes_lengths.2.1
            obtain ⟨_, _, rd8519⟩ := endFileAddressX_skip_cat hnotCatWord rd8473
            by_cases hdog : fileAddressWhat I = fileAddressDogBytes
            · have hdogWord :
                  calldataWord I.calldata 4 = ABI.bytesToWord fileAddressDogBytes :=
                fileAddressWhatWord_eq_of_bytes_eq hdog
              have hslotCouple : endSlotWord ⟨3⟩ σ_evm I = endSlotWord ⟨3⟩ σ_solm I :=
                accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
              have hbody :
                  ExecTransitionBody config contract evmSolm (fileAddressLocals I)
                    fileAddressTransition.body
                    (.returned { contract := contract, locals := fileAddressLocals I }
                      (fileAddressPostState evmSolm ⟨3⟩ I) none) := by
                simpa [evmSolm] using
                  endFileAddressSourceBodyDogOk (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hliveSolm hvat hcat hdog
              exact (endFileAddressX_dog_ok hperm hdogWord rd8519)
                |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                  (by simp [fileAddressPostState, evmSolm, initState, storageStore_createdAccounts])
                  (by
                    rw [hslotCouple]
                    simpa [fileAddressPostState, evmSolm, initState, storageStore_accountMap] using
                      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩
                        (setAddressOffset0Word (endSlotWord ⟨3⟩ σ_solm I)
                          (fileAddressDataKey I)) hAccounts)
                  (by
                    simpa [fileAddressTransition] using
                      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                        (dvs := []) rfl (by native_decide) (by native_decide)))
            · have hnotDogWord :
                  calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressDogBytes :=
                fileAddressWhatWord_ne_of_bytes_ne hdog fileAddressBytes_lengths.2.2.1
              obtain ⟨_, _, rd8565⟩ := endFileAddressX_skip_dog hnotDogWord rd8519
              by_cases hvow : fileAddressWhat I = fileAddressVowBytes
              · have hvowWord :
                    calldataWord I.calldata 4 = ABI.bytesToWord fileAddressVowBytes :=
                  fileAddressWhatWord_eq_of_bytes_eq hvow
                have hslotCouple :
                    endSlotWord ⟨4⟩ σ_evm I = endSlotWord ⟨4⟩ σ_solm I :=
                  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
                have hbody :
                    ExecTransitionBody config contract evmSolm (fileAddressLocals I)
                      fileAddressTransition.body
                      (.returned { contract := contract, locals := fileAddressLocals I }
                        (fileAddressPostState evmSolm ⟨4⟩ I) none) := by
                  simpa [evmSolm] using
                    endFileAddressSourceBodyVowOk (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      hwv hauthSolm hliveSolm hvat hcat hdog hvow
                exact (endFileAddressX_vow_ok hperm hvowWord rd8565)
                  |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                    (by simp [fileAddressPostState, evmSolm, initState, storageStore_createdAccounts])
                    (by
                      rw [hslotCouple]
                      simpa [fileAddressPostState, evmSolm, initState, storageStore_accountMap] using
                        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩
                          (setAddressOffset0Word (endSlotWord ⟨4⟩ σ_solm I)
                            (fileAddressDataKey I)) hAccounts)
                    (by
                      simpa [fileAddressTransition] using
                        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                          (dvs := []) rfl (by native_decide) (by native_decide)))
              · have hnotVowWord :
                    calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressVowBytes :=
                  fileAddressWhatWord_ne_of_bytes_ne hvow fileAddressBytes_lengths.2.2.2.1
                obtain ⟨_, _, rd8611⟩ := endFileAddressX_skip_vow hnotVowWord rd8565
                by_cases hpot : fileAddressWhat I = fileAddressPotBytes
                · have hpotWord :
                      calldataWord I.calldata 4 = ABI.bytesToWord fileAddressPotBytes :=
                    fileAddressWhatWord_eq_of_bytes_eq hpot
                  have hslotCouple :
                      endSlotWord ⟨5⟩ σ_evm I = endSlotWord ⟨5⟩ σ_solm I :=
                    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
                  have hbody :
                      ExecTransitionBody config contract evmSolm (fileAddressLocals I)
                        fileAddressTransition.body
                        (.returned { contract := contract, locals := fileAddressLocals I }
                          (fileAddressPostState evmSolm ⟨5⟩ I) none) := by
                    simpa [evmSolm] using
                      endFileAddressSourceBodyPotOk (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        hwv hauthSolm hliveSolm hvat hcat hdog hvow hpot
                  exact (endFileAddressX_pot_ok hperm hpotWord rd8611)
                    |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                      (by simp [fileAddressPostState, evmSolm, initState, storageStore_createdAccounts])
                      (by
                        rw [hslotCouple]
                        simpa [fileAddressPostState, evmSolm, initState, storageStore_accountMap] using
                          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩
                            (setAddressOffset0Word (endSlotWord ⟨5⟩ σ_solm I)
                              (fileAddressDataKey I)) hAccounts)
                      (by
                        simpa [fileAddressTransition] using
                          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                            (dvs := []) rfl (by native_decide) (by native_decide)))
                · have hnotPotWord :
                      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressPotBytes :=
                    fileAddressWhatWord_ne_of_bytes_ne hpot
                      fileAddressBytes_lengths.2.2.2.2.1
                  obtain ⟨_, _, rd8657⟩ := endFileAddressX_skip_pot hnotPotWord rd8611
                  by_cases hspot : fileAddressWhat I = fileAddressSpotBytes
                  · have hspotWord :
                        calldataWord I.calldata 4 = ABI.bytesToWord fileAddressSpotBytes :=
                      fileAddressWhatWord_eq_of_bytes_eq hspot
                    have hslotCouple :
                        endSlotWord ⟨6⟩ σ_evm I = endSlotWord ⟨6⟩ σ_solm I :=
                      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
                    have hbody :
                        ExecTransitionBody config contract evmSolm (fileAddressLocals I)
                          fileAddressTransition.body
                          (.returned { contract := contract, locals := fileAddressLocals I }
                            (fileAddressPostState evmSolm ⟨6⟩ I) none) := by
                      simpa [evmSolm] using
                        endFileAddressSourceBodySpotOk (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          hwv hauthSolm hliveSolm hvat hcat hdog hvow hpot hspot
                    exact (endFileAddressX_spot_ok hperm hspotWord rd8657)
                      |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                        (by simp [fileAddressPostState, evmSolm, initState, storageStore_createdAccounts])
                        (by
                          rw [hslotCouple]
                          simpa [fileAddressPostState, evmSolm, initState, storageStore_accountMap] using
                            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩
                              (setAddressOffset0Word (endSlotWord ⟨6⟩ σ_solm I)
                                (fileAddressDataKey I)) hAccounts)
                        (by
                          simpa [fileAddressTransition] using
                            (returnEquiv.fallthrough (o := ByteArray.empty) (r := none)
                              (t := []) (dvs := []) rfl (by native_decide) (by native_decide)))
                  · have hnotSpotWord :
                        calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressSpotBytes :=
                      fileAddressWhatWord_ne_of_bytes_ne hspot
                        fileAddressBytes_lengths.2.2.2.2.2.1
                    obtain ⟨_, _, rd8704⟩ := endFileAddressX_skip_spot hnotSpotWord rd8657
                    by_cases hcure : fileAddressWhat I = fileAddressCureBytes
                    · have hcureWord :
                          calldataWord I.calldata 4 = ABI.bytesToWord fileAddressCureBytes :=
                        fileAddressWhatWord_eq_of_bytes_eq hcure
                      have hslotCouple :
                          endSlotWord ⟨7⟩ σ_evm I = endSlotWord ⟨7⟩ σ_solm I :=
                        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
                      have hbody :
                          ExecTransitionBody config contract evmSolm (fileAddressLocals I)
                            fileAddressTransition.body
                            (.returned { contract := contract, locals := fileAddressLocals I }
                              (fileAddressPostState evmSolm ⟨7⟩ I) none) := by
                        simpa [evmSolm] using
                          endFileAddressSourceBodyCureOk (cA := cA) (gh := gh) (bl := bl)
                            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            hwv hauthSolm hliveSolm hvat hcat hdog hvow hpot hspot hcure
                      exact (endFileAddressX_cure_ok hperm hcureWord rd8704)
                        |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                          (by simp [fileAddressPostState, evmSolm, initState, storageStore_createdAccounts])
                          (by
                            rw [hslotCouple]
                            simpa [fileAddressPostState, evmSolm, initState,
                              storageStore_accountMap] using
                              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩
                                (setAddressOffset0Word (endSlotWord ⟨7⟩ σ_solm I)
                                  (fileAddressDataKey I)) hAccounts)
                          (by
                            simpa [fileAddressTransition] using
                              (returnEquiv.fallthrough (o := ByteArray.empty) (r := none)
                                (t := []) (dvs := []) rfl (by native_decide) (by native_decide)))
                    · have hnotCureWord :
                          calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressCureBytes :=
                        fileAddressWhatWord_ne_of_bytes_ne hcure
                          fileAddressBytes_lengths.2.2.2.2.2.2
                      have hbody :
                          ExecTransitionBody config contract evmSolm (fileAddressLocals I)
                            fileAddressTransition.body .reverted := by
                        simpa [evmSolm] using
                          endFileAddressSourceBodyUnrecognizedReverts
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            hwv hauthSolm hliveSolm hvat hcat hdog hvow hpot hspot hcure
                      exact (endFileAddressX_unrecognized hnotCureWord rd8704)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hliveSolm : fileAddressLiveWord σ_solm I ≠ ⟨1⟩ := by
          intro hbad
          exact hlive (by rw [hliveCouple, hbad])
        have hbody :
            ExecTransitionBody config contract evmSolm (fileAddressLocals I)
              fileAddressTransition.body .reverted := by
          simpa [evmSolm] using
            endFileAddressSourceBodyNotLiveReverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm
        exact (endFileAddressX_notLive (I := I) hlive rd8357)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
        intro hbad
        exact hauth (by rw [hauthCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (fileAddressLocals I)
            fileAddressTransition.body .reverted := by
        simpa [evmSolm] using
          endFileAddressSourceBodyAuthReverts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hauthSolm
      exact (endFileAddressX_unauthorized (I := I) hauth rd8268)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact (endFileAddressX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (endDecode_fileAddress_none_short hsz4 (by omega))

end Benchmarks.Dss.End
