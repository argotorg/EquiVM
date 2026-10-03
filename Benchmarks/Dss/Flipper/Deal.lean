import Reasoning.ExternalCall
import Benchmarks.Dss.Flipper.DealTicEVM
import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## `deal(uint256)` -/

theorem flipperDecode_deal_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
      (transitionSignature dealTransition).paramTypes I.calldata =
        some (dealLocals I) := by
  simpa [config, dealTransition, transitionSignature, dealLocals, dealId]
    using (flipperDecodeCalldataLegacyUInt256_ok (cd := I.calldata) (x := "id") hsz36)

theorem flipperDecode_deal_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (dealTransition.params.map Param.name)
      (transitionSignature dealTransition).paramTypes I.calldata = none := by
  simpa [config, dealTransition, transitionSignature]
    using (flipperDecodeCalldataLegacyUInt256_none_short (cd := I.calldata)
      (x := "id") hsz4 hshort)

theorem flipperReachDealBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 3)) :
    ∃ k C, RD flipperBytecode I g (initState σ σ₀ g A I)
        ⟨841⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : flipperSelWord I = ⟨0xc959c42b⟩ :=
    flipperSelWord_eq_of_beq I hsz 0xc9 0x59 0xc4 0x2b ⟨0xc959c42b⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc 4))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachLowLowBody 4 (by omega) ⟨841⟩ hcode hwv hsz hsize hroot hlow
    heq0 htake (by jump_dest) (by native_decide)

theorem flipperDealBodyCoreShort {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact (flipperDealX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flipperDecode_deal_none_short hsz4 hshort)

theorem flipperDealBodyCoreTicZero {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hsz36 : 36 ≤ I.calldata.size)
    (hticEvm : bidTicWord (dealId I) σ I = ⟨0⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  let locals := dealLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperDealSourceBodyTicZero
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hticEvm)
  exact (flipperDealX_ticZero hticEvm hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreNotFinished {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hsz36 : 36 ≤ I.calldata.size)
    (hticNeEvm : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticGeEvm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidTicWord (dealId I) σ I).toNat)
    (hendGeEvm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidEndWord (dealId I) σ I).toNat) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  let locals := dealLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperDealSourceBodyNotFinished
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hticNeEvm hticGeEvm hendGeEvm)
  exact (flipperDealX_notFinished hticNeEvm hticGeEvm hendGeEvm hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreCatNoCodeEndExpired {σ σ₀ A I}
    {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hsz36 : 36 ≤ I.calldata.size)
    (hticNeEvm : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticGeEvm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidTicWord (dealId I) σ I).toNat)
    (hendLtEvm :
      (bidEndWord (dealId I) σ I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hcatZero :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  let locals := dealLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨_, _, rd5558⟩ :=
    flipperDealX_endExpired hticNeEvm hticGeEvm hendLtEvm hdecoded
  have hfinishedSolm :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true) :=
    evalExpr_dealFinishedGuard_true_right
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hticNeEvm hticGeEvm hendLtEvm
  have hcatNoCode :=
    flipperCatCode_zero_of_codeSize_zero
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatZero
  have hbody :
      ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperDealSourceBodyCatNoCode
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hfinishedSolm hcatNoCode)
  exact (flipperDealX_catNoCode hcatZero rd5558)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreCatNoCodeTicExpired {σ σ₀ A I}
    {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hsz36 : 36 ≤ I.calldata.size)
    (hticNeEvm : bidTicWord (dealId I) σ I ≠ ⟨0⟩)
    (hticLtEvm :
      (bidTicWord (dealId I) σ I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hcatZero :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  let locals := dealLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨_, _, rd5558⟩ :=
    flipperDealX_ticExpired_catMem hticNeEvm hticLtEvm hdecoded
  have hfinishedSolm :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true) :=
    evalExpr_dealFinishedGuard_true_left
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hticNeEvm hticLtEvm
  have hcatNoCode :=
    flipperCatCode_zero_of_codeSize_zero
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatZero
  have hbody :
      ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperDealSourceBodyCatNoCode
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hfinishedSolm hcatNoCode)
  exact (flipperDealX_catNoCode hcatZero rd5558)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreCatCallDepthLimit {σ σ₀ A I}
    {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hsz36 : 36 ≤ I.calldata.size)
    (hfinishedEvm :
      (bidTicWord (dealId I) σ I ≠ ⟨0⟩ ∧
          (bidTicWord (dealId I) σ I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat) ∨
        (bidTicWord (dealId I) σ I ≠ ⟨0⟩ ∧
          (UInt256.ofNat I.header.timestamp).toNat ≤
            (bidTicWord (dealId I) σ I).toNat ∧
          (bidEndWord (dealId I) σ I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat))
    (hcatNe :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩)
    (hdepthEq : I.depth = 1024) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  obtain ⟨_, _, rd5558⟩ :
      ∃ k' C', RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5558⟩
        [dealId I, ⟨323⟩, flipperSelWord I]
        (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
    rcases hfinishedEvm with ⟨hticNe, hticLt⟩ | ⟨hticNe, hticGe, hendLt⟩
    · exact flipperDealX_ticExpired_catMem hticNe hticLt hdecoded
    · exact flipperDealX_endExpired hticNe hticGe hendLt hdecoded
  have hfinishedSolm :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true) := by
    rcases hfinishedEvm with ⟨hticNeEvm, hticLtEvm⟩ | ⟨hticNeEvm, hticGeEvm, hendLtEvm⟩
    · exact evalExpr_dealFinishedGuard_true_left
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNeEvm hticLtEvm
    · exact evalExpr_dealFinishedGuard_true_right
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNeEvm hticGeEvm hendLtEvm
  have hcatCode := flipperCatCode_pos_of_codeSize_ne_zero
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatNe
  have hcatEncode :
      config.externalABI.encode? "claw"
        (dealClawArgVals (initState σ σ₀ (Sat256.ofUInt256 g) A I)) =
          some ((dealCatCallMem σ I).readWithPadding 128 36) := by
    simpa [dealClawArgVals, dealClawArgValsOf, initState, flipperSlotWord,
      solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      bidTabWord, bidSlotOfWord, bidBaseOfWord] using dealCatCallMem_encode σ I
  have hcallCat :=
    Reasoning.Theory.callNotMade_depthLimit (cfg := config)
      (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (tgt := EVM.address (flipperCatAddress σ I)) (name := "claw")
      (args := dealClawArgVals (initState σ σ₀ (Sat256.ofUInt256 g) A I))
      (calldata := (dealCatCallMem σ I).readWithPadding 128 36)
      (callPerm := true) hcatEncode (by simpa [initState] using hdepthEq)
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (dealLocals I)
        dealTransition.body .reverted := by
    simpa using
      (flipperDealSourceBodyCatCallFailure
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hfinishedSolm hcatCode hcallCat)
  exact (flipperDealX_catCallDepthLimit hcatNe hdepthEq rd5558)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreCatPostCall {σ σ₀ A I}
    {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hsz36 : 36 ≤ I.calldata.size)
    (hfinishedEvm :
      (bidTicWord (dealId I) σ I ≠ ⟨0⟩ ∧
          (bidTicWord (dealId I) σ I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat) ∨
        (bidTicWord (dealId I) σ I ≠ ⟨0⟩ ∧
          (UInt256.ofNat I.header.timestamp).toNat ≤
            (bidTicWord (dealId I) σ I).toNat ∧
          (bidEndWord (dealId I) σ I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat))
    (hcatNe :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩)
    (hdepthNe : I.depth ≠ 1024) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  obtain ⟨_, _, rd5558⟩ :
      ∃ k' C', RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5558⟩
        [dealId I, ⟨323⟩, flipperSelWord I]
        (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
    rcases hfinishedEvm with ⟨hticNe, hticLt⟩ | ⟨hticNe, hticGe, hendLt⟩
    · exact flipperDealX_ticExpired_catMem hticNe hticLt hdecoded
    · exact flipperDealX_endExpired hticNe hticGe hendLt hdecoded
  have hfinishedSolm :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true) := by
    rcases hfinishedEvm with ⟨hticNeEvm, hticLtEvm⟩ | ⟨hticNeEvm, hticGeEvm, hendLtEvm⟩
    · exact evalExpr_dealFinishedGuard_true_left
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNeEvm hticLtEvm
    · exact evalExpr_dealFinishedGuard_true_right
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNeEvm hticGeEvm hendLtEvm
  have hcatCode := flipperCatCode_pos_of_codeSize_ne_zero
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatNe
  have hdepthLt : I.depth.val < 1024 := by
    by_contra hnot
    have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
    have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
    have hval : I.depth.val = 1024 := by omega
    exact hdepthNe (Fin.ext hval)
  obtain ⟨σ_cat, zCat, outCat, A_cat, k5654, C5654, rd5654,
      hcallCatRaw, houtCat⟩ :=
    flipperDealX_catPostCall hcatNe hperm hdepthLt rd5558
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmCat : EVM.State := { evm0 with accountMap := σ_cat, substate := A_cat }
  have hcatArgsEq :
      [Value.int (Int.ofNat (bidTabWord (dealId I) σ I).toNat)] =
        dealClawArgVals evm0 := by
    simpa [dealClawArgVals, dealClawArgValsOf, evm0, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      bidTabWord, flipperSlotWord, solcSlotWord] using
      (rfl : [Value.int (Int.ofNat (bidTabWord (dealId I) σ I).toNat)] =
        [Value.int (Int.ofNat (bidTabWord (dealId I) σ I).toNat)])
  have hcallCat :
      typedCallViaEVM config evm0
        (EVM.address (flipperCatAddress σ I)) "claw" 0
        (dealClawArgVals evm0) (zCat, evmCat, outCat) true := by
    rw [← hcatArgsEq]
    simpa [evm0, evmCat] using hcallCatRaw
  cases zCat
  · have hcallCatFalse :
        typedCallViaEVM config evm0
          (EVM.address (flipperCatAddress σ I)) "claw" 0
          (dealClawArgVals evm0) (false, evmCat, outCat) true := by
      simpa using hcallCat
    have hbody :
        ExecTransitionBody config contract evm0 (dealLocals I) dealTransition.body
          .reverted := by
      simpa [evm0] using
        (flipperDealSourceBodyCatCallFailure
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hfinishedSolm hcatCode hcallCatFalse)
    exact (flipperDealX_catCallFailure (by simpa using rd5654) houtCat)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have rd5654True : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5654⟩
        (⟨1⟩ :: ⟨164⟩ :: ⟨3865913243⟩ :: flipperCatTargetWord σ I ::
          dealId I :: ⟨323⟩ :: flipperSelWord I :: [])
        (dealCatCallMem σ I) (UInt256.ofNat 6) outCat σ_cat
        k5654 C5654 := by
      simpa using rd5654
    have hcallCatTrue :
        typedCallViaEVM config evm0
          (EVM.address (flipperCatAddress σ I)) "claw" 0
          (dealClawArgVals evm0) (true, evmCat, outCat) true := by
      simpa using hcallCat
    obtain ⟨_, _, rd5673⟩ := flipperDealX_catCallSuccessToVatStart rd5654True
    by_cases hvatZero :
        Reasoning.Theory.extCodeSizeWord σ_cat (flipperVatTargetWord σ_cat I) = ⟨0⟩
    · have hvatNoCode :
          (UInt256.ofNat
            ((evmCat.lookupAccount
              (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
              0 (fun acc => acc.code.size))).toNat = 0 := by
        simpa [evmCat, evm0, initState, State.lookupAccount] using
          flipper_extCodeSizeWord_zero_lookup_code_zero
            (σ := σ_cat) (target := flipperVatTargetWord σ_cat I)
            (addr := flipperVatAddress σ_cat I)
            (flipperVatAddress_eq_target σ_cat I) hvatZero
      have hbody :
          ExecTransitionBody config contract evm0 (dealLocals I) dealTransition.body
            .reverted := by
        simpa [evm0] using
          (flipperDealSourceBodyVatNoCode
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmCat := evmCat) (outCat := outCat)
            hwv hfinishedSolm hcatCode hcallCatTrue hvatNoCode)
      exact (flipperDealX_vatNoCode hvatZero rd5673)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hvatCodeSolm :
          0 <
            (UInt256.ofNat
              ((evmCat.lookupAccount
                (flipperVatAddress evmCat.accountMap evmCat.executionEnv)).option
                0 (fun acc => acc.code.size))).toNat := by
        simpa [evmCat, evm0, initState, State.lookupAccount] using
          flipper_extCodeSizeWord_pos_lookup_code_pos
            (σ := σ_cat) (target := flipperVatTargetWord σ_cat I)
            (addr := flipperVatAddress σ_cat I)
            (flipperVatAddress_eq_target σ_cat I) hvatZero
      obtain ⟨σ_vat, zVat, outVat, A_vat, k1615, C1615, rd1615,
          hcallVatRaw, houtVat⟩ :=
        flipperDealX_vatPostCall hvatZero hperm hdepthLt rd5673
      let evmVat : EVM.State :=
        { evmCat with accountMap := σ_vat, substate := A_vat }
      have hcallVat :
          typedCallViaEVM config evmCat
            (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv))
            "flux" 0 (dealFluxArgValsOf evmCat (dealId I))
            (zVat, evmVat, outVat) true := by
        simpa [evmCat, evm0, evmVat, initState] using hcallVatRaw
      cases zVat
      · have rd1615False : RD flipperBytecode I (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1615⟩
            (⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ :: flipperVatTargetWord σ_cat I ::
              dealId I :: ⟨323⟩ :: flipperSelWord I :: [])
            (dealVatFluxCallMem σ σ_cat I) (UInt256.ofNat 9) outVat
            σ_vat k1615 C1615 := by
          simpa using rd1615
        have hcallVatFalse :
            typedCallViaEVM config evmCat
              (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv))
              "flux" 0 (dealFluxArgValsOf evmCat (dealId I))
              (false, evmVat, outVat) true := by
          simpa using hcallVat
        have hbody :
            ExecTransitionBody config contract evm0 (dealLocals I) dealTransition.body
              .reverted := by
          simpa [evm0] using
            (flipperDealSourceBodyVatCallFailure
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmCat := evmCat) (evmVat := evmVat)
              (outCat := outCat) (outVat := outVat)
              hwv hfinishedSolm hcatCode hcallCatTrue hvatCodeSolm
              hcallVatFalse)
        exact (flipperDealX_vatCallFailure rd1615False houtVat)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have rd1615True : RD flipperBytecode I (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1615⟩
            (⟨1⟩ :: ⟨260⟩ :: ⟨1628552750⟩ :: flipperVatTargetWord σ_cat I ::
              dealId I :: ⟨323⟩ :: flipperSelWord I :: [])
            (dealVatFluxCallMem σ σ_cat I) (UInt256.ofNat 9) outVat
            σ_vat k1615 C1615 := by
          simpa using rd1615
        obtain ⟨k1633, C1633, rd1633⟩ :=
          flipperDealX_vatCallSuccessToDeleteStart rd1615True
        have hret :=
          flipperDealX_vatDeleteReturnFromPostCall
            (σmem := σ) (σcall := σ_cat)
            (σ := σ_vat) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (k := k1633) (C := C1633) (out := outVat)
            hperm rd1633
        have hcallVatTrue :
            typedCallViaEVM config evmCat
              (EVM.address (flipperVatAddress evmCat.accountMap evmCat.executionEnv))
              "flux" 0 (dealFluxArgValsOf evmCat (dealId I))
              (true, evmVat, outVat) true := by
          simpa using hcallVat
        let locals2 : Store :=
          ((dealLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
            (collapseReturns [])
        have hbody :
            ExecTransitionBody config contract evm0 (dealLocals I) dealTransition.body
              (.returned { contract := contract, locals := locals2 }
                (bidDeletedEVM evmVat (dealId I)) none) := by
          simpa [evm0, locals2] using
            (flipperDealSourceBodySuccess
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmCat := evmCat) (evmVat := evmVat)
              (outCat := outCat) (outVat := outVat)
              hwv hfinishedSolm hcatCode hcallCatTrue hvatCodeSolm hcallVatTrue)
        have haccounts :
            dealBidDeleteAccountMap I σ_vat (dealId I) =
              (bidDeletedEVM evmVat (dealId I)).accountMap := by
          simpa [dealBidDeleteAccountMap, evmVat, evmCat, evm0, initState] using
            (bidDeleteCollapsedAccountMap_eq_bidDeletedEVM evmVat (dealId I))
        exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
          haccounts
          (by
            rw [show dealTransition.returnType = [] by rfl]
            exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))

theorem flipperDealBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hfinished :
        (bidTicWord (dealId I) σ I ≠ ⟨0⟩ ∧
            (bidTicWord (dealId I) σ I).toNat <
              (UInt256.ofNat I.header.timestamp).toNat) ∨
          (bidTicWord (dealId I) σ I ≠ ⟨0⟩ ∧
            (UInt256.ofNat I.header.timestamp).toNat ≤
              (bidTicWord (dealId I) σ I).toNat ∧
            (bidEndWord (dealId I) σ I).toNat <
              (UInt256.ofNat I.header.timestamp).toNat) →
          Reasoning.Theory.extCodeSizeWord σ
              (flipperCatTargetWord σ I) ≠ ⟨0⟩ →
        runtimeEquivalenceFor config contract σ σ₀ g A I := by
      intro hfinishedEvm hcatNe
      by_cases hdepthEq : I.depth = 1024
      · exact flipperDealBodyCoreCatCallDepthLimit hcode hsize hwv hsel hsz36
          hfinishedEvm hcatNe hdepthEq
      · exact flipperDealBodyCoreCatPostCall hcode hsize hperm hwv hsel hsz36
          hfinishedEvm hcatNe hdepthEq
    by_cases hticEvm : bidTicWord (dealId I) σ I = ⟨0⟩
    · exact flipperDealBodyCoreTicZero hcode hsize hwv hsel hsz36 hticEvm
    · by_cases hticLtEvm :
          (bidTicWord (dealId I) σ I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat
      · by_cases hcatZero :
            Reasoning.Theory.extCodeSizeWord σ
              (flipperCatTargetWord σ I) = ⟨0⟩
        · exact flipperDealBodyCoreCatNoCodeTicExpired hcode hsize hwv hsel hsz36
            hticEvm hticLtEvm hcatZero
        · exact hfinished (Or.inl ⟨hticEvm, hticLtEvm⟩) hcatZero
      · have hticGeEvm :
            (UInt256.ofNat I.header.timestamp).toNat ≤
              (bidTicWord (dealId I) σ I).toNat := by
          omega
        by_cases hendLtEvm :
            (bidEndWord (dealId I) σ I).toNat <
              (UInt256.ofNat I.header.timestamp).toNat
        · by_cases hcatZero :
              Reasoning.Theory.extCodeSizeWord σ
                (flipperCatTargetWord σ I) = ⟨0⟩
          · exact flipperDealBodyCoreCatNoCodeEndExpired hcode hsize hwv hsel hsz36
              hticEvm hticGeEvm hendLtEvm hcatZero
          · exact hfinished (Or.inr ⟨hticEvm, hticGeEvm, hendLtEvm⟩) hcatZero
        · have hendGeEvm :
              (UInt256.ofNat I.header.timestamp).toNat ≤
                (bidEndWord (dealId I) σ I).toNat := by
            omega
          exact flipperDealBodyCoreNotFinished hcode hsize hwv hsel hsz36
            hticEvm hticGeEvm hendGeEvm
  · have hshort : I.calldata.size < 36 := by
      omega
    exact flipperDealBodyCoreShort hcode hsize hwv hsel hshort

end Benchmarks.Dss.Flipper
