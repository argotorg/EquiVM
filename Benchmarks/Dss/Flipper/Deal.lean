import Benchmarks.Dss.Flipper.ExternalCallTransport
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

theorem flipperReachDealBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 3)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨841⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
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

theorem flipperDealBodyCoreShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  exact (flipperDealX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flipperDecode_deal_none_short hsz4 hshort)

theorem flipperDealBodyCoreTicZero {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hticEvm : bidTicWord (dealId I) σ_evm I = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  let locals := dealLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hpacked :
      flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_evm I =
        flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bidPackedSlotOfWord (dealId I)) ⟨0⟩
  have hticSolm : bidTicWord (dealId I) σ_solm I = ⟨0⟩ := by
    simpa [bidTicWord, flipperUint48Offset20Word, hpacked] using hticEvm
  have hbody :
      ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperDealSourceBodyTicZero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hticSolm)
  exact (flipperDealX_ticZero hticEvm hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreNotFinished {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hticNeEvm : bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩)
    (hticGeEvm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidTicWord (dealId I) σ_evm I).toNat)
    (hendGeEvm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidEndWord (dealId I) σ_evm I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  let locals := dealLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hpacked :
      flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_evm I =
        flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bidPackedSlotOfWord (dealId I)) ⟨0⟩
  have hticEq : bidTicWord (dealId I) σ_evm I = bidTicWord (dealId I) σ_solm I := by
    simp [bidTicWord, flipperUint48Offset20Word, hpacked]
  have hendEq : bidEndWord (dealId I) σ_evm I = bidEndWord (dealId I) σ_solm I := by
    simp [bidEndWord, flipperUint48Offset26Word, hpacked]
  have hticNeSolm : bidTicWord (dealId I) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hticNeEvm (by simpa [hticEq] using hzero)
  have hticGeSolm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidTicWord (dealId I) σ_solm I).toNat := by
    simpa [← hticEq] using hticGeEvm
  have hendGeSolm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidEndWord (dealId I) σ_solm I).toNat := by
    simpa [← hendEq] using hendGeEvm
  have hbody :
      ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperDealSourceBodyNotFinished (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hticNeSolm hticGeSolm hendGeSolm)
  exact (flipperDealX_notFinished hticNeEvm hticGeEvm hendGeEvm hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreCatNoCodeEndExpired {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hticNeEvm : bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩)
    (hticGeEvm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidTicWord (dealId I) σ_evm I).toNat)
    (hendLtEvm :
      (bidEndWord (dealId I) σ_evm I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hcatZero :
      Reasoning.Theory.extCodeSizeWord σ_evm (flipperCatTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  let locals := dealLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hpacked :
      flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_evm I =
        flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bidPackedSlotOfWord (dealId I)) ⟨0⟩
  have hticEq : bidTicWord (dealId I) σ_evm I = bidTicWord (dealId I) σ_solm I := by
    simp [bidTicWord, flipperUint48Offset20Word, hpacked]
  have hendEq : bidEndWord (dealId I) σ_evm I = bidEndWord (dealId I) σ_solm I := by
    simp [bidEndWord, flipperUint48Offset26Word, hpacked]
  have hticNeSolm : bidTicWord (dealId I) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hticNeEvm (by simpa [hticEq] using hzero)
  have hticGeSolm :
      (UInt256.ofNat I.header.timestamp).toNat ≤ (bidTicWord (dealId I) σ_solm I).toNat := by
    simpa [← hticEq] using hticGeEvm
  have hendLtSolm :
      (bidEndWord (dealId I) σ_solm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat := by
    simpa [← hendEq] using hendLtEvm
  obtain ⟨_, _, rd5558⟩ :=
    flipperDealX_endExpired hticNeEvm hticGeEvm hendLtEvm hdecoded
  have hfinishedSolm :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true) :=
    evalExpr_dealFinishedGuard_true_right (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hticNeSolm hticGeSolm hendLtSolm
  have hcatZeroSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (flipperCatTargetWord σ_solm I) = ⟨0⟩ :=
    flipperCatCodeSize_zero_accountMapEquiv hAccounts hcatZero
  have hcatNoCode :=
    flipperCatCode_zero_of_codeSize_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatZeroSolm
  have hbody :
      ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperDealSourceBodyCatNoCode (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hfinishedSolm hcatNoCode)
  exact (flipperDealX_catNoCode hcatZero rd5558)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreCatNoCodeTicExpired {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hticNeEvm : bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩)
    (hticLtEvm :
      (bidTicWord (dealId I) σ_evm I).toNat < (UInt256.ofNat I.header.timestamp).toNat)
    (hcatZero :
      Reasoning.Theory.extCodeSizeWord σ_evm (flipperCatTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  let locals := dealLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hpacked :
      flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_evm I =
        flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bidPackedSlotOfWord (dealId I)) ⟨0⟩
  have hticEq : bidTicWord (dealId I) σ_evm I = bidTicWord (dealId I) σ_solm I := by
    simp [bidTicWord, flipperUint48Offset20Word, hpacked]
  have hticNeSolm : bidTicWord (dealId I) σ_solm I ≠ ⟨0⟩ := by
    intro hzero
    exact hticNeEvm (by simpa [hticEq] using hzero)
  have hticLtSolm :
      (bidTicWord (dealId I) σ_solm I).toNat <
        (UInt256.ofNat I.header.timestamp).toNat := by
    simpa [← hticEq] using hticLtEvm
  obtain ⟨_, _, rd5558⟩ :=
    flipperDealX_ticExpired_catMem hticNeEvm hticLtEvm hdecoded
  have hfinishedSolm :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true) :=
    evalExpr_dealFinishedGuard_true_left (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hticNeSolm hticLtSolm
  have hcatZeroSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (flipperCatTargetWord σ_solm I) = ⟨0⟩ :=
    flipperCatCodeSize_zero_accountMapEquiv hAccounts hcatZero
  have hcatNoCode :=
    flipperCatCode_zero_of_codeSize_zero (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatZeroSolm
  have hbody :
      ExecTransitionBody config contract evm0 locals dealTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperDealSourceBodyCatNoCode (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hfinishedSolm hcatNoCode)
  exact (flipperDealX_catNoCode hcatZero rd5558)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreCatCallDepthLimit {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfinishedEvm :
      (bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩ ∧
          (bidTicWord (dealId I) σ_evm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat) ∨
        (bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩ ∧
          (UInt256.ofNat I.header.timestamp).toNat ≤
            (bidTicWord (dealId I) σ_evm I).toNat ∧
          (bidEndWord (dealId I) σ_evm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat))
    (hcatNe :
      Reasoning.Theory.extCodeSizeWord σ_evm (flipperCatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepthEq : I.depth = 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  have hpacked :
      flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_evm I =
        flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bidPackedSlotOfWord (dealId I)) ⟨0⟩
  have hticEq : bidTicWord (dealId I) σ_evm I = bidTicWord (dealId I) σ_solm I := by
    simp [bidTicWord, flipperUint48Offset20Word, hpacked]
  have hendEq : bidEndWord (dealId I) σ_evm I = bidEndWord (dealId I) σ_solm I := by
    simp [bidEndWord, flipperUint48Offset26Word, hpacked]
  obtain ⟨_, _, rd5558⟩ :
      ∃ k' C', RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5558⟩
        [dealId I, ⟨323⟩, flipperSelWord I]
        (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k' C' := by
    rcases hfinishedEvm with ⟨hticNe, hticLt⟩ | ⟨hticNe, hticGe, hendLt⟩
    · exact flipperDealX_ticExpired_catMem hticNe hticLt hdecoded
    · exact flipperDealX_endExpired hticNe hticGe hendLt hdecoded
  have hfinishedSolm :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true) := by
    rcases hfinishedEvm with ⟨hticNeEvm, hticLtEvm⟩ | ⟨hticNeEvm, hticGeEvm, hendLtEvm⟩
    · have hticNeSolm : bidTicWord (dealId I) σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact hticNeEvm (by simpa [hticEq] using hzero)
      have hticLtSolm :
          (bidTicWord (dealId I) σ_solm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat := by
        simpa [← hticEq] using hticLtEvm
      exact evalExpr_dealFinishedGuard_true_left (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNeSolm hticLtSolm
    · have hticNeSolm : bidTicWord (dealId I) σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact hticNeEvm (by simpa [hticEq] using hzero)
      have hticGeSolm :
          (UInt256.ofNat I.header.timestamp).toNat ≤
            (bidTicWord (dealId I) σ_solm I).toNat := by
        simpa [← hticEq] using hticGeEvm
      have hendLtSolm :
          (bidEndWord (dealId I) σ_solm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat := by
        simpa [← hendEq] using hendLtEvm
      exact evalExpr_dealFinishedGuard_true_right (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNeSolm hticGeSolm hendLtSolm
  have hcatNeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (flipperCatTargetWord σ_solm I) ≠
        ⟨0⟩ :=
    flipperCatCodeSize_ne_zero_accountMapEquiv hAccounts hcatNe
  have hcatCode := flipperCatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatNeSolm
  have hcatEncode :
      config.externalABI.encode? "claw"
        (dealClawArgVals (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
          some ((dealCatCallMem σ_solm I).readWithPadding 128 36) := by
    simpa [dealClawArgVals, dealClawArgValsOf, initState, flipperSlotWord,
      solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      bidTabWord, bidSlotOfWord, bidBaseOfWord] using dealCatCallMem_encode σ_solm I
  have hcallCat :=
    Reasoning.Theory.callNotMade_depthLimit (cfg := config)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      (tgt := EVM.address (flipperCatAddress σ_solm I)) (name := "claw")
      (args := dealClawArgVals (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (calldata := (dealCatCallMem σ_solm I).readWithPadding 128 36)
      (callPerm := true) hcatEncode (by simpa [initState] using hdepthEq)
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (dealLocals I)
        dealTransition.body .reverted := by
    simpa using
      (flipperDealSourceBodyCatCallFailure (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hfinishedSolm hcatCode hcallCat)
  exact (flipperDealX_catCallDepthLimit hcatNe hdepthEq rd5558)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperDealBodyCoreCatPostCall {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfinishedEvm :
      (bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩ ∧
          (bidTicWord (dealId I) σ_evm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat) ∨
        (bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩ ∧
          (UInt256.ofNat I.header.timestamp).toNat ≤
            (bidTicWord (dealId I) σ_evm I).toNat ∧
          (bidEndWord (dealId I) σ_evm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat))
    (hcatNe :
      Reasoning.Theory.extCodeSizeWord σ_evm (flipperCatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepthNe : I.depth ≠ 1024) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dealTransition :=
    flipperDispatchDeal hsel
  have hreach := flipperReachDealBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  have hdecode := flipperDecode_deal_ok (I := I) hsz36
  obtain ⟨_, _, hdecoded⟩ := flipperDealX_decoded (g := Sat256.ofUInt256 g)
    hsz36 hsize hreach
  have hpacked :
      flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_evm I =
        flipperSlotWord (bidPackedSlotOfWord (dealId I)) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bidPackedSlotOfWord (dealId I)) ⟨0⟩
  have hticEq : bidTicWord (dealId I) σ_evm I = bidTicWord (dealId I) σ_solm I := by
    simp [bidTicWord, flipperUint48Offset20Word, hpacked]
  have hendEq : bidEndWord (dealId I) σ_evm I = bidEndWord (dealId I) σ_solm I := by
    simp [bidEndWord, flipperUint48Offset26Word, hpacked]
  obtain ⟨_, _, rd5558⟩ :
      ∃ k' C', RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5558⟩
        [dealId I, ⟨323⟩, flipperSelWord I]
        (dealHashMem2 I) (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k' C' := by
    rcases hfinishedEvm with ⟨hticNe, hticLt⟩ | ⟨hticNe, hticGe, hendLt⟩
    · exact flipperDealX_ticExpired_catMem hticNe hticLt hdecoded
    · exact flipperDealX_endExpired hticNe hticGe hendLt hdecoded
  have hfinishedSolm :
      evalExpr? config { contract := contract, locals := dealLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) dealFinishedGuard =
          .ok (.bool true) := by
    rcases hfinishedEvm with ⟨hticNeEvm, hticLtEvm⟩ | ⟨hticNeEvm, hticGeEvm, hendLtEvm⟩
    · have hticNeSolm : bidTicWord (dealId I) σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact hticNeEvm (by simpa [hticEq] using hzero)
      have hticLtSolm :
          (bidTicWord (dealId I) σ_solm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat := by
        simpa [← hticEq] using hticLtEvm
      exact evalExpr_dealFinishedGuard_true_left (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNeSolm hticLtSolm
    · have hticNeSolm : bidTicWord (dealId I) σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact hticNeEvm (by simpa [hticEq] using hzero)
      have hticGeSolm :
          (UInt256.ofNat I.header.timestamp).toNat ≤
            (bidTicWord (dealId I) σ_solm I).toNat := by
        simpa [← hticEq] using hticGeEvm
      have hendLtSolm :
          (bidEndWord (dealId I) σ_solm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat := by
        simpa [← hendEq] using hendLtEvm
      exact evalExpr_dealFinishedGuard_true_right (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        hticNeSolm hticGeSolm hendLtSolm
  have hcatNeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (flipperCatTargetWord σ_solm I) ≠
        ⟨0⟩ :=
    flipperCatCodeSize_ne_zero_accountMapEquiv hAccounts hcatNe
  have hcatCode := flipperCatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcatNeSolm
  have hdepthLt : I.depth.val < 1024 := by
    by_contra hnot
    have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
    have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
    have hval : I.depth.val = 1024 := by omega
    exact hdepthNe (Fin.ext hval)
  obtain ⟨cA_cat, σ_cat, zCat, outCat, A_cat, k5654, C5654, rd5654,
      hcallCatEvmRaw, houtCat⟩ :=
    flipperDealX_catPostCall hcatNe hperm hdepthLt rd5558
  let evm0Evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmCatEvm :=
    { evm0Evm with accountMap := σ_cat, substate := A_cat, createdAccounts := cA_cat }
  have hcallCatEvm :
      typedCallViaEVM config evm0Evm
        (EVM.address (flipperCatAddress σ_evm I)) "claw" 0
        [Value.int (Int.ofNat (bidTabWord (dealId I) σ_evm I).toNat)]
        (zCat, evmCatEvm, outCat) true := by
    simpa [evm0Evm, evmCatEvm] using hcallCatEvmRaw
  obtain ⟨σ_cat_solm, A_cat_solm, hcallCatSolmRaw, hCatStateEquiv⟩ :=
    flipper_typedCallViaEVM_accountMapEquiv_noSubstate
      (evm_solm := evm0Solm) hcallCatEvm
      (by simpa [evm0Evm, evm0Solm] using hAccounts)
      (by simp [evm0Evm, evm0Solm, initState])
      (by simp [evm0Evm, evm0Solm, initState])
      (by simp [evm0Evm, evm0Solm, initState])
      (by simp [evm0Evm, evm0Solm, initState])
      (by simp [evm0Evm, evm0Solm, initState])
  let evmCatSolm : EVM.State :=
    { evm0Solm with
      accountMap := σ_cat_solm
      substate := A_cat_solm
      createdAccounts := cA_cat }
  have hcatTargetEq :
      EVM.address (flipperCatAddress σ_evm I) =
        EVM.address (flipperCatAddress σ_solm I) := by
    rw [flipperCatAddress_accountMapEquiv hAccounts]
  have htabEq : bidTabWord (dealId I) σ_evm I = bidTabWord (dealId I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (bidSlotOfWord (dealId I) ⟨5⟩) ⟨0⟩
  have hcatArgsEqRaw :
      [Value.int (Int.ofNat (bidTabWord (dealId I) σ_evm I).toNat)] =
        [Value.int (Int.ofNat (bidTabWord (dealId I) σ_solm I).toNat)] := by
    rw [htabEq]
  have hcatArgsEq :
      [Value.int (Int.ofNat (bidTabWord (dealId I) σ_evm I).toNat)] =
        dealClawArgVals evm0Solm := by
    simpa [dealClawArgVals, dealClawArgValsOf, evm0Solm, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, bidTabWord] using hcatArgsEqRaw
  have hcallCatSolm :
      typedCallViaEVM config evm0Solm
        (EVM.address (flipperCatAddress σ_solm I)) "claw" 0
        (dealClawArgVals evm0Solm) (zCat, evmCatSolm, outCat) true := by
    have hcallCatSolmRaw' :
        typedCallViaEVM config evm0Solm
          (EVM.address (flipperCatAddress σ_solm I)) "claw" 0
          [Value.int (Int.ofNat (bidTabWord (dealId I) σ_evm I).toNat)]
          (zCat, evmCatSolm, outCat) true := by
      simpa [evmCatSolm, evmCatEvm, hcatTargetEq] using hcallCatSolmRaw
    rw [← hcatArgsEq]
    exact hcallCatSolmRaw'
  cases zCat
  · have hcallCatSolmFalse :
        typedCallViaEVM config evm0Solm
          (EVM.address (flipperCatAddress σ_solm I)) "claw" 0
          (dealClawArgVals evm0Solm) (false, evmCatSolm, outCat) true := by
      simpa using hcallCatSolm
    have hbody :
        ExecTransitionBody config contract evm0Solm (dealLocals I) dealTransition.body
          .reverted := by
      simpa [evm0Solm] using
        (flipperDealSourceBodyCatCallFailure (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hfinishedSolm hcatCode hcallCatSolmFalse)
    exact (flipperDealX_catCallFailure (by simpa using rd5654) houtCat)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have rd5654True : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5654⟩
        (⟨1⟩ :: ⟨164⟩ :: ⟨3865913243⟩ :: flipperCatTargetWord σ_evm I ::
          dealId I :: ⟨323⟩ :: flipperSelWord I :: [])
        (dealCatCallMem σ_evm I) (UInt256.ofNat 6) outCat (cA_cat, σ_cat)
        k5654 C5654 := by
      simpa using rd5654
    have hcallCatSolmTrue :
        typedCallViaEVM config evm0Solm
          (EVM.address (flipperCatAddress σ_solm I)) "claw" 0
          (dealClawArgVals evm0Solm) (true, evmCatSolm, outCat) true := by
      simpa using hcallCatSolm
    have hCatStateEquiv' : EVMStateEquiv evmCatEvm evmCatSolm := by
      simpa [evmCatSolm, evmCatEvm] using hCatStateEquiv
    have hAccountsCat : accountMapEquiv σ_cat σ_cat_solm := by
      simpa [evmCatEvm, evmCatSolm] using hCatStateEquiv'.accountMap
    obtain ⟨_, _, rd5673⟩ := flipperDealX_catCallSuccessToVatStart rd5654True
    by_cases hvatZero :
        Reasoning.Theory.extCodeSizeWord σ_cat (flipperVatTargetWord σ_cat I) = ⟨0⟩
    · have hvatZeroSolm :
          Reasoning.Theory.extCodeSizeWord σ_cat_solm
              (flipperVatTargetWord σ_cat_solm I) = ⟨0⟩ :=
        flipperVatCodeSize_zero_accountMapEquiv hAccountsCat hvatZero
      have hvatNoCode :
          (UInt256.ofNat
            ((evmCatSolm.lookupAccount
              (flipperVatAddress evmCatSolm.accountMap evmCatSolm.executionEnv)).option
              0 (fun acc => acc.code.size))).toNat = 0 := by
        simpa [evmCatSolm, evm0Solm, initState, State.lookupAccount] using
          flipper_extCodeSizeWord_zero_lookup_code_zero
            (σ := σ_cat_solm) (target := flipperVatTargetWord σ_cat_solm I)
            (addr := flipperVatAddress σ_cat_solm I)
            (flipperVatAddress_eq_target σ_cat_solm I) hvatZeroSolm
      have hbody :
          ExecTransitionBody config contract evm0Solm (dealLocals I) dealTransition.body
            .reverted := by
        simpa [evm0Solm] using
          (flipperDealSourceBodyVatNoCode (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (evmCat := evmCatSolm) (outCat := outCat)
            hwv hfinishedSolm hcatCode hcallCatSolmTrue hvatNoCode)
      exact (flipperDealX_vatNoCode hvatZero rd5673)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hvatNeSolm :
          Reasoning.Theory.extCodeSizeWord σ_cat_solm
              (flipperVatTargetWord σ_cat_solm I) ≠ ⟨0⟩ :=
        flipperVatCodeSize_ne_zero_accountMapEquiv hAccountsCat hvatZero
      have hvatCodeSolm :
          0 <
            (UInt256.ofNat
              ((evmCatSolm.lookupAccount
                (flipperVatAddress evmCatSolm.accountMap evmCatSolm.executionEnv)).option
                0 (fun acc => acc.code.size))).toNat := by
        simpa [evmCatSolm, evm0Solm, initState, State.lookupAccount] using
          flipper_extCodeSizeWord_pos_lookup_code_pos
            (σ := σ_cat_solm) (target := flipperVatTargetWord σ_cat_solm I)
            (addr := flipperVatAddress σ_cat_solm I)
            (flipperVatAddress_eq_target σ_cat_solm I) hvatNeSolm
      obtain ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k1615, C1615, rd1615,
          hcallVatEvmRaw, houtVat⟩ :=
        flipperDealX_vatPostCall hvatZero hperm hdepthLt rd5673
      let evmVatEvm : EVM.State :=
        { evmCatEvm with
          accountMap := σ_vat
          substate := A_vat
          createdAccounts := cA_vat }
      have hcallVatEvm :
          typedCallViaEVM config evmCatEvm
            (EVM.address (flipperVatAddress σ_cat I)) "flux" 0
            (dealFluxArgValsOf evmCatEvm (dealId I)) (zVat, evmVatEvm, outVat) true := by
        simpa [evmCatEvm, evmVatEvm] using hcallVatEvmRaw
      obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hVatStateEquiv⟩ :=
        flipper_typedCallViaEVM_accountMapEquiv_noSubstate
          (evm_solm := evmCatSolm) hcallVatEvm hCatStateEquiv'.accountMap
          (by simp [evmCatEvm, evmCatSolm, evm0Evm, evm0Solm, initState])
          (by simp [evmCatEvm, evmCatSolm])
          (by simp [evmCatEvm, evmCatSolm, evm0Evm, evm0Solm, initState])
          (by simp [evmCatEvm, evmCatSolm, evm0Evm, evm0Solm, initState])
          (by simpa using hCatStateEquiv'.executionEnv.symm)
      let evmVatSolm : EVM.State :=
        { evmCatSolm with
          accountMap := σ_vat_solm
          substate := A_vat_solm
          createdAccounts := cA_vat }
      have hvatTargetEq :
          EVM.address (flipperVatAddress σ_cat I) =
            EVM.address (flipperVatAddress evmCatSolm.accountMap evmCatSolm.executionEnv) := by
        have haddr : flipperVatAddress σ_cat I = flipperVatAddress σ_cat_solm I :=
          flipperVatAddress_accountMapEquiv hAccountsCat
        rw [haddr]
        simp [evmCatSolm, evm0Solm, initState]
      have hfluxArgsEq :
          dealFluxArgValsOf evmCatEvm (dealId I) =
            dealFluxArgValsOf evmCatSolm (dealId I) := by
        have hloadIlk :
            Solm.EVM.storageLoad evmCatEvm evmCatSolm.executionEnv.codeOwner ⟨3⟩ =
              Solm.EVM.storageLoad evmCatSolm evmCatSolm.executionEnv.codeOwner ⟨3⟩ :=
          storageLoad_accountMapEquiv hCatStateEquiv'.accountMap
            evmCatSolm.executionEnv.codeOwner ⟨3⟩
        have hloadGuy :
            Solm.EVM.storageLoad evmCatEvm evmCatSolm.executionEnv.codeOwner
                (bidPackedSlotOfWord (dealId I)) =
              Solm.EVM.storageLoad evmCatSolm evmCatSolm.executionEnv.codeOwner
                (bidPackedSlotOfWord (dealId I)) :=
          storageLoad_accountMapEquiv hCatStateEquiv'.accountMap
            evmCatSolm.executionEnv.codeOwner (bidPackedSlotOfWord (dealId I))
        have hloadLot :
            Solm.EVM.storageLoad evmCatEvm evmCatSolm.executionEnv.codeOwner
                (bidSlotOfWord (dealId I) ⟨1⟩) =
              Solm.EVM.storageLoad evmCatSolm evmCatSolm.executionEnv.codeOwner
                (bidSlotOfWord (dealId I) ⟨1⟩) :=
          storageLoad_accountMapEquiv hCatStateEquiv'.accountMap
            evmCatSolm.executionEnv.codeOwner (bidSlotOfWord (dealId I) ⟨1⟩)
        simp [dealFluxArgValsOf, hCatStateEquiv'.executionEnv, hloadIlk, hloadGuy,
          hloadLot]
      have hcallVatSolm :
          typedCallViaEVM config evmCatSolm
            (EVM.address (flipperVatAddress evmCatSolm.accountMap evmCatSolm.executionEnv))
            "flux" 0 (dealFluxArgValsOf evmCatSolm (dealId I))
            (zVat, evmVatSolm, outVat) true := by
        have hcallVatSolmRaw' :
            typedCallViaEVM config evmCatSolm
              (EVM.address (flipperVatAddress σ_cat I)) "flux" 0
              (dealFluxArgValsOf evmCatEvm (dealId I))
              (zVat, evmVatSolm, outVat) true := by
          simpa [evmVatSolm, evmVatEvm] using hcallVatSolmRaw
        rw [hvatTargetEq, hfluxArgsEq] at hcallVatSolmRaw'
        exact hcallVatSolmRaw'
      cases zVat
      · have rd1615False : RD flipperBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1615⟩
            (⟨0⟩ :: ⟨260⟩ :: ⟨1628552750⟩ :: flipperVatTargetWord σ_cat I ::
              dealId I :: ⟨323⟩ :: flipperSelWord I :: [])
            (dealVatFluxCallMem σ_evm σ_cat I) (UInt256.ofNat 9) outVat
            (cA_vat, σ_vat) k1615 C1615 := by
          simpa using rd1615
        have hcallVatSolmFalse :
            typedCallViaEVM config evmCatSolm
              (EVM.address (flipperVatAddress evmCatSolm.accountMap evmCatSolm.executionEnv))
              "flux" 0 (dealFluxArgValsOf evmCatSolm (dealId I))
              (false, evmVatSolm, outVat) true := by
          simpa using hcallVatSolm
        have hbody :
            ExecTransitionBody config contract evm0Solm (dealLocals I) dealTransition.body
              .reverted := by
          simpa [evm0Solm] using
            (flipperDealSourceBodyVatCallFailure (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmCat := evmCatSolm) (evmVat := evmVatSolm)
              (outCat := outCat) (outVat := outVat)
              hwv hfinishedSolm hcatCode hcallCatSolmTrue hvatCodeSolm
              hcallVatSolmFalse)
        exact (flipperDealX_vatCallFailure rd1615False houtVat)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have rd1615True : RD flipperBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1615⟩
            (⟨1⟩ :: ⟨260⟩ :: ⟨1628552750⟩ :: flipperVatTargetWord σ_cat I ::
              dealId I :: ⟨323⟩ :: flipperSelWord I :: [])
            (dealVatFluxCallMem σ_evm σ_cat I) (UInt256.ofNat 9) outVat
            (cA_vat, σ_vat) k1615 C1615 := by
          simpa using rd1615
        obtain ⟨k1633, C1633, rd1633⟩ :=
          flipperDealX_vatCallSuccessToDeleteStart rd1615True
        have hret :=
          flipperDealX_vatDeleteReturnFromPostCall
            (cA := cA) (gh := gh) (bl := bl) (σmem := σ_evm) (σcall := σ_cat)
            (σ := σ_vat) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            (cA' := cA_vat) (k := k1633) (C := C1633) (out := outVat)
            hperm rd1633
        have hcallVatSolmTrue :
            typedCallViaEVM config evmCatSolm
              (EVM.address (flipperVatAddress evmCatSolm.accountMap evmCatSolm.executionEnv))
              "flux" 0 (dealFluxArgValsOf evmCatSolm (dealId I))
              (true, evmVatSolm, outVat) true := by
          simpa using hcallVatSolm
        let locals2 : Store :=
          ((dealLocals I).insert "_clawRet" (collapseReturns [])).insert "_fluxRet"
            (collapseReturns [])
        have hbody :
            ExecTransitionBody config contract evm0Solm (dealLocals I) dealTransition.body
              (.returned { contract := contract, locals := locals2 }
                (bidDeletedEVM evmVatSolm (dealId I)) none) := by
          simpa [evm0Solm, locals2] using
            (flipperDealSourceBodySuccess (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              (evmCat := evmCatSolm) (evmVat := evmVatSolm)
              (outCat := outCat) (outVat := outVat)
              hwv hfinishedSolm hcatCode hcallCatSolmTrue hvatCodeSolm hcallVatSolmTrue)
        have hVatStateEquiv' : EVMStateEquiv evmVatEvm evmVatSolm := by
          simpa [evmVatEvm, evmVatSolm] using hVatStateEquiv
        have hVatAccounts : accountMapEquiv σ_vat σ_vat_solm := by
          simpa [evmVatEvm, evmVatSolm] using hVatStateEquiv'.accountMap
        have hcollapsed :
            accountMapEquiv (dealBidDeleteAccountMap I σ_vat (dealId I))
              (bidDeleteCollapsedAccountMap I.codeOwner σ_vat_solm (dealId I)) := by
          simpa [dealBidDeleteAccountMap] using
            (bidDeleteCollapsedAccountMap_accountMapEquiv
              (owner := I.codeOwner) (id := dealId I) hVatAccounts)
        have hdeleted :
            accountMapEquiv (bidDeleteCollapsedAccountMap I.codeOwner σ_vat_solm (dealId I))
              (bidDeletedEVM evmVatSolm (dealId I)).accountMap := by
          have h := bidDeleteCollapsedAccountMap_accountMapEquiv_bidDeletedEVM
            evmVatSolm (dealId I)
          simpa [evmVatSolm, evmCatSolm, evm0Solm, initState] using h
        have haccounts :
            accountMapEquiv (dealBidDeleteAccountMap I σ_vat (dealId I))
              (bidDeletedEVM evmVatSolm (dealId I)).accountMap :=
          accountMapEquiv.trans hcollapsed hdeleted
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          (by simp [evmVatSolm, bidDeletedEVM, storageStore_createdAccounts])
          haccounts
          (by
            rw [show dealTransition.returnType = [] by rfl]
            exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))

theorem flipperDealBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hfinished :
        (bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩ ∧
            (bidTicWord (dealId I) σ_evm I).toNat <
              (UInt256.ofNat I.header.timestamp).toNat) ∨
          (bidTicWord (dealId I) σ_evm I ≠ ⟨0⟩ ∧
            (UInt256.ofNat I.header.timestamp).toNat ≤
              (bidTicWord (dealId I) σ_evm I).toNat ∧
            (bidEndWord (dealId I) σ_evm I).toNat <
              (UInt256.ofNat I.header.timestamp).toNat) →
          Reasoning.Theory.extCodeSizeWord σ_evm
              (flipperCatTargetWord σ_evm I) ≠ ⟨0⟩ →
        runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
      intro hfinishedEvm hcatNe
      by_cases hdepthEq : I.depth = 1024
      · exact flipperDealBodyCoreCatCallDepthLimit hcode hsize hwv hsel hAccounts hsz36
          hfinishedEvm hcatNe hdepthEq
      · exact flipperDealBodyCoreCatPostCall hcode hsize hperm hwv hsel hAccounts hsz36
          hfinishedEvm hcatNe hdepthEq
    by_cases hticEvm : bidTicWord (dealId I) σ_evm I = ⟨0⟩
    · exact flipperDealBodyCoreTicZero hcode hsize hwv hsel hAccounts hsz36 hticEvm
    · by_cases hticLtEvm :
          (bidTicWord (dealId I) σ_evm I).toNat <
            (UInt256.ofNat I.header.timestamp).toNat
      · by_cases hcatZero :
            Reasoning.Theory.extCodeSizeWord σ_evm
              (flipperCatTargetWord σ_evm I) = ⟨0⟩
        · exact flipperDealBodyCoreCatNoCodeTicExpired hcode hsize hwv hsel hAccounts hsz36
            hticEvm hticLtEvm hcatZero
        · exact hfinished (Or.inl ⟨hticEvm, hticLtEvm⟩) hcatZero
      · have hticGeEvm :
            (UInt256.ofNat I.header.timestamp).toNat ≤
              (bidTicWord (dealId I) σ_evm I).toNat := by
          omega
        by_cases hendLtEvm :
            (bidEndWord (dealId I) σ_evm I).toNat <
              (UInt256.ofNat I.header.timestamp).toNat
        · by_cases hcatZero :
              Reasoning.Theory.extCodeSizeWord σ_evm
                (flipperCatTargetWord σ_evm I) = ⟨0⟩
          · exact flipperDealBodyCoreCatNoCodeEndExpired hcode hsize hwv hsel hAccounts hsz36
              hticEvm hticGeEvm hendLtEvm hcatZero
          · exact hfinished (Or.inr ⟨hticEvm, hticGeEvm, hendLtEvm⟩) hcatZero
        · have hendGeEvm :
              (UInt256.ofNat I.header.timestamp).toNat ≤
                (bidEndWord (dealId I) σ_evm I).toNat := by
            omega
          exact flipperDealBodyCoreNotFinished hcode hsize hwv hsel hAccounts hsz36
            hticEvm hticGeEvm hendGeEvm
  · have hshort : I.calldata.size < 36 := by
      omega
    exact flipperDealBodyCoreShort hcode hsize hwv hsel hshort

end Benchmarks.Dss.Flipper
