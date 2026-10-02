import Examples.UniswapV2Pair.DispatchSelectors

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Low selector branch reach -/

/-- Standard solc prologue/guards/selector load, stopping at the root selector split. -/
theorem uniswapReachRootSplit {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapRootSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  simpa [uniswapRootSplitPc, uniswapSelWord] using
    solcLegacyDispatchReachSelector (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := uniswapV2PairBytecode)
      (bodyPc := (⟨18⟩ : UInt256)) (loadPc := (⟨26⟩ : UInt256))
      (firstPc := uniswapRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := (⟨425⟩ : UInt256)) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem uniswapX_callvalue_ne {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem uniswapX_short {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  obtain ⟨_, _, h18⟩ := solcGuardCallvalueZero
    (ctgt := (⟨16⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest)
  have h425 := h18.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 ⟨425⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h425 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-- Reach the low-half split from the root split. -/
theorem uniswapReachLowSplit {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k32, C32, h32⟩ :=
    uniswapReachRootSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h249 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapRootSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 uniswapRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h250 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [uniswapLowSplitPc, uniswapRootSplitPc, armTgt, pushAt] using
      h249.jumpdest (by decide) (by simp)
  exact ⟨_, _, h250⟩

/-- Reach the high-half split from the root split. -/
theorem uniswapReachHighSplit {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapHighSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k32, C32, h32⟩ :=
    uniswapReachRootSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapHighSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k32 + 5) (C32 + 22) := by
    simpa [uniswapHighSplitPc, uniswapRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 uniswapRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

/-- Reach the first arm in Uniswap's lowest selector group. -/
theorem uniswapReachLowestFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h358 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapLowSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k250 + 5)
        (C250 + 22) :=
    RD.selectorSplitTakenAuto h250 uniswapLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h359 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k250 + 5 + 1) (C250 + 22 + 1) := by
    simpa [uniswapLowestFirstArmPc, uniswapLowestJumpdestPc, uniswapLowSplitPc, armTgt, pushAt]
      using h358.jumpdest (by decide) (by simp)
  exact ⟨_, _, h359⟩

/-- Reach the first arm in Uniswap's middle-low selector group. -/
theorem uniswapReachMidLowFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapMidLowFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h261 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapMidLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k250 + 5) (C250 + 22) := by
    simpa [uniswapMidLowSplitPc, uniswapLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h250 uniswapLowSplitWellFormed hlow (by simp)
  have h320 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapMidLowSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k250 + 5 + 5)
        (C250 + 22 + 22) :=
    RD.selectorSplitTakenAuto h261 uniswapMidLowSplitWellFormed hmidLow (by jump_dest) (by simp)
  have h321 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapMidLowFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k250 + 5 + 5 + 1) (C250 + 22 + 22 + 1) := by
    simpa [uniswapMidLowFirstArmPc, uniswapMidLowJumpdestPc, uniswapMidLowSplitPc, armTgt, pushAt]
      using h320.jumpdest (by decide) (by simp)
  exact ⟨_, _, h321⟩

/-- Reach the first arm in Uniswap's low-upper selector group. -/
theorem uniswapReachLowUpperFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapLowUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h261 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapMidLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k250 + 5) (C250 + 22) := by
    simpa [uniswapMidLowSplitPc, uniswapLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h250 uniswapLowSplitWellFormed hlow (by simp)
  have h272 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapLowUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k250 + 5 + 5) (C250 + 22 + 22) := by
    simpa [uniswapLowUpperFirstArmPc, uniswapMidLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h261 uniswapMidLowSplitWellFormed hmidLow (by simp)
  exact ⟨_, _, h272⟩

/-- Reach the first arm in Uniswap's high-upper selector group. -/
theorem uniswapReachHighUpperFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhighMid :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighMidSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapHighUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapHighMidSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k43 + 5) (C43 + 22) := by
    simpa [uniswapHighMidSplitPc, uniswapHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 uniswapHighSplitWellFormed hhigh (by simp)
  have h65 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapHighUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k43 + 5 + 5) (C43 + 22 + 22) := by
    simpa [uniswapHighUpperFirstArmPc, uniswapHighMidSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h54 uniswapHighMidSplitWellFormed hhighMid (by simp)
  exact ⟨_, _, h65⟩

/-- Reach the first arm in Uniswap's high-middle selector group. -/
theorem uniswapReachHighMiddleFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhighMid :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighMidSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapHighMiddleFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapHighMidSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k43 + 5) (C43 + 22) := by
    simpa [uniswapHighMidSplitPc, uniswapHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 uniswapHighSplitWellFormed hhigh (by simp)
  have h113 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighMidSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k43 + 5 + 5)
        (C43 + 22 + 22) :=
    RD.selectorSplitTakenAuto h54 uniswapHighMidSplitWellFormed hhighMid (by jump_dest) (by simp)
  have h114 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapHighMiddleFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k43 + 5 + 5 + 1) (C43 + 22 + 22 + 1) := by
    simpa [uniswapHighMiddleFirstArmPc, uniswapHighMiddleJumpdestPc, uniswapHighMidSplitPc,
      armTgt, pushAt] using h113.jumpdest (by decide) (by simp)
  exact ⟨_, _, h114⟩

/-- Reach the high-lower split in Uniswap's high selector branch. -/
theorem uniswapReachHighLowerSplit {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapHighLowerSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h151 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k43 + 5) (C43 + 22) :=
    RD.selectorSplitTakenAuto h43 uniswapHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h152 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapHighLowerSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [uniswapHighLowerSplitPc, uniswapHighLowerJumpdestPc, uniswapHighSplitPc, armTgt,
      pushAt] using h151.jumpdest (by decide) (by simp)
  exact ⟨_, _, h152⟩

/-- Reach the first arm in Uniswap's high-lower selector group. -/
theorem uniswapReachHighLowerFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩)
    (hlower :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighLowerSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapHighLowerFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k152, C152, h152⟩ :=
    uniswapReachHighLowerSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have h163 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapHighLowerFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k152 + 5) (C152 + 22) := by
    simpa [uniswapHighLowerFirstArmPc, uniswapHighLowerSplitPc, selArmNextPc,
      armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h152 uniswapHighLowerSplitWellFormed hlower (by simp)
  exact ⟨_, _, h163⟩

/-- Reach the first arm in Uniswap's high-lowest selector group. -/
theorem uniswapReachHighLowestFirstArm {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩)
    (hlower :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighLowerSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
        uniswapHighLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  obtain ⟨k152, C152, h152⟩ :=
    uniswapReachHighLowerSplit (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have h211 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighLowerSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ (k152 + 5) (C152 + 22) :=
    RD.selectorSplitTakenAuto h152 uniswapHighLowerSplitWellFormed hlower (by jump_dest) (by simp)
  have h212 : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I)
      uniswapHighLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty σ (k152 + 5 + 1) (C152 + 22 + 1) := by
    simpa [uniswapHighLowestFirstArmPc, uniswapHighLowestJumpdestPc, uniswapHighLowerSplitPc,
      armTgt, pushAt] using h211.jumpdest (by decide) (by simp)
  exact ⟨_, _, h212⟩

theorem uniswapJumpToNoMatchRevert {σ σ₀ A I} {g : Sat256}
    {pc : UInt256} {k C : ℕ}
    (h : RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) pc
      [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hpush : decode uniswapV2PairBytecode pc = some (.Push .PUSH2, some (⟨425⟩, 2)))
    (hjump : decode uniswapV2PairBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  have h425 := h.push2 ⟨425⟩ hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h425 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem uniswapX_noMatch {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 27 → (uniswapSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev uniswapV2PairBytecode g (initState σ σ₀ g A I) := by
  have hselectorNoMatch (i : ℕ) (hi : i < 27) (c0 c1 c2 c3 : UInt8) (sel : UInt256)
      (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
      (hbytes : uniswapSelBytes i = (⟨#[c0, c1, c2, c3]⟩ : ByteArray)) :
      UInt256.eq sel (uniswapSelWord I) = ⟨0⟩ := by
    dsimp [uniswapSelWord]
    rw [evmSelectorDecode hsz c0 c1 c2 c3 sel hsel]
    have hno := hnm i hi
    rw [hbytes] at hno
    simp [hno]
  have heqLowest : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 0 (by omega) 0x02 0x2c 0x0d 0x9f _ (by native_decide) rfl
    · exact hselectorNoMatch 1 (by omega) 0x06 0xfd 0xde 0x03 _ (by native_decide) rfl
    · exact hselectorNoMatch 2 (by omega) 0x09 0x02 0xf1 0xac _ (by native_decide) rfl
    · exact hselectorNoMatch 3 (by omega) 0x09 0x5e 0xa7 0xb3 _ (by native_decide) rfl
    · exact hselectorNoMatch 4 (by omega) 0x0d 0xfe 0x16 0x81 _ (by native_decide) rfl
    · exact hselectorNoMatch 5 (by omega) 0x18 0x16 0x0d 0xdd _ (by native_decide) rfl
  have heqMidLow : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 6 (by omega) 0x23 0xb8 0x72 0xdd _ (by native_decide) rfl
    · exact hselectorNoMatch 7 (by omega) 0x30 0xad 0xf8 0x1f _ (by native_decide) rfl
    · exact hselectorNoMatch 8 (by omega) 0x31 0x3c 0xe5 0x67 _ (by native_decide) rfl
  have heqLowUpper : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 9 (by omega) 0x36 0x44 0xe5 0x15 _ (by native_decide) rfl
    · exact hselectorNoMatch 10 (by omega) 0x48 0x5c 0xc9 0x55 _ (by native_decide) rfl
    · exact hselectorNoMatch 11 (by omega) 0x59 0x09 0xc0 0xd5 _ (by native_decide) rfl
    · exact hselectorNoMatch 12 (by omega) 0x5a 0x3d 0x54 0x93 _ (by native_decide) rfl
  have heqHighUpper : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 23 (by omega) 0xd2 0x12 0x20 0xa7 _ (by native_decide) rfl
    · exact hselectorNoMatch 24 (by omega) 0xd5 0x05 0xac 0xcf _ (by native_decide) rfl
    · exact hselectorNoMatch 25 (by omega) 0xdd 0x62 0xed 0x3e _ (by native_decide) rfl
    · exact hselectorNoMatch 26 (by omega) 0xff 0xf6 0xca 0xe9 _ (by native_decide) rfl
  have heqHighMiddle : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 20 (by omega) 0xba 0x9a 0x7a 0x56 _ (by native_decide) rfl
    · exact hselectorNoMatch 21 (by omega) 0xbc 0x25 0xcf 0x77 _ (by native_decide) rfl
    · exact hselectorNoMatch 22 (by omega) 0xc4 0x5a 0x01 0x55 _ (by native_decide) rfl
  have heqHighLower : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 16 (by omega) 0x7e 0xce 0xbe 0x00 _ (by native_decide) rfl
    · exact hselectorNoMatch 17 (by omega) 0x89 0xaf 0xcb 0x44 _ (by native_decide) rfl
    · exact hselectorNoMatch 18 (by omega) 0x95 0xd8 0x9b 0x41 _ (by native_decide) rfl
    · exact hselectorNoMatch 19 (by omega) 0xa9 0x05 0x9c 0xbb _ (by native_decide) rfl
  have heqHighLowest : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 13 (by omega) 0x6a 0x62 0x78 0x42 _ (by native_decide) rfl
    · exact hselectorNoMatch 14 (by omega) 0x70 0xa0 0x82 0x31 _ (by native_decide) rfl
    · exact hselectorNoMatch 15 (by omega) 0x74 0x64 0xfc 0x3d _ (by native_decide) rfl
  by_cases hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩
  · by_cases hhigh :
        UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) =
          ⟨0⟩
    · by_cases hhighMid :
          UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighMidSplitPc) (uniswapSelWord I) =
            ⟨0⟩
      · obtain ⟨_, _, h65⟩ := uniswapReachHighUpperFirstArm
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hhigh hhighMid
        have h109 := h65
          |>.selectorArmNotTakenAuto (uniswapHighUpperArmsWellFormed 0 (by omega))
              (heqHighUpper 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighUpperArmsWellFormed 1 (by omega))
              (heqHighUpper 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighUpperArmsWellFormed 2 (by omega))
              (heqHighUpper 2 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighUpperArmsWellFormed 3 (by omega))
              (heqHighUpper 3 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h109 (by native_decide) (by native_decide)
      · obtain ⟨_, _, h114⟩ := uniswapReachHighMiddleFirstArm
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hhigh hhighMid
        have h147 := h114
          |>.selectorArmNotTakenAuto (uniswapHighMiddleArmsWellFormed 0 (by omega))
              (heqHighMiddle 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighMiddleArmsWellFormed 1 (by omega))
              (heqHighMiddle 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighMiddleArmsWellFormed 2 (by omega))
              (heqHighMiddle 2 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h147 (by native_decide) (by native_decide)
    · by_cases hlower :
        UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighLowerSplitPc) (uniswapSelWord I) =
          ⟨0⟩
      · obtain ⟨_, _, h163⟩ := uniswapReachHighLowerFirstArm
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hhigh hlower
        have h207 := h163
          |>.selectorArmNotTakenAuto (uniswapHighLowerArmsWellFormed 0 (by omega))
              (heqHighLower 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowerArmsWellFormed 1 (by omega))
              (heqHighLower 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowerArmsWellFormed 2 (by omega))
              (heqHighLower 2 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowerArmsWellFormed 3 (by omega))
              (heqHighLower 3 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h207 (by native_decide) (by native_decide)
      · obtain ⟨_, _, h212⟩ := uniswapReachHighLowestFirstArm
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hhigh hlower
        have h245 := h212
          |>.selectorArmNotTakenAuto (uniswapHighLowestArmsWellFormed 0 (by omega))
              (heqHighLowest 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowestArmsWellFormed 1 (by omega))
              (heqHighLowest 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapHighLowestArmsWellFormed 2 (by omega))
              (heqHighLowest 2 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h245 (by native_decide) (by native_decide)
  · by_cases hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) =
        ⟨0⟩
    · by_cases hmidLow :
        UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) =
          ⟨0⟩
      · obtain ⟨_, _, h272⟩ := uniswapReachLowUpperFirstArm
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hlow hmidLow
        have h316 := h272
          |>.selectorArmNotTakenAuto (uniswapLowUpperArmsWellFormed 0 (by omega))
              (heqLowUpper 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapLowUpperArmsWellFormed 1 (by omega))
              (heqLowUpper 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapLowUpperArmsWellFormed 2 (by omega))
              (heqLowUpper 2 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapLowUpperArmsWellFormed 3 (by omega))
              (heqLowUpper 3 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h316 (by native_decide) (by native_decide)
      · obtain ⟨_, _, h321⟩ := uniswapReachMidLowFirstArm
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hroot hlow hmidLow
        have h354 := h321
          |>.selectorArmNotTakenAuto (uniswapMidLowArmsWellFormed 0 (by omega))
              (heqMidLow 0 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapMidLowArmsWellFormed 1 (by omega))
              (heqMidLow 1 (by omega)) (by simp)
          |>.selectorArmNotTakenAuto (uniswapMidLowArmsWellFormed 2 (by omega))
              (heqMidLow 2 (by omega)) (by simp)
        exact uniswapJumpToNoMatchRevert h354 (by native_decide) (by native_decide)
    · obtain ⟨_, _, h359⟩ := uniswapReachLowestFirstArm
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hlow
      have h425 := h359
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 0 (by omega))
            (heqLowest 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 1 (by omega))
            (heqLowest 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 2 (by omega))
            (heqLowest 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 3 (by omega))
            (heqLowest 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 4 (by omega))
            (heqLowest 4 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (uniswapLowestArmsWellFormed 5 (by omega))
            (heqLowest 5 (by omega)) (by simp)
      have h426 := h425.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
      exact RD.solcPush1Dup1Revert0 h426 (by native_decide) (by native_decide)
        (by native_decide) (by simp only [List.length_singleton]; omega)

theorem uniswapNonPayable {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  exact (uniswapX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (uniswapBodyReverts_nonPayable t htmem
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem uniswapShortRevert {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  exact (uniswapX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (uniswapDispatch_none_short hsz)

theorem uniswapNoDispatch {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 27 → (uniswapSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (uniswapX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (uniswapDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (uniswapX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (uniswapDispatch_none_short hshort)


end UniswapV2Pair
