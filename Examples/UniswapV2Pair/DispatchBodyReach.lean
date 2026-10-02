import Examples.UniswapV2Pair.DispatchReach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-- Reach a selected body in Uniswap's lowest selector group. -/
theorem uniswapReachLowestBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h359⟩ :=
    uniswapReachLowestFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i h359
    (fun j hj => uniswapLowestArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's middle-low selector group. -/
theorem uniswapReachMidLowBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h321⟩ :=
    uniswapReachMidLowFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hmidLow
  exact RD.dispatchTo bodyPC i h321
    (fun j hj => uniswapMidLowArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's low-upper selector group. -/
theorem uniswapReachLowUpperBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h272⟩ :=
    uniswapReachLowUpperFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hmidLow
  exact RD.dispatchTo bodyPC i h272
    (fun j hj => uniswapLowUpperArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-upper selector group. -/
theorem uniswapReachHighUpperBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
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
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h65⟩ :=
    uniswapReachHighUpperFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighMid
  exact RD.dispatchTo bodyPC i h65
    (fun j hj => uniswapHighUpperArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-middle selector group. -/
theorem uniswapReachHighMiddleBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
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
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h114⟩ :=
    uniswapReachHighMiddleFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighMid
  exact RD.dispatchTo bodyPC i h114
    (fun j hj => uniswapHighMiddleArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-lower selector group. -/
theorem uniswapReachHighLowerBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
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
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h163⟩ :=
    uniswapReachHighLowerFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hlower
  exact RD.dispatchTo bodyPC i h163
    (fun j hj => uniswapHighLowerArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-lowest selector group. -/
theorem uniswapReachHighLowestBody {σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
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
        ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc j))
        (uniswapSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq
        (armSelNat uniswapV2PairBytecode
          (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc i))
        (uniswapSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J uniswapV2PairBytecode 0).contains bodyPC = true)
    (hbody :
      armTgt uniswapV2PairBytecode
        (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc i) = bodyPC) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h212⟩ :=
    uniswapReachHighLowestFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hlower
  exact RD.dispatchTo bodyPC i h212
    (fun j hj => uniswapHighLowestArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach the `PERMIT_TYPEHASH()` body entry through the optimized dispatcher. -/
theorem uniswapReachPermitTypehashBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨933⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x30adf81f⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x30 0xad 0xf8 0x1f ⟨0x30adf81f⟩ (by decide) hsel
  exact uniswapReachMidLowBody 1 (by decide) ⟨933⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `decimals()` body entry through the optimized dispatcher. -/
theorem uniswapReachDecimalsBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨941⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x313ce567⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x31 0x3c 0xe5 0x67 ⟨0x313ce567⟩ (by decide) hsel
  exact uniswapReachMidLowBody 2 (by decide) ⟨941⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `transferFrom(address,address,uint256)` body entry through the optimized dispatcher. -/
theorem uniswapReachTransferFromBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨879⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x23b872dd⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd ⟨0x23b872dd⟩ (by decide) hsel
  exact uniswapReachMidLowBody 0 (by decide) ⟨879⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `DOMAIN_SEPARATOR()` body entry through the optimized dispatcher. -/
theorem uniswapReachDomainSeparatorBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x36, 0x44, 0xe5, 0x15]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨971⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x3644e515⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x36 0x44 0xe5 0x15 ⟨0x3644e515⟩ (by decide) hsel
  exact uniswapReachLowUpperBody 0 (by decide) ⟨971⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `initialize(address,address)` body entry through the optimized dispatcher. -/
theorem uniswapReachInitializeBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨979⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x485cc955⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x48 0x5c 0xc9 0x55 ⟨0x485cc955⟩ (by decide) hsel
  exact uniswapReachLowUpperBody 1 (by decide) ⟨979⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `price0CumulativeLast()` body entry through the optimized dispatcher. -/
theorem uniswapReachPrice0CumulativeLastBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x59, 0x09, 0xc0, 0xd5]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1025⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x5909c0d5⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x59 0x09 0xc0 0xd5 ⟨0x5909c0d5⟩ (by decide) hsel
  exact uniswapReachLowUpperBody 2 (by decide) ⟨1025⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `price1CumulativeLast()` body entry through the optimized dispatcher. -/
theorem uniswapReachPrice1CumulativeLastBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x5a, 0x3d, 0x54, 0x93]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1033⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x5a3d5493⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x5a 0x3d 0x54 0x93 ⟨0x5a3d5493⟩ (by decide) hsel
  exact uniswapReachLowUpperBody 3 (by decide) ⟨1033⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `balanceOf(address)` body entry through the optimized dispatcher. -/
theorem uniswapReachBalanceOfBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1079⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x70a08231⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x70 0xa0 0x82 0x31 ⟨0x70a08231⟩ (by decide) hsel
  exact uniswapReachHighLowestBody 1 (by decide) ⟨1079⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `kLast()` body entry through the optimized dispatcher. -/
theorem uniswapReachKLastBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x74, 0x64, 0xfc, 0x3d]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1117⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x7464fc3d⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x74 0x64 0xfc 0x3d ⟨0x7464fc3d⟩ (by decide) hsel
  exact uniswapReachHighLowestBody 2 (by decide) ⟨1117⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `nonces(address)` body entry through the optimized dispatcher. -/
theorem uniswapReachNoncesBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1125⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x7ecebe00⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x7e 0xce 0xbe 0x00 ⟨0x7ecebe00⟩ (by decide) hsel
  exact uniswapReachHighLowerBody 0 (by decide) ⟨1125⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `MINIMUM_LIQUIDITY()` body entry through the optimized dispatcher. -/
theorem uniswapReachMinimumLiquidityBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xba, 0x9a, 0x7a, 0x56]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1278⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0xba9a7a56⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xba 0x9a 0x7a 0x56 ⟨0xba9a7a56⟩ (by decide) hsel
  exact uniswapReachHighMiddleBody 0 (by decide) ⟨1278⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `factory()` body entry through the optimized dispatcher. -/
theorem uniswapReachFactoryBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1324⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0xc45a0155⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xc4 0x5a 0x01 0x55 ⟨0xc45a0155⟩ (by decide) hsel
  exact uniswapReachHighMiddleBody 2 (by decide) ⟨1324⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `token1()` body entry through the optimized dispatcher. -/
theorem uniswapReachToken1Body {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1332⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0xd21220a7⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xd2 0x12 0x20 0xa7 ⟨0xd21220a7⟩ (by decide) hsel
  exact uniswapReachHighUpperBody 0 (by decide) ⟨1332⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `allowance(address,address)` body entry through the optimized dispatcher. -/
theorem uniswapReachAllowanceBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1421⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0xdd62ed3e⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xdd 0x62 0xed 0x3e ⟨0xdd62ed3e⟩ (by decide) hsel
  exact uniswapReachHighUpperBody 2 (by decide) ⟨1421⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `sync()` body entry through the optimized dispatcher. -/
theorem uniswapReachSyncBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1467⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0xfff6cae9⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xff 0xf6 0xca 0xe9 ⟨0xfff6cae9⟩ (by decide) hsel
  exact uniswapReachHighUpperBody 3 (by decide) ⟨1467⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `skim(address)` body entry through the optimized dispatcher. -/
theorem uniswapReachSkimBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1286⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0xbc25cf77⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xbc 0x25 0xcf 0x77 ⟨0xbc25cf77⟩ (by decide) hsel
  exact uniswapReachHighMiddleBody 1 (by decide) ⟨1286⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `getReserves()` body entry through the optimized dispatcher. -/
theorem uniswapReachGetReservesBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x09, 0x02, 0xf1, 0xac]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨697⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x0902f1ac⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x09 0x02 0xf1 0xac ⟨0x0902f1ac⟩ (by decide) hsel
  exact uniswapReachLowestBody 2 (by decide) ⟨697⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `token0()` body entry through the optimized dispatcher. -/
theorem uniswapReachToken0Body {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨817⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x0dfe1681⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x0d 0xfe 0x16 0x81 ⟨0x0dfe1681⟩ (by decide) hsel
  exact uniswapReachLowestBody 4 (by decide) ⟨817⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j <;> decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `approve(address,uint256)` body entry through the optimized dispatcher. -/
theorem uniswapReachApproveBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨753⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x095ea7b3⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 ⟨0x095ea7b3⟩ (by decide) hsel
  exact uniswapReachLowestBody 3 (by decide) ⟨753⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `totalSupply()` body entry through the optimized dispatcher. -/
theorem uniswapReachTotalSupplyBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨853⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0x18160ddd⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd ⟨0x18160ddd⟩ (by decide) hsel
  have hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  have hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide
  exact uniswapReachLowestBody 5 (by decide) ⟨853⟩ hcode hwv hsz hsize hroot hlow
    (fun j hj => by
      rw [hword]
      interval_cases j <;> decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `transfer(address,uint256)` body entry through the optimized dispatcher. -/
theorem uniswapReachTransferBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState σ σ₀ g A I) ⟨1234⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : uniswapSelWord I = ⟨0xa9059cbb⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xa9 0x05 0x9c 0xbb ⟨0xa9059cbb⟩ (by decide) hsel
  exact uniswapReachHighLowerBody 3 (by decide) ⟨1234⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals native_decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)


end UniswapV2Pair
