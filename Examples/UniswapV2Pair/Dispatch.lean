import Examples.UniswapV2Pair.Common
import Mathlib.Tactic.IntervalCases

/-!
# UniswapV2Pair dispatcher reach slices

Small, bytecode-local dispatcher facts for the optimized binary selector tree.  These lemmas stop at
function body entries and are meant to feed the per-function `...BodyCore` lemmas from `Correct.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Dispatcher layout -/

/-- Root `GT` split after the standard solc selector load. -/
abbrev uniswapRootSplitPc : UInt256 := ⟨32⟩

/-- Low-half `GT` split reached from the root for selectors below `0x6a627842`. -/
abbrev uniswapLowSplitPc : UInt256 := ⟨250⟩

/-- Middle-low `GT` split for selectors at least `0x23b872dd` and below `0x6a627842`. -/
abbrev uniswapMidLowSplitPc : UInt256 := ⟨261⟩

/-- Lowest selector group jump destination for selectors below `0x23b872dd`. -/
abbrev uniswapLowestJumpdestPc : UInt256 := ⟨358⟩

/-- First arm in the lowest selector group (`swap`, `name`, ..., `totalSupply`). -/
abbrev uniswapLowestFirstArmPc : UInt256 := ⟨359⟩

/-- Middle-low selector group jump destination for selectors below `0x3644e515`. -/
abbrev uniswapMidLowJumpdestPc : UInt256 := ⟨320⟩

/-- First arm in the middle-low selector group (`transferFrom`, `PERMIT_TYPEHASH`, `decimals`). -/
abbrev uniswapMidLowFirstArmPc : UInt256 := ⟨321⟩

/-- First arm in the low-upper selector group (`DOMAIN_SEPARATOR`, `initialize`, prices). -/
abbrev uniswapLowUpperFirstArmPc : UInt256 := ⟨272⟩

/-- High-half split reached from the root for selectors at least `0x6a627842`. -/
abbrev uniswapHighSplitPc : UInt256 := ⟨43⟩

/-- Upper high-half split for selectors at least `0xba9a7a56`. -/
abbrev uniswapHighMidSplitPc : UInt256 := ⟨54⟩

/-- First arm in the high-upper selector group (`token1`, `permit`, `allowance`, `sync`). -/
abbrev uniswapHighUpperFirstArmPc : UInt256 := ⟨65⟩

/-- High-middle selector group jump destination. -/
abbrev uniswapHighMiddleJumpdestPc : UInt256 := ⟨113⟩

/-- First arm in the high-middle selector group (`MINIMUM_LIQUIDITY`, `skim`, `factory`). -/
abbrev uniswapHighMiddleFirstArmPc : UInt256 := ⟨114⟩

/-- High-lower selector split jump destination. -/
abbrev uniswapHighLowerJumpdestPc : UInt256 := ⟨151⟩

/-- High-lower selector split for selectors below `0xba9a7a56`. -/
abbrev uniswapHighLowerSplitPc : UInt256 := ⟨152⟩

/-- First arm in the high-lower selector group (`nonces`, `burn`, `symbol`, `transfer`). -/
abbrev uniswapHighLowerFirstArmPc : UInt256 := ⟨163⟩

/-- High-lowest selector group jump destination. -/
abbrev uniswapHighLowestJumpdestPc : UInt256 := ⟨211⟩

/-- First arm in the high-lowest selector group (`mint`, `balanceOf`, `kLast`). -/
abbrev uniswapHighLowestFirstArmPc : UInt256 := ⟨212⟩

set_option maxHeartbeats 1000000 in
/-- The lowest selector group contains six linear `EQ` arms. -/
theorem uniswapLowestArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapLowestFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The middle-low selector group contains three linear `EQ` arms. -/
theorem uniswapMidLowArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapMidLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The low-upper selector group contains four linear `EQ` arms. -/
theorem uniswapLowUpperArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapLowUpperFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high-upper selector group contains four linear `EQ` arms. -/
theorem uniswapHighUpperArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapHighUpperFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high-middle selector group contains three linear `EQ` arms. -/
theorem uniswapHighMiddleArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapHighMiddleFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high-lower selector group contains four linear `EQ` arms. -/
theorem uniswapHighLowerArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapHighLowerFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
/-- The high-lowest selector group contains three linear `EQ` arms. -/
theorem uniswapHighLowestArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed uniswapV2PairBytecode
      (nthArmPc uniswapV2PairBytecode uniswapHighLowestFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

/-- The root selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapRootSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The low selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapLowSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The middle-low selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapMidLowSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapMidLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The high selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapHighSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The high-middle selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapHighMidSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapHighMidSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

/-- The high-lower selector split is `DUP1; PUSH4; GT; PUSH2; JUMPI`. -/
theorem uniswapHighLowerSplitWellFormed :
    selectorSplitWellFormed uniswapV2PairBytecode uniswapHighLowerSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

-- LIBRARY CANDIDATE: Reasoning.Solc — turn a 4-byte calldata-prefix match into equality with
-- the solc selector word (`CALLDATALOAD 0; SHR 224`), parameterized by the selector bytes.
theorem uniswapSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    uniswapSelWord I = sel := by
  apply u256_inj
  dsimp [uniswapSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

-- LIBRARY CANDIDATE: Reasoning.Dispatch — a matched fixed-width selector prefix implies
-- calldata is at least that selector width.
theorem calldata_size_ge_of_selIs (I : ExecutionEnv) (sel : ByteArray) (hselSize : sel.size = 4)
    (hsel : (sel == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  rw [hselSize, ByteArray.size_extract] at hs
  omega

/-! ## Low selector branch reach -/

-- GENERALIZES Reasoning.Solc.solcDispatchReachSelector — support legacy solc selector load
-- emitted as `PUSH1 0; CALLDATALOAD; PUSH1 224; SHR` instead of `PUSH0; ...`.
-- LIBRARY CANDIDATE: Reasoning.Solc — generic solc-0.5.x dispatcher prefix driver,
-- parameterized by bytecode, first split PC, and the zero-push opcode/width.
/-- Standard solc prologue/guards/selector load, stopping at the root selector split. -/
theorem uniswapReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapRootSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  obtain ⟨_, _, h18⟩ := solcGuardCallvalueZero
    (ctgt := (⟨16⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest)
  obtain ⟨k26, C26, h26⟩ := solcCalldataOk
    (bodyPc := (⟨18⟩ : UInt256)) (selLoadTgt := (⟨425⟩ : UInt256))
    (opR := .PUSH2) (wR := 2)
    h18 hsz hsize (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h32 := evm_run h26 with [push1 ⟨0⟩, calldataload, push1 ⟨224⟩, shr]
  refine ⟨k26 + 1 + 1 + 1 + 1, C26 + 3 + 3 + 3 + 3, ?_⟩
  simpa [uniswapRootSplitPc, uniswapSelWord] using h32

/-- Reach the low-half split from the root split. -/
theorem uniswapReachLowSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    uniswapReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h249 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapRootSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 uniswapRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h250 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [uniswapLowSplitPc, uniswapRootSplitPc, armTgt, pushAt] using
      h249.jumpdest (by decide) (by simp)
  exact ⟨_, _, h250⟩

/-- Reach the high-half split from the root split. -/
theorem uniswapReachHighSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    uniswapReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [uniswapHighSplitPc, uniswapRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 uniswapRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

/-- Reach the first arm in Uniswap's lowest selector group. -/
theorem uniswapReachLowestFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h358 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapLowSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k250 + 5)
        (C250 + 22) :=
    RD.selectorSplitTakenAuto h250 uniswapLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h359 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5 + 1) (C250 + 22 + 1) := by
    simpa [uniswapLowestFirstArmPc, uniswapLowestJumpdestPc, uniswapLowSplitPc, armTgt, pushAt]
      using h358.jumpdest (by decide) (by simp)
  exact ⟨_, _, h359⟩

/-- Reach the first arm in Uniswap's middle-low selector group. -/
theorem uniswapReachMidLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapMidLowFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h261 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapMidLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5) (C250 + 22) := by
    simpa [uniswapMidLowSplitPc, uniswapLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h250 uniswapLowSplitWellFormed hlow (by simp)
  have h320 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapMidLowSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k250 + 5 + 5)
        (C250 + 22 + 22) :=
    RD.selectorSplitTakenAuto h261 uniswapMidLowSplitWellFormed hmidLow (by jump_dest) (by simp)
  have h321 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapMidLowFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5 + 5 + 1) (C250 + 22 + 22 + 1) := by
    simpa [uniswapMidLowFirstArmPc, uniswapMidLowJumpdestPc, uniswapMidLowSplitPc, armTgt, pushAt]
      using h320.jumpdest (by decide) (by simp)
  exact ⟨_, _, h321⟩

/-- Reach the first arm in Uniswap's low-upper selector group. -/
theorem uniswapReachLowUpperFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) ≠ ⟨0⟩)
    (hlow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapLowSplitPc) (uniswapSelWord I) = ⟨0⟩)
    (hmidLow :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapMidLowSplitPc) (uniswapSelWord I) =
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapLowUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k250, C250, h250⟩ :=
    uniswapReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h261 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapMidLowSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5) (C250 + 22) := by
    simpa [uniswapMidLowSplitPc, uniswapLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h250 uniswapLowSplitWellFormed hlow (by simp)
  have h272 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapLowUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k250 + 5 + 5) (C250 + 22 + 22) := by
    simpa [uniswapLowUpperFirstArmPc, uniswapMidLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h261 uniswapMidLowSplitWellFormed hmidLow (by simp)
  exact ⟨_, _, h272⟩

/-- Reach the first arm in Uniswap's high-upper selector group. -/
theorem uniswapReachHighUpperFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighMidSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [uniswapHighMidSplitPc, uniswapHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 uniswapHighSplitWellFormed hhigh (by simp)
  have h65 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighUpperFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 5) (C43 + 22 + 22) := by
    simpa [uniswapHighUpperFirstArmPc, uniswapHighMidSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h54 uniswapHighMidSplitWellFormed hhighMid (by simp)
  exact ⟨_, _, h65⟩

/-- Reach the first arm in Uniswap's high-middle selector group. -/
theorem uniswapReachHighMiddleFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighMiddleFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighMidSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [uniswapHighMidSplitPc, uniswapHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 uniswapHighSplitWellFormed hhigh (by simp)
  have h113 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighMidSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k43 + 5 + 5)
        (C43 + 22 + 22) :=
    RD.selectorSplitTakenAuto h54 uniswapHighMidSplitWellFormed hhighMid (by jump_dest) (by simp)
  have h114 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighMiddleFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 5 + 1) (C43 + 22 + 22 + 1) := by
    simpa [uniswapHighMiddleFirstArmPc, uniswapHighMiddleJumpdestPc, uniswapHighMidSplitPc,
      armTgt, pushAt] using h113.jumpdest (by decide) (by simp)
  exact ⟨_, _, h114⟩

/-- Reach the high-lower split in Uniswap's high selector branch. -/
theorem uniswapReachHighLowerSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapRootSplitPc) (uniswapSelWord I) =
        ⟨0⟩)
    (hhigh :
      UInt256.gt (armSelNat uniswapV2PairBytecode uniswapHighSplitPc) (uniswapSelWord I) ≠
        ⟨0⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighLowerSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    uniswapReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h151 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) :=
    RD.selectorSplitTakenAuto h43 uniswapHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h152 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighLowerSplitPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [uniswapHighLowerSplitPc, uniswapHighLowerJumpdestPc, uniswapHighSplitPc, armTgt,
      pushAt] using h151.jumpdest (by decide) (by simp)
  exact ⟨_, _, h152⟩

/-- Reach the first arm in Uniswap's high-lower selector group. -/
theorem uniswapReachHighLowerFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighLowerFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k152, C152, h152⟩ :=
    uniswapReachHighLowerSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have h163 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighLowerFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k152 + 5) (C152 + 22) := by
    simpa [uniswapHighLowerFirstArmPc, uniswapHighLowerSplitPc, selArmNextPc,
      armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h152 uniswapHighLowerSplitWellFormed hlower (by simp)
  exact ⟨_, _, h163⟩

/-- Reach the first arm in Uniswap's high-lowest selector group. -/
theorem uniswapReachHighLowestFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
        uniswapHighLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k152, C152, h152⟩ :=
    uniswapReachHighLowerSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  have h211 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt uniswapV2PairBytecode uniswapHighLowerSplitPc) [uniswapSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k152 + 5) (C152 + 22) :=
    RD.selectorSplitTakenAuto h152 uniswapHighLowerSplitWellFormed hlower (by jump_dest) (by simp)
  have h212 : RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I)
      uniswapHighLowestFirstArmPc [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k152 + 5 + 1) (C152 + 22 + 1) := by
    simpa [uniswapHighLowestFirstArmPc, uniswapHighLowestJumpdestPc, uniswapHighLowerSplitPc,
      armTgt, pushAt] using h211.jumpdest (by decide) (by simp)
  exact ⟨_, _, h212⟩

/-- Reach a selected body in Uniswap's lowest selector group. -/
theorem uniswapReachLowestBody {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h359⟩ :=
    uniswapReachLowestFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i h359
    (fun j hj => uniswapLowestArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's middle-low selector group. -/
theorem uniswapReachMidLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h321⟩ :=
    uniswapReachMidLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hmidLow
  exact RD.dispatchTo bodyPC i h321
    (fun j hj => uniswapMidLowArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's low-upper selector group. -/
theorem uniswapReachLowUpperBody {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h272⟩ :=
    uniswapReachLowUpperFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hmidLow
  exact RD.dispatchTo bodyPC i h272
    (fun j hj => uniswapLowUpperArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-upper selector group. -/
theorem uniswapReachHighUpperBody {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h65⟩ :=
    uniswapReachHighUpperFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighMid
  exact RD.dispatchTo bodyPC i h65
    (fun j hj => uniswapHighUpperArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-middle selector group. -/
theorem uniswapReachHighMiddleBody {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h114⟩ :=
    uniswapReachHighMiddleFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighMid
  exact RD.dispatchTo bodyPC i h114
    (fun j hj => uniswapHighMiddleArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-lower selector group. -/
theorem uniswapReachHighLowerBody {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h163⟩ :=
    uniswapReachHighLowerFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hlower
  exact RD.dispatchTo bodyPC i h163
    (fun j hj => uniswapHighLowerArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach a selected body in Uniswap's high-lowest selector group. -/
theorem uniswapReachHighLowestBody {cA gh bl σ σ₀ A I} {g : Sat256}
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
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h212⟩ :=
    uniswapReachHighLowestFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hlower
  exact RD.dispatchTo bodyPC i h212
    (fun j hj => uniswapHighLowestArmsWellFormed j (le_trans hj hi))
    heq0 htake
    (by rw [hbody]; exact hjd)
    hbody
    (by simp)

/-- Reach the `PERMIT_TYPEHASH()` body entry through the optimized dispatcher. -/
theorem uniswapReachPermitTypehashBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨933⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachDecimalsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨941⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachTransferFromBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨879⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachDomainSeparatorBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x36, 0x44, 0xe5, 0x15]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨971⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachInitializeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x48, 0x5c, 0xc9, 0x55]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨979⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachPrice0CumulativeLastBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x59, 0x09, 0xc0, 0xd5]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1025⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachPrice1CumulativeLastBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x5a, 0x3d, 0x54, 0x93]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1033⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachBalanceOfBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1079⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachKLastBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x74, 0x64, 0xfc, 0x3d]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1117⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachNoncesBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1125⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachMinimumLiquidityBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xba, 0x9a, 0x7a, 0x56]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1278⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachFactoryBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xc4, 0x5a, 0x01, 0x55]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1324⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachToken1Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xd2, 0x12, 0x20, 0xa7]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1332⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachAllowanceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1421⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachSyncBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xff, 0xf6, 0xca, 0xe9]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1467⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachSkimBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1286⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachGetReservesBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x09, 0x02, 0xf1, 0xac]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨697⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachToken0Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0d, 0xfe, 0x16, 0x81]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨817⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachApproveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨753⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachTotalSupplyBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨853⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
theorem uniswapReachTransferBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1234⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
