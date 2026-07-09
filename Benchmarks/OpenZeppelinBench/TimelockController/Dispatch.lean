import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController runtime dispatcher reach lemmas

The dispatcher is solc 0.8.35's balanced depth-3 binary search over 28 selectors: a free-memory
pointer prologue, a `calldatasize < 4` guard that falls through to the payable receive / short-revert
handler (pc 434) rather than reverting inline, a selector load, and a tree of `GT` pivot splits whose
leaves are linear `EQ` arm groups.  There is **no shared callvalue guard** — `receive` is payable, so
each non-payable function guards its own callvalue at its entry.

Dispatch tree (anchor pcs read off the bytecode; each split is `DUP1; PUSH4 pivot; GT; PUSH2 lo; JUMPI`):

```
root@18 (0x8065657f hashOperation):  sel<piv → jd231→N232 ; else → N29
  N232@232 (0x2ab0f529 isOperationDone): sel<piv → jd338→N339 ; else → N243
    N339@339 (0x134008d3 execute):        sel<piv → jd397→G397@398 ; else → G350@350
    N243@243 (0x36568abe renounceRole):   sel<piv → jd301→G301@302 ; else → G254@254
  N29@29 (0xbc197c81 onERC1155BatchReceived): sel<piv → jd135→N136 ; else → N40
    N136@136 (0x91d14854 hasRole):        sel<piv → jd194→G194@195 ; else → G147@147
    N40@40 (0xd547741f revokeRole):        sel<piv → jd98→G98@99   ; else → G51@51
```

Leaf arm groups (arm order = bytecode order):
* G51  @51  : revokeRole@1350, executeBatch@1381, onERC1155Received@1400, getMinDelay@1443
* G98  @99  : onERC1155BatchReceived@1233, cancel@1276, getTimestamp@1307
* G147 @147 : hasRole@1101, DEFAULT_ADMIN_ROLE@1132, CANCELLER_ROLE@1151, hashOperationBatch@1202
* G194 @195 : hashOperation@988, scheduleBatch@1019, PROPOSER_ROLE@1050
* G254 @254 : renounceRole@851, isOperationPending@882, updateDelay@913, getOperationState@944
* G301 @302 : isOperationDone@758, grantRole@789, isOperation@820
* G350 @350 : execute@595, isOperationReady@614, onERC721Received@645, getRoleAdmin@712
* G397 @398 : schedule@445, supportsInterface@478, EXECUTOR_ROLE@530
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Prologue: reach the root split -/

/-- Prologue: install free-mem-ptr, pass the `size ≥ 4` calldata guard (fall through), load the
    selector, reaching the root split at pc 18 with the selector word on the stack.  No callvalue
    guard (payable `receive`). -/
theorem tlcReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨18⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have h5 := (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    |>.push1 ⟨128⟩ (by native_decide) (by decide)
    |>.push1 ⟨64⟩ (by native_decide) (by decide)
    |>.mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide)
        mem_cost (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
        (by decide) (by decide)
  have h13 := h5
    |>.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.pushConst (⟨434⟩ : UInt256) (width := 2) (op := .PUSH2) (by native_decide)
        (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (lt_four_eq_zero_of_ge hsz hsize)
        (by simp only [List.length]; omega)
  obtain ⟨k, C, h18⟩ := solcSelectorLoad h13 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by simp only [List.length]; omega)
  exact ⟨k, C, h18⟩

/-! ## Split / arm well-formedness -/

theorem tlcRootSplitWF : selectorSplitWellFormed timelockControllerBenchBytecode ⟨18⟩ := by
  dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide

theorem tlcN29SplitWF : selectorSplitWellFormed timelockControllerBenchBytecode ⟨29⟩ := by
  dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide

theorem tlcN40SplitWF : selectorSplitWellFormed timelockControllerBenchBytecode ⟨40⟩ := by
  dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide

theorem tlcN136SplitWF : selectorSplitWellFormed timelockControllerBenchBytecode ⟨136⟩ := by
  dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide

theorem tlcN232SplitWF : selectorSplitWellFormed timelockControllerBenchBytecode ⟨232⟩ := by
  dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide

theorem tlcN243SplitWF : selectorSplitWellFormed timelockControllerBenchBytecode ⟨243⟩ := by
  dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide

theorem tlcN339SplitWF : selectorSplitWellFormed timelockControllerBenchBytecode ⟨339⟩ := by
  dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide

theorem tlcG51ArmsWF :
    ∀ j, j ≤ 3 → armWellFormed timelockControllerBenchBytecode
      (nthArmPc timelockControllerBenchBytecode ⟨51⟩ j) := by
  intro j hj; interval_cases j <;>
    (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

theorem tlcG98ArmsWF :
    ∀ j, j ≤ 2 → armWellFormed timelockControllerBenchBytecode
      (nthArmPc timelockControllerBenchBytecode ⟨99⟩ j) := by
  intro j hj; interval_cases j <;>
    (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

theorem tlcG147ArmsWF :
    ∀ j, j ≤ 3 → armWellFormed timelockControllerBenchBytecode
      (nthArmPc timelockControllerBenchBytecode ⟨147⟩ j) := by
  intro j hj; interval_cases j <;>
    (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

theorem tlcG194ArmsWF :
    ∀ j, j ≤ 2 → armWellFormed timelockControllerBenchBytecode
      (nthArmPc timelockControllerBenchBytecode ⟨195⟩ j) := by
  intro j hj; interval_cases j <;>
    (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

theorem tlcG254ArmsWF :
    ∀ j, j ≤ 3 → armWellFormed timelockControllerBenchBytecode
      (nthArmPc timelockControllerBenchBytecode ⟨254⟩ j) := by
  intro j hj; interval_cases j <;>
    (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

theorem tlcG301ArmsWF :
    ∀ j, j ≤ 2 → armWellFormed timelockControllerBenchBytecode
      (nthArmPc timelockControllerBenchBytecode ⟨302⟩ j) := by
  intro j hj; interval_cases j <;>
    (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

theorem tlcG350ArmsWF :
    ∀ j, j ≤ 3 → armWellFormed timelockControllerBenchBytecode
      (nthArmPc timelockControllerBenchBytecode ⟨350⟩ j) := by
  intro j hj; interval_cases j <;>
    (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

theorem tlcG397ArmsWF :
    ∀ j, j ≤ 2 → armWellFormed timelockControllerBenchBytecode
      (nthArmPc timelockControllerBenchBytecode ⟨398⟩ j) := by
  intro j hj; interval_cases j <;>
    (dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)

/-! ## Internal-node reaches (parameterised over the split directions taken to get there) -/

/-- Root not taken (`sel ≥ 0x8065657f`): fall through to `N29`. -/
theorem tlcReach29 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨29⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h18⟩ := tlcReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  exact ⟨_, _, by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc]
      using RD.selectorSplitNotTakenAuto h18 tlcRootSplitWF hroot (by simp)⟩

/-- Root taken (`sel < 0x8065657f`): jump 231, step jumpdest to `N232`. -/
theorem tlcReach232 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨232⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h18⟩ := tlcReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have h231 := RD.selectorSplitTakenAuto h18 tlcRootSplitWF hroot (by jump_dest) (by simp)
  exact ⟨_, _, h231.jumpdest (by native_decide) (by simp)⟩

/-- `N29` not taken (`sel ≥ 0xbc197c81`): fall through to `N40`. -/
theorem tlcReach40 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) = ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨40⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h29r⟩ := tlcReach29 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot
  exact ⟨_, _, by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc]
      using RD.selectorSplitNotTakenAuto h29r tlcN29SplitWF h29 (by simp)⟩

/-- `N29` taken (`sel < 0xbc197c81`): jump 135, step jumpdest to `N136`. -/
theorem tlcReach136 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨136⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h29r⟩ := tlcReach29 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot
  have h135 := RD.selectorSplitTakenAuto h29r tlcN29SplitWF h29 (by jump_dest) (by simp)
  exact ⟨_, _, h135.jumpdest (by native_decide) (by simp)⟩

/-- `N232` not taken (`sel ≥ 0x2ab0f529`): fall through to `N243`. -/
theorem tlcReach243 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) = ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨243⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h232r⟩ := tlcReach232 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot
  exact ⟨_, _, by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc]
      using RD.selectorSplitNotTakenAuto h232r tlcN232SplitWF h232 (by simp)⟩

/-- `N232` taken (`sel < 0x2ab0f529`): jump 338, step jumpdest to `N339`. -/
theorem tlcReach339 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨339⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h232r⟩ := tlcReach232 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot
  have h338 := RD.selectorSplitTakenAuto h232r tlcN232SplitWF h232 (by jump_dest) (by simp)
  exact ⟨_, _, h338.jumpdest (by native_decide) (by simp)⟩

/-! ## Leaf-group first-arm reaches -/

/-- `N40` not taken (`sel ≥ 0xd547741f`): fall through to arms `@51` (G51). -/
theorem tlcReachG51First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) = ⟨0⟩)
    (h40 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨40⟩) (tlcSelWord I) = ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨51⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h40r⟩ := tlcReach40 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h29
  exact ⟨_, _, by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc]
      using RD.selectorSplitNotTakenAuto h40r tlcN40SplitWF h40 (by simp)⟩

/-- `N40` taken (`sel < 0xd547741f`): jump 98, step jumpdest to arms `@99` (G98). -/
theorem tlcReachG98First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) = ⟨0⟩)
    (h40 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨40⟩) (tlcSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨99⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h40r⟩ := tlcReach40 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h29
  have h98 := RD.selectorSplitTakenAuto h40r tlcN40SplitWF h40 (by jump_dest) (by simp)
  exact ⟨_, _, h98.jumpdest (by native_decide) (by simp)⟩

/-- `N136` not taken (`sel ≥ 0x91d14854`): fall through to arms `@147` (G147). -/
theorem tlcReachG147First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h136 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨136⟩) (tlcSelWord I) = ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨147⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h136r⟩ := tlcReach136 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h29
  exact ⟨_, _, by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc]
      using RD.selectorSplitNotTakenAuto h136r tlcN136SplitWF h136 (by simp)⟩

/-- `N136` taken (`sel < 0x91d14854`): jump 194, step jumpdest to arms `@195` (G194). -/
theorem tlcReachG194First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h136 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨136⟩) (tlcSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨195⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h136r⟩ := tlcReach136 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h29
  have h194 := RD.selectorSplitTakenAuto h136r tlcN136SplitWF h136 (by jump_dest) (by simp)
  exact ⟨_, _, h194.jumpdest (by native_decide) (by simp)⟩

/-- `N243` not taken (`sel ≥ 0x36568abe`): fall through to arms `@254` (G254). -/
theorem tlcReachG254First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) = ⟨0⟩)
    (h243 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨243⟩) (tlcSelWord I) = ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨254⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h243r⟩ := tlcReach243 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h232
  exact ⟨_, _, by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc]
      using RD.selectorSplitNotTakenAuto h243r tlcN243SplitWF h243 (by simp)⟩

/-- `N243` taken (`sel < 0x36568abe`): jump 301, step jumpdest to arms `@302` (G301). -/
theorem tlcReachG301First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) = ⟨0⟩)
    (h243 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨243⟩) (tlcSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨302⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h243r⟩ := tlcReach243 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h232
  have h301 := RD.selectorSplitTakenAuto h243r tlcN243SplitWF h243 (by jump_dest) (by simp)
  exact ⟨_, _, h301.jumpdest (by native_decide) (by simp)⟩

/-- `N339` not taken (`sel ≥ 0x134008d3`): fall through to arms `@350` (G350). -/
theorem tlcReachG350First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h339 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨339⟩) (tlcSelWord I) = ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨350⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h339r⟩ := tlcReach339 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h232
  exact ⟨_, _, by
    simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc]
      using RD.selectorSplitNotTakenAuto h339r tlcN339SplitWF h339 (by simp)⟩

/-- `N339` taken (`sel < 0x134008d3`): jump 397, step jumpdest to arms `@398` (G397). -/
theorem tlcReachG397First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h339 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨339⟩) (tlcSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨398⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h339r⟩ := tlcReach339 (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h232
  have h397 := RD.selectorSplitTakenAuto h339r tlcN339SplitWF h339 (by jump_dest) (by simp)
  exact ⟨_, _, h397.jumpdest (by native_decide) (by simp)⟩

/-! ## Per-group body reaches (dispatcher fold to a matched arm's body pc) -/

theorem tlcReachG51Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) = ⟨0⟩)
    (h40 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨40⟩) (tlcSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨51⟩ j)) (tlcSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨51⟩ i)) (tlcSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J timelockControllerBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨51⟩ i) = bodyPC) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ := tlcReachG51First (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h29 h40
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => tlcG51ArmsWF j (le_trans hj hi)) heq0 htake (by simpa [hbody] using hjd) hbody
    (by simp)

theorem tlcReachG98Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) = ⟨0⟩)
    (h40 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨40⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨99⟩ j)) (tlcSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨99⟩ i)) (tlcSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J timelockControllerBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨99⟩ i) = bodyPC) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ := tlcReachG98First (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h29 h40
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => tlcG98ArmsWF j (le_trans hj hi)) heq0 htake (by simpa [hbody] using hjd) hbody
    (by simp)

theorem tlcReachG147Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h136 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨136⟩) (tlcSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨147⟩ j)) (tlcSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨147⟩ i)) (tlcSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J timelockControllerBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨147⟩ i) = bodyPC) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ := tlcReachG147First (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h29 h136
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => tlcG147ArmsWF j (le_trans hj hi)) heq0 htake (by simpa [hbody] using hjd) hbody
    (by simp)

theorem tlcReachG194Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩)
    (h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h136 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨136⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨195⟩ j)) (tlcSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨195⟩ i)) (tlcSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J timelockControllerBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨195⟩ i) = bodyPC) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ := tlcReachG194First (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h29 h136
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => tlcG194ArmsWF j (le_trans hj hi)) heq0 htake (by simpa [hbody] using hjd) hbody
    (by simp)

theorem tlcReachG254Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) = ⟨0⟩)
    (h243 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨243⟩) (tlcSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨254⟩ j)) (tlcSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨254⟩ i)) (tlcSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J timelockControllerBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨254⟩ i) = bodyPC) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ := tlcReachG254First (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h232 h243
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => tlcG254ArmsWF j (le_trans hj hi)) heq0 htake (by simpa [hbody] using hjd) hbody
    (by simp)

theorem tlcReachG301Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) = ⟨0⟩)
    (h243 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨243⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨302⟩ j)) (tlcSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨302⟩ i)) (tlcSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J timelockControllerBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨302⟩ i) = bodyPC) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ := tlcReachG301First (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h232 h243
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => tlcG301ArmsWF j (le_trans hj hi)) heq0 htake (by simpa [hbody] using hjd) hbody
    (by simp)

theorem tlcReachG350Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h339 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨339⟩) (tlcSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨350⟩ j)) (tlcSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨350⟩ i)) (tlcSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J timelockControllerBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨350⟩ i) = bodyPC) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ := tlcReachG350First (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h232 h339
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => tlcG350ArmsWF j (le_trans hj hi)) heq0 htake (by simpa [hbody] using hjd) hbody
    (by simp)

theorem tlcReachG397Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = timelockControllerBenchBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (h339 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨339⟩) (tlcSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨398⟩ j)) (tlcSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨398⟩ i)) (tlcSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J timelockControllerBenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨398⟩ i) = bodyPC) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ := tlcReachG397First (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hroot h232 h339
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => tlcG397ArmsWF j (le_trans hj hi)) heq0 htake (by simpa [hbody] using hjd) hbody
    (by simp)

end OpenZeppelinBench.TimelockController
