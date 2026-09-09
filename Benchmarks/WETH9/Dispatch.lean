import Benchmarks.WETH9.Trusted

/-!
# WETH9 runtime dispatcher reach lemmas

The WETH9 dispatcher is solc 0.5.16's one-level binary search: a free-memory-pointer prologue, a
`calldatasize < 4` guard that falls through to the **payable fallback** (pc 156) rather than
reverting, a selector load, a root `GT 0x313ce567` split, and two linear `EQ` arm groups.  Unlike
the standard solc prologue there is **no shared callvalue guard** — `deposit`/`fallback` are payable,
so each non-payable function guards its own callvalue at its entry.

This file threads `initState` to each function's body-entry pc with the selector word on the stack.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## Prologue and root split -/

/-- WETH9 prologue: install free-mem-ptr, pass the `size ≥ 4` calldata guard (fall through), load the
    selector, reaching the root split at pc 19 with the selector word on the stack. -/
theorem weth9ReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨19⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have h5 := (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    |>.push1 ⟨128⟩ (by decide +native) (by decide)
    |>.push1 ⟨64⟩ (by decide +native) (by decide)
    |>.mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by decide +native)
        mem_cost (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
        (by decide) (by decide)
  have h13 := h5
    |>.push1 ⟨4⟩ (by decide +native) (by simp only [List.length]; omega)
    |>.calldatasize (by decide +native) (by simp only [List.length]; omega)
    |>.lt (by decide +native) (by simp only [List.length]; omega)
    |>.pushConst (⟨156⟩ : UInt256) (width := 2) (op := .PUSH2) (by decide +native)
        (by decide +native) (by simp only [List.length]; omega)
    |>.jumpiNT (by decide +native) (lt_four_eq_zero_of_ge hsz hsize)
        (by simp only [List.length]; omega)
  obtain ⟨k, C, h19⟩ := solcLegacySelectorLoad h13 (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by simp only [List.length]; omega)
  exact ⟨k, C, h19⟩

/-- The root binary-search split is `DUP1; PUSH4 0x313ce567; GT; PUSH2 100; JUMPI`. -/
theorem weth9RootSplitWellFormed : selectorSplitWellFormed weth9Bytecode ⟨19⟩ := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

/-- The upper selector group contains six linear `EQ` arms (pc 30). -/
theorem weth9UpperArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed weth9Bytecode (nthArmPc weth9Bytecode ⟨30⟩ j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

/-- The lower selector group contains five linear `EQ` arms (pc 101). -/
theorem weth9LowerArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed weth9Bytecode (nthArmPc weth9Bytecode ⟨101⟩ j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

/-- Not taken at the root split (`sel ≥ 0x313ce567`): fall through to the upper arm at pc 30. -/
theorem weth9ReachUpperArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hb : UInt256.gt (armSelNat weth9Bytecode ⟨19⟩) (weth9SelWord I) = ⟨0⟩) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨30⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h19⟩ := weth9ReachSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  exact ⟨_, _, RD.selectorSplitNotTakenAuto h19 weth9RootSplitWellFormed hb (by simp)⟩

/-- Taken at the root split (`sel < 0x313ce567`): jump to pc 100 and step its `JUMPDEST`, reaching
    the lower arm at pc 101. -/
theorem weth9ReachLowerArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hb : UInt256.gt (armSelNat weth9Bytecode ⟨19⟩) (weth9SelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨101⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h19⟩ := weth9ReachSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have h100 := RD.selectorSplitTakenAuto h19 weth9RootSplitWellFormed hb (by jump_dest) (by simp)
  exact ⟨_, _, h100.jumpdest (by decide +native) (by simp only [List.length]; omega)⟩

/-! ## Per-function body reaches

Each reach derives the concrete selector word from the `selIs` byte match, picks the arm half by the
`GT`-split direction, and folds `RD.dispatchTo` to the body-entry pc. -/

/-- Reach `decimals()` body (pc 529): upper arm index 0. -/
theorem weth9ReachDecimals {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 5)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨529⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨826074471⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x31 0x3c 0xe5 0x67 ⟨826074471⟩ (by decide +native) hsel
  obtain ⟨_, _, h30⟩ := weth9ReachUpperArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨529⟩ 0 h30 (fun j hj => weth9UpperArmsWellFormed j (by omega))
    (fun j hj => by omega) (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `balanceOf(address)` decode entry (pc 572): upper arm index 1. -/
theorem weth9ReachBalanceOf {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 6)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨572⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨1889567281⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x70 0xa0 0x82 0x31 ⟨1889567281⟩ (by decide +native) hsel
  obtain ⟨_, _, h30⟩ := weth9ReachUpperArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨572⟩ 1 h30 (fun j hj => weth9UpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `symbol()` body (pc 623): upper arm index 2. -/
theorem weth9ReachSymbol {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 7)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨623⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨2514000705⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x95 0xd8 0x9b 0x41 ⟨2514000705⟩ (by decide +native) hsel
  obtain ⟨_, _, h30⟩ := weth9ReachUpperArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨623⟩ 2 h30 (fun j hj => weth9UpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `transfer(address,uint256)` decode entry (pc 644): upper arm index 3. -/
theorem weth9ReachTransfer {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 8)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨644⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨2835717307⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xa9 0x05 0x9c 0xbb ⟨2835717307⟩ (by decide +native) hsel
  obtain ⟨_, _, h30⟩ := weth9ReachUpperArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨644⟩ 3 h30 (fun j hj => weth9UpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach the `deposit()`/fallback handler entry (pc 156): upper arm index 4. -/
theorem weth9ReachDepositEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 9)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨156⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨3504541104⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xd0 0xe3 0x0d 0xb0 ⟨3504541104⟩ (by decide +native) hsel
  obtain ⟨_, _, h30⟩ := weth9ReachUpperArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨156⟩ 4 h30 (fun j hj => weth9UpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `allowance(address,address)` decode entry (pc 701): upper arm index 5. -/
theorem weth9ReachAllowance {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 10)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨701⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨3714247998⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xdd 0x62 0xed 0x3e ⟨3714247998⟩ (by decide +native) hsel
  obtain ⟨_, _, h30⟩ := weth9ReachUpperArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨701⟩ 5 h30 (fun j hj => weth9UpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `name()` body (pc 166): lower arm index 0. -/
theorem weth9ReachName {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 0)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨166⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨117300739⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x06 0xfd 0xde 0x03 ⟨117300739⟩ (by decide +native) hsel
  obtain ⟨_, _, h101⟩ := weth9ReachLowerArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨166⟩ 0 h101 (fun j hj => weth9LowerArmsWellFormed j (by omega))
    (fun j hj => by omega) (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `approve(address,uint256)` decode entry (pc 304): lower arm index 1. -/
theorem weth9ReachApprove {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 1)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨304⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨157198259⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x09 0x5e 0xa7 0xb3 ⟨157198259⟩ (by decide +native) hsel
  obtain ⟨_, _, h101⟩ := weth9ReachLowerArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨304⟩ 1 h101 (fun j hj => weth9LowerArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `totalSupply()` body (pc 381): lower arm index 2. -/
theorem weth9ReachTotalSupply {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 2)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨381⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨404098525⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x18 0x16 0x0d 0xdd ⟨404098525⟩ (by decide +native) hsel
  obtain ⟨_, _, h101⟩ := weth9ReachLowerArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨381⟩ 2 h101 (fun j hj => weth9LowerArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `transferFrom(address,address,uint256)` decode entry (pc 420): lower arm index 3. -/
theorem weth9ReachTransferFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 3)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨420⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨599290589⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x23 0xb8 0x72 0xdd ⟨599290589⟩ (by decide +native) hsel
  obtain ⟨_, _, h101⟩ := weth9ReachLowerArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨420⟩ 3 h101 (fun j hj => weth9LowerArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

/-- Reach `withdraw(uint256)` decode entry (pc 487): lower arm index 4. -/
theorem weth9ReachWithdraw {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 4)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨487⟩
      [weth9SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : weth9SelWord I = ⟨773487949⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x2e 0x1a 0x7d 0x4d ⟨773487949⟩ (by decide +native) hsel
  obtain ⟨_, _, h101⟩ := weth9ReachLowerArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize (by rw [hsw]; decide +native)
  exact RD.dispatchTo ⟨487⟩ 4 h101 (fun j hj => weth9LowerArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; decide +native)
    (by rw [hsw]; decide +native) (by jump_dest) (by decide +native) (by simp)

end Benchmarks.WETH9
