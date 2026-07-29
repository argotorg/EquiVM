import Examples.Ballot.Bytecode
import Examples.Ballot.Spec
import Examples.Ballot.Vote
import Examples.Ballot.Chairperson
import Examples.Ballot.Proposals
import Examples.Ballot.Voters
import Examples.Ballot.GiveRightToVote
import Examples.Ballot.WinningProposal
import Examples.Ballot.WinnerName
import Examples.Ballot.DelegateComplete
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# Ballot — top-level correctness proof

This is the routing proof for `ballotCorrect : runtimeEquivalence …`.  It mirrors
`Examples/ERC20/Correct.lean`: `by_cases` on `callvalue = 0`, `size ≥ 4`, then each of the eight
selectors, dispatching to that function's body obligation, with the shared revert paths.

Each `ballot<Fn>Body` is discharged by a `…BodyCore` lemma in its own
`Examples/Ballot/<Fn>.lean` or delegate-specific support file, and the three shared revert
obligations are closed below.

⚠️ **Dispatcher shape.**  Unlike ERC20's *linear* selector dispatcher (`DUP1; PUSH4; EQ; PUSH2;
JUMPI` arms, driven by `solcDispatchReachBody`/`nthArmPc`), solc emits a **binary-search**
dispatcher for Ballot's 8 selectors (a `GT`-pivot tree: at pc 36 `DUP1; PUSH4 0x609ff1bd; GT;
PUSH2 0x58; JUMPI` splits the low/high halves).  `Reasoning.Solc` now provides the shared one-level
binary selector drivers; this file supplies only Ballot's concrete split/arm well-formedness facts
and selector-byte coupling.

Body entry PCs (dispatch targets), read off the bytecode disassembly:
| selector | function | body PC |
|---|---|---|
| `0x0121b93f` | `vote(uint256)`              | `137` (`0x89`) |
| `0x013cf08b` | `proposals(uint256)`         | `158` (`0x9e`) |
| `0x2e4176cf` | `chairperson()`              | `203` (`0xcb`) |
| `0x5c19a95c` | `delegate(address)`          | `245` (`0xf5`) |
| `0x609ff1bd` | `winningProposal()`          | `264` (`0x108`) |
| `0x9e7b8d61` | `giveRightToVote(address)`   | `286` (`0x11e`) |
| `0xa3ec138d` | `voters(address)`            | `305` (`0x131`) |
| `0xe2ba53f0` | `winnerName()`               | `417` (`0x1a1`) |
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Ballot

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev ballotSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop := (sel == I.calldata.extract 0 4) = true

/-- Ballot's eight function selectors, in `ballotContract.transitions` (dispatch) order. -/
def ballotSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x01, 0x21, 0xb9, 0x3f]⟩  -- vote
  | 1 => ⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩  -- proposals
  | 2 => ⟨#[0x2e, 0x41, 0x76, 0xcf]⟩  -- chairperson
  | 3 => ⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩  -- delegate
  | 4 => ⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩  -- winningProposal
  | 5 => ⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩  -- giveRightToVote
  | 6 => ⟨#[0xa3, 0xec, 0x13, 0x8d]⟩  -- voters
  | _ => ⟨#[0xe2, 0xba, 0x53, 0xf0]⟩  -- winnerName

/-! ## Binary-search dispatcher machinery -/

/-- Ballot's binary-search selector split begins after the standard solc selector load. -/
abbrev ballotSplitPc : UInt256 := ⟨30⟩
/-- The high selector group falls through from the split to pc 41. -/
abbrev ballotHighFirstArmPc : UInt256 := ⟨41⟩
/-- The low selector group is reached by a taken split jump to this `JUMPDEST`. -/
abbrev ballotLowJumpdestPc : UInt256 := ⟨88⟩
/-- The low selector group begins after the `JUMPDEST` at pc 88. -/
abbrev ballotLowFirstArmPc : UInt256 := ⟨89⟩

/-- Ballot's `DUP1; PUSH4 pivot; GT; PUSH2 low; JUMPI` split is well-formed. -/
theorem ballotSplitWellFormed : selectorSplitWellFormed ballotBytecode ballotSplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Ballot's high-half selector arms decode as `DUP1; PUSH4; EQ; PUSH2; JUMPI`. -/
theorem ballotHighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed ballotBytecode
      (nthArmPc ballotBytecode ballotHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Ballot's low-half selector arms decode as `DUP1; PUSH4; EQ; PUSH2; JUMPI`. -/
theorem ballotLowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed ballotBytecode
      (nthArmPc ballotBytecode ballotLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- If `calldata[0:4]` matches a selector byte literal, the EVM selector word is that literal. -/
theorem ballotSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ballotSelWord I = sel := by
  apply u256_inj
  dsimp [ballotSelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

/-- Low-half selector coupling (`EQ` outcome agrees with calldata byte comparison). -/
theorem ballotLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc j))
        (ballotSelWord I)
      = if (ballotSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

/-- High-half selector coupling (`EQ` outcome agrees with calldata byte comparison). -/
theorem ballotHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc j))
        (ballotSelWord I)
      = if (ballotSelBytes (j + 4) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

/-- Selector identification inside the low half. -/
theorem ballotLowMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size) (hsel : (ballotSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc j))
        (ballotSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc i))
        (ballotSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = ballotSelBytes i := (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [ballotLowArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [ballotLowArmEq I hsz i hi, hci]
    interval_cases i <;> decide

/-- Selector identification inside the high half. -/
theorem ballotHighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (ballotSelBytes (i + 4) == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc j))
        (ballotSelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc i))
        (ballotSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = ballotSelBytes (i + 4) :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [ballotHighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [ballotHighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

/-- A low-half selector makes the pivot `GT` branch jump to the low group. -/
theorem ballotPivotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size) (hsel : (ballotSelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat ballotBytecode ballotSplitPc) (ballotSelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : ballotSelWord I = armSelNat ballotBytecode ballotLowFirstArmPc :=
      ballotSelWord_eq_of_beq I hsz 0x01 0x21 0xb9 0x3f _ (by decide)
        (by simpa [ballotSelBytes] using hsel)
    rw [hword]; decide
  · have hword : ballotSelWord I =
        armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc 1) :=
      ballotSelWord_eq_of_beq I hsz 0x01 0x3c 0xf0 0x8b _ (by decide)
        (by simpa [ballotSelBytes] using hsel)
    rw [hword]; decide
  · have hword : ballotSelWord I =
        armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc 2) :=
      ballotSelWord_eq_of_beq I hsz 0x2e 0x41 0x76 0xcf _ (by decide)
        (by simpa [ballotSelBytes] using hsel)
    rw [hword]; decide
  · have hword : ballotSelWord I =
        armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc 3) :=
      ballotSelWord_eq_of_beq I hsz 0x5c 0x19 0xa9 0x5c _ (by decide)
        (by simpa [ballotSelBytes] using hsel)
    rw [hword]; decide

/-- A high-half selector makes the pivot `GT` branch fall through to the high group. -/
theorem ballotPivotNotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (ballotSelBytes (i + 4) == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat ballotBytecode ballotSplitPc) (ballotSelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : ballotSelWord I = armSelNat ballotBytecode ballotSplitPc :=
      ballotSelWord_eq_of_beq I hsz 0x60 0x9f 0xf1 0xbd _ (by decide)
        (by simpa [ballotSelBytes] using hsel)
    rw [hword]; decide
  · have hword : ballotSelWord I =
        armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc 1) :=
      ballotSelWord_eq_of_beq I hsz 0x9e 0x7b 0x8d 0x61 _ (by decide)
        (by simpa [ballotSelBytes] using hsel)
    rw [hword]; decide
  · have hword : ballotSelWord I =
        armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc 2) :=
      ballotSelWord_eq_of_beq I hsz 0xa3 0xec 0x13 0x8d _ (by decide)
        (by simpa [ballotSelBytes] using hsel)
    rw [hword]; decide
  · have hword : ballotSelWord I =
        armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc 3) :=
      ballotSelWord_eq_of_beq I hsz 0xe2 0xba 0x53 0xf0 _ (by decide)
        (by simpa [ballotSelBytes] using hsel)
    rw [hword]; decide

/-- Standard solc prologue/guards/selector-load, stopping at Ballot's pivot split. -/
theorem ballotReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ballotSplitPc
        [ballotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed ballotBytecode ballotSplitPc := by
    solc_dispatch_prefix
  simpa [ballotSelWord, solcSelectorWord] using
    (solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix (by jump_dest))

/-- Reach a body in Ballot's high selector half. -/
theorem ballotReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat ballotBytecode ballotSplitPc) (ballotSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc j))
        (ballotSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc i))
        (ballotSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J ballotBytecode 0).contains bodyPC = true)
    (hbody : armTgt ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [ballotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed ballotBytecode ballotSplitPc := by
    solc_dispatch_prefix
  simpa [ballotSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachHighBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := ballotBytecode) (splitPc := ballotSplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) ballotSplitWellFormed
      (by simpa [ballotSelWord, solcSelectorWord] using hpivot)
      (fun j hj => by
        simpa [ballotHighFirstArmPc, ballotSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          ballotHighArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [ballotSelWord, solcSelectorWord, ballotHighFirstArmPc, ballotSplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using heq0 j hj)
      (by
        simpa [ballotSelWord, solcSelectorWord, ballotHighFirstArmPc, ballotSplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using htake)
      hjd
      (by
        simpa [ballotHighFirstArmPc, ballotSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

/-- Reach a body in Ballot's low selector half. -/
theorem ballotReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat ballotBytecode ballotSplitPc) (ballotSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc j))
        (ballotSelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc i))
        (ballotSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J ballotBytecode 0).contains bodyPC = true)
    (hbody : armTgt ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [ballotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed ballotBytecode ballotSplitPc := by
    solc_dispatch_prefix
  simpa [ballotSelWord, solcSelectorWord] using
    (solcBinaryDispatchReachLowBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := ballotBytecode) (splitPc := ballotSplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) ballotSplitWellFormed
      (by simpa [ballotSelWord, solcSelectorWord] using hpivot) (by jump_dest) (by decide)
      (fun j hj => by
        simpa [ballotLowFirstArmPc, ballotLowJumpdestPc, ballotSplitPc, armTgt, pushAt,
          selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          ballotLowArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [ballotSelWord, solcSelectorWord, ballotLowFirstArmPc, ballotLowJumpdestPc,
          ballotSplitPc, armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          heq0 j hj)
      (by
        simpa [ballotSelWord, solcSelectorWord, ballotLowFirstArmPc, ballotLowJumpdestPc,
          ballotSplitPc, armTgt, pushAt, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using htake)
      hjd
      (by
        simpa [ballotLowFirstArmPc, ballotLowJumpdestPc, ballotSplitPc, armTgt, pushAt,
          selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

/-! ## Per-function body obligations (one `…BodyCore` per `Examples/Ballot/<Fn>.lean`, TODO) -/

/-- `vote(uint256)` body (pc 137) refines its transition. -/
theorem ballotVoteBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x01, 0x21, 0xb9, 0x3f]⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨137⟩ [ballotSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact ballotVoteBodyCore hcode hsize hperm hwv hsel hreach hAccounts

/-- `proposals(uint256)` getter body (pc 158) refines its transition. -/
theorem ballotProposalsBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨158⟩ [ballotSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact ballotProposalsBodyCore hcode hsize hwv hsel hreach hAccounts

/-- `chairperson()` getter body (pc 203) refines its transition. -/
theorem ballotChairpersonBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x2e, 0x41, 0x76, 0xcf]⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨203⟩ [ballotSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact ballotChairpersonBodyCore hcode hwv hsel hreach hAccounts

/-- `delegate(address)` body (pc 245) refines its transition. -/
theorem ballotDelegateBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨245⟩ [ballotSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact ballotDelegateBodyCoreComplete hcode hsize hperm hwv hsel hreach hAccounts

/-- `winningProposal()` body (pc 264) refines its transition.  `public`, so this body is the shared
    routine reused by `winnerName`'s internal call (the `Reuse` pattern). -/
theorem ballotWinningProposalBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨264⟩ [ballotSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact ballotWinningProposalBodyCore hcode hsize hwv hsel hreach hAccounts

/-- `giveRightToVote(address)` body (pc 286) refines its transition. -/
theorem ballotGiveRightToVoteBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨286⟩ [ballotSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact ballotGiveRightToVoteBodyCore hcode hsize hperm hwv hsel hreach hAccounts

/-- `voters(address)` getter body (pc 305) refines its transition. -/
theorem ballotVotersBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xa3, 0xec, 0x13, 0x8d]⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [ballotSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact ballotVotersBodyCore hcode hsize hwv hsel hreach hAccounts

/-- `winnerName()` body (pc 417) refines its transition (calls `winningProposal` internally). -/
theorem ballotWinnerNameBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xe2, 0xba, 0x53, 0xf0]⟩)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨417⟩ [ballotSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact ballotWinnerNameBodyCore hcode hsize hwv hsel hreach hAccounts

/-! ## Revert obligations -/

/-- No calldata shorter than four bytes can dispatch to a Ballot function. -/
theorem ballotDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg ballotContract cd = none := by
  rw [dispatchMsg_eq_dispatchList ballotContract cd (by rfl)]
  change dispatchList
    [voteTransition, proposalsGetter, chairpersonGetter, delegateTransition,
      winningProposalTransition, giveRightToVoteTransition, votersGetter, winnerNameTransition]
      cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, ballotVoteSelectorBytes]; rfl
    · rw [selectorOf, ballotProposalsSelectorBytes]; rfl
    · rw [selectorOf, ballotChairpersonSelectorBytes]; rfl
    · rw [selectorOf, ballotDelegateSelectorBytes]; rfl
    · rw [selectorOf, ballotWinningProposalSelectorBytes]; rfl
    · rw [selectorOf, ballotGiveRightToVoteSelectorBytes]; rfl
    · rw [selectorOf, ballotVotersSelectorBytes]; rfl
    · rw [selectorOf, ballotWinnerNameSelectorBytes]; rfl) h

/-- If all eight Ballot selectors miss, `dispatchMsg` returns `none`. -/
theorem ballotDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 8 → (ballotSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg ballotContract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [ballotContract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, ballotVoteSelectorBytes]; simpa [ballotSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, ballotProposalsSelectorBytes]; simpa [ballotSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, ballotChairpersonSelectorBytes]; simpa [ballotSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, ballotDelegateSelectorBytes]; simpa [ballotSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, ballotWinningProposalSelectorBytes]; simpa [ballotSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, ballotGiveRightToVoteSelectorBytes]
    simpa [ballotSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, ballotVotersSelectorBytes]; simpa [ballotSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, ballotWinnerNameSelectorBytes]; simpa [ballotSelBytes] using hnm 7 (by omega)

/-- Every Ballot transition body reverts when the non-payable guard sees non-zero callvalue. -/
theorem ballotBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ ballotContract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody ballotConfig ballotContract evm locals t.body .reverted := by
  simp [ballotContract] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-- EVM non-payable guard reverts when `callvalue ≠ 0`. -/
theorem ballotX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt ballotBytecode) (opC := solcGuardTgtOp ballotBytecode)
    (wC := solcGuardTgtWidth ballotBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- EVM calldata-size guard reverts when calldata is shorter than a selector. -/
theorem ballotX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt ballotBytecode) (opC := solcGuardTgtOp ballotBytecode)
    (wC := solcGuardTgtWidth ballotBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc ballotBytecode)
    (rtgt := solcCalldataRevertTgt ballotBytecode)
    (opR := solcCalldataRevertTgtOp ballotBytecode)
    (wR := solcCalldataRevertTgtWidth ballotBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

/-- With enough calldata for a selector but no selector match, Ballot's dispatcher reverts. -/
theorem ballotX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 8 → (ballotSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotLowFirstArmPc j))
        (ballotSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [ballotLowArmEq I hsz j hj, hnm j (by omega)]
    rfl
  have heqHigh0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat ballotBytecode (nthArmPc ballotBytecode ballotHighFirstArmPc j))
        (ballotSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [ballotHighArmEq I hsz j hj, hnm (j + 4) (by omega)]
    rfl
  obtain ⟨kS, CS, hsplit⟩ := ballotReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  by_cases hpivot : UInt256.gt (armSelNat ballotBytecode ballotSplitPc) (ballotSelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit ballotSplitWellFormed hpivot (by simp)
    have h85 := h41
      |>.selectorArmNotTakenAuto (ballotHighArmsWellFormed 0 (by omega))
          (heqHigh0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ballotHighArmsWellFormed 1 (by omega))
          (heqHigh0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ballotHighArmsWellFormed 2 (by omega))
          (heqHigh0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ballotHighArmsWellFormed 3 (by omega))
          (heqHigh0 3 (by omega)) (by simp)
    have h85' : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨85⟩
        [ballotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [ballotHighFirstArmPc, ballotSplitPc, nthArmPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h85
    obtain ⟨_, _, h85rd⟩ := h85'
    exact h85rd.revertStub (by decide) (by decide) (by decide) (by simp)
  · have h88 := RD.selectorSplitTakenAuto hsplit ballotSplitWellFormed hpivot (by jump_dest) (by simp)
    have h89 := h88.jumpdest (by decide) (by simp)
    have h133 := h89
      |>.selectorArmNotTakenAuto (ballotLowArmsWellFormed 0 (by omega))
          (heqLow0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ballotLowArmsWellFormed 1 (by omega))
          (heqLow0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ballotLowArmsWellFormed 2 (by omega))
          (heqLow0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ballotLowArmsWellFormed 3 (by omega))
          (heqLow0 3 (by omega)) (by simp)
    have h133' : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨133⟩
        [ballotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5 + 5, CS + 22 + 1 + 22 + 22 + 22 + 22, ?_⟩
      simpa [ballotLowFirstArmPc, ballotLowJumpdestPc, ballotSplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
        selArmPush4Pc] using h133
    obtain ⟨_, _, h133rd⟩ := h133'
    have h134 := h133rd.jumpdest (by decide) (by simp)
    exact h134.revertStub (by decide) (by decide) (by decide) (by simp)

/-- `callvalue ≠ 0` ⇒ both sides revert (non-payable global guard). -/
theorem ballotNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (ballotX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg ballotContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ ballotContract.transitions := by
          rw [dispatchMsg_eq_dispatchList ballotContract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (ballotBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than a selector (`size < 4`) ⇒ the size guard reverts before dispatch. -/
theorem ballotShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (ballotX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (ballotDispatch_none_short hsz)

/-- `size ≥ 4` but no selector matches ⇒ `dispatchMsg = none` and the EVM falls through to revert. -/
theorem ballotNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 8 → (ballotSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (ballotX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm).reEquivNoDispatch
      hcode (ballotDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (ballotX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch hcode
      (ballotDispatch_none_short hshort)

/-! ## Top-level theorem — drive the dispatcher, route each body to its correctness -/

/-- The deployed Ballot runtime bytecode refines the Solm specification, for every initial state. -/
theorem ballotCorrect : runtimeEquivalence ballotConfig ballotBytecode ballotContract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm
      hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · -- callvalue = 0, size ≥ 4: dispatch on the selector
      by_cases h0 : selIs I ⟨#[0x01, 0x21, 0xb9, 0x3f]⟩
      · exact ballotVoteBody hcode hsize hperm hwv h0
          (ballotReachLowBody 0 (by omega) ⟨137⟩ hcode hwv hsz hsize
            (ballotPivotTaken 0 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h0))
            (ballotLowMatches 0 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h0)).1
            (ballotLowMatches 0 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h0)).2
            (by jump_dest) (by decide)) hAccounts
      · by_cases h1 : selIs I ⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩
        · exact ballotProposalsBody hcode hsize hperm hwv h1
            (ballotReachLowBody 1 (by omega) ⟨158⟩ hcode hwv hsz hsize
              (ballotPivotTaken 1 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h1))
              (ballotLowMatches 1 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h1)).1
              (ballotLowMatches 1 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h1)).2
              (by jump_dest) (by decide)) hAccounts
        · by_cases h2 : selIs I ⟨#[0x2e, 0x41, 0x76, 0xcf]⟩
          · exact ballotChairpersonBody hcode hsize hperm hwv h2
              (ballotReachLowBody 2 (by omega) ⟨203⟩ hcode hwv hsz hsize
                (ballotPivotTaken 2 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h2))
                (ballotLowMatches 2 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h2)).1
                (ballotLowMatches 2 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h2)).2
                (by jump_dest) (by decide)) hAccounts
          · by_cases h3 : selIs I ⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩
            · exact ballotDelegateBody hcode hsize hperm hwv h3
                (ballotReachLowBody 3 (by omega) ⟨245⟩ hcode hwv hsz hsize
                  (ballotPivotTaken 3 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h3))
                  (ballotLowMatches 3 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h3)).1
                  (ballotLowMatches 3 (by omega) hsz (by simpa [selIs, ballotSelBytes] using h3)).2
                  (by jump_dest) (by decide)) hAccounts
            · by_cases h4 : selIs I ⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩
              · exact ballotWinningProposalBody hcode hsize hperm hwv h4
                  (ballotReachHighBody 0 (by omega) ⟨264⟩ hcode hwv hsz hsize
                    (ballotPivotNotTaken 0 (by omega) hsz
                      (by simpa [selIs, ballotSelBytes] using h4))
                    (ballotHighMatches 0 (by omega) hsz
                      (by simpa [selIs, ballotSelBytes] using h4)).1
                    (ballotHighMatches 0 (by omega) hsz
                      (by simpa [selIs, ballotSelBytes] using h4)).2
                    (by jump_dest) (by decide)) hAccounts
              · by_cases h5 : selIs I ⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩
                · exact ballotGiveRightToVoteBody hcode hsize hperm hwv h5
                    (ballotReachHighBody 1 (by omega) ⟨286⟩ hcode hwv hsz hsize
                      (ballotPivotNotTaken 1 (by omega) hsz
                        (by simpa [selIs, ballotSelBytes] using h5))
                      (ballotHighMatches 1 (by omega) hsz
                        (by simpa [selIs, ballotSelBytes] using h5)).1
                      (ballotHighMatches 1 (by omega) hsz
                        (by simpa [selIs, ballotSelBytes] using h5)).2
                      (by jump_dest) (by decide)) hAccounts
                · by_cases h6 : selIs I ⟨#[0xa3, 0xec, 0x13, 0x8d]⟩
                  · exact ballotVotersBody hcode hsize hperm hwv h6
                      (ballotReachHighBody 2 (by omega) ⟨305⟩ hcode hwv hsz hsize
                        (ballotPivotNotTaken 2 (by omega) hsz
                          (by simpa [selIs, ballotSelBytes] using h6))
                        (ballotHighMatches 2 (by omega) hsz
                          (by simpa [selIs, ballotSelBytes] using h6)).1
                        (ballotHighMatches 2 (by omega) hsz
                          (by simpa [selIs, ballotSelBytes] using h6)).2
                        (by jump_dest) (by decide)) hAccounts
                  · by_cases h7 : selIs I ⟨#[0xe2, 0xba, 0x53, 0xf0]⟩
                    · exact ballotWinnerNameBody hcode hsize hperm hwv h7
                        (ballotReachHighBody 3 (by omega) ⟨417⟩ hcode hwv hsz hsize
                          (ballotPivotNotTaken 3 (by omega) hsz
                            (by simpa [selIs, ballotSelBytes] using h7))
                          (ballotHighMatches 3 (by omega) hsz
                            (by simpa [selIs, ballotSelBytes] using h7)).1
                          (ballotHighMatches 3 (by omega) hsz
                            (by simpa [selIs, ballotSelBytes] using h7)).2
                          (by jump_dest) (by decide)) hAccounts
                    · -- size ≥ 4 but no selector matches
                      refine ballotNoDispatch hcode hsize hperm hwv ?_
                      intro i hi
                      interval_cases i
                      · simpa [selIs, ballotSelBytes] using h0
                      · simpa [selIs, ballotSelBytes] using h1
                      · simpa [selIs, ballotSelBytes] using h2
                      · simpa [selIs, ballotSelBytes] using h3
                      · simpa [selIs, ballotSelBytes] using h4
                      · simpa [selIs, ballotSelBytes] using h5
                      · simpa [selIs, ballotSelBytes] using h6
                      · simpa [selIs, ballotSelBytes] using h7
    · -- callvalue = 0, size < 4: size guard reverts before dispatch
      exact ballotShortRevert hcode hsize hperm hwv (by omega)
  · -- callvalue ≠ 0: non-payable revert
    exact ballotNonPayable hcode hwv

end Ballot
