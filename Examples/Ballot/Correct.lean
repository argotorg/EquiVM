import Examples.Ballot.Bytecode
import Examples.Ballot.Spec
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# Ballot — top-level correctness **scaffold**

This is the routing skeleton for `ballotCorrect : runtimeEquivalence!?! …`.  It mirrors
`Examples/ERC20/Correct.lean`: `by_cases` on `callvalue = 0`, `size ≥ 4`, then each of the eight
selectors, dispatching to that function's body obligation, with the shared revert paths.

**Every leaf is a `sorry`** — the obligations below are the work-list:

* one `ballot<Fn>Body` per interface function (8), each to be discharged by a `…BodyCore` lemma in
  its own `Examples/Ballot/<Fn>.lean` (decode → Solm body → EVM trace → connect), exactly as the
  ERC20 example splits per function;
* the three revert obligations (`ballotNonPayable`, `ballotShortRevert`, `ballotNoDispatch`).

⚠️ **Dispatcher shape.**  Unlike ERC20's *linear* selector dispatcher (`DUP1; PUSH4; EQ; PUSH2;
JUMPI` arms, driven by `solcDispatchReachBody`/`nthArmPc`), solc emits a **binary-search**
dispatcher for Ballot's 8 selectors (a `GT`-pivot tree: at pc 36 `DUP1; PUSH4 0x609ff1bd; GT;
PUSH2 0x58; JUMPI` splits the low/high halves).  The generic `Reach`/`Solc` dispatch driver does
**not** yet cover this, so the body obligations fold reachability in (rather than taking an
`hreach` cursor).  A reusable `RD`-level binary-search-dispatch driver is a **LIBRARY CANDIDATE**
(proposed `Reasoning/Solc.lean` or `Reasoning/Reach.lean`); once it exists, refactor each
`ballot<Fn>Body` to take the dispatcher-reached cursor like `erc20<Fn>Body`.

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

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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

/-! ## Per-function body obligations (one `…BodyCore` per `Examples/Ballot/<Fn>.lean`, TODO) -/

/-- `vote(uint256)` body (pc 137) refines its transition. -/
theorem ballotVoteBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x01, 0x21, 0xb9, 0x3f]⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- `proposals(uint256)` getter body (pc 158) refines its transition. -/
theorem ballotProposalsBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- `chairperson()` getter body (pc 203) refines its transition. -/
theorem ballotChairpersonBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x2e, 0x41, 0x76, 0xcf]⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- `delegate(address)` body (pc 245) refines its transition. -/
theorem ballotDelegateBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- `winningProposal()` body (pc 264) refines its transition.  `public`, so this body is the shared
    routine reused by `winnerName`'s internal call (the `Reuse` pattern). -/
theorem ballotWinningProposalBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- `giveRightToVote(address)` body (pc 286) refines its transition. -/
theorem ballotGiveRightToVoteBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- `voters(address)` getter body (pc 305) refines its transition. -/
theorem ballotVotersBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xa3, 0xec, 0x13, 0x8d]⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- `winnerName()` body (pc 417) refines its transition (calls `winningProposal` internally). -/
theorem ballotWinnerNameBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xe2, 0xba, 0x53, 0xf0]⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-! ## Revert obligations -/

/-- `callvalue ≠ 0` ⇒ both sides revert (non-payable global guard). -/
theorem ballotNonPayable {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- Calldata shorter than a selector (`size < 4`) ⇒ the size guard reverts before dispatch. -/
theorem ballotShortRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-- `size ≥ 4` but no selector matches ⇒ `dispatchMsg = none` and the EVM falls through to revert. -/
theorem ballotNoDispatch {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 8 → (ballotSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  sorry

/-! ## Top-level theorem — drive the dispatcher, route each body to its correctness -/

/-- The deployed Ballot runtime bytecode refines the Solm specification, for every initial state. -/
theorem ballotCorrect : runtimeEquivalence!?! ballotConfig ballotBytecode ballotContract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize hperm => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · -- callvalue = 0, size ≥ 4: dispatch on the selector
      by_cases h0 : selIs I ⟨#[0x01, 0x21, 0xb9, 0x3f]⟩
      · exact ballotVoteBody hcode hsize hperm hwv h0
      · by_cases h1 : selIs I ⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩
        · exact ballotProposalsBody hcode hsize hperm hwv h1
        · by_cases h2 : selIs I ⟨#[0x2e, 0x41, 0x76, 0xcf]⟩
          · exact ballotChairpersonBody hcode hsize hperm hwv h2
          · by_cases h3 : selIs I ⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩
            · exact ballotDelegateBody hcode hsize hperm hwv h3
            · by_cases h4 : selIs I ⟨#[0x60, 0x9f, 0xf1, 0xbd]⟩
              · exact ballotWinningProposalBody hcode hsize hperm hwv h4
              · by_cases h5 : selIs I ⟨#[0x9e, 0x7b, 0x8d, 0x61]⟩
                · exact ballotGiveRightToVoteBody hcode hsize hperm hwv h5
                · by_cases h6 : selIs I ⟨#[0xa3, 0xec, 0x13, 0x8d]⟩
                  · exact ballotVotersBody hcode hsize hperm hwv h6
                  · by_cases h7 : selIs I ⟨#[0xe2, 0xba, 0x53, 0xf0]⟩
                    · exact ballotWinnerNameBody hcode hsize hperm hwv h7
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
