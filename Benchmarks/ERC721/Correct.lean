import Benchmarks.ERC721.Bytecode
import Benchmarks.ERC721.Constructor
import Benchmarks.ERC721.Spec
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# ERC721 — top-level correctness **scaffold**

Routing skeleton for `erc721Correct : runtimeEquivalence …`, mirroring
`Examples/ERC20/Correct.lean` / `Examples/Ballot/Correct.lean`: `by_cases` on `callvalue = 0`,
`size ≥ 4`, then each of the seven selectors, dispatching to that function's body obligation, with
the shared revert paths.

**Every leaf is a `sorry`** — the work-list:
* one `erc721<Fn>Body` per interface function (7), each to be discharged by a `…BodyCore` lemma in
  its own `Benchmarks/ERC721/<Fn>.lean` (decode → Solm body → EVM trace → connect);
* the three revert obligations (`erc721NonPayable`, `erc721ShortRevert`, `erc721NoDispatch`).

⚠️ **Dispatcher: binary search (shared with `Ballot`).**  solc emits a `GT`-pivot dispatcher for
these 7 selectors — at pc 30 `DUP1; PUSH4 0x6352211e; GT; PUSH2 0x58; JUMPI` splits low/high, each
half a normal linear `EQ`-arm chain. This needs the **same binary-search-dispatch driver** being
built for Ballot (`RD.gt` + `RD.selectorSplit*`); reuse it here. Until it lands, the body
obligations fold reachability in. See `Examples/Ballot/HANDOFF.md §2`.

Dispatch structure (read off the bytecode):
- pivot `0x6352211e`; taken (`selWord < pivot`) → low group at JUMPDEST 88 → arms at pc **89**;
  not taken → high group arms at pc **41**.

| selector | function | body PC | group |
|---|---|---|---|
| `0x081812fc` | `getApproved(uint256)`                 | `126` (0x7e)  | low |
| `0x095ea7b3` | `approve(address,uint256)`             | `195` (0xc3)  | low |
| `0x23b872dd` | `transferFrom(address,address,uint256)`| `216` (0xd8)  | low |
| `0x6352211e` | `ownerOf(uint256)`                     | `235` (0xeb)  | high |
| `0x70a08231` | `balanceOf(address)`                   | `254` (0xfe)  | high |
| `0xa22cb465` | `setApprovalForAll(address,bool)`      | `287` (0x11f) | high |
| `0xe985e9c5` | `isApprovedForAll(address,address)`    | `356` (0x164) | high |
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC721

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev erc721SelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop := (sel == I.calldata.extract 0 4) = true

/-- ERC721's seven selectors, in `erc721Contract.transitions` (dispatch) order. -/
def erc721SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩  -- approve
  | 1 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩  -- balanceOf
  | 2 => ⟨#[0x08, 0x18, 0x12, 0xfc]⟩  -- getApproved
  | 3 => ⟨#[0xe9, 0x85, 0xe9, 0xc5]⟩  -- isApprovedForAll
  | 4 => ⟨#[0x63, 0x52, 0x21, 0x1e]⟩  -- ownerOf
  | 5 => ⟨#[0xa2, 0x2c, 0xb4, 0x65]⟩  -- setApprovalForAll
  | _ => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩  -- transferFrom

/-! ## Per-function body obligations (one `…BodyCore` per `Benchmarks/ERC721/<Fn>.lean`, TODO) -/

/-- `approve(address,uint256)` body (pc 195) refines its transition. -/
theorem erc721ApproveBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-- `balanceOf(address)` body (pc 254) refines its transition. -/
theorem erc721BalanceOfBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-- `getApproved(uint256)` getter body (pc 126) refines its transition. -/
theorem erc721GetApprovedBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x08, 0x18, 0x12, 0xfc]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-- `isApprovedForAll(address,address)` getter body (pc 356) refines its transition. -/
theorem erc721IsApprovedForAllBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xe9, 0x85, 0xe9, 0xc5]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-- `ownerOf(uint256)` body (pc 235) refines its transition. -/
theorem erc721OwnerOfBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x63, 0x52, 0x21, 0x1e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-- `setApprovalForAll(address,bool)` body (pc 287) refines its transition. -/
theorem erc721SetApprovalForAllBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xa2, 0x2c, 0xb4, 0x65]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-- `transferFrom(address,address,uint256)` body (pc 216) refines its transition. -/
theorem erc721TransferFromBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-! ## Revert obligations -/

/-- `callvalue ≠ 0` ⇒ both sides revert (non-payable global guard). -/
theorem erc721NonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-- Calldata shorter than a selector (`size < 4`) ⇒ the size guard reverts before dispatch. -/
theorem erc721ShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-- `size ≥ 4` but no selector matches ⇒ `dispatchMsg = none` and the EVM falls through to revert. -/
theorem erc721NoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = erc721Bytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 7 → (erc721SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor erc721Config erc721Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  sorry

/-! ## Top-level theorem — drive the dispatcher, route each body to its correctness -/

/-- The deployed ERC721 runtime bytecode refines the Solm specification, for every initial state. -/
theorem erc721Correct : runtimeEquivalence erc721Config erc721Bytecode erc721Contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm
      hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
      · exact erc721ApproveBody hcode hsize hperm hwv h0 hAccounts
      · by_cases h1 : selIs I ⟨#[0x70, 0xa0, 0x82, 0x31]⟩
        · exact erc721BalanceOfBody hcode hsize hperm hwv h1 hAccounts
        · by_cases h2 : selIs I ⟨#[0x08, 0x18, 0x12, 0xfc]⟩
          · exact erc721GetApprovedBody hcode hsize hperm hwv h2 hAccounts
          · by_cases h3 : selIs I ⟨#[0xe9, 0x85, 0xe9, 0xc5]⟩
            · exact erc721IsApprovedForAllBody hcode hsize hperm hwv h3 hAccounts
            · by_cases h4 : selIs I ⟨#[0x63, 0x52, 0x21, 0x1e]⟩
              · exact erc721OwnerOfBody hcode hsize hperm hwv h4 hAccounts
              · by_cases h5 : selIs I ⟨#[0xa2, 0x2c, 0xb4, 0x65]⟩
                · exact erc721SetApprovalForAllBody hcode hsize hperm hwv h5 hAccounts
                · by_cases h6 : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩
                  · exact erc721TransferFromBody hcode hsize hperm hwv h6 hAccounts
                  · -- size ≥ 4 but no selector matches
                    refine erc721NoDispatch hcode hsize hperm hwv ?_
                    intro i hi
                    interval_cases i
                    · simpa [selIs, erc721SelBytes] using h0
                    · simpa [selIs, erc721SelBytes] using h1
                    · simpa [selIs, erc721SelBytes] using h2
                    · simpa [selIs, erc721SelBytes] using h3
                    · simpa [selIs, erc721SelBytes] using h4
                    · simpa [selIs, erc721SelBytes] using h5
                    · simpa [selIs, erc721SelBytes] using h6
    · exact erc721ShortRevert hcode hsize hperm hwv (by omega)
  · exact erc721NonPayable hcode hwv

theorem erc721ContractCorrect :
    contractEquivalence erc721Config erc721CreationBytecode erc721Bytecode erc721Contract :=
  contractEquivalence.intro erc721ConstructorCorrect erc721Correct

end ERC721
