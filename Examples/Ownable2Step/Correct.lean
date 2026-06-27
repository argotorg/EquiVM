import Examples.Ownable2Step.Bytecode
import Examples.Ownable2Step.Spec
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
# Ownable2Step — top-level correctness **scaffold**

Routing skeleton for `ownableCorrect : runtimeEquivalence!?! …`, mirroring `Examples/ERC20/Correct.lean`.
solc emits a **linear** selector dispatcher (5 arms from pc 30), so — unlike Ballot/ERC721 — this
needs **no new machinery**: reuse the existing `solcDispatchReachBody`/`nthArmPc`/`selectorArm*`
driver verbatim (swap bytecode/selectors/PCs). `Examples/ERC20/Correct.lean` is the direct template.

**Every leaf is a `sorry`** — the work-list:
* one `ownable<Fn>Body` per function (5), each discharged by a `…BodyCore` in `Examples/Ownable2Step/<Fn>.lean`;
* the three revert obligations (`ownableNonPayable`, `ownableShortRevert`, `ownableNoDispatch`).

Dispatch arms (firstArmPc = 30), read off the bytecode:
| arm | selector | function | body PC |
|---|---|---|---|
| 0 | `0x715018a6` | `renounceOwnership()`         | `89`  |
| 1 | `0x79ba5097` | `acceptOwnership()`          | `99`  |
| 2 | `0x8da5cb5b` | `owner()`                    | `107` |
| 3 | `0xe30c3978` | `pendingOwner()`             | `147` |
| 4 | `0xf2fde38b` | `transferOwnership(address)` | `164` |
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Ownable2Step

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev ownableSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop := (sel == I.calldata.extract 0 4) = true

/-- The 5 selectors in `ownableContract.transitions` (dispatch) order. -/
def ownableSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩  -- owner
  | 1 => ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩  -- pendingOwner
  | 2 => ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩  -- transferOwnership
  | 3 => ⟨#[0x79, 0xba, 0x50, 0x97]⟩  -- acceptOwnership
  | _ => ⟨#[0x71, 0x50, 0x18, 0xa6]⟩  -- renounceOwnership

/-! ## Per-function body obligations (one `…BodyCore` per `Examples/Ownable2Step/<Fn>.lean`, TODO) -/

/-- `owner()` body (pc 107) refines its transition. -/
theorem ownableOwnerBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = ownableBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ownableConfig ownableContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

/-- `pendingOwner()` body (pc 147) refines its transition. -/
theorem ownablePendingOwnerBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = ownableBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ownableConfig ownableContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

/-- `transferOwnership(address)` body (pc 164) refines its transition. -/
theorem ownableTransferOwnershipBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = ownableBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ownableConfig ownableContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

/-- `acceptOwnership()` body (pc 99) refines its transition. -/
theorem ownableAcceptOwnershipBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = ownableBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x79, 0xba, 0x50, 0x97]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ownableConfig ownableContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

/-- `renounceOwnership()` body (pc 89) refines its transition. -/
theorem ownableRenounceOwnershipBody {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = ownableBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0x71, 0x50, 0x18, 0xa6]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ownableConfig ownableContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

/-! ## Revert obligations -/

/-- `callvalue ≠ 0` ⇒ both sides revert (non-payable global guard). -/
theorem ownableNonPayable {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = ownableBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor ownableConfig ownableContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

/-- Calldata shorter than a selector (`size < 4`) ⇒ the size guard reverts before dispatch. -/
theorem ownableShortRevert {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = ownableBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor ownableConfig ownableContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

/-- `size ≥ 4` but no selector matches ⇒ `dispatchMsg = none` and the EVM falls through to revert. -/
theorem ownableNoDispatch {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = ownableBytecode) (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 5 → (ownableSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor ownableConfig ownableContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  sorry

/-! ## Top-level theorem -/

/-- The deployed Ownable2Step runtime bytecode refines the Solm specification. -/
theorem ownableCorrect : runtimeEquivalence!?! ownableConfig ownableBytecode ownableContract := by
  refine ⟨fun cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm g A I hcode hsize hperm
      hAccounts _hOriginalAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩
      · exact ownableOwnerBody hcode hsize hperm hwv h0 hAccounts
      · by_cases h1 : selIs I ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩
        · exact ownablePendingOwnerBody hcode hsize hperm hwv h1 hAccounts
        · by_cases h2 : selIs I ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩
          · exact ownableTransferOwnershipBody hcode hsize hperm hwv h2 hAccounts
          · by_cases h3 : selIs I ⟨#[0x79, 0xba, 0x50, 0x97]⟩
            · exact ownableAcceptOwnershipBody hcode hsize hperm hwv h3 hAccounts
            · by_cases h4 : selIs I ⟨#[0x71, 0x50, 0x18, 0xa6]⟩
              · exact ownableRenounceOwnershipBody hcode hsize hperm hwv h4 hAccounts
              · refine ownableNoDispatch hcode hsize hperm hwv ?_
                intro i hi
                interval_cases i
                · simpa [selIs, ownableSelBytes] using h0
                · simpa [selIs, ownableSelBytes] using h1
                · simpa [selIs, ownableSelBytes] using h2
                · simpa [selIs, ownableSelBytes] using h3
                · simpa [selIs, ownableSelBytes] using h4
    · exact ownableShortRevert hcode hsize hperm hwv (by omega)
  · exact ownableNonPayable hcode hwv

end Ownable2Step
