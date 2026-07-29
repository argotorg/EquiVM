import Benchmarks.Xxx.SpecSyntax
import Solm.Semantics
import Solm.SolidityLayout

/-!
# Xxx spec assembly (TEMPLATE) — derived, not authored

Single-source flow: the contract is DEFINED by `SpecSyntax.lean`; this file only references it
and assembles what the surface syntax cannot carry — named handles for the proof files, the
storage layout, the external-call ABI, and the `Config`.  Nothing here restates the contract.

(Audited two-file flow instead: this file holds the hand-written AST — see
`Benchmarks/Dss/Pot/Spec.lean` — and `SpecSyntax.lean` proves `rfl`-equality against it.)
-/

open Solm ABI

namespace Benchmarks.Xxx

/-! ## The contract AST in Sol⁻ -/

def contract : ContractDecl := Syntax.contractSyntax

/-- Named handles in `contract.transitions` (selector) order — what the per-function proof
    files unfold.  All defeq projections; keep the index comments honest. -/
abbrev constructorDecl : ConstructorDecl := contract.ctor
abbrev setValueTransition : TransitionDecl := contract.transitions[0]!  -- setValue(uint256)
abbrev valueTransition : TransitionDecl := contract.transitions[1]!     -- value()

/-! ## Types shared with the proof files -/

def uint256Int : IntType := .uint ⟨256, by decide⟩

/-! ## Storage layout — the part that stays hand-written

Derivable only when the contract uses Solidity's standard layout; packing, nested
mapping→array→struct shapes, and compact strings need the per-contract cases below
(cf. `Examples/Ballot/Spec.lean`, `Benchmarks/WETH9/Spec.lean`). -/

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

-- TODO: match the deployed bytecode's slot assignment.
def storageLayoutRaw : EvaledStorageRef -> EVM.State -> Option StorageLoc
  | { base := "wards", steps := [.mindex a] }, _ => some (wordLoc (mapSlot (keyValueToWord a) ⟨0⟩))
  | { base := "value", steps := [] }, _ => some (wordLoc ⟨1⟩)
  | _, _ => none

def storageLayout : StorageLayout := solidityStorageLayout storageLayoutRaw

/-! ## Config -/

-- TODO for contracts with external calls: a real `ExternalCallABI` with the callee selectors
-- (cf. `Benchmarks/EAS/Attester/Spec.lean`); `abiDecodeMode` per compiler version.
def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.Xxx
