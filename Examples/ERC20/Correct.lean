import Examples.ERC20.Bytecode
import Examples.ERC20.Spec
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc

/-!
# ERC20 — correctness statement and dispatcher scaffold

Unlike `Truth`, `Pow`, and `Caller`, the full per-branch trace + storage-mutating body proofs are
not done yet.  `erc20Correct` is the target (still an axiom).  `erc20ReachTransfer` below is a
**scaffold**: it wires the generic solc-dispatcher building blocks
(`solcGuardPrologueRD → solcGuardCallvalueZero → solcCalldataOk → solcSelectorLoad`, then
`selectorArmNotTaken`/`selectorArmTaken`) into ERC20's concrete six-arm chain to reach a function
body entry.  The selector-identification EQ outcomes and the bodies are left as `sorry` — it exists
only to check the dispatch API composes (it does).
-/

open Solm Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC20

/-- The deployed runtime bytecode refines the Solm specification, for every initial state. -/
axiom erc20Correct :
    runtimeEquivalence!?! erc20Config erc20Bytecode erc20Contract

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev erc20SelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- **Dispatch scaffold (transfer branch).**  `cv = 0`, `calldatasize ≥ 4`: prologue → guards →
    selector load → skip approve/totalSupply/transferFrom/balanceOf → take transfer, reaching the
    transfer body entry (pc 274).  EQ outcomes (selector identification) left as `sorry`. -/
theorem erc20ReachTransfer {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩
        [erc20SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  -- prologue → pc 8, [isZero(cv), cv]
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- callvalue = 0 → pc 17, []
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero (ctgt := ⟨15⟩) (opC := .PUSH2) (wC := 2)
    h0 hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  -- calldatasize ≥ 4 → pc 25, []
  obtain ⟨_, _, h2⟩ := solcCalldataOk (selLoadTgt := ⟨96⟩) (opR := .PUSH2) (wR := 2)
    h1 hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- selector load → pc 30, [selWord]
  obtain ⟨_, _, h3⟩ := solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide) (by simp)
  -- skip approve (30 → 41)
  have h4 := RD.selectorArmNotTaken (selNat := ⟨0x095ea7b3⟩) (tgt := ⟨100⟩)
    (op := .PUSH2) (width := 2) h3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by sorry) (by simp)
  -- skip totalSupply (41 → 52)
  have h5 := RD.selectorArmNotTaken (selNat := ⟨0x18160ddd⟩) (tgt := ⟨148⟩)
    (op := .PUSH2) (width := 2) h4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by sorry) (by simp)
  -- skip transferFrom (52 → 63)
  have h6 := RD.selectorArmNotTaken (selNat := ⟨0x23b872dd⟩) (tgt := ⟨178⟩)
    (op := .PUSH2) (width := 2) h5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by sorry) (by simp)
  -- skip balanceOf (63 → 74)
  have h7 := RD.selectorArmNotTaken (selNat := ⟨0x70a08231⟩) (tgt := ⟨226⟩)
    (op := .PUSH2) (width := 2) h6 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by sorry) (by simp)
  -- take transfer (74 → 274)
  exact ⟨_, _, RD.selectorArmTaken (selNat := ⟨0xa9059cbb⟩) (tgt := ⟨274⟩) (op := .PUSH2) (width := 2)
    h7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by sorry)
    (by jump_dest) (by simp)⟩

end ERC20
