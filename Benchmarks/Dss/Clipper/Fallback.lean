import Benchmarks.Dss.Clipper.Dispatch

/-!
# MakerDAO/Sky DSS Clipper fallback and global-revert scaffolds
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

macro "clipper_decode" : tactic =>
  `(tactic|
    (rw [clipperDecodeBeforeFirstPatch _ (by assumption) _ (by native_decide)]
     native_decide))

theorem clipperSplitNotTaken {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc next selWord pivot tgt : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 pc (selWord :: rest) mem aw rdata acc k C)
    (hdup : decode code pc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc pc) = some (.Push .PUSH4, some (pivot, 4)))
    (hgt : decode code (selArmEqPc pc) = some (.GT, .none))
    (hop : Operation.POp.PUSH2 ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc pc) = some (.Push .PUSH2, some (tgt, 2)))
    (hjumpi : decode code (selArmJumpiPc pc 2) = some (.JUMPI, .none))
    (hb : UInt256.gt pivot selWord = ⟨0⟩) (hnext : selArmNextPc pc 2 = next)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 next (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) := by
  rw [← hnext]
  exact h.selectorSplitNotTaken hdup hpush4 hgt hop hpushT hjumpi hb hov

theorem clipperSplitTaken {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc selWord pivot tgt : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 pc (selWord :: rest) mem aw rdata acc k C)
    (hdup : decode code pc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc pc) = some (.Push .PUSH4, some (pivot, 4)))
    (hgt : decode code (selArmEqPc pc) = some (.GT, .none))
    (hop : Operation.POp.PUSH2 ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc pc) = some (.Push .PUSH2, some (tgt, 2)))
    (hjumpi : decode code (selArmJumpiPc pc 2) = some (.JUMPI, .none))
    (hb : UInt256.gt pivot selWord ≠ ⟨0⟩) (hjd : (D_J code 0).contains tgt = true)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 tgt (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) :=
  h.selectorSplitTaken hdup hpush4 hgt hop hpushT hjumpi hb hjd hov

theorem clipperArmNotTaken {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc next selWord sel tgt : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 pc (selWord :: rest) mem aw rdata acc k C)
    (hdup : decode code pc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc pc) = some (.Push .PUSH4, some (sel, 4)))
    (heq : decode code (selArmEqPc pc) = some (.EQ, .none))
    (hop : Operation.POp.PUSH2 ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc pc) = some (.Push .PUSH2, some (tgt, 2)))
    (hjumpi : decode code (selArmJumpiPc pc 2) = some (.JUMPI, .none))
    (hb : UInt256.eq sel selWord = ⟨0⟩) (hnext : selArmNextPc pc 2 = next)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 next (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) := by
  rw [← hnext]
  exact h.selectorArmNotTaken hdup hpush4 heq hop hpushT hjumpi hb hov

theorem clipperArmTaken {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc selWord sel tgt : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 pc (selWord :: rest) mem aw rdata acc k C)
    (hdup : decode code pc = some (.DUP1, .none))
    (hpush4 : decode code (selArmPush4Pc pc) = some (.Push .PUSH4, some (sel, 4)))
    (heq : decode code (selArmEqPc pc) = some (.EQ, .none))
    (hop : Operation.POp.PUSH2 ≠ .PUSH0)
    (hpushT : decode code (selArmPushTgtPc pc) = some (.Push .PUSH2, some (tgt, 2)))
    (hjumpi : decode code (selArmJumpiPc pc 2) = some (.JUMPI, .none))
    (hb : UInt256.eq sel selWord ≠ ⟨0⟩) (hjd : (D_J code 0).contains tgt = true)
    (hov : rest.length + 3 ≤ 1024) :
    RD code ee g s0 tgt (selWord :: rest) mem aw rdata acc (k + 5) (C + 22) :=
  h.selectorArmTaken hdup hpush4 heq hop hpushT hjumpi hb hjd hov

theorem clipperFallbackRevertAt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code ee g s0 (⟨463⟩ : UInt256) stk mem aw rdata acc k C)
    (hov : stk.length + 2 ≤ 1024) :
    RDrev code g s0 := by
  have h464 := h.jumpdest
    (by
        change decode code (⟨463⟩ : UInt256) = some (.JUMPDEST, .none)
        clipper_decode)
    (by omega)
  exact RD.uniswapPush1Dup1Revert0 h464
    (by
        change decode code ((⟨463⟩ : UInt256) + ⟨1⟩) =
          some (.Push .PUSH1, some (⟨0⟩, 1))
        clipper_decode)
    (by
        change decode code ((⟨463⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2) =
          some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code ((⟨463⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
          some (.REVERT, .none)
        clipper_decode)
    hov

theorem clipperJumpFallbackRevert {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hpush : decode code pc = some (.Push .PUSH2, some (⟨463⟩, 2)))
    (hjump : decode code (pc + UInt256.ofNat 3) = some (.JUMP, .none))
    (hov : stk.length + 2 ≤ 1024) :
    RDrev code g s0 := by
  have h463 := h.push2 ⟨463⟩ hpush (by omega)
    |>.jump hjump
      (clipperJumpDestBeforeFirstPatch v hpatch (⟨463⟩ : UInt256) (by native_decide))
      (by omega)
  exact clipperFallbackRevertAt v hpatch h463 hov

theorem clipperBodyReverts_nonPayable (v : ClipperImmutables) (t : TransitionDecl)
    (ht : t ∈ (contract v).transitions) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl
  all_goals exact bodyReverts_nonPayable h

theorem clipperX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨0⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨2⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨4⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨5⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨6⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨7⟩ : UInt256) (by native_decide)];
        native_decide)
  have h12 := h0.push2 ⟨16⟩
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨8⟩ : UInt256) (by native_decide)];
        native_decide)
    (by simp only [List.length]; omega)
    |>.jumpiNT
      (by
          change decode code (⟨11⟩ : UInt256) = some (.JUMPI, .none)
          rw [clipperDecodeBeforeFirstPatch v hpatch (⟨11⟩ : UInt256) (by native_decide)]
          native_decide)
      (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h12
    (by
        change decode code (⟨12⟩ : UInt256) =
          some (.Push .PUSH1, some (⟨0⟩, 1))
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨12⟩ : UInt256) (by native_decide)]
        native_decide)
    (by
        change decode code (⟨14⟩ : UInt256) = some (.DUP1, .none)
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨14⟩ : UInt256) (by native_decide)]
        native_decide)
    (by
        change decode code (⟨15⟩ : UInt256) = some (.REVERT, .none)
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨15⟩ : UInt256) (by native_decide)]
        native_decide)
    (by simp only [List.length]; omega)

theorem clipperX_short {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨0⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨2⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨4⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨5⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨6⟩ : UInt256) (by native_decide)];
        native_decide)
    (by rw [clipperDecodeBeforeFirstPatch v hpatch (⟨7⟩ : UInt256) (by native_decide)];
        native_decide)
  obtain ⟨_, _, h18⟩ := solcGuardCallvalueZero
    (ctgt := (⟨16⟩ : UInt256)) (opC := .PUSH2) (wC := 2) h0 hwv
    (by decide)
    (by
        change decode code (⟨8⟩ : UInt256) =
          some (.Push .PUSH2, some (⟨16⟩, 2))
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨8⟩ : UInt256) (by native_decide)]
        native_decide)
    (by
        change decode code (⟨11⟩ : UInt256) = some (.JUMPI, .none)
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨11⟩ : UInt256) (by native_decide)]
        native_decide)
    (by
        change decode code (⟨16⟩ : UInt256) = some (.JUMPDEST, .none)
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨16⟩ : UInt256) (by native_decide)]
        native_decide)
    (by
        rw [show ((⟨16⟩ : UInt256) + ⟨1⟩) = (⟨17⟩ : UInt256) from by native_decide]
        change decode code (⟨17⟩ : UInt256) = some (.POP, .none)
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨17⟩ : UInt256) (by native_decide)]
        native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨16⟩ : UInt256) (by native_decide))
  have h463 := h18
    |>.push1 ⟨4⟩
      (by
          change decode code (⟨18⟩ : UInt256) =
            some (.Push .PUSH1, some (⟨4⟩, 1))
          rw [clipperDecodeBeforeFirstPatch v hpatch (⟨18⟩ : UInt256) (by native_decide)]
          native_decide)
      (by simp only [List.length]; omega)
    |>.calldatasize
      (by
          change decode code (⟨20⟩ : UInt256) = some (.CALLDATASIZE, .none)
          rw [clipperDecodeBeforeFirstPatch v hpatch (⟨20⟩ : UInt256) (by native_decide)]
          native_decide)
      (by simp only [List.length]; omega)
    |>.lt
      (by
          change decode code (⟨21⟩ : UInt256) = some (.LT, .none)
          rw [clipperDecodeBeforeFirstPatch v hpatch (⟨21⟩ : UInt256) (by native_decide)]
          native_decide)
      (by simp only [List.length]; omega)
    |>.push2 ⟨463⟩
      (by
          change decode code (⟨22⟩ : UInt256) =
            some (.Push .PUSH2, some (⟨463⟩, 2))
          rw [clipperDecodeBeforeFirstPatch v hpatch (⟨22⟩ : UInt256) (by native_decide)]
          native_decide)
      (by simp only [List.length]; omega)
    |>.jumpiT
      (by
          change decode code (⟨25⟩ : UInt256) = some (.JUMPI, .none)
          rw [clipperDecodeBeforeFirstPatch v hpatch (⟨25⟩ : UInt256) (by native_decide)]
          native_decide)
      (lt_four_ne_zero_of_lt hsz)
      (clipperJumpDestBeforeFirstPatch v hpatch (⟨463⟩ : UInt256) (by native_decide))
      (by simp only [List.length]; omega)
  have h464 := h463.jumpdest
    (by
        change decode code (⟨463⟩ : UInt256) = some (.JUMPDEST, .none)
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨463⟩ : UInt256) (by native_decide)]
        native_decide)
    (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h464
    (by
        rw [show ((⟨463⟩ : UInt256) + ⟨1⟩) = (⟨464⟩ : UInt256) from by native_decide]
        change decode code (⟨464⟩ : UInt256) =
          some (.Push .PUSH1, some (⟨0⟩, 1))
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨464⟩ : UInt256) (by native_decide)]
        native_decide)
    (by
        rw [show ((⟨463⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2) =
          (⟨466⟩ : UInt256) from by native_decide]
        change decode code (⟨466⟩ : UInt256) = some (.DUP1, .none)
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨466⟩ : UInt256) (by native_decide)]
        native_decide)
    (by
        rw [show ((⟨463⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
          (⟨467⟩ : UInt256) from by native_decide]
        change decode code (⟨467⟩ : UInt256) = some (.REVERT, .none)
        rw [clipperDecodeBeforeFirstPatch v hpatch (⟨467⟩ : UInt256) (by native_decide)]
        native_decide)
    (by simp only [List.length]; omega)

theorem clipperReachRoot {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨32⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  simpa [clipperSelWord, solcSelectorWord] using
    (solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (code := code)
      (bodyPc := (⟨18⟩ : UInt256)) (loadPc := (⟨26⟩ : UInt256))
      (firstPc := (⟨32⟩ : UInt256)) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := (⟨463⟩ : UInt256)) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by clipper_decode) (by clipper_decode) (by clipper_decode)
      (by clipper_decode) (by clipper_decode) (by clipper_decode)
      (by decide)
      (by
          change decode code (⟨8⟩ : UInt256) = some (.Push .PUSH2, some (⟨16⟩, 2))
          clipper_decode)
      (by
          change decode code ((⟨8⟩ : UInt256) + UInt256.ofNat (2 + 1)) =
            some (.JUMPI, .none)
          clipper_decode)
      (by
          change decode code (⟨16⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by
          change decode code ((⟨16⟩ : UInt256) + ⟨1⟩) = some (.POP, .none)
          clipper_decode)
      (clipperJumpDestBeforeFirstPatch v hpatch (⟨16⟩ : UInt256) (by native_decide))
      (by native_decide)
      (by
          change decode code (⟨18⟩ : UInt256) =
            some (.Push .PUSH1, some (⟨4⟩, 1))
          clipper_decode)
      (by
          change decode code ((⟨18⟩ : UInt256) + UInt256.ofNat 2) =
            some (.CALLDATASIZE, .none)
          clipper_decode)
      (by
          change decode code ((⟨18⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩) =
            some (.LT, .none)
          clipper_decode)
      (by decide)
      (by
          change decode code ((⟨18⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
            some (.Push .PUSH2, some (⟨463⟩, 2))
          clipper_decode)
      (by
          change decode code
            ((⟨18⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat (2 + 1)) =
              some (.JUMPI, .none)
          clipper_decode)
      (by native_decide)
      (by
          change decode code (⟨26⟩ : UInt256) =
            some (.Push .PUSH1, some (⟨0⟩, 1))
          clipper_decode)
      (by
          change decode code ((⟨26⟩ : UInt256) + UInt256.ofNat 2) =
            some (.CALLDATALOAD, .none)
          clipper_decode)
      (by
          change decode code ((⟨26⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩) =
            some (.Push .PUSH1, some (⟨224⟩, 1))
          clipper_decode)
      (by
          change decode code
            ((⟨26⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) =
              some (.SHR, .none)
          clipper_decode)
      (by native_decide))

theorem clipperNoMatchGroupARevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (v : ClipperImmutables) (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hzero : ∀ i, i < 29 → UInt256.eq (clipperSelNat i) (clipperSelWord ee) = ⟨0⟩)
    (h65 : RD code ee g s0 (⟨65⟩ : UInt256) [clipperSelWord ee] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h76 := clipperArmNotTaken (pc := (⟨65⟩ : UInt256)) (next := (⟨76⟩ : UInt256))
    (sel := clipperSelNat 12) (tgt := (⟨1349⟩ : UInt256)) h65
    (by
        change decode code (⟨65⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨65⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 12, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨65⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨65⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1349⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨65⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 12 (by omega)) (by native_decide) (by simp)
  have h87 := clipperArmNotTaken (pc := (⟨76⟩ : UInt256)) (next := (⟨87⟩ : UInt256))
    (sel := clipperSelNat 14) (tgt := (⟨1357⟩ : UInt256)) h76
    (by
        change decode code (⟨76⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨76⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 14, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨76⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨76⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1357⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨76⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 14 (by omega)) (by native_decide) (by simp)
  have h98 := clipperArmNotTaken (pc := (⟨87⟩ : UInt256)) (next := (⟨98⟩ : UInt256))
    (sel := clipperSelNat 10) (tgt := (⟨1365⟩ : UInt256)) h87
    (by
        change decode code (⟨87⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨87⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 10, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨87⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨87⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1365⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨87⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 10 (by omega)) (by native_decide) (by simp)
  have h109 := clipperArmNotTaken (pc := (⟨98⟩ : UInt256)) (next := (⟨109⟩ : UInt256))
    (sel := clipperSelNat 16) (tgt := (⟨1409⟩ : UInt256)) h98
    (by
        change decode code (⟨98⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨98⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 16, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨98⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨98⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1409⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨98⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 16 (by omega)) (by native_decide) (by simp)
  exact clipperJumpFallbackRevert v hpatch h109
    (by
        change decode code (⟨109⟩ : UInt256) = some (.Push .PUSH2, some (⟨463⟩, 2))
        clipper_decode)
    (by
        change decode code ((⟨109⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
        clipper_decode)
    (by simp)

theorem clipperNoMatchGroupBRevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (v : ClipperImmutables) (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hzero : ∀ i, i < 29 → UInt256.eq (clipperSelNat i) (clipperSelWord ee) = ⟨0⟩)
    (h114 : RD code ee g s0 (⟨114⟩ : UInt256) [clipperSelWord ee] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h125 := clipperArmNotTaken (pc := (⟨114⟩ : UInt256)) (next := (⟨125⟩ : UInt256))
    (sel := clipperSelNat 3) (tgt := (⟨1258⟩ : UInt256)) h114
    (by
        change decode code (⟨114⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨114⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 3, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨114⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨114⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1258⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨114⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 3 (by omega)) (by native_decide) (by simp)
  have h136 := clipperArmNotTaken (pc := (⟨125⟩ : UInt256)) (next := (⟨136⟩ : UInt256))
    (sel := clipperSelNat 4) (tgt := (⟨1295⟩ : UInt256)) h125
    (by
        change decode code (⟨125⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨125⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 4, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨125⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨125⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1295⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨125⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 4 (by omega)) (by native_decide) (by simp)
  have h147 := clipperArmNotTaken (pc := (⟨136⟩ : UInt256)) (next := (⟨147⟩ : UInt256))
    (sel := clipperSelNat 27) (tgt := (⟨1303⟩ : UInt256)) h136
    (by
        change decode code (⟨136⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨136⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 27, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨136⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨136⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1303⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨136⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 27 (by omega)) (by native_decide) (by simp)
  have h158 := clipperArmNotTaken (pc := (⟨147⟩ : UInt256)) (next := (⟨158⟩ : UInt256))
    (sel := clipperSelNat 8) (tgt := (⟨1341⟩ : UInt256)) h147
    (by
        change decode code (⟨147⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨147⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 8, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨147⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨147⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1341⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨147⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 8 (by omega)) (by native_decide) (by simp)
  exact clipperJumpFallbackRevert v hpatch h158
    (by
        change decode code (⟨158⟩ : UInt256) = some (.Push .PUSH2, some (⟨463⟩, 2))
        clipper_decode)
    (by
        change decode code ((⟨158⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
        clipper_decode)
    (by simp)

theorem clipperNoMatchGroupCRevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (v : ClipperImmutables) (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hzero : ∀ i, i < 29 → UInt256.eq (clipperSelNat i) (clipperSelWord ee) = ⟨0⟩)
    (h174 : RD code ee g s0 (⟨174⟩ : UInt256) [clipperSelWord ee] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h185 := clipperArmNotTaken (pc := (⟨174⟩ : UInt256)) (next := (⟨185⟩ : UInt256))
    (sel := clipperSelNat 13) (tgt := (⟨1057⟩ : UInt256)) h174
    (by
        change decode code (⟨174⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨174⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 13, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨174⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨174⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1057⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨174⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 13 (by omega)) (by native_decide) (by simp)
  have h196 := clipperArmNotTaken (pc := (⟨185⟩ : UInt256)) (next := (⟨196⟩ : UInt256))
    (sel := clipperSelNat 2) (tgt := (⟨1115⟩ : UInt256)) h185
    (by
        change decode code (⟨185⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨185⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 2, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨185⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨185⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1115⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨185⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 2 (by omega)) (by native_decide) (by simp)
  have h207 := clipperArmNotTaken (pc := (⟨196⟩ : UInt256)) (next := (⟨207⟩ : UInt256))
    (sel := clipperSelNat 7) (tgt := (⟨1123⟩ : UInt256)) h196
    (by
        change decode code (⟨196⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨196⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 7, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨196⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨196⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1123⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨196⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 7 (by omega)) (by native_decide) (by simp)
  have h218 := clipperArmNotTaken (pc := (⟨207⟩ : UInt256)) (next := (⟨218⟩ : UInt256))
    (sel := clipperSelNat 18) (tgt := (⟨1161⟩ : UInt256)) h207
    (by
        change decode code (⟨207⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨207⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 18, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨207⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨207⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨1161⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨207⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 18 (by omega)) (by native_decide) (by simp)
  exact clipperJumpFallbackRevert v hpatch h218
    (by
        change decode code (⟨218⟩ : UInt256) = some (.Push .PUSH2, some (⟨463⟩, 2))
        clipper_decode)
    (by
        change decode code ((⟨218⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
        clipper_decode)
    (by simp)

theorem clipperNoMatchGroupDRevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (v : ClipperImmutables) (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hzero : ∀ i, i < 29 → UInt256.eq (clipperSelNat i) (clipperSelWord ee) = ⟨0⟩)
    (h223 : RD code ee g s0 (⟨223⟩ : UInt256) [clipperSelWord ee] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h234 := clipperArmNotTaken (pc := (⟨223⟩ : UInt256)) (next := (⟨234⟩ : UInt256))
    (sel := clipperSelNat 20) (tgt := (⟨875⟩ : UInt256)) h223
    (by
        change decode code (⟨223⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨223⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 20, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨223⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨223⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨875⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨223⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 20 (by omega)) (by native_decide) (by simp)
  have h245 := clipperArmNotTaken (pc := (⟨234⟩ : UInt256)) (next := (⟨245⟩ : UInt256))
    (sel := clipperSelNat 0) (tgt := (⟨883⟩ : UInt256)) h234
    (by
        change decode code (⟨234⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨234⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 0, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨234⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨234⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨883⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨234⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 0 (by omega)) (by native_decide) (by simp)
  have h256 := clipperArmNotTaken (pc := (⟨245⟩ : UInt256)) (next := (⟨256⟩ : UInt256))
    (sel := clipperSelNat 22) (tgt := (⟨912⟩ : UInt256)) h245
    (by
        change decode code (⟨245⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨245⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 22, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨245⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨245⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨912⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨245⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 22 (by omega)) (by native_decide) (by simp)
  exact clipperJumpFallbackRevert v hpatch h256
    (by
        change decode code (⟨256⟩ : UInt256) = some (.Push .PUSH2, some (⟨463⟩, 2))
        clipper_decode)
    (by
        change decode code ((⟨256⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
        clipper_decode)
    (by simp)

theorem clipperNoMatchGroupERevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (v : ClipperImmutables) (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hzero : ∀ i, i < 29 → UInt256.eq (clipperSelNat i) (clipperSelWord ee) = ⟨0⟩)
    (h283 : RD code ee g s0 (⟨283⟩ : UInt256) [clipperSelWord ee] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h294 := clipperArmNotTaken (pc := (⟨283⟩ : UInt256)) (next := (⟨294⟩ : UInt256))
    (sel := clipperSelNat 6) (tgt := (⟨752⟩ : UInt256)) h283
    (by
        change decode code (⟨283⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨283⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 6, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨283⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨283⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨752⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨283⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 6 (by omega)) (by native_decide) (by simp)
  have h305 := clipperArmNotTaken (pc := (⟨294⟩ : UInt256)) (next := (⟨305⟩ : UInt256))
    (sel := clipperSelNat 11) (tgt := (⟨760⟩ : UInt256)) h294
    (by
        change decode code (⟨294⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨294⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 11, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨294⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨294⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨760⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨294⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 11 (by omega)) (by native_decide) (by simp)
  have h316 := clipperArmNotTaken (pc := (⟨305⟩ : UInt256)) (next := (⟨316⟩ : UInt256))
    (sel := clipperSelNat 26) (tgt := (⟨829⟩ : UInt256)) h305
    (by
        change decode code (⟨305⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨305⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 26, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨305⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨305⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨829⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨305⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 26 (by omega)) (by native_decide) (by simp)
  have h327 := clipperArmNotTaken (pc := (⟨316⟩ : UInt256)) (next := (⟨327⟩ : UInt256))
    (sel := clipperSelNat 17) (tgt := (⟨837⟩ : UInt256)) h316
    (by
        change decode code (⟨316⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨316⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 17, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨316⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨316⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨837⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨316⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 17 (by omega)) (by native_decide) (by simp)
  exact clipperJumpFallbackRevert v hpatch h327
    (by
        change decode code (⟨327⟩ : UInt256) = some (.Push .PUSH2, some (⟨463⟩, 2))
        clipper_decode)
    (by
        change decode code ((⟨327⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
        clipper_decode)
    (by simp)

theorem clipperNoMatchGroupFRevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (v : ClipperImmutables) (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hzero : ∀ i, i < 29 → UInt256.eq (clipperSelNat i) (clipperSelWord ee) = ⟨0⟩)
    (h332 : RD code ee g s0 (⟨332⟩ : UInt256) [clipperSelWord ee] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h343 := clipperArmNotTaken (pc := (⟨332⟩ : UInt256)) (next := (⟨343⟩ : UInt256))
    (sel := clipperSelNat 9) (tgt := (⟨673⟩ : UInt256)) h332
    (by
        change decode code (⟨332⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨332⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 9, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨332⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨332⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨673⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨332⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 9 (by omega)) (by native_decide) (by simp)
  have h354 := clipperArmNotTaken (pc := (⟨343⟩ : UInt256)) (next := (⟨354⟩ : UInt256))
    (sel := clipperSelNat 19) (tgt := (⟨708⟩ : UInt256)) h343
    (by
        change decode code (⟨343⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨343⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 19, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨343⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨343⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨708⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨343⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 19 (by omega)) (by native_decide) (by simp)
  have h365 := clipperArmNotTaken (pc := (⟨354⟩ : UInt256)) (next := (⟨365⟩ : UInt256))
    (sel := clipperSelNat 25) (tgt := (⟨744⟩ : UInt256)) h354
    (by
        change decode code (⟨354⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨354⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 25, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨354⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨354⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨744⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨354⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 25 (by omega)) (by native_decide) (by simp)
  exact clipperJumpFallbackRevert v hpatch h365
    (by
        change decode code (⟨365⟩ : UInt256) = some (.Push .PUSH2, some (⟨463⟩, 2))
        clipper_decode)
    (by
        change decode code ((⟨365⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
        clipper_decode)
    (by simp)

theorem clipperNoMatchGroupGRevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (v : ClipperImmutables) (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hzero : ∀ i, i < 29 → UInt256.eq (clipperSelNat i) (clipperSelWord ee) = ⟨0⟩)
    (h381 : RD code ee g s0 (⟨381⟩ : UInt256) [clipperSelWord ee] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h392 := clipperArmNotTaken (pc := (⟨381⟩ : UInt256)) (next := (⟨392⟩ : UInt256))
    (sel := clipperSelNat 21) (tgt := (⟨592⟩ : UInt256)) h381
    (by
        change decode code (⟨381⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨381⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 21, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨381⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨381⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨592⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨381⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 21 (by omega)) (by native_decide) (by simp)
  have h403 := clipperArmNotTaken (pc := (⟨392⟩ : UInt256)) (next := (⟨403⟩ : UInt256))
    (sel := clipperSelNat 1) (tgt := (⟨600⟩ : UInt256)) h392
    (by
        change decode code (⟨392⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨392⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 1, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨392⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨392⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨600⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨392⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 1 (by omega)) (by native_decide) (by simp)
  have h414 := clipperArmNotTaken (pc := (⟨403⟩ : UInt256)) (next := (⟨414⟩ : UInt256))
    (sel := clipperSelNat 28) (tgt := (⟨608⟩ : UInt256)) h403
    (by
        change decode code (⟨403⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨403⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 28, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨403⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨403⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨608⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨403⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 28 (by omega)) (by native_decide) (by simp)
  have h425 := clipperArmNotTaken (pc := (⟨414⟩ : UInt256)) (next := (⟨425⟩ : UInt256))
    (sel := clipperSelNat 23) (tgt := (⟨637⟩ : UInt256)) h414
    (by
        change decode code (⟨414⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨414⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 23, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨414⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨414⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨637⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨414⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 23 (by omega)) (by native_decide) (by simp)
  exact clipperJumpFallbackRevert v hpatch h425
    (by
        change decode code (⟨425⟩ : UInt256) = some (.Push .PUSH2, some (⟨463⟩, 2))
        clipper_decode)
    (by
        change decode code ((⟨425⟩ : UInt256) + UInt256.ofNat 3) = some (.JUMP, .none)
        clipper_decode)
    (by simp)

theorem clipperNoMatchGroupHRevert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (v : ClipperImmutables) (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hzero : ∀ i, i < 29 → UInt256.eq (clipperSelNat i) (clipperSelWord ee) = ⟨0⟩)
    (h430 : RD code ee g s0 (⟨430⟩ : UInt256) [clipperSelWord ee] mem aw rdata acc k C) :
    RDrev code g s0 := by
  have h441 := clipperArmNotTaken (pc := (⟨430⟩ : UInt256)) (next := (⟨441⟩ : UInt256))
    (sel := clipperSelNat 5) (tgt := (⟨468⟩ : UInt256)) h430
    (by
        change decode code (⟨430⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨430⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 5, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨430⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨430⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨468⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨430⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 5 (by omega)) (by native_decide) (by simp)
  have h452 := clipperArmNotTaken (pc := (⟨441⟩ : UInt256)) (next := (⟨452⟩ : UInt256))
    (sel := clipperSelNat 24) (tgt := (⟨494⟩ : UInt256)) h441
    (by
        change decode code (⟨441⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨441⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 24, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨441⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨441⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨494⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨441⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 24 (by omega)) (by native_decide) (by simp)
  have h463 := clipperArmNotTaken (pc := (⟨452⟩ : UInt256)) (next := (⟨463⟩ : UInt256))
    (sel := clipperSelNat 15) (tgt := (⟨504⟩ : UInt256)) h452
    (by
        change decode code (⟨452⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨452⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 15, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨452⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨452⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨504⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨452⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (hzero 15 (by omega)) (by native_decide) (by simp)
  exact clipperFallbackRevertAt v hpatch h463 (by simp)

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem clipperNonPayable (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (clipperX_callvalue_ne (g := Sat256.ofUInt256 g) v hpatch hcode hwv).reEquivElim
    hcode fun _ _ hrev => by
      by_cases hdisp : dispatchMsg (contract v) I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ (contract v).transitions := by
          rw [dispatchMsg_eq_dispatchList (contract v) I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode (config v).abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (clipperBodyReverts_nonPayable v t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- `size < 4` or no selector matches: no Solm dispatch and EVM fallthrough reverts. -/
theorem clipperNoDispatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 29 → (clipperSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · have hzero : ∀ i, i < 29 →
        UInt256.eq (clipperSelNat i) (clipperSelWord I) = ⟨0⟩ := by
      intro i hi
      rw [clipperSelectorEq I hsz i hi, hnm i hi]
      rfl
    have hrev : RDrev code (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
      obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        v hpatch hcode hwv hsz hsize
      by_cases hroot :
          UInt256.gt (clipperSelNat 20) (clipperSelWord I) = ⟨0⟩
      · have h43 := clipperSplitNotTaken (pc := (⟨32⟩ : UInt256))
          (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
          (tgt := (⟨260⟩ : UInt256)) h32
          (by
              change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none)
              clipper_decode)
          (by
              change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
                some (.Push .PUSH4, some (clipperSelNat 20, 4))
              clipper_decode)
          (by
              change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none)
              clipper_decode)
          (by decide)
          (by
              change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
                some (.Push .PUSH2, some (⟨260⟩, 2))
              clipper_decode)
          (by
              change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) =
                some (.JUMPI, .none)
              clipper_decode)
          hroot (by native_decide) (by simp)
        by_cases h43pivot :
            UInt256.gt (clipperSelNat 3) (clipperSelWord I) = ⟨0⟩
        · have h54 := clipperSplitNotTaken (pc := (⟨43⟩ : UInt256))
            (next := (⟨54⟩ : UInt256)) (pivot := clipperSelNat 3)
            (tgt := (⟨162⟩ : UInt256)) h43
            (by
                change decode code (⟨43⟩ : UInt256) = some (.DUP1, .none)
                clipper_decode)
            (by
                change decode code (selArmPush4Pc (⟨43⟩ : UInt256)) =
                  some (.Push .PUSH4, some (clipperSelNat 3, 4))
                clipper_decode)
            (by
                change decode code (selArmEqPc (⟨43⟩ : UInt256)) = some (.GT, .none)
                clipper_decode)
            (by decide)
            (by
                change decode code (selArmPushTgtPc (⟨43⟩ : UInt256)) =
                  some (.Push .PUSH2, some (⟨162⟩, 2))
                clipper_decode)
            (by
                change decode code (selArmJumpiPc (⟨43⟩ : UInt256) 2) =
                  some (.JUMPI, .none)
                clipper_decode)
            h43pivot (by native_decide) (by simp)
          by_cases h54pivot :
              UInt256.gt (clipperSelNat 12) (clipperSelWord I) = ⟨0⟩
          · have h65 := clipperSplitNotTaken (pc := (⟨54⟩ : UInt256))
              (next := (⟨65⟩ : UInt256)) (pivot := clipperSelNat 12)
              (tgt := (⟨113⟩ : UInt256)) h54
              (by
                  change decode code (⟨54⟩ : UInt256) = some (.DUP1, .none)
                  clipper_decode)
              (by
                  change decode code (selArmPush4Pc (⟨54⟩ : UInt256)) =
                    some (.Push .PUSH4, some (clipperSelNat 12, 4))
                  clipper_decode)
              (by
                  change decode code (selArmEqPc (⟨54⟩ : UInt256)) =
                    some (.GT, .none)
                  clipper_decode)
              (by decide)
              (by
                  change decode code (selArmPushTgtPc (⟨54⟩ : UInt256)) =
                    some (.Push .PUSH2, some (⟨113⟩, 2))
                  clipper_decode)
              (by
                  change decode code (selArmJumpiPc (⟨54⟩ : UInt256) 2) =
                    some (.JUMPI, .none)
                  clipper_decode)
              h54pivot (by native_decide) (by simp)
            exact clipperNoMatchGroupARevert v hpatch hzero h65
          · have h113 := clipperSplitTaken (pc := (⟨54⟩ : UInt256))
              (pivot := clipperSelNat 12) (tgt := (⟨113⟩ : UInt256)) h54
              (by
                  change decode code (⟨54⟩ : UInt256) = some (.DUP1, .none)
                  clipper_decode)
              (by
                  change decode code (selArmPush4Pc (⟨54⟩ : UInt256)) =
                    some (.Push .PUSH4, some (clipperSelNat 12, 4))
                  clipper_decode)
              (by
                  change decode code (selArmEqPc (⟨54⟩ : UInt256)) =
                    some (.GT, .none)
                  clipper_decode)
              (by decide)
              (by
                  change decode code (selArmPushTgtPc (⟨54⟩ : UInt256)) =
                    some (.Push .PUSH2, some (⟨113⟩, 2))
                  clipper_decode)
              (by
                  change decode code (selArmJumpiPc (⟨54⟩ : UInt256) 2) =
                    some (.JUMPI, .none)
                  clipper_decode)
              h54pivot
              (clipperJumpDestBeforeFirstPatch v hpatch (⟨113⟩ : UInt256)
                (by native_decide))
              (by simp)
            have h114 := h113.jumpdest
              (by
                  change decode code (⟨113⟩ : UInt256) = some (.JUMPDEST, .none)
                  clipper_decode)
              (by simp)
            exact clipperNoMatchGroupBRevert v hpatch hzero h114
        · have h162 := clipperSplitTaken (pc := (⟨43⟩ : UInt256))
            (pivot := clipperSelNat 3) (tgt := (⟨162⟩ : UInt256)) h43
            (by
                change decode code (⟨43⟩ : UInt256) = some (.DUP1, .none)
                clipper_decode)
            (by
                change decode code (selArmPush4Pc (⟨43⟩ : UInt256)) =
                  some (.Push .PUSH4, some (clipperSelNat 3, 4))
                clipper_decode)
            (by
                change decode code (selArmEqPc (⟨43⟩ : UInt256)) = some (.GT, .none)
                clipper_decode)
            (by decide)
            (by
                change decode code (selArmPushTgtPc (⟨43⟩ : UInt256)) =
                  some (.Push .PUSH2, some (⟨162⟩, 2))
                clipper_decode)
            (by
                change decode code (selArmJumpiPc (⟨43⟩ : UInt256) 2) =
                  some (.JUMPI, .none)
                clipper_decode)
            h43pivot
            (clipperJumpDestBeforeFirstPatch v hpatch (⟨162⟩ : UInt256)
              (by native_decide))
            (by simp)
          have h163 := h162.jumpdest
            (by
                change decode code (⟨162⟩ : UInt256) = some (.JUMPDEST, .none)
                clipper_decode)
            (by simp)
          by_cases h163pivot :
              UInt256.gt (clipperSelNat 13) (clipperSelWord I) = ⟨0⟩
          · have h174 := clipperSplitNotTaken (pc := (⟨163⟩ : UInt256))
              (next := (⟨174⟩ : UInt256)) (pivot := clipperSelNat 13)
              (tgt := (⟨222⟩ : UInt256)) h163
              (by
                  change decode code (⟨163⟩ : UInt256) = some (.DUP1, .none)
                  clipper_decode)
              (by
                  change decode code (selArmPush4Pc (⟨163⟩ : UInt256)) =
                    some (.Push .PUSH4, some (clipperSelNat 13, 4))
                  clipper_decode)
              (by
                  change decode code (selArmEqPc (⟨163⟩ : UInt256)) =
                    some (.GT, .none)
                  clipper_decode)
              (by decide)
              (by
                  change decode code (selArmPushTgtPc (⟨163⟩ : UInt256)) =
                    some (.Push .PUSH2, some (⟨222⟩, 2))
                  clipper_decode)
              (by
                  change decode code (selArmJumpiPc (⟨163⟩ : UInt256) 2) =
                    some (.JUMPI, .none)
                  clipper_decode)
              h163pivot (by native_decide) (by simp)
            exact clipperNoMatchGroupCRevert v hpatch hzero h174
          · have h222 := clipperSplitTaken (pc := (⟨163⟩ : UInt256))
              (pivot := clipperSelNat 13) (tgt := (⟨222⟩ : UInt256)) h163
              (by
                  change decode code (⟨163⟩ : UInt256) = some (.DUP1, .none)
                  clipper_decode)
              (by
                  change decode code (selArmPush4Pc (⟨163⟩ : UInt256)) =
                    some (.Push .PUSH4, some (clipperSelNat 13, 4))
                  clipper_decode)
              (by
                  change decode code (selArmEqPc (⟨163⟩ : UInt256)) =
                    some (.GT, .none)
                  clipper_decode)
              (by decide)
              (by
                  change decode code (selArmPushTgtPc (⟨163⟩ : UInt256)) =
                    some (.Push .PUSH2, some (⟨222⟩, 2))
                  clipper_decode)
              (by
                  change decode code (selArmJumpiPc (⟨163⟩ : UInt256) 2) =
                    some (.JUMPI, .none)
                  clipper_decode)
              h163pivot
              (clipperJumpDestBeforeFirstPatch v hpatch (⟨222⟩ : UInt256)
                (by native_decide))
              (by simp)
            have h223 := h222.jumpdest
              (by
                  change decode code (⟨222⟩ : UInt256) = some (.JUMPDEST, .none)
                  clipper_decode)
              (by simp)
            exact clipperNoMatchGroupDRevert v hpatch hzero h223
      · have h260 := clipperSplitTaken (pc := (⟨32⟩ : UInt256))
          (pivot := clipperSelNat 20) (tgt := (⟨260⟩ : UInt256)) h32
          (by
              change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none)
              clipper_decode)
          (by
              change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
                some (.Push .PUSH4, some (clipperSelNat 20, 4))
              clipper_decode)
          (by
              change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none)
              clipper_decode)
          (by decide)
          (by
              change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
                some (.Push .PUSH2, some (⟨260⟩, 2))
              clipper_decode)
          (by
              change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) =
                some (.JUMPI, .none)
              clipper_decode)
          hroot
          (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256)
            (by native_decide))
          (by simp)
        have h261 := h260.jumpdest
          (by
              change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none)
              clipper_decode)
          (by simp)
        by_cases h261pivot :
            UInt256.gt (clipperSelNat 9) (clipperSelWord I) = ⟨0⟩
        · have h272 := clipperSplitNotTaken (pc := (⟨261⟩ : UInt256))
            (next := (⟨272⟩ : UInt256)) (pivot := clipperSelNat 9)
            (tgt := (⟨369⟩ : UInt256)) h261
            (by
                change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none)
                clipper_decode)
            (by
                change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
                  some (.Push .PUSH4, some (clipperSelNat 9, 4))
                clipper_decode)
            (by
                change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none)
                clipper_decode)
            (by decide)
            (by
                change decode code (selArmPushTgtPc (⟨261⟩ : UInt256)) =
                  some (.Push .PUSH2, some (⟨369⟩, 2))
                clipper_decode)
            (by
                change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) =
                  some (.JUMPI, .none)
                clipper_decode)
            h261pivot (by native_decide) (by simp)
          by_cases h272pivot :
              UInt256.gt (clipperSelNat 6) (clipperSelWord I) = ⟨0⟩
          · have h283 := clipperSplitNotTaken (pc := (⟨272⟩ : UInt256))
              (next := (⟨283⟩ : UInt256)) (pivot := clipperSelNat 6)
              (tgt := (⟨331⟩ : UInt256)) h272
              (by
                  change decode code (⟨272⟩ : UInt256) = some (.DUP1, .none)
                  clipper_decode)
              (by
                  change decode code (selArmPush4Pc (⟨272⟩ : UInt256)) =
                    some (.Push .PUSH4, some (clipperSelNat 6, 4))
                  clipper_decode)
              (by
                  change decode code (selArmEqPc (⟨272⟩ : UInt256)) =
                    some (.GT, .none)
                  clipper_decode)
              (by decide)
              (by
                  change decode code (selArmPushTgtPc (⟨272⟩ : UInt256)) =
                    some (.Push .PUSH2, some (⟨331⟩, 2))
                  clipper_decode)
              (by
                  change decode code (selArmJumpiPc (⟨272⟩ : UInt256) 2) =
                    some (.JUMPI, .none)
                  clipper_decode)
              h272pivot (by native_decide) (by simp)
            exact clipperNoMatchGroupERevert v hpatch hzero h283
          · have h331 := clipperSplitTaken (pc := (⟨272⟩ : UInt256))
              (pivot := clipperSelNat 6) (tgt := (⟨331⟩ : UInt256)) h272
              (by
                  change decode code (⟨272⟩ : UInt256) = some (.DUP1, .none)
                  clipper_decode)
              (by
                  change decode code (selArmPush4Pc (⟨272⟩ : UInt256)) =
                    some (.Push .PUSH4, some (clipperSelNat 6, 4))
                  clipper_decode)
              (by
                  change decode code (selArmEqPc (⟨272⟩ : UInt256)) =
                    some (.GT, .none)
                  clipper_decode)
              (by decide)
              (by
                  change decode code (selArmPushTgtPc (⟨272⟩ : UInt256)) =
                    some (.Push .PUSH2, some (⟨331⟩, 2))
                  clipper_decode)
              (by
                  change decode code (selArmJumpiPc (⟨272⟩ : UInt256) 2) =
                    some (.JUMPI, .none)
                  clipper_decode)
              h272pivot
              (clipperJumpDestBeforeFirstPatch v hpatch (⟨331⟩ : UInt256)
                (by native_decide))
              (by simp)
            have h332 := h331.jumpdest
              (by
                  change decode code (⟨331⟩ : UInt256) = some (.JUMPDEST, .none)
                  clipper_decode)
              (by simp)
            exact clipperNoMatchGroupFRevert v hpatch hzero h332
        · have h369 := clipperSplitTaken (pc := (⟨261⟩ : UInt256))
            (pivot := clipperSelNat 9) (tgt := (⟨369⟩ : UInt256)) h261
            (by
                change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none)
                clipper_decode)
            (by
                change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
                  some (.Push .PUSH4, some (clipperSelNat 9, 4))
                clipper_decode)
            (by
                change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none)
                clipper_decode)
            (by decide)
            (by
                change decode code (selArmPushTgtPc (⟨261⟩ : UInt256)) =
                  some (.Push .PUSH2, some (⟨369⟩, 2))
                clipper_decode)
            (by
                change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) =
                  some (.JUMPI, .none)
                clipper_decode)
            h261pivot
            (clipperJumpDestBeforeFirstPatch v hpatch (⟨369⟩ : UInt256)
              (by native_decide))
            (by simp)
          have h370 := h369.jumpdest
            (by
                change decode code (⟨369⟩ : UInt256) = some (.JUMPDEST, .none)
                clipper_decode)
            (by simp)
          by_cases h370pivot :
              UInt256.gt (clipperSelNat 21) (clipperSelWord I) = ⟨0⟩
          · have h381 := clipperSplitNotTaken (pc := (⟨370⟩ : UInt256))
              (next := (⟨381⟩ : UInt256)) (pivot := clipperSelNat 21)
              (tgt := (⟨429⟩ : UInt256)) h370
              (by
                  change decode code (⟨370⟩ : UInt256) = some (.DUP1, .none)
                  clipper_decode)
              (by
                  change decode code (selArmPush4Pc (⟨370⟩ : UInt256)) =
                    some (.Push .PUSH4, some (clipperSelNat 21, 4))
                  clipper_decode)
              (by
                  change decode code (selArmEqPc (⟨370⟩ : UInt256)) =
                    some (.GT, .none)
                  clipper_decode)
              (by decide)
              (by
                  change decode code (selArmPushTgtPc (⟨370⟩ : UInt256)) =
                    some (.Push .PUSH2, some (⟨429⟩, 2))
                  clipper_decode)
              (by
                  change decode code (selArmJumpiPc (⟨370⟩ : UInt256) 2) =
                    some (.JUMPI, .none)
                  clipper_decode)
              h370pivot (by native_decide) (by simp)
            exact clipperNoMatchGroupGRevert v hpatch hzero h381
          · have h429 := clipperSplitTaken (pc := (⟨370⟩ : UInt256))
              (pivot := clipperSelNat 21) (tgt := (⟨429⟩ : UInt256)) h370
              (by
                  change decode code (⟨370⟩ : UInt256) = some (.DUP1, .none)
                  clipper_decode)
              (by
                  change decode code (selArmPush4Pc (⟨370⟩ : UInt256)) =
                    some (.Push .PUSH4, some (clipperSelNat 21, 4))
                  clipper_decode)
              (by
                  change decode code (selArmEqPc (⟨370⟩ : UInt256)) =
                    some (.GT, .none)
                  clipper_decode)
              (by decide)
              (by
                  change decode code (selArmPushTgtPc (⟨370⟩ : UInt256)) =
                    some (.Push .PUSH2, some (⟨429⟩, 2))
                  clipper_decode)
              (by
                  change decode code (selArmJumpiPc (⟨370⟩ : UInt256) 2) =
                    some (.JUMPI, .none)
                  clipper_decode)
              h370pivot
              (clipperJumpDestBeforeFirstPatch v hpatch (⟨429⟩ : UInt256)
                (by native_decide))
              (by simp)
            have h430 := h429.jumpdest
              (by
                  change decode code (⟨429⟩ : UInt256) = some (.JUMPDEST, .none)
                  clipper_decode)
              (by simp)
            exact clipperNoMatchGroupHRevert v hpatch hzero h430
    exact hrev.reEquivNoDispatch hcode (clipperDispatch_none_nomatch v hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (clipperX_short (g := Sat256.ofUInt256 g) v hpatch hcode hwv hshort)
      |>.reEquivNoDispatch hcode (clipperDispatch_none_short v hshort)

end Benchmarks.Dss.Clipper
