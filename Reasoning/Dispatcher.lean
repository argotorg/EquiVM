import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody

/-!
# Dispatcher — one driver for the whole solc selector dispatcher

A solc external entry is: the free-pointer prologue, the callvalue guard, the calldata-size
guard, the selector load, and then a **selector tree**: zero or more `GT` pivot splits whose
leaves are linear chains of `EQ` arms, each chain ending in a revert.  `Reasoning.Solc` proves
the prologue and the one-level split; every contract with a deeper tree re-assembled the walk
from the primitives.  This file closes that gap:

* `SelTree` describes a dispatcher tree.  `SelTree.readAt` parses it off the bytecode (not
  trusted), `SelTree.check` validates it against the bytecode (a `Bool`, closed by
  `native_decide`), and `SelTree.lookup` is its semantics: the body pc a selector word reaches.
* `solcEntryCheck` validates the prologue through the selector load, for both selector-load
  generations (`PUSH0` and legacy `PUSH1 0`); `solcRootPc` is the tree's root pc.
* `RD.selTreeLookup` is the soundness theorem: a checked tree reaches `lookup`'s body pc, and
  reverts when `lookup` is `none`.  `solcDispatchReachArm` packages it from `initState`.
* The Solm side: `dispatchMsg_eq_some_of_table` / `dispatchMsg_none_of_table` from one
  selector table `contract.transitions.map selectorOf = sels`.
* `runtimeEquivalence_of_solcDispatcher` assembles the top-level theorem from per-selector
  body obligations (`SelectorBody`) and the checks above.

Everything the contract supplies is either a `native_decide`-closed check on its bytecode, the
selector table, or a body lemma; no dispatcher pcs, pivots, or arm indices are written by hand.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Reasoning.Reach

/-! ## Revert stubs -/

/-- The `revert(0,0)` stub at `pc`, in either generation: `PUSH1 0; DUP1; REVERT` (legacy) or
    `PUSH0; PUSH0; REVERT`. -/
def solcRevertStubB (code : ByteArray) (pc : UInt256) : Bool :=
  (decide (decode code pc = some (.Push .PUSH1, some (⟨0⟩, 1)))
    && (decide (decode code (pc + UInt256.ofNat 2) = some (.DUP1, .none))
    && decide (decode code (pc + UInt256.ofNat 2 + ⟨1⟩) = some (.REVERT, .none))))
  || (decide (decode code pc = some (.PUSH0, .none))
    && (decide (decode code (pc + ⟨1⟩) = some (.PUSH0, .none))
    && decide (decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))))

/-- A cursor at a checked revert stub reverts. -/
theorem RD.solcRevertStub {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hstub : solcRevertStubB code pc = true) (hov : stk.length + 2 ≤ 1024) :
    RDrev code g s0 := by
  simp only [solcRevertStubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hstub
  rcases hstub with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact RD.solcPush1Dup1Revert0 h h0 h1 h2 hov
  · exact RD.revertStub h h0 h1 h2 hov

/-! ## Selector trees -/

/-- How a linear arm chain ends when no arm matches. -/
inductive GroupTail where
  /-- The revert block follows the last arm inline: `JUMPDEST; <revert stub>`. -/
  | fall
  /-- `PUSHk revertPc; JUMP` follows the last arm; `JUMPDEST; <revert stub>` sits at `revertPc`. -/
  | jump
  deriving Repr, DecidableEq

/-- A solc selector dispatcher: `GT` pivot splits over linear `EQ` arm chains. -/
inductive SelTree where
  /-- Arms `(selector word, body pc)` in bytecode order, then the no-match tail. -/
  | group (arms : List (UInt256 × UInt256)) (tail : GroupTail)
  /-- `DUP1; PUSH4 pivot; GT; PUSHk low; JUMPI`: `sel < pivot` goes `low`, else falls to `high`. -/
  | split (pivot : UInt256) (low high : SelTree)
  deriving Repr

/-- The word solc compares selectors against: the big-endian value of the 4 selector bytes. -/
def selWordOf (s : ByteArray) : UInt256 := UInt256.ofNat (fromBytesBigEndian s.data.toList)

namespace SelTree

/-- First arm whose selector equals `w`. -/
def lookupArms : List (UInt256 × UInt256) → UInt256 → Option UInt256
  | [], _ => none
  | (s, b) :: rest, w => if s = w then some b else lookupArms rest w

/-- The body pc the dispatcher sends selector word `w` to (`none` = no match, revert). -/
def lookup : SelTree → UInt256 → Option UInt256
  | .group arms _, w => lookupArms arms w
  | .split pivot low high, w => if w.toNat < pivot.toNat then low.lookup w else high.lookup w

/-- Every arm selector word in the tree. -/
def selectors : SelTree → List UInt256
  | .group arms _ => arms.map Prod.fst
  | .split _ low high => low.selectors ++ high.selectors

/-! ### Bytecode checks

All checks are `Bool`s over `decode`, so a contract closes them with one `native_decide`. -/

/-- Arm at `pc`: `DUP1; PUSH4 s; EQ; PUSHk b; JUMPI`, with `b` a jump destination. -/
def armCheck (code : ByteArray) (pc s b : UInt256) : Bool :=
  decide (decode code pc = some (.DUP1, .none))
  && (decide (decode code (selArmPush4Pc pc) = some (.Push .PUSH4, some (s, 4)))
  && (decide (decode code (selArmEqPc pc) = some (.EQ, .none))
  && (decide (armTgtOp code pc ≠ .PUSH0)
  && (decide (decode code (selArmPushTgtPc pc)
        = some (.Push (armTgtOp code pc), some (armTgt code pc, armTgtWidth code pc)))
  && (decide (decode code (selArmJumpiPc pc (armTgtWidth code pc)) = some (.JUMPI, .none))
  && (decide (armTgt code pc = b)
  && (D_J code 0).contains b))))))

/-- Arm chain starting at `pc`. -/
def armsCheck (code : ByteArray) : UInt256 → List (UInt256 × UInt256) → Bool
  | _, [] => true
  | pc, (s, b) :: rest =>
      armCheck code pc s b && armsCheck code (selArmNextPc pc (armTgtWidth code pc)) rest

/-- The pc after the last arm of a chain starting at `pc`. -/
def armsEnd (code : ByteArray) : UInt256 → List (UInt256 × UInt256) → UInt256
  | pc, [] => pc
  | pc, _ :: rest => armsEnd code (selArmNextPc pc (armTgtWidth code pc)) rest

/-- The no-match tail at `pc`. -/
def tailCheck (code : ByteArray) (pc : UInt256) : GroupTail → Bool
  | .fall => decide (decode code pc = some (.JUMPDEST, .none)) && solcRevertStubB code (pc + ⟨1⟩)
  | .jump =>
      decide ((pushAt code pc).1 ≠ .PUSH0)
      && (decide (decode code pc
            = some (.Push (pushAt code pc).1, some ((pushAt code pc).2.1, (pushAt code pc).2.2)))
      && (decide (decode code (pc + UInt256.ofNat (pushAt code pc).2.2.succ) = some (.JUMP, .none))
      && ((D_J code 0).contains (pushAt code pc).2.1
      && (decide (decode code (pushAt code pc).2.1 = some (.JUMPDEST, .none))
      && solcRevertStubB code ((pushAt code pc).2.1 + ⟨1⟩)))))

/-- Split at `pc`: `DUP1; PUSH4 pivot; GT; PUSHk low; JUMPI`, `low` a `JUMPDEST`. -/
def splitCheck (code : ByteArray) (pc pivot : UInt256) : Bool :=
  decide (decode code pc = some (.DUP1, .none))
  && (decide (decode code (selArmPush4Pc pc) = some (.Push .PUSH4, some (pivot, 4)))
  && (decide (decode code (selArmEqPc pc) = some (.GT, .none))
  && (decide (armTgtOp code pc ≠ .PUSH0)
  && (decide (decode code (selArmPushTgtPc pc)
        = some (.Push (armTgtOp code pc), some (armTgt code pc, armTgtWidth code pc)))
  && (decide (decode code (selArmJumpiPc pc (armTgtWidth code pc)) = some (.JUMPI, .none))
  && ((D_J code 0).contains (armTgt code pc)
  && decide (decode code (armTgt code pc) = some (.JUMPDEST, .none))))))))

/-- The whole tree matches the bytecode from `pc`. -/
def check (code : ByteArray) : SelTree → UInt256 → Bool
  | .group arms tail, pc => armsCheck code pc arms && tailCheck code (armsEnd code pc arms) tail
  | .split pivot low high, pc =>
      splitCheck code pc pivot
      && (low.check code (armTgt code pc + ⟨1⟩)
      && high.check code (selArmNextPc pc (armTgtWidth code pc)))

/-! ### Reading the tree off the bytecode (a convenience; `check` is what is trusted) -/

/-- Parse the dispatcher at `pc` (`fuel` bounds the recursion). -/
def read? (code : ByteArray) : ℕ → UInt256 → Option SelTree
  | 0, _ => none
  | fuel + 1, pc =>
    match decode code pc with
    | some (.DUP1, .none) =>
      match decode code (selArmPush4Pc pc) with
      | some (.Push .PUSH4, some (x, 4)) =>
        match decode code (selArmEqPc pc) with
        | some (.GT, .none) => do
            let low ← read? code fuel (armTgt code pc + ⟨1⟩)
            let high ← read? code fuel (selArmNextPc pc (armTgtWidth code pc))
            pure (.split x low high)
        | some (.EQ, .none) => do
            match ← read? code fuel (selArmNextPc pc (armTgtWidth code pc)) with
            | .group arms tail => pure (.group ((x, armTgt code pc) :: arms) tail)
            | .split .. => none
        | _ => none
      | _ => none
    | some (.JUMPDEST, .none) => some (.group [] .fall)
    | some (.Push _, some _) => some (.group [] .jump)
    | _ => none

/-- The dispatcher tree at `pc` (an empty falling group if parsing fails; `check` then fails). -/
def readAt (code : ByteArray) (pc : UInt256) : SelTree :=
  (read? code 4096 pc).getD (.group [] .fall)

/-! ### Lookup facts -/

theorem lookupArms_some_mem :
    ∀ {arms : List (UInt256 × UInt256)} {w b : UInt256},
      lookupArms arms w = some b → w ∈ arms.map Prod.fst
  | [], _, _, h => by simp [lookupArms] at h
  | (s, _) :: arms, w, b, h => by
      simp only [lookupArms] at h
      split at h
      · rename_i hsw
        simp [hsw]
      · exact List.mem_cons_of_mem _ (lookupArms_some_mem h)

/-- A selector word that reaches a body is one of the tree's arm selectors. -/
theorem lookup_some_mem :
    ∀ {t : SelTree} {w b : UInt256}, t.lookup w = some b → w ∈ t.selectors
  | .group _ _, _, _, h => lookupArms_some_mem h
  | .split _ low high, w, b, h => by
      simp only [lookup] at h
      split at h
      · exact List.mem_append_left _ (lookup_some_mem h)
      · exact List.mem_append_right _ (lookup_some_mem h)

theorem lookup_eq_none_of_not_mem {t : SelTree} {w : UInt256} (h : w ∉ t.selectors) :
    t.lookup w = none := by
  cases hl : t.lookup w with
  | none => rfl
  | some b => exact absurd (lookup_some_mem hl) h

end SelTree

/-! ## Soundness of `check` -/

theorem pushAt_of_decode {code : ByteArray} {pc v : UInt256} {op : Operation.POp} {w : ℕ}
    (h : decode code pc = some (.Push op, some (v, w))) : pushAt code pc = (op, v, w) := by
  simp [pushAt, h]

/-- A checked no-match tail reverts. -/
theorem RD.groupTailRevert {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ} {tail : GroupTail}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (htail : SelTree.tailCheck code pc tail = true) (hov : stk.length + 2 ≤ 1024) :
    RDrev code g s0 := by
  cases tail with
  | fall =>
      simp only [SelTree.tailCheck, Bool.and_eq_true, decide_eq_true_eq] at htail
      obtain ⟨hjd, hstub⟩ := htail
      exact RD.solcRevertStub (RD.jumpdest h hjd (by omega)) hstub hov
  | jump =>
      simp only [SelTree.tailCheck, Bool.and_eq_true, decide_eq_true_eq] at htail
      obtain ⟨hop, hpush, hjump, hjd, hdest, hstub⟩ := htail
      have rd1 := RD.pushConst h _ hop hpush (by omega)
      have rd2 := RD.jump rd1 hjump hjd (by omega)
      have rd3 := RD.jumpdest rd2 hdest (by omega)
      exact RD.solcRevertStub rd3 hstub hov

/-- Walking a checked arm chain: a matching arm reaches its body; no match reaches the chain end. -/
theorem RD.selArmsReach {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {w : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {rest : List UInt256}
    (hov : rest.length + 3 ≤ 1024) :
    ∀ (arms : List (UInt256 × UInt256)) {pc : UInt256} {k C : ℕ},
      SelTree.armsCheck code pc arms = true →
      RD code ee g s0 pc (w :: rest) mem aw rdata acc k C →
      (∀ b, SelTree.lookupArms arms w = some b →
        ∃ k' C', RD code ee g s0 b (w :: rest) mem aw rdata acc k' C')
      ∧ (SelTree.lookupArms arms w = none →
        ∃ k' C', RD code ee g s0 (SelTree.armsEnd code pc arms) (w :: rest) mem aw rdata acc k' C')
  | [], pc, k, C, _, h =>
      ⟨fun _ hb => by simp [SelTree.lookupArms] at hb, fun _ => ⟨k, C, h⟩⟩
  | (s, b) :: arms, pc, k, C, hchk, h => by
      simp only [SelTree.armsCheck, Bool.and_eq_true] at hchk
      obtain ⟨harm, hrest⟩ := hchk
      simp only [SelTree.armCheck, Bool.and_eq_true, decide_eq_true_eq] at harm
      obtain ⟨hdup, hpush4, heq, hop, hpushT, hjumpi, htgt, hjd⟩ := harm
      have hsel : armSelNat code pc = s := by
        simp [armSelNat, pushAt_of_decode hpush4]
      have hwf : armWellFormed code pc :=
        ⟨hdup, by rw [hsel]; exact hpush4, heq, hop, hpushT, hjumpi⟩
      by_cases hsw : s = w
      · have hb : UInt256.eq (armSelNat code pc) w ≠ ⟨0⟩ := by
          rw [hsel, hsw, u256_eq_refl]; exact one_ne_zero_uint
        have hjd' : (D_J code 0).contains (armTgt code pc) = true := by rw [htgt]; exact hjd
        have rd := RD.selectorArmTakenAuto h hwf hb hjd' hov
        rw [htgt] at rd
        refine ⟨fun b' hb' => ?_, fun hn => ?_⟩
        · simp only [SelTree.lookupArms, if_pos hsw, Option.some.injEq] at hb'
          subst hb'
          exact ⟨_, _, rd⟩
        · simp [SelTree.lookupArms, hsw] at hn
      · have hb : UInt256.eq (armSelNat code pc) w = ⟨0⟩ := by
          rw [hsel]; exact u256_eq_of_ne hsw
        have rd := RD.selectorArmNotTakenAuto h hwf hb hov
        have ih := RD.selArmsReach hov arms hrest rd
        simp only [SelTree.lookupArms, if_neg hsw, SelTree.armsEnd]
        exact ih

/-- **Soundness of the tree check.**  From the root cursor, a checked tree reaches the body
    `lookup` names for the selector word, and reverts when `lookup` is `none`. -/
theorem RD.selTreeLookup {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {w : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {rest : List UInt256}
    (hov : rest.length + 3 ≤ 1024) :
    ∀ (t : SelTree) {pc : UInt256} {k C : ℕ},
      t.check code pc = true →
      RD code ee g s0 pc (w :: rest) mem aw rdata acc k C →
      (∀ b, t.lookup w = some b → ∃ k' C', RD code ee g s0 b (w :: rest) mem aw rdata acc k' C')
      ∧ (t.lookup w = none → RDrev code g s0)
  | .group arms tail, pc, k, C, hchk, h => by
      simp only [SelTree.check, Bool.and_eq_true] at hchk
      obtain ⟨harms, htail⟩ := hchk
      obtain ⟨hsome, hnone⟩ := RD.selArmsReach hov arms harms h
      refine ⟨fun b hb => hsome b hb, fun hn => ?_⟩
      obtain ⟨k', C', rdEnd⟩ := hnone hn
      exact RD.groupTailRevert rdEnd htail (by simp only [List.length_cons]; omega)
  | .split pivot low high, pc, k, C, hchk, h => by
      simp only [SelTree.check, Bool.and_eq_true] at hchk
      obtain ⟨hsplit, hlow, hhigh⟩ := hchk
      simp only [SelTree.splitCheck, Bool.and_eq_true, decide_eq_true_eq] at hsplit
      obtain ⟨hdup, hpush4, hgt, hop, hpushT, hjumpi, hjd, hdest⟩ := hsplit
      have hsel : armSelNat code pc = pivot := by
        simp [armSelNat, pushAt_of_decode hpush4]
      have hwf : selectorSplitWellFormed code pc :=
        ⟨hdup, by rw [hsel]; exact hpush4, hgt, hop, hpushT, hjumpi⟩
      by_cases hlt : w.toNat < pivot.toNat
      · have hb : UInt256.gt (armSelNat code pc) w ≠ ⟨0⟩ := by
          rw [hsel, ugt_one hlt]; exact one_ne_zero_uint
        have rd := RD.selectorSplitTakenAuto h hwf hb hjd hov
        have rd' := RD.jumpdest rd hdest (by simp only [List.length_cons]; omega)
        have ih := RD.selTreeLookup hov low hlow rd'
        simp only [SelTree.lookup, if_pos hlt]
        exact ih
      · have hb : UInt256.gt (armSelNat code pc) w = ⟨0⟩ := by
          rw [hsel]; exact ugt_zero (by omega)
        have rd := RD.selectorSplitNotTakenAuto h hwf hb hov
        have ih := RD.selTreeLookup hov high hhigh rd
        simp only [SelTree.lookup, if_neg hlt]
        exact ih

/-! ## The external-entry prefix

Prologue, callvalue guard, calldata-size guard, and selector load, with every pc read off the
bytecode (`solcGuardTgt`, `solcDispatchBodyPc`, … from `Reasoning.Solc`).  The selector load is
`PUSH0; CALLDATALOAD; PUSH1 0xe0; SHR` or, in legacy solc, `PUSH1 0; CALLDATALOAD; PUSH1 0xe0;
SHR`; `solcRootPc` is the pc after it, where the selector tree starts. -/

/-- The selector load starts with `PUSH1 0` (legacy solc) rather than `PUSH0`. -/
def solcSelectorLoadLegacy (code : ByteArray) : Bool :=
  decide (decode code (solcSelectorLoadPc code) = some (.Push .PUSH1, some (⟨0⟩, 1)))

/-- The pc after the selector load: the dispatcher tree's root. -/
def solcRootPc (code : ByteArray) : UInt256 :=
  if solcSelectorLoadLegacy code then
    solcSelectorLoadPc code + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩
  else
    solcSelectorLoadPc code + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩

/-- The selector-load block, in either generation. -/
def solcSelectorLoadCheck (code : ByteArray) : Bool :=
  if solcSelectorLoadLegacy code then
    decide (decode code (solcSelectorLoadPc code + UInt256.ofNat 2) = some (.CALLDATALOAD, .none))
    && (decide (decode code (solcSelectorLoadPc code + UInt256.ofNat 2 + ⟨1⟩)
          = some (.Push .PUSH1, some (⟨224⟩, 1)))
    && decide (decode code (solcSelectorLoadPc code + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2)
          = some (.SHR, .none)))
  else
    decide (decode code (solcSelectorLoadPc code) = some (.PUSH0, .none))
    && (decide (decode code (solcSelectorLoadPc code + ⟨1⟩) = some (.CALLDATALOAD, .none))
    && (decide (decode code (solcSelectorLoadPc code + ⟨1⟩ + ⟨1⟩)
          = some (.Push .PUSH1, some (⟨224⟩, 1)))
    && decide (decode code (solcSelectorLoadPc code + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2)
          = some (.SHR, .none))))

/-- The whole external-entry prefix. -/
def solcEntryCheck (code : ByteArray) : Bool :=
  decide (decode code ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)))
  && (decide (decode code ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)))
  && (decide (decode code ⟨4⟩ = some (.MSTORE, .none))
  && (decide (decode code ⟨5⟩ = some (.CALLVALUE, .none))
  && (decide (decode code ⟨6⟩ = some (.DUP1, .none))
  && (decide (decode code ⟨7⟩ = some (.ISZERO, .none))
  && (decide (solcGuardTgtOp code ≠ .PUSH0)
  && (decide (decode code ⟨8⟩
        = some (.Push (solcGuardTgtOp code), some (solcGuardTgt code, solcGuardTgtWidth code)))
  && (decide (decode code (solcGuardJumpiPc code) = some (.JUMPI, .none))
  && (solcRevertStubB code (solcGuardJumpiPc code + ⟨1⟩)
  && (decide (decode code (solcGuardTgt code) = some (.JUMPDEST, .none))
  && (decide (decode code (solcGuardTgt code + ⟨1⟩) = some (.POP, .none))
  && ((D_J code 0).contains (solcGuardTgt code)
  && (decide (decode code (solcDispatchBodyPc code) = some (.Push .PUSH1, some (⟨4⟩, 1)))
  && (decide (decode code (solcDispatchBodyPc code + UInt256.ofNat 2)
        = some (.CALLDATASIZE, .none))
  && (decide (decode code (solcDispatchBodyPc code + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
  && (decide (solcCalldataRevertTgtOp code ≠ .PUSH0)
  && (decide (decode code (solcCalldataRevertPushPc code)
        = some (.Push (solcCalldataRevertTgtOp code),
            some (solcCalldataRevertTgt code, solcCalldataRevertTgtWidth code)))
  && (decide (decode code (solcCalldataJumpiPc code) = some (.JUMPI, .none))
  && (decide (decode code (solcCalldataRevertTgt code) = some (.JUMPDEST, .none))
  && ((D_J code 0).contains (solcCalldataRevertTgt code)
  && (solcRevertStubB code (solcCalldataRevertTgt code + ⟨1⟩)
  && solcSelectorLoadCheck code)))))))))))))))))))))

/-- `callvalue ≠ 0`: the guard falls into its revert stub. -/
theorem solcEntryCallvalueRevert {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code) (hwv : I.weiValue ≠ ⟨0⟩) (hchk : solcEntryCheck code = true) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  simp only [solcEntryCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hd0, hd2, hd4, hd5, hd6, hd7, hgOp, hgPush, hgJumpi, hgStub, _⟩ := hchk
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode hd0 hd2 hd4 hd5 hd6 hd7
  have h1 := RD.pushConst h0 (solcGuardTgt code) hgOp hgPush (by simp)
  have h2 := RD.jumpiNT h1 hgJumpi (isZero_eq_zero_of_ne hwv) (by simp)
  exact RD.solcRevertStub h2 hgStub (by simp)

/-- `callvalue = 0`, `calldatasize < 4`: the size guard jumps to its revert stub. -/
theorem solcEntryShortRevert {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩) (hshort : I.calldata.size < 4)
    (hchk : solcEntryCheck code = true) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  simp only [solcEntryCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hd0, hd2, hd4, hd5, hd6, hd7, hgOp, hgPush, hgJumpi, _, hgDest, hgPop, hgJd,
    hcPush4, hcSize, hcLt, hcOp, hcPush, hcJumpi, hcDest, hcJd, hcStub, _⟩ := hchk
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode hd0 hd2 hd4 hd5 hd6 hd7
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt code) (opC := solcGuardTgtOp code) (wC := solcGuardTgtWidth code)
    h0 hwv hgOp hgPush hgJumpi hgDest hgPop hgJd
  have h2 := RD.push1 h1 ⟨4⟩ hcPush4 (by simp)
  have h3 := RD.calldatasize h2 hcSize (by simp)
  have h4 := RD.lt h3 hcLt (by simp)
  have h5 := RD.pushConst h4 (solcCalldataRevertTgt code) hcOp hcPush (by simp)
  have h6 := RD.jumpiT h5 hcJumpi (lt_four_ne_zero_of_lt hshort) hcJd (by simp)
  have h7 := RD.jumpdest h6 hcDest (by simp)
  exact RD.solcRevertStub h7 hcStub (by simp)

/-- `callvalue = 0`, `calldatasize ≥ 4`: the prefix reaches the tree root with the selector word. -/
theorem solcEntryReachRoot {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hchk : solcEntryCheck code = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (solcRootPc code)
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  simp only [solcEntryCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hd0, hd2, hd4, hd5, hd6, hd7, hgOp, hgPush, hgJumpi, _, hgDest, hgPop, hgJd,
    hcPush4, hcSize, hcLt, hcOp, hcPush, hcJumpi, _, _, _, hload⟩ := hchk
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode hd0 hd2 hd4 hd5 hd6 hd7
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt code) (opC := solcGuardTgtOp code) (wC := solcGuardTgtWidth code)
    h0 hwv hgOp hgPush hgJumpi hgDest hgPop hgJd
  obtain ⟨_, _, h2⟩ := solcCalldataOk
    (selLoadTgt := solcCalldataRevertTgt code)
    (opR := solcCalldataRevertTgtOp code) (wR := solcCalldataRevertTgtWidth code)
    h1 hsz hsize hcPush4 hcSize hcLt hcOp hcPush hcJumpi
  by_cases hleg : solcSelectorLoadLegacy code = true
  · unfold solcSelectorLoadCheck at hload
    rw [if_pos hleg] at hload
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hload
    obtain ⟨hl1, hl2, hl3⟩ := hload
    have hl0 : decode code (solcSelectorLoadPc code) = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
      simpa [solcSelectorLoadLegacy] using hleg
    obtain ⟨k3, C3, h3⟩ := solcLegacySelectorLoad h2 hl0 hl1 hl2 hl3 (by simp)
    refine ⟨k3, C3, ?_⟩
    rw [solcRootPc, if_pos hleg]
    exact h3
  · unfold solcSelectorLoadCheck at hload
    rw [if_neg hleg] at hload
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hload
    obtain ⟨hl0, hl1, hl2, hl3⟩ := hload
    obtain ⟨k3, C3, h3⟩ := solcSelectorLoad h2 hl0 hl1 hl2 hl3 (by simp)
    refine ⟨k3, C3, ?_⟩
    rw [solcRootPc, if_neg hleg]
    exact h3

/-! ## Selector words -/

theorem fromBytesBigEndian_lt_size_of_length4 {l : List UInt8} (hl : l.length = 4) :
    fromBytesBigEndian l < UInt256.size := by
  match l, hl with
  | [a0, a1, a2, a3], _ =>
    rw [fromBytesBigEndian_four]
    have b0 : a0.toNat < 256 := a0.toFin.isLt
    have b1 : a1.toNat < 256 := a1.toFin.isLt
    have b2 : a2.toNat < 256 := a2.toFin.isLt
    have b3 : a3.toNat < 256 := a3.toFin.isLt
    have : (256 : ℕ) ^ 4 < UInt256.size := by decide
    have : a3.toNat + 256 * (a2.toNat + 256 * (a1.toNat + 256 * a0.toNat)) < 256 ^ 4 := by
      have h256 : (256 : ℕ) ^ 4 = 256 * (256 * (256 * 256)) := by norm_num
      rw [h256]
      omega
    omega

/-- `ByteArray` `==` is reflexive. -/
theorem byteArray_beq_of_eq {a b : ByteArray} (h : a = b) : (a == b) = true := by
  subst h
  show (a.data == a.data) = true
  exact beq_self_eq_true a.data

/-- A matching 4-byte selector fixes the EVM selector word. -/
theorem solcSelectorWord_eq_selWordOf {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    {s : ByteArray} (hs : s.size = 4) (hmatch : (s == I.calldata.extract 0 4) = true) :
    solcSelectorWord I = selWordOf s := by
  have hs' : s = I.calldata.extract 0 4 := byteArray_eq_of_beq hmatch
  have hlen : s.data.toList.length = 4 := by
    rw [Array.length_toList]; exact hs
  apply u256_inj
  rw [selWordOf, ulit_toNat' _ (fromBytesBigEndian_lt_size_of_length4 hlen)]
  show (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩).toNat
    = fromBytesBigEndian s.data.toList
  rw [selector_toNat I.calldata hsz, hs', ByteArray.data_extract, Array.toList_extract]
  simp

/-- The EVM selector word of calldata matching none of the table's selectors is none of the
    tree's arm words, provided every arm word comes from the table. -/
theorem solcSelectorWord_not_mem_of_table {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    {sels : List ByteArray} {words : List UInt256}
    (hsz4 : ∀ s ∈ sels, s.size = 4)
    (hcover : ∀ w ∈ words, ∃ s ∈ sels, selWordOf s = w)
    (hnm : ∀ s ∈ sels, (s == I.calldata.extract 0 4) = false) :
    solcSelectorWord I ∉ words := by
  intro hmem
  obtain ⟨s, hs, hw⟩ := hcover _ hmem
  have hlen : s.data.toList.length = 4 := by
    rw [Array.length_toList]; exact hsz4 s hs
  have hnum : fromBytesBigEndian s.data.toList = fromBytesBigEndian (I.calldata.data.toList.take 4) := by
    have h1 : (selWordOf s).toNat = fromBytesBigEndian s.data.toList := by
      rw [selWordOf]; exact ulit_toNat' _ (fromBytesBigEndian_lt_size_of_length4 hlen)
    rw [← h1, hw]
    exact selector_toNat I.calldata hsz
  have hlen' : (I.calldata.data.toList.take 4).length = 4 := by
    have h4 : 4 ≤ I.calldata.data.size := hsz
    rw [List.length_take, Array.length_toList]
    omega
  have hlist := fromBytesBigEndian_inj4 hlen hlen' hnum
  have heq : s = I.calldata.extract 0 4 := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    apply Array.toList_inj.mp
    rw [hlist, Array.toList_extract]
    simp
  have := hnm s hs
  rw [byteArray_beq_of_eq heq] at this
  exact Bool.true_eq_false.mp this |>.elim

/-- **Reach a function body through the dispatcher.**  Given the checked prefix and tree, a
    matching 4-byte selector, and the tree's `lookup` of that selector's word, the run from
    `initState` reaches the body pc with the selector word on the stack. -/
theorem solcDispatchReachArm {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (t : SelTree) {s : ByteArray} {bodyPc : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hentry : solcEntryCheck code = true) (htree : t.check code (solcRootPc code) = true)
    (hs : s.size = 4) (hsel : (s == I.calldata.extract 0 4) = true)
    (hlookup : t.lookup (selWordOf s) = some bodyPc) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) bodyPc
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I s hs hsel
  obtain ⟨k, C, rd⟩ := solcEntryReachRoot hcode hwv hsz hsize hentry
  have hw : solcSelectorWord I = selWordOf s := solcSelectorWord_eq_selWordOf hsz hs hsel
  rw [hw] at rd ⊢
  exact (RD.selTreeLookup (by simp) t htree rd).1 bodyPc hlookup

/-- **No selector matches**: the dispatcher reverts. -/
theorem solcDispatchNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (t : SelTree) {sels : List ByteArray}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hentry : solcEntryCheck code = true) (htree : t.check code (solcRootPc code) = true)
    (hsz4 : ∀ s ∈ sels, s.size = 4)
    (hcover : ∀ w ∈ t.selectors, ∃ s ∈ sels, selWordOf s = w)
    (hnm : ∀ s ∈ sels, (s == I.calldata.extract 0 4) = false) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  by_cases hsz : 4 ≤ I.calldata.size
  · obtain ⟨k, C, rd⟩ := solcEntryReachRoot hcode hwv hsz hsize hentry
    have hnone := SelTree.lookup_eq_none_of_not_mem
      (solcSelectorWord_not_mem_of_table hsz hsz4 hcover hnm)
    exact (RD.selTreeLookup (by simp) t htree rd).2 hnone
  · exact solcEntryShortRevert hcode hwv (by omega) hentry

end Reasoning.Reach

namespace Reasoning.Theory

open Reasoning.Reach

/-! ## Solm dispatch from a selector table

A contract proves `contract.transitions.map selectorOf = sels` once (unfolding its transition
list and rewriting each selector axiom); every `dispatchMsg` fact then follows. -/

theorem dispatchList_eq_some_of_index (cd : ByteArray) (ts : List TransitionDecl) :
    ∀ (i : ℕ) (hi : i < ts.length),
      (∀ j (hj : j < i), (selectorOf (ts[j]'(Nat.lt_trans hj hi)) == cd.extract 0 4) = false) →
      (selectorOf ts[i] == cd.extract 0 4) = true →
      dispatchList ts cd = some ts[i] := by
  induction ts with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons t ts ih =>
    intro i hi hpre hhit
    cases i with
    | zero =>
        have hhit' : (selectorOf t == cd.extract 0 4) = true := hhit
        rw [dispatchList_cons, if_pos hhit']
        rfl
    | succ i =>
        have h0 : (selectorOf t == cd.extract 0 4) = false := hpre 0 (Nat.succ_pos i)
        rw [dispatchList_cons, if_neg (by rw [h0]; simp)]
        exact ih i (Nat.lt_of_succ_lt_succ hi)
          (fun j hj => hpre (j + 1) (Nat.succ_lt_succ hj)) hhit

/-- Selector `i` of the table matches ⇒ `dispatchMsg` returns transition `i`. -/
theorem dispatchMsg_eq_some_of_table {contract : ContractDecl} {sels : List ByteArray}
    {cd : ByteArray}
    (hsels : contract.transitions.map selectorOf = sels)
    (hnodup : sels.Pairwise (fun a b => (a == b) = false))
    (i : ℕ) (hi : i < sels.length) (hhit : (sels[i] == cd.extract 0 4) = true)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    dispatchMsg contract cd
      = some (contract.transitions[i]'(by rw [← List.length_map selectorOf, hsels]; exact hi)) := by
  subst hsels
  have hi' : i < contract.transitions.length := by simpa using hi
  have hcd : selectorOf contract.transitions[i] = cd.extract 0 4 := by
    have := byteArray_eq_of_beq hhit
    simpa using this
  rw [dispatchMsg_eq_dispatchList contract cd hfallback hreceive]
  apply dispatchList_eq_some_of_index cd contract.transitions i hi'
  · intro j hj
    have hp := (List.pairwise_iff_getElem.mp hnodup) j i
      (by simpa using Nat.lt_trans hj hi') hi hj
    simp only [List.getElem_map] at hp
    rw [← hcd]
    exact hp
  · simpa using hhit

/-- No table selector matches ⇒ `dispatchMsg` returns nothing. -/
theorem dispatchMsg_none_of_table {contract : ContractDecl} {sels : List ByteArray}
    {cd : ByteArray}
    (hsels : contract.transitions.map selectorOf = sels)
    (hnm : ∀ s ∈ sels, (s == cd.extract 0 4) = false)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    dispatchMsg contract cd = none :=
  dispatchMsg_none_of_all_ne hfallback hreceive fun t ht =>
    hnm _ (hsels ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)

/-! ## The top-level theorem from per-selector bodies -/

/-- The body obligation for one selector: the shape every per-function `…Body` lemma has. -/
abbrev SelectorBody (cfg : Config) (contract : ContractDecl) (code sel : ByteArray) : Prop :=
  ∀ {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256},
    I.code = code → I.calldata.size < UInt256.size → I.perm = true → I.weiValue = ⟨0⟩ →
    (sel == I.calldata.extract 0 4) = true → accountMapEquiv σ_evm σ_solm →
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I

/-- `runtimeEquivalence` from: one body per table selector, the non-zero-callvalue case, and the
    no-selector-matches case. -/
theorem runtimeEquivalence_of_selectors {cfg : Config} {contract : ContractDecl}
    {code : ByteArray} (sels : List ByteArray)
    (hbodies : ∀ i (hi : i < sels.length), SelectorBody cfg contract code sels[i])
    (hpay : ∀ {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
      {bl : ProcessedBlocks} {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
      {g : UInt256},
      I.code = code → I.calldata.size < UInt256.size → I.perm = true → I.weiValue ≠ ⟨0⟩ →
      accountMapEquiv σ_evm σ_solm →
      runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I)
    (hnone : ∀ {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
      {bl : ProcessedBlocks} {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
      {g : UInt256},
      I.code = code → I.calldata.size < UInt256.size → I.perm = true → I.weiValue = ⟨0⟩ →
      (∀ s ∈ sels, (s == I.calldata.extract 0 4) = false) → accountMapEquiv σ_evm σ_solm →
      runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I) :
    runtimeEquivalence cfg code contract := by
  refine runtimeEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hex : ∃ i, ∃ hi : i < sels.length, (sels[i] == I.calldata.extract 0 4) = true
    · obtain ⟨i, hi, hs⟩ := hex
      exact hbodies i hi hcode hsize hperm hwv hs hAccounts
    · refine hnone hcode hsize hperm hwv ?_ hAccounts
      intro s hs
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
      exact Bool.eq_false_iff.mpr fun ht => hex ⟨i, hi, ht⟩
  · exact hpay hcode hsize hperm hwv hAccounts

/-- The statement every non-payable Solm body opens with. -/
def nonpayableGuard : Stmt := .require (.binary .eq (.env .callvalue) (.intLit 0))

/-- `callvalue ≠ 0` with the EVM reverting: every transition body opening with the non-payable
    guard reverts too, so whatever Solm dispatches, the case closes. -/
theorem runtimeEquivalenceFor_nonPayable {cfg : Config} {contract : ContractDecl}
    {code : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue ≠ ⟨0⟩)
    (hrev : RDrev code (Sat256.ofUInt256 g) (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hguard : contract.transitions.all (fun t => decide (t.body.head? = some nonpayableGuard)) = true)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  refine hrev.reEquivElim hcode fun _ _ hrevΞ => ?_
  by_cases hdisp : dispatchMsg contract I.calldata = none
  · exact reEquiv_noDispatch hdisp hrevΞ
  · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
    have htmem : t ∈ contract.transitions := by
      rw [dispatchMsg_eq_dispatchList contract I.calldata hfallback hreceive] at ht
      exact dispatchList_some_mem ht
    by_cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
        (transitionSignature t).paramTypes I.calldata = none
    · exact reEquiv_decodingFailed ht hdec hrevΞ hfallback hreceive
    · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
      have hhead : t.body.head? = some nonpayableGuard := by
        have := List.all_eq_true.mp hguard t htmem
        simpa using this
      obtain ⟨rest, hbody⟩ : ∃ rest, t.body = nonpayableGuard :: rest := by
        cases hb : t.body with
        | nil => simp [hb] at hhead
        | cons s rest =>
            rw [hb] at hhead
            simp only [List.head?_cons, Option.some.injEq] at hhead
            exact ⟨rest, by rw [hhead]⟩
      refine reEquiv_execution ht hca ?_
        (by rw [hrevΞ]; exact execResultsEquiv.revert rfl rfl) hfallback hreceive
      rw [hbody]
      exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)

/-- **The whole-dispatcher driver.**  `runtimeEquivalence` from the checked entry prefix and
    selector tree, the selector table, and one `SelectorBody` per table entry. -/
theorem runtimeEquivalence_of_solcDispatcher {cfg : Config} {contract : ContractDecl}
    {code : ByteArray} (t : SelTree) (sels : List ByteArray)
    (hentry : solcEntryCheck code = true)
    (htree : t.check code (solcRootPc code) = true)
    (hsels : contract.transitions.map selectorOf = sels)
    (hsz4 : ∀ s ∈ sels, s.size = 4)
    (hcover : ∀ w ∈ t.selectors, ∃ s ∈ sels, selWordOf s = w)
    (hguard : contract.transitions.all
      (fun tr => decide (tr.body.head? = some nonpayableGuard)) = true)
    (hbodies : ∀ i (hi : i < sels.length), SelectorBody cfg contract code sels[i])
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalence cfg code contract := by
  refine runtimeEquivalence_of_selectors sels hbodies ?_ ?_
  · intro cA gh bl σ_evm σ_solm σ₀ A I g hcode _ _ hwv _
    exact runtimeEquivalenceFor_nonPayable hcode hwv
      (solcEntryCallvalueRevert hcode hwv hentry) hguard hfallback hreceive
  · intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize _ hwv hnm _
    exact (solcDispatchNoMatchRevert (g := Sat256.ofUInt256 g) t hcode hwv hsize hentry htree
      hsz4 hcover hnm).reEquivNoDispatch hcode (dispatchMsg_none_of_table hsels hnm hfallback hreceive)

end Reasoning.Theory
