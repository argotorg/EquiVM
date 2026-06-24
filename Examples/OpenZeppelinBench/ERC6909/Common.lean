import Examples.OpenZeppelinBench.ERC6909.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Storage
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ERC6909-wide selector and dispatcher helpers -/

/-- The 4-byte function selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev erc6909SelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- ERC6909 selectors in bytecode dispatcher order. -/
def erc6909SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x00, 0xfd, 0xd5, 0x8e]⟩  -- balanceOf
  | 1 => ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩  -- supportsInterface
  | 2 => ⟨#[0x09, 0x5b, 0xcd, 0xb6]⟩  -- transfer
  | 3 => ⟨#[0x42, 0x6a, 0x84, 0x93]⟩  -- approve
  | 4 => ⟨#[0x55, 0x8a, 0x72, 0x97]⟩  -- setOperator
  | 5 => ⟨#[0x59, 0x8a, 0xf9, 0xe7]⟩  -- allowance
  | 6 => ⟨#[0xb6, 0x36, 0x3c, 0xf2]⟩  -- isOperator
  | _ => ⟨#[0xfe, 0x99, 0x04, 0x9a]⟩  -- transferFrom

/-- ERC6909's binary-search selector split begins after the standard solc selector load. -/
abbrev erc6909SplitPc : UInt256 := ⟨30⟩
/-- The high selector group falls through from the split to pc 41. -/
abbrev erc6909HighFirstArmPc : UInt256 := ⟨41⟩
/-- The low selector group is reached by a taken split jump to this `JUMPDEST`. -/
abbrev erc6909LowJumpdestPc : UInt256 := ⟨88⟩
/-- The low selector group begins after the `JUMPDEST` at pc 88. -/
abbrev erc6909LowFirstArmPc : UInt256 := ⟨89⟩
/-- The first standard `PUSH4` arm in the low group, after the `balanceOf` `PUSH3` arm. -/
abbrev erc6909LowRestFirstArmPc : UInt256 := ⟨99⟩

/-- `ByteArray` `==` reflects equality. -/
theorem byteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

/-- If `calldata[0:4]` matches a selector byte literal, the EVM selector word is that literal. -/
theorem erc6909SelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    erc6909SelWord I = sel := by
  apply u256_inj
  dsimp [erc6909SelWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

/-- ERC6909's split decodes as `DUP1; PUSH4 pivot; GT; PUSH2 low; JUMPI`. -/
theorem erc6909SplitWellFormed : selectorSplitWellFormed erc6909BenchBytecode erc6909SplitPc := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The first low-half arm (`balanceOf`) decodes as `DUP1; PUSH3; EQ; PUSH2; JUMPI`. -/
theorem erc6909BalanceArmWellFormed :
    armWellFormedW erc6909BenchBytecode erc6909LowFirstArmPc 3 := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- ERC6909's high-half selector arms decode as standard `PUSH4` arms. -/
theorem erc6909HighArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed erc6909BenchBytecode
      (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- ERC6909's low-half arms after `balanceOf` decode as standard `PUSH4` arms. -/
theorem erc6909LowRestArmsWellFormed :
    ∀ j, j ≤ 2 → armWellFormed erc6909BenchBytecode
      (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### Selector-byte coupling -/

theorem erc6909BalanceArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (armSelNatW erc6909BenchBytecode erc6909LowFirstArmPc) (erc6909SelWord I)
      = if (erc6909SelBytes 0 == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  exact evmSelectorDecode hsz 0x00 0xfd 0xd5 0x8e _ (by decide)

theorem erc6909LowRestArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc j))
        (erc6909SelWord I)
      = if (erc6909SelBytes (j + 1) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem erc6909HighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc j))
        (erc6909SelWord I)
      = if (erc6909SelBytes (j + 4) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

theorem erc6909LowRestMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 3)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (erc6909SelBytes (i + 1) == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc j))
        (erc6909SelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc i))
        (erc6909SelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = erc6909SelBytes (i + 1) :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [erc6909LowRestArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [erc6909LowRestArmEq I hsz i hi, hci]
    interval_cases i <;> decide

theorem erc6909HighMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (erc6909SelBytes (i + 4) == I.calldata.extract 0 4) = true) :
    (∀ j, j < i →
      UInt256.eq
        (armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc j))
        (erc6909SelWord I) = ⟨0⟩)
    ∧ UInt256.eq
        (armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc i))
        (erc6909SelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = erc6909SelBytes (i + 4) :=
    (byteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [erc6909HighArmEq I hsz j (by omega), hci]
    interval_cases i <;> interval_cases j <;> decide
  · rw [erc6909HighArmEq I hsz i hi, hci]
    interval_cases i <;> decide

/-- A low-half selector makes the pivot `GT` branch jump to the low group. -/
theorem erc6909PivotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (erc6909SelBytes i == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat erc6909BenchBytecode erc6909SplitPc) (erc6909SelWord I) ≠ ⟨0⟩ := by
  interval_cases i
  · have hword : erc6909SelWord I = armSelNatW erc6909BenchBytecode erc6909LowFirstArmPc :=
      erc6909SelWord_eq_of_beq I hsz 0x00 0xfd 0xd5 0x8e _ (by decide)
        (by simpa [erc6909SelBytes] using hsel)
    rw [hword]; decide
  · have hword : erc6909SelWord I =
        armSelNat erc6909BenchBytecode erc6909LowRestFirstArmPc :=
      erc6909SelWord_eq_of_beq I hsz 0x01 0xff 0xc9 0xa7 _ (by decide)
        (by simpa [erc6909SelBytes] using hsel)
    rw [hword]; decide
  · have hword : erc6909SelWord I =
        armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc 1) :=
      erc6909SelWord_eq_of_beq I hsz 0x09 0x5b 0xcd 0xb6 _ (by decide)
        (by simpa [erc6909SelBytes] using hsel)
    rw [hword]; decide
  · have hword : erc6909SelWord I =
        armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc 2) :=
      erc6909SelWord_eq_of_beq I hsz 0x42 0x6a 0x84 0x93 _ (by decide)
        (by simpa [erc6909SelBytes] using hsel)
    rw [hword]; decide

/-- A high-half selector makes the pivot `GT` branch fall through to the high group. -/
theorem erc6909PivotNotTaken {I : ExecutionEnv} (i : ℕ) (hi : i < 4)
    (hsz : 4 ≤ I.calldata.size)
    (hsel : (erc6909SelBytes (i + 4) == I.calldata.extract 0 4) = true) :
    UInt256.gt (armSelNat erc6909BenchBytecode erc6909SplitPc) (erc6909SelWord I) = ⟨0⟩ := by
  interval_cases i
  · have hword : erc6909SelWord I = armSelNat erc6909BenchBytecode erc6909SplitPc :=
      erc6909SelWord_eq_of_beq I hsz 0x55 0x8a 0x72 0x97 _ (by decide)
        (by simpa [erc6909SelBytes] using hsel)
    rw [hword]; decide
  · have hword : erc6909SelWord I =
        armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc 1) :=
      erc6909SelWord_eq_of_beq I hsz 0x59 0x8a 0xf9 0xe7 _ (by decide)
        (by simpa [erc6909SelBytes] using hsel)
    rw [hword]; decide
  · have hword : erc6909SelWord I =
        armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc 2) :=
      erc6909SelWord_eq_of_beq I hsz 0xb6 0x36 0x3c 0xf2 _ (by decide)
        (by simpa [erc6909SelBytes] using hsel)
    rw [hword]; decide
  · have hword : erc6909SelWord I =
        armSelNat erc6909BenchBytecode (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc 3) :=
      erc6909SelWord_eq_of_beq I hsz 0xfe 0x99 0x04 0x9a _ (by decide)
        (by simpa [erc6909SelBytes] using hsel)
    rw [hword]; decide

/-! ### Dispatcher reachability -/

/-- Standard solc prologue/guards/selector-load, stopping at ERC6909's pivot split. -/
theorem erc6909ReachSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc6909BenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) erc6909SplitPc
        [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed erc6909BenchBytecode erc6909SplitPc := by
    solc_dispatch_prefix
  simpa [erc6909SelWord, solcSelectorWord] using
    (solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hprefix (by jump_dest))

/-- Reach a body in ERC6909's high selector half. -/
theorem erc6909ReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = erc6909BenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat erc6909BenchBytecode erc6909SplitPc) (erc6909SelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat erc6909BenchBytecode
          (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc j))
        (erc6909SelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat erc6909BenchBytecode
          (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc i))
        (erc6909SelWord I) ≠ ⟨0⟩)
    (hjd : (D_J erc6909BenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt erc6909BenchBytecode
        (nthArmPc erc6909BenchBytecode erc6909HighFirstArmPc i) = bodyPC) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hprefix : solcDispatchPrefixWellFormed erc6909BenchBytecode erc6909SplitPc := by
    solc_dispatch_prefix
  simpa [erc6909SelWord, solcSelectorWord] using
    (solcBinaryDispatchReachHighBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (code := erc6909BenchBytecode) (splitPc := erc6909SplitPc) (bodyPC := bodyPC) (i := i)
      hcode hwv hsz hsize hprefix (by jump_dest) erc6909SplitWellFormed
      (by simpa [erc6909SelWord, solcSelectorWord] using hpivot)
      (fun j hj => by
        simpa [erc6909HighFirstArmPc, erc6909SplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          erc6909HighArmsWellFormed j (le_trans hj hi))
      (fun j hj => by
        simpa [erc6909SelWord, solcSelectorWord, erc6909HighFirstArmPc, erc6909SplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using heq0 j hj)
      (by
        simpa [erc6909SelWord, solcSelectorWord, erc6909HighFirstArmPc, erc6909SplitPc,
          selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
          selArmPush4Pc] using htake)
      hjd
      (by
        simpa [erc6909HighFirstArmPc, erc6909SplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using hbody))

/-- Reach the special `balanceOf` body through the low split and `PUSH3` selector arm. -/
theorem erc6909ReachBalanceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = erc6909BenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat erc6909BenchBytecode erc6909SplitPc)
        (erc6909SelWord I) ≠ ⟨0⟩)
    (htake : UInt256.eq (armSelNatW erc6909BenchBytecode erc6909LowFirstArmPc)
        (erc6909SelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨136⟩
        [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, hsplit⟩ := erc6909ReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h88 := hsplit.selectorSplitTakenAuto erc6909SplitWellFormed hpivot (by jump_dest) (by simp)
  have h89 := h88.jumpdest (by decide) (by simp)
  have h136 := RD.selectorArmWidthTakenAuto 3 h89 erc6909BalanceArmWellFormed htake
    (by jump_dest) (by simp)
  refine ⟨k0 + 5 + 1 + 5, C0 + 22 + 1 + 22, ?_⟩
  simpa [erc6909LowFirstArmPc, erc6909LowJumpdestPc, erc6909SplitPc, selArmPushSelPcW,
    selArmEqPcW, selArmPushTgtPcW, selArmJumpiPcW, selArmNextPcW, armTgtW, armTgtWidthW]
    using h136

/-- Reach a body in the low selector half after the special `balanceOf` arm. -/
theorem erc6909ReachLowRestBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = erc6909BenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hpivot : UInt256.gt (armSelNat erc6909BenchBytecode erc6909SplitPc)
        (erc6909SelWord I) ≠ ⟨0⟩)
    (hbalance0 : UInt256.eq (armSelNatW erc6909BenchBytecode erc6909LowFirstArmPc)
        (erc6909SelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat erc6909BenchBytecode
          (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc j))
        (erc6909SelWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat erc6909BenchBytecode
          (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc i))
        (erc6909SelWord I) ≠ ⟨0⟩)
    (hjd : (D_J erc6909BenchBytecode 0).contains bodyPC = true)
    (hbody : armTgt erc6909BenchBytecode
        (nthArmPc erc6909BenchBytecode erc6909LowRestFirstArmPc i) = bodyPC) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, hsplit⟩ := erc6909ReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h88 := hsplit.selectorSplitTakenAuto erc6909SplitWellFormed hpivot (by jump_dest) (by simp)
  have h89 := h88.jumpdest (by decide) (by simp)
  have h99 := RD.selectorArmWidthNotTakenAuto 3 h89 erc6909BalanceArmWellFormed hbalance0
    (by simp)
  have hdispatch := RD.dispatchTo (code := erc6909BenchBytecode) (bodyPC := bodyPC) (i := i)
    (start := erc6909LowRestFirstArmPc) h99
    (fun j hj => erc6909LowRestArmsWellFormed j (le_trans hj hi))
    heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)
  obtain ⟨k', C', hbody'⟩ := hdispatch
  exact ⟨k', C', by
    simpa [erc6909LowRestFirstArmPc, erc6909LowFirstArmPc, erc6909LowJumpdestPc,
      erc6909SplitPc, selArmPushSelPcW, selArmEqPcW, selArmPushTgtPcW, selArmJumpiPcW,
      selArmNextPcW, armTgtW, armTgtWidthW] using hbody'⟩

end OpenZeppelinBench.ERC6909
