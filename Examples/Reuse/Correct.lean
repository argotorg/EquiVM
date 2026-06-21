import Examples.Reuse.Bytecode
import Examples.Reuse.Spec
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.EVMWord
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Stepping
import Reasoning.Reach
import Solm.Equiv
import Mathlib.Tactic.IntervalCases

/-!
# Reuse — correctness

The deployed (optimizer-on) runtime bytecode of `C` refines its Solm spec (`Reuse.cContract`) under
`cConfig`.

The point of this example is the **internal-call reuse** scenario: `f` is a public function (its own
external ABI entry) that `g` calls internally.  solc emits `f`'s body once as a shared routine, so
the proof should introduce a single `RD`-routine lemma for that body and apply it at *both* the
external-entry refinement (`f`) and the internal-call refinement (inside `g`) — without re-unfolding
`f`'s body.  See `C.sol` for the compiled-shape evidence.

The bytecode proof uses the trusted `valid_jumps`/selector facts in `Bytecode.lean`, then discharges
the optimizer-on dispatch, decode, and shared-body routine.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

/-- The 4-byte selector word the dispatcher computes from `calldata[0:32]`. -/
abbrev cSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The single `uint256` ABI argument decoded from calldata offset 4. -/
abbrev cArgWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)

/-- The Solm value corresponding to `C`'s single `uint256` ABI argument. -/
abbrev cArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (cArgWord I).toNat)

/-- The decoded calldata store for `f(uint256)` and `g(uint256)`. -/
abbrev cArgStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "v" (cArgValue I)

/-- `C`'s two selector arms begin at pc 28 (`f(uint256)`). -/
abbrev cFirstArmPc : UInt256 := ⟨28⟩

/-- `C`'s selectors in bytecode dispatch order. -/
def cSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xb3, 0xde, 0x64, 0x8b]⟩
  | _ => ⟨#[0xe4, 0x20, 0x26, 0x4a]⟩

/-- The word returned by the shared `f` routine on the EVM happy path. -/
abbrev cFResultWord (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (cArgWord I) ⟨2⟩ + ⟨1⟩

/-- The Solm value returned by `f` on the happy path. -/
abbrev cFResultValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (cFResultWord I).toNat)

/-- The standard Solidity panic selector word used by checked arithmetic reverts. -/
def cPanicSelector : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def cPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray cPanicSelector).write 0 mem 0 32

noncomputable def cPanicMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨17⟩ : UInt256)).write 0 (cPanicMem0 mem) 4 32

/-- `ByteArray` `==` reflects equality. -/
theorem cByteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

/-- Both selector arms decode as `DUP1; PUSH4; EQ; PUSH1; JUMPI`. -/
theorem cArmsWellFormed :
    ∀ j, j ≤ 1 → armWellFormed cBytecode (nthArmPc cBytecode cFirstArmPc j) := by
  intro j hj
  interval_cases j
  all_goals exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- EVM selector coupling for `f(uint256)`. -/
theorem cFEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨3017696395⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0xb3, 0xde, 0x64, 0x8b]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xb3 0xde 0x64 0x8b ⟨3017696395⟩ (by decide)

/-- EVM selector coupling for `g(uint256)`. -/
theorem cGEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨3827312202⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0xe4, 0x20, 0x26, 0x4a]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xe4 0x20 0x26 0x4a ⟨3827312202⟩ (by decide)

/-- Per-arm selector coupling. -/
theorem cArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 2) :
    UInt256.eq (armSelNat cBytecode (nthArmPc cBytecode cFirstArmPc j)) (cSelWord I)
      = if (cSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j
  · exact cFEvmSelector hsz
  · exact cGEvmSelector hsz

/-- Selector identification for the two-arm dispatcher. -/
theorem cMatches {I : ExecutionEnv} (i : ℕ) (hi : i < 2) (hsz : 4 ≤ I.calldata.size)
    (hsel : (cSelBytes i == I.calldata.extract 0 4) = true) :
    (∀ j, j < i → UInt256.eq (armSelNat cBytecode (nthArmPc cBytecode cFirstArmPc j))
        (cSelWord I) = ⟨0⟩)
    ∧ UInt256.eq (armSelNat cBytecode (nthArmPc cBytecode cFirstArmPc i))
        (cSelWord I) ≠ ⟨0⟩ := by
  have hci : I.calldata.extract 0 4 = cSelBytes i := (cByteArray_eq_of_beq hsel).symm
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [cArmEq I hsz j (by omega), hci]
    interval_cases i
    · omega
    ·
      interval_cases j
      decide
  · rw [cArmEq I hsz i hi, hci]
    interval_cases i <;> decide

/-- Generic dispatcher driver: reaches the selected external wrapper body. -/
theorem cReachBody {cA gh bl σ σ₀ A I} {g : Sat256} (i : ℕ) (hi1 : i ≤ 1)
    (bodyPC : UInt256)
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat cBytecode (nthArmPc cBytecode cFirstArmPc j))
        (cSelWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat cBytecode (nthArmPc cBytecode cFirstArmPc i))
        (cSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J cBytecode 0).contains bodyPC = true)
    (hbody : armTgt cBytecode (nthArmPc cBytecode cFirstArmPc i) = bodyPC) :
    ∃ k C, RD cBytecode I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [cSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := cFirstArmPc) (bodyPC := bodyPC) (i := i)
    hcode hwv hsz hsize (by solc_dispatch_prefix) (by jump_dest)
    (fun j hj => cArmsWellFormed j (le_trans hj hi1)) heq0 htake hjd hbody

theorem cDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg Reuse.cContract cd = none := by
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList [Reuse.fTransition, Reuse.gTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl
    · rw [selectorOf, cFSelectorBytes]; rfl
    · rw [selectorOf, cGSelectorBytes]; rfl) h

theorem cDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 2 → (cSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg Reuse.cContract cd = none := by
  apply dispatchMsg_none_of_all_ne
  intro t ht
  simp [Reuse.cContract] at ht
  rcases ht with rfl | rfl
  · rw [selectorOf, cFSelectorBytes]; simpa [cSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, cGSelectorBytes]; simpa [cSelBytes] using hnm 1 (by omega)

theorem cDispatch_f {cd : ByteArray}
    (hsel : ((⟨#[0xb3, 0xde, 0x64, 0x8b]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg Reuse.cContract cd = some Reuse.fTransition := by
  apply dispatchMsg_eq_some_of_split (pre := []) (post := [Reuse.gTransition])
  · rfl
  · intro t ht; cases ht
  · rw [selectorOf, cFSelectorBytes]; exact hsel

theorem cDispatch_g {cd : ByteArray}
    (hf : ((⟨#[0xb3, 0xde, 0x64, 0x8b]⟩ : ByteArray) == cd.extract 0 4) = false)
    (hg : ((⟨#[0xe4, 0x20, 0x26, 0x4a]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg Reuse.cContract cd = some Reuse.gTransition := by
  apply dispatchMsg_eq_some_of_split (pre := [Reuse.fTransition]) (post := [])
  · rfl
  · intro t ht
    simp at ht
    rcases ht with rfl
    rw [selectorOf, cFSelectorBytes]; exact hf
  · rw [selectorOf, cGSelectorBytes]; exact hg

theorem cBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ Reuse.cContract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody cConfig Reuse.cContract evm locals t.body .reverted := by
  simp [Reuse.cContract] at ht
  rcases ht with rfl | rfl <;> exact bodyReverts_nonPayable h

theorem cX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := solcGuardTgt cBytecode) (opC := solcGuardTgtOp cBytecode)
    (wC := solcGuardTgtWidth cBytecode)
    (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    hwv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem cX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt cBytecode) (opC := solcGuardTgtOp cBytecode)
    (wC := solcGuardTgtWidth cBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  exact solcCalldataShortRevert
    (bodyPc := solcDispatchBodyPc cBytecode)
    (rtgt := solcCalldataRevertTgt cBytecode)
    (opR := solcCalldataRevertTgtOp cBytecode)
    (wR := solcCalldataRevertTgtWidth cBytecode)
    h1 hsz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by jump_dest) (by decide) (by decide) (by decide)

/-- With calldata long enough for a selector but no selector match, the dispatcher reverts. -/
theorem cX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 2 → (cSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat cBytecode (nthArmPc cBytecode cFirstArmPc j))
        (cSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [cArmEq I hsz j hj, hnm j hj]
    rfl
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt cBytecode) (opC := solcGuardTgtOp cBytecode)
    (wC := solcGuardTgtWidth cBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  obtain ⟨k2, C2, h2⟩ := solcCalldataOk
    (bodyPc := solcDispatchBodyPc cBytecode)
    (selLoadTgt := solcCalldataRevertTgt cBytecode)
    (opR := solcCalldataRevertTgtOp cBytecode)
    (wR := solcCalldataRevertTgtWidth cBytecode)
    h1 hsz hsize (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, C3, h3⟩ := solcSelectorLoad h2 (by decide) (by decide) (by decide) (by decide) (by simp)
  have h4 : RD cBytecode I g (initState cA gh bl σ σ₀ g A I) cFirstArmPc
      [cSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3 C3 := by
    simpa [cFirstArmPc, cSelWord, solcFirstArmPcFromPrefix, solcSelectorLoadPc,
      solcCalldataJumpiPc, solcCalldataRevertPushPc, solcDispatchBodyPc] using h3
  have h5 := h4
    |>.selectorArmNotTakenAuto (cArmsWellFormed 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cArmsWellFormed 1 (by omega)) (heq0 1 (by omega)) (by simp)
  have h48 : ∃ k C, RD cBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨48⟩
      [cSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    refine ⟨k3 + 5 + 5, C3 + 22 + 22, ?_⟩
    simpa [cFirstArmPc, nthArmPc, selArmNextPc, armTgtWidth, selArmJumpiPc,
      selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h5
  obtain ⟨_, _, h48rd⟩ := h48
  exact evm_run h48rd with [
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- Calldata decode for `f(uint256)` succeeds when the one word argument is present. -/
theorem cDecode_f_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (Reuse.fTransition.params.map Param.name)
        (transitionSignature Reuse.fTransition).paramTypes I.calldata = some (cArgStore I) := by
  show decodeCalldata ["v"] [Reuse.uint256] I.calldata = _
  simpa [Reuse.uint256, abiUInt256, cArgStore, cArgValue, cArgWord, calldataWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "v") hsz36 hbig

/-- Calldata decode for `g(uint256)` succeeds when the one word argument is present. -/
theorem cDecode_g_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (Reuse.gTransition.params.map Param.name)
        (transitionSignature Reuse.gTransition).paramTypes I.calldata = some (cArgStore I) := by
  show decodeCalldata ["v"] [Reuse.uint256] I.calldata = _
  simpa [Reuse.uint256, abiUInt256, cArgStore, cArgValue, cArgWord, calldataWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "v") hsz36 hbig

/-- `f(uint256)` calldata decode fails when the argument word is incomplete. -/
theorem cDecode_f_none_short {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldata (Reuse.fTransition.params.map Param.name)
        (transitionSignature Reuse.fTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["v"] [Reuse.uint256] I.calldata = none
  simpa [Reuse.uint256, abiUInt256]
    using decodeCalldata_uint256_none_short (cd := I.calldata) (x := "v") hshort

/-- `g(uint256)` calldata decode fails when the argument word is incomplete. -/
theorem cDecode_g_none_short {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldata (Reuse.gTransition.params.map Param.name)
        (transitionSignature Reuse.gTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["v"] [Reuse.uint256] I.calldata = none
  simpa [Reuse.uint256, abiUInt256]
    using decodeCalldata_uint256_none_short (cd := I.calldata) (x := "v") hshort

/-- `f(uint256)` calldata decode fails on the huge-size branch matching solc's signed check. -/
theorem cDecode_f_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (Reuse.fTransition.params.map Param.name)
        (transitionSignature Reuse.fTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["v"] [Reuse.uint256] I.calldata = none
  simpa [Reuse.uint256, abiUInt256]
    using decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "v") hbig

/-- `g(uint256)` calldata decode fails on the huge-size branch matching solc's signed check. -/
theorem cDecode_g_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (Reuse.gTransition.params.map Param.name)
        (transitionSignature Reuse.gTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["v"] [Reuse.uint256] I.calldata = none
  simpa [Reuse.uint256, abiUInt256]
    using decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "v") hbig

namespace Reasoning.Theory

theorem cOr_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.OR, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.lor a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.OR, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_or s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem cGt_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.GT, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.gt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.GT, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_gt s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem cDiv_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DIV, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stMul s (UInt256.div a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DIV, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_div s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Glow, stMul]

theorem cDiv_mul2 {v : UInt256} (h : 2 * v.toNat < UInt256.size) :
    UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩ = v := by
  apply u256_inj
  unfold UInt256.div UInt256.toNat
  simp
  change (UInt256.mul v ⟨2⟩).toNat / 2 = v.toNat
  rw [mul2_toNat h]
  exact Nat.mul_div_right v.toNat (by norm_num)

theorem cMul2_wrap_toNat {v : UInt256} (hover : UInt256.size ≤ 2 * v.toNat) :
    (UInt256.mul v ⟨2⟩).toNat = 2 * v.toNat - UInt256.size := by
  show (v.val * (⟨2⟩ : UInt256).val).val = 2 * v.toNat - UInt256.size
  rw [Fin.val_mul]
  change (v.toNat * 2) % UInt256.size = 2 * v.toNat - UInt256.size
  rw [Nat.mul_comm]
  have hlt : 2 * v.toNat < 2 * UInt256.size := by
    have hvlt : v.toNat < UInt256.size := v.val.isLt
    omega
  rw [Nat.mod_eq_sub_mod hover]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem cDiv_mul2_overflow_lt {v : UInt256} (hover : UInt256.size ≤ 2 * v.toNat) :
    (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩).toNat < v.toNat := by
  have hprod : (UInt256.mul v ⟨2⟩).toNat = 2 * v.toNat - UInt256.size :=
    cMul2_wrap_toNat hover
  have hdiv : (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩).toNat =
      (2 * v.toNat - UInt256.size) / 2 := by
    unfold Ethereum.UInt256.div Ethereum.UInt256.toNat
    simp only
    change (UInt256.mul v ⟨2⟩).toNat / (⟨2⟩ : UInt256).toNat = _
    rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide, hprod]
    change (2 * v.toNat - UInt256.size) / 2 = (2 * v.toNat - UInt256.size) / 2
    rfl
  rw [hdiv]
  apply Nat.lt_of_not_ge
  intro hge
  have hm := Nat.le_div_two_iff_mul_two_le.mp hge
  have hpos : 0 < UInt256.size := by
    norm_num [UInt256.size]
  omega

theorem cEq_mul2_div_overflow {v : UInt256} (hover : UInt256.size ≤ 2 * v.toNat) :
    UInt256.eq v (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩) = ⟨0⟩ := by
  apply u256_eq_of_ne
  intro heqv
  have hlt := cDiv_mul2_overflow_lt hover
  have hnat := congrArg UInt256.toNat heqv
  omega

theorem cUgt_zero {a b : UInt256} (h : a.toNat ≤ b.toNat) : UInt256.gt a b = ⟨0⟩ := by
  show UInt256.fromBool (decide (a > b)) = ⟨0⟩
  rw [decide_eq_false (show ¬ (a > b) from by
    show ¬ (a.toNat > b.toNat)
    omega)]
  rfl

theorem cAdd1_overflow_gt {v : UInt256} (hover : UInt256.size ≤ v.toNat + 1) :
    UInt256.gt ⟨1⟩ (v + ⟨1⟩) = ⟨1⟩ := by
  have hvlt : v.toNat < UInt256.size := v.val.isLt
  have hle : v.toNat + 1 ≤ UInt256.size := by
    omega
  have hv : v.toNat + 1 = UInt256.size := by
    omega
  have hsum : (v + ⟨1⟩).toNat = 0 := by
    rw [uadd_toNat]
    change (v.toNat + 1) % UInt256.size = 0
    rw [hv, Nat.mod_self]
  show UInt256.fromBool (decide ((⟨1⟩ : UInt256) > (v + ⟨1⟩))) = ⟨1⟩
  rw [decide_eq_true]
  · rfl
  · show (⟨1⟩ : UInt256).toNat > (v + ⟨1⟩).toNat
    rw [hsum]
    decide

end Reasoning.Theory

namespace Reasoning.Reach

/-- Reuse-local `OR` combinator used by solc's checked-multiply routine. -/
theorem RD.cOr {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.OR, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.lor a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => Reasoning.Theory.cOr_xstep hc hp hdec hs hov)

/-- Reuse-local `GT` combinator used by solc's checked-add routine. -/
theorem RD.cGt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.GT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.gt a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => Reasoning.Theory.cGt_xstep hc hp hdec hs hov)

/-- Reuse-local `DIV` combinator used by solc's checked-multiply routine. -/
theorem RD.cDiv {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DIV, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.div a b :: t) mem aw rdata acc (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := Reasoning.Theory.cDiv_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMul s (UInt256.div a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMul]; exact hcode
      · simp only [stMul]; rw [hpc]
      · rfl
      · simp only [stMul]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMul]; exact hmem
      · simp only [stMul]; exact haw
      · simp only [stMul]; exact hrdata
      · simp only [stMul]; exact hacc
      · exact hee
      · exact hworld

/-- Reuse's Solidity checked-arithmetic panic block at pc 161. -/
theorem RD.cPanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨161⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev cBytecode g s0 := by
  have hsel : UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = cPanicSelector := by
    decide
  have rd168₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0 ]
  have rd168 := rd168₀
  rw [hsel] at rd168
  have rd171 := evm_run rd168 with [
    raw mstore 0 (cPanicMem0 mem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩ ]
  have rd176 := evm_run rd171 with [
    raw mstore 0 (cPanicMem mem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, push0 ]
  exact rd176.rev 0 (by decide) mem_cost (by evm_ov)

/-- Reuse's solc checked multiply routine at pc 181, specialized to `v * 2`. -/
theorem RD.cCheckedMul2 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨181⟩ (⟨2⟩ :: v :: ret :: R) mem aw rdata acc k C)
    (hmul : 2 * v.toNat < UInt256.size)
    (hret : (D_J cBytecode 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD cBytecode ee g s0 ret (UInt256.mul v ⟨2⟩ :: R) mem aw rdata acc k' C' := by
  have hcond :
      UInt256.lor
          (UInt256.eq v (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩))
          (UInt256.isZero ⟨2⟩) ≠ ⟨0⟩ := by
    rw [Reasoning.Theory.cDiv_mul2 hmul, uInt256_eq_self]
    decide
  exact ⟨_, _, evm_run h with [
    jumpdest, dup1, dup3, mul, dup2, iszero, dup3, dup3, cDiv, dup5, eq, cOr,
    push1 ⟨121⟩, jumpiT hcond (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

/-- Reuse's checked multiply routine panics when `v * 2` overflows. -/
theorem RD.cCheckedMul2_overflow {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨181⟩ (⟨2⟩ :: v :: ret :: R) mem (UInt256.ofNat 3)
      rdata acc k C)
    (hover : UInt256.size ≤ 2 * v.toNat) (hov : R.length + 10 ≤ 1024) :
    RDrev cBytecode g s0 := by
  have heq : UInt256.eq v (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩) = ⟨0⟩ :=
    Reasoning.Theory.cEq_mul2_div_overflow hover
  have hcond :
      UInt256.lor
          (UInt256.eq v (UInt256.div (UInt256.mul v ⟨2⟩) ⟨2⟩))
          (UInt256.isZero ⟨2⟩) = ⟨0⟩ := by
    rw [heq]
    decide
  have rd193₀ := evm_run h with [
    jumpdest, dup1, dup3, mul, dup2, iszero, dup3, dup3, cDiv, dup5, eq, cOr ]
  have rd193 := rd193₀
  rw [hcond] at rd193
  have rd196 := evm_run rd193 with [ push1 ⟨121⟩, jumpiNT (by decide) ]
  have rd161 := evm_run rd196 with [ push1 ⟨121⟩, push1 ⟨161⟩, jump (by jump_dest) ]
  exact RD.cPanicOverflowRevert rd161 (by evm_ov)

/-- Reuse's solc checked add routine at pc 201, specialized to `v + 1`. -/
theorem RD.cCheckedAdd1 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨201⟩ (⟨1⟩ :: v :: ret :: R) mem aw rdata acc k C)
    (hadd : v.toNat + 1 < UInt256.size)
    (hret : (D_J cBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD cBytecode ee g s0 ret ((v + ⟨1⟩) :: R) mem aw rdata acc k' C' := by
  have hsum : (v + ⟨1⟩).toNat = v.toNat + 1 := add1_toNat hadd
  have hgt : UInt256.gt ⟨1⟩ (v + ⟨1⟩) = ⟨0⟩ :=
    Reasoning.Theory.cUgt_zero (by
      change 1 ≤ (v + ⟨1⟩).toNat
      rw [hsum]
      omega)
  have hcond : UInt256.isZero (UInt256.gt ⟨1⟩ (v + ⟨1⟩)) ≠ ⟨0⟩ := by
    rw [hgt]
    decide
  exact ⟨_, _, evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3, cGt, iszero,
    push1 ⟨121⟩, jumpiT hcond (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

/-- Reuse's checked add routine panics when `v + 1` overflows. -/
theorem RD.cCheckedAdd1_overflow {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨201⟩ (⟨1⟩ :: v :: ret :: R) mem (UInt256.ofNat 3)
      rdata acc k C)
    (hover : UInt256.size ≤ v.toNat + 1) (hov : R.length + 7 ≤ 1024) :
    RDrev cBytecode g s0 := by
  have hgt : UInt256.gt ⟨1⟩ (v + ⟨1⟩) = ⟨1⟩ :=
    Reasoning.Theory.cAdd1_overflow_gt hover
  have rd208₀ := evm_run h with [
    jumpdest, dup1, dup3, add, dup1, dup3, cGt ]
  have rd208 := rd208₀
  rw [hgt] at rd208
  have rd209₀ := evm_run rd208 with [ iszero ]
  have rd209 := rd209₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd209
  have rd212 := evm_run rd209 with [ push1 ⟨121⟩, jumpiNT (by decide) ]
  have rd161 := evm_run rd212 with [ push1 ⟨121⟩, push1 ⟨161⟩, jump (by jump_dest) ]
  exact RD.cPanicOverflowRevert rd161 (by evm_ov)

/-- The shared `f` routine at pc 102, used by both external `f` and internal `g`. -/
theorem RD.cFRoutine {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨102⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hbound : 2 * v.toNat + 1 < UInt256.size)
    (hret : (D_J cBytecode 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD cBytecode ee g s0 ret ((UInt256.mul v ⟨2⟩ + ⟨1⟩) :: R)
      mem aw rdata acc k' C' := by
  have hmul : 2 * v.toNat < UInt256.size := by omega
  have hprod : (UInt256.mul v ⟨2⟩).toNat = 2 * v.toNat := mul2_toNat hmul
  have hadd : (UInt256.mul v ⟨2⟩).toNat + 1 < UInt256.size := by
    rw [hprod]
    exact hbound
  have rd181 := evm_run h with [
    jumpdest, push0, push1 ⟨112⟩, dup3, push1 ⟨2⟩, push1 ⟨181⟩,
    jump (by jump_dest) ]
  obtain ⟨_, _, rd112⟩ := RD.cCheckedMul2 rd181 hmul (by jump_dest) (by evm_ov)
  have rd201 := evm_run rd112 with [
    jumpdest, push1 ⟨121⟩, swap1, push1 ⟨1⟩, push1 ⟨201⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd121⟩ := RD.cCheckedAdd1 rd201 hadd (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd121 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

/-- The shared `f` routine panics when checked arithmetic would overflow. -/
theorem RD.cFRoutine_overflow {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨102⟩ (v :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hover : UInt256.size ≤ 2 * v.toNat + 1) (hov : R.length + 13 ≤ 1024) :
    RDrev cBytecode g s0 := by
  have rd181 := evm_run h with [
    jumpdest, push0, push1 ⟨112⟩, dup3, push1 ⟨2⟩, push1 ⟨181⟩,
    jump (by jump_dest) ]
  by_cases hmulOver : UInt256.size ≤ 2 * v.toNat
  · exact RD.cCheckedMul2_overflow rd181 hmulOver (by evm_ov)
  · have hmul : 2 * v.toNat < UInt256.size := by
      omega
    have hprod : (UInt256.mul v ⟨2⟩).toNat = 2 * v.toNat := mul2_toNat hmul
    have haddOver : UInt256.size ≤ (UInt256.mul v ⟨2⟩).toNat + 1 := by
      rw [hprod]
      exact hover
    obtain ⟨_, _, rd112⟩ := RD.cCheckedMul2 rd181 hmul (by jump_dest) (by evm_ov)
    have rd201 := evm_run rd112 with [
      jumpdest, push1 ⟨121⟩, swap1, push1 ⟨1⟩, push1 ⟨201⟩, jump (by jump_dest) ]
    exact RD.cCheckedAdd1_overflow rd201 haddOver (by evm_ov)

/-- External return wrapper at pc 67: ABI-encode and return one `uint256` word. -/
theorem RD.cEncodeReturn {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val : UInt256} {Rt : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨67⟩ (val :: Rt) solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : Rt.length + 4 ≤ 1024) :
    RDret cBytecode g s0 acc (UInt256.toByteArray val) :=
  evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide) mem_cost
      (solcReturnMem_mload64 val)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
        solcReturnMem_read128])
      (by evm_ov) ]

/-- Reuse's shared one-`uint256` ABI decoder at pc 139, returning to a dynamic address. -/
theorem RD.cDecodeUint256 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨139⟩ (⟨4⟩ :: de :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub de ⟨4⟩) ⟨32⟩ = ⟨0⟩)
    (hret : (D_J cBytecode 0).contains ret = true) (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD cBytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push1 ⟨154⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, pop, calldataload, swap2, swap1, pop, jump hret ]⟩

/-- Reuse's ABI decoder failure path at pc 139 (`calldata` too short or huge). -/
theorem RD.cDecodeUint256_revert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cBytecode ee g s0 ⟨139⟩ (⟨4⟩ :: de :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub de ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 15 ≤ 1024) :
    RDrev cBytecode g s0 :=
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push1 ⟨154⟩,
    jumpiNT (by rw [hsltval]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

end Reasoning.Reach

/-- External `f(uint256)` wrapper: dispatch and decode, then jump into the shared `f` routine. -/
theorem cX_f_to102 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hmatch : (cSelBytes 0 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD cBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨102⟩
        [cArgWord I, ⟨67⟩, cSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨heq0, htake⟩ := cMatches 0 (by omega) (by omega) hmatch
  obtain ⟨k, C, rd52⟩ :=
    cReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) 0 (by omega) ⟨52⟩ hcode hwv (by omega)
      hsize heq0 htake (by jump_dest) (by decide)
  have rd139 := evm_run rd52 with [
    jumpdest, push1 ⟨67⟩, push1 ⟨63⟩, calldatasize, push1 ⟨4⟩, push1 ⟨139⟩,
    jump (by jump_dest) ]
  have hsltval :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsz255 hsize
  obtain ⟨k1, C1, rd63⟩ := RD.cDecodeUint256 rd139 hsltval (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd63 with [
    jumpdest, push1 ⟨102⟩, jump (by jump_dest) ]⟩

/-- External `g(uint256)` wrapper: dispatch and decode, then jump to `g`'s body at pc 127. -/
theorem cX_g_to127 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (_hfmiss : (cSelBytes 0 == I.calldata.extract 0 4) = false)
    (hgmatch : (cSelBytes 1 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD cBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨127⟩
        [cArgWord I, ⟨100⟩, cSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨heq0, htake⟩ := cMatches 1 (by omega) (by omega) hgmatch
  obtain ⟨k, C, rd85⟩ :=
    cReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) 1 (by omega) ⟨85⟩ hcode hwv (by omega)
      hsize heq0 htake (by jump_dest) (by decide)
  have rd139 := evm_run rd85 with [
    jumpdest, push1 ⟨100⟩, push1 ⟨96⟩, calldatasize, push1 ⟨4⟩, push1 ⟨139⟩,
    jump (by jump_dest) ]
  have hsltval :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hsz255 hsize
  obtain ⟨k1, C1, rd96⟩ := RD.cDecodeUint256 rd139 hsltval (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd96 with [
    jumpdest, push1 ⟨127⟩, jump (by jump_dest) ]⟩

/-- `g`'s body performs an internal jump into the same shared `f` routine at pc 102. -/
theorem cX_g_internalCall_to102 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (rd127 : RD cBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨127⟩
        [cArgWord I, ⟨100⟩, cSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD cBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨102⟩
        [cArgWord I, ⟨134⟩, cArgWord I, ⟨100⟩, cSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run rd127 with [
    jumpdest, push1 ⟨134⟩, dup2, push1 ⟨102⟩, jump (by jump_dest) ]⟩

/-- External `f(uint256)` happy path: decode, run the shared routine, encode one word. -/
theorem cX_f_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hmatch : (cSelBytes 0 == I.calldata.extract 0 4) = true)
    (hbound : 2 * (cArgWord I).toNat + 1 < UInt256.size) :
    RDret cBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (cFResultWord I)) := by
  obtain ⟨_, _, rd102⟩ := cX_f_to102 (g := g) hcode hwv hsz36 hsz255 hsize hmatch
  obtain ⟨_, _, rd67⟩ := RD.cFRoutine rd102 hbound (by jump_dest) (by evm_ov)
  exact RD.cEncodeReturn rd67 (by evm_ov)

/-- External `f(uint256)` overflow path: the shared routine panics. -/
theorem cX_f_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hmatch : (cSelBytes 0 == I.calldata.extract 0 4) = true)
    (hover : UInt256.size ≤ 2 * (cArgWord I).toNat + 1) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd102⟩ := cX_f_to102 (g := g) hcode hwv hsz36 hsz255 hsize hmatch
  exact RD.cFRoutine_overflow rd102 hover (by evm_ov)

/-- External `g(uint256)` happy path: reuse `f`'s routine and store its result in slot 0. -/
theorem cX_g_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true)
    (hfmiss : (cSelBytes 0 == I.calldata.extract 0 4) = false)
    (hgmatch : (cSelBytes 1 == I.calldata.extract 0 4) = true)
    (hbound : 2 * (cArgWord I).toNat + 1 < UInt256.size) :
    RDret cBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩ (cFResultWord I)) ByteArray.empty := by
  obtain ⟨_, _, rd127⟩ :=
    cX_g_to127 (g := g) hcode hwv hsz36 hsz255 hsize hfmiss hgmatch
  obtain ⟨_, _, rd102⟩ := cX_g_internalCall_to102 rd127
  obtain ⟨_, _, rd134⟩ := RD.cFRoutine rd102 hbound (by jump_dest) (by evm_ov)
  have rd136 := evm_run rd134 with [ jumpdest, push0 ]
  obtain ⟨_, _, rd137⟩ := RD.sstore rd136 hperm (by decide) (by evm_ov)
  have rd100 := evm_run rd137 with [ pop, jump (by jump_dest), jumpdest ]
  exact rd100.stop (by decide) (by evm_ov)

/-- External `g(uint256)` overflow path: the internal call to `f` panics before storage writes. -/
theorem cX_g_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hfmiss : (cSelBytes 0 == I.calldata.extract 0 4) = false)
    (hgmatch : (cSelBytes 1 == I.calldata.extract 0 4) = true)
    (hover : UInt256.size ≤ 2 * (cArgWord I).toNat + 1) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd127⟩ :=
    cX_g_to127 (g := g) hcode hwv hsz36 hsz255 hsize hfmiss hgmatch
  obtain ⟨_, _, rd102⟩ := cX_g_internalCall_to102 rd127
  exact RD.cFRoutine_overflow rd102 hover (by evm_ov)

/-! ## Decode-failure traces -/

/-- External `f(uint256)`: selector matched, but the `uint256` word is incomplete. -/
theorem cX_f_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hmatch : (cSelBytes 0 == I.calldata.extract 0 4) = true) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨heq0, htake⟩ := cMatches 0 (by omega) hsz4 hmatch
  obtain ⟨_, _, rd52⟩ :=
    cReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) 0 (by omega) ⟨52⟩ hcode hwv hsz4
      hsize heq0 htake (by jump_dest) (by decide)
  have rd139 := evm_run rd52 with [
    jumpdest, push1 ⟨67⟩, push1 ⟨63⟩, calldatasize, push1 ⟨4⟩, push1 ⟨139⟩,
    jump (by jump_dest) ]
  have hsltval :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact RD.cDecodeUint256_revert rd139 hsltval (by evm_ov)

/-- External `f(uint256)`: selector matched, but solc's signed length check rejects huge calldata. -/
theorem cX_f_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hmatch : (cSelBytes 0 == I.calldata.extract 0 4) = true) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨heq0, htake⟩ := cMatches 0 (by omega) hsz4 hmatch
  obtain ⟨_, _, rd52⟩ :=
    cReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) 0 (by omega) ⟨52⟩ hcode hwv hsz4
      hsize heq0 htake (by jump_dest) (by decide)
  have rd139 := evm_run rd52 with [
    jumpdest, push1 ⟨67⟩, push1 ⟨63⟩, calldatasize, push1 ⟨4⟩, push1 ⟨139⟩,
    jump (by jump_dest) ]
  have hsltval :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact RD.cDecodeUint256_revert rd139 hsltval (by evm_ov)

/-- External `g(uint256)`: selector matched, but the `uint256` word is incomplete. -/
theorem cX_g_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (_hfmiss : (cSelBytes 0 == I.calldata.extract 0 4) = false)
    (hgmatch : (cSelBytes 1 == I.calldata.extract 0 4) = true) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨heq0, htake⟩ := cMatches 1 (by omega) hsz4 hgmatch
  obtain ⟨_, _, rd85⟩ :=
    cReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) 1 (by omega) ⟨85⟩ hcode hwv hsz4
      hsize heq0 htake (by jump_dest) (by decide)
  have rd139 := evm_run rd85 with [
    jumpdest, push1 ⟨100⟩, push1 ⟨96⟩, calldatasize, push1 ⟨4⟩, push1 ⟨139⟩,
    jump (by jump_dest) ]
  have hsltval :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  exact RD.cDecodeUint256_revert rd139 hsltval (by evm_ov)

/-- External `g(uint256)`: selector matched, but solc's signed length check rejects huge calldata. -/
theorem cX_g_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (_hfmiss : (cSelBytes 0 == I.calldata.extract 0 4) = false)
    (hgmatch : (cSelBytes 1 == I.calldata.extract 0 4) = true) :
    RDrev cBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨heq0, htake⟩ := cMatches 1 (by omega) hsz4 hgmatch
  obtain ⟨_, _, rd85⟩ :=
    cReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) 1 (by omega) ⟨85⟩ hcode hwv hsz4
      hsize heq0 htake (by jump_dest) (by decide)
  have rd139 := evm_run rd85 with [
    jumpdest, push1 ⟨100⟩, push1 ⟨96⟩, calldatasize, push1 ⟨4⟩, push1 ⟨139⟩,
    jump (by jump_dest) ]
  have hsltval :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact RD.cDecodeUint256_revert rd139 hsltval (by evm_ov)

/-! ## Source-side body obligations -/

theorem cFResultWord_toNat {I : ExecutionEnv}
    (hbound : 2 * (cArgWord I).toNat + 1 < UInt256.size) :
    (cFResultWord I).toNat = 2 * (cArgWord I).toNat + 1 := by
  unfold cFResultWord
  have hmul : 2 * (cArgWord I).toNat < UInt256.size := by omega
  have hprod : (UInt256.mul (cArgWord I) ⟨2⟩).toNat = 2 * (cArgWord I).toNat :=
    mul2_toNat hmul
  have hadd : (UInt256.mul (cArgWord I) ⟨2⟩).toNat + 1 < UInt256.size := by
    rw [hprod]
    exact hbound
  rw [add1_toNat hadd, hprod]

theorem cArgStore_v (I : ExecutionEnv) :
    (cArgStore I).get? "v" = some (cArgValue I) := by
  simp [cArgStore, cArgValue]

theorem cEvalFReturn_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound : 2 * (cArgWord I).toNat + 1 < UInt256.size) :
    evalExpr? cConfig { contract := Reuse.cContract, locals := cArgStore I } evm
      (.inRange Reuse.uint256Int
        (.binary .add (.binary .mul (.var "v") (.intLit 2)) (.intLit 1))) =
      .ok (cFResultValue I) := by
  have hres := cFResultWord_toNat (I := I) hbound
  have hnotNeg : ¬ Int.ofNat (cArgWord I).toNat * 2 + 1 < 0 := by
    have hn : 0 ≤ Int.ofNat (cArgWord I).toNat := Int.natCast_nonneg _
    nlinarith
  have hnotGe : ¬ Int.ofNat (cArgWord I).toNat * 2 + 1 ≥ (2 : Int) ^ 256 := by
    have hlt : Int.ofNat (2 * (cArgWord I).toNat + 1) < (2 : Int) ^ 256 :=
      Int.ofNat_lt.mpr (by simpa [UInt256.size] using hbound)
    have heq : Int.ofNat (2 * (cArgWord I).toNat + 1) =
        Int.ofNat (cArgWord I).toNat * 2 + 1 := by
      rw [show 2 * (cArgWord I).toNat + 1 = (cArgWord I).toNat * 2 + 1 by omega]
      simp
    omega
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [cArgStore_v]
  simp only [evalBinaryOp?, Reuse.uint256Int]
  rw [show (decide (Int.ofNat (cArgWord I).toNat * 2 + 1 < 0) ||
        decide (Int.ofNat (cArgWord I).toNat * 2 + 1 ≥ (2 : Int) ^ 256)) = false by
      rw [decide_eq_false hnotNeg, decide_eq_false hnotGe]
      rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [cFResultValue]
  rw [hres]
  rw [show Int.ofNat (2 * (cArgWord I).toNat + 1) =
      Int.ofNat (cArgWord I).toNat * 2 + 1 by
      rw [show 2 * (cArgWord I).toNat + 1 = (cArgWord I).toNat * 2 + 1 by omega]
      simp]

theorem cEvalFReturn_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ 2 * (cArgWord I).toNat + 1) :
    evalExpr? cConfig { contract := Reuse.cContract, locals := cArgStore I } evm
      (.inRange Reuse.uint256Int
        (.binary .add (.binary .mul (.var "v") (.intLit 2)) (.intLit 1))) = .revert := by
  have hge : Int.ofNat (cArgWord I).toNat * 2 + 1 ≥ (2 : Int) ^ 256 := by
    have hge' : (2 : Int) ^ 256 ≤ Int.ofNat (2 * (cArgWord I).toNat + 1) :=
      Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)
    have heq : Int.ofNat (2 * (cArgWord I).toNat + 1) =
        Int.ofNat (cArgWord I).toNat * 2 + 1 := by
      rw [show 2 * (cArgWord I).toNat + 1 = (cArgWord I).toNat * 2 + 1 by omega]
      simp
    omega
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [cArgStore_v]
  simp only [evalBinaryOp?, Reuse.uint256Int]
  rw [show (decide (Int.ofNat (cArgWord I).toNat * 2 + 1 < 0) ||
        decide (Int.ofNat (cArgWord I).toNat * 2 + 1 ≥ (2 : Int) ^ 256)) = true by
      rw [decide_eq_true hge]
      simp]
  rfl

theorem cFBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : 2 * (cArgWord I).toNat + 1 < UInt256.size) :
    ExecTransitionBody cConfig Reuse.cContract evm (cArgStore I) Reuse.fTransition.body
      (.returned { contract := Reuse.cContract, locals := cArgStore I } evm
        (some (cFResultValue I))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).returns
      (cEvalFReturn_ok evm I hbound)

theorem cFBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hover : UInt256.size ≤ 2 * (cArgWord I).toNat + 1) :
    ExecTransitionBody cConfig Reuse.cContract evm (cArgStore I) Reuse.fTransition.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (cEvalFReturn_revert evm I hover)))

abbrev cGStoreAfterF (I : ExecutionEnv) : Store :=
  (cArgStore I).insert "r" (cFResultValue I)

theorem cGStoreAfterF_r (I : ExecutionEnv) :
    (cGStoreAfterF I).get? "r" = some (cFResultValue I) := by
  simp [cGStoreAfterF, cFResultValue]

theorem cGStoreAfterF_s_none (I : ExecutionEnv) :
    (cGStoreAfterF I).get? "s" = none := by
  simp [cGStoreAfterF, cArgStore, cFResultValue, cArgValue]

theorem cEvalArgs_v (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? cConfig { contract := Reuse.cContract, locals := cArgStore I } evm [.var "v"] =
      .ok [cArgValue I] := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, cArgStore_v, EvalResult.bind, bind, pure]

theorem cEvalR (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? cConfig { contract := Reuse.cContract, locals := cGStoreAfterF I } evm (.var "r") =
      .ok (cFResultValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, cGStoreAfterF_r]

theorem cLookupF : lookupCallable? Reuse.cContract "f" = some Reuse.fTransition.toCallable := by
  rfl

theorem cBindFArg (I : ExecutionEnv) :
    bindParams? Reuse.fTransition.toCallable.params [cArgValue I] = some (cArgStore I) := by
  change bindParams? [{ name := "v", ty := Reuse.uint256 }] [cArgValue I] =
    some ((∅ : Store).insert "v" (cArgValue I))
  rfl

theorem cWordOfInt_ofNat_toNat (a : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

theorem cStorageLocStore_uint256 (evm : EVM.State) (val : UInt256) :
    storageLocStore evm Reuse.sLoc (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ val) := by
  unfold storageLocStore storageLocWriteWord Reuse.sLoc
  simp only [valueToWord, cWordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = val.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]),
    fromBytes'_toBytesLEWithSizeProof]

theorem cAssignS (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? cConfig { contract := Reuse.cContract, locals := cGStoreAfterF I } evm
        .storage Reuse.sRef (cFResultValue I) =
      .ok ({ contract := Reuse.cContract, locals := cGStoreAfterF I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ (cFResultWord I)) := by
  apply assignStorageRef_storage_scalar
    (er := ({ base := "s", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int Reuse.uint256Int)) (loc := Reuse.sLoc)
  · exact cGStoreAfterF_s_none I
  · simp [evalStorageRef, evalStorageRefSteps, Reuse.sRef, EvalResult.bind, bind, pure]
  · simp [storageTypeAt?, Reuse.cContract]
  · rfl
  · exact cStorageLocStore_uint256 evm (cFResultWord I)

theorem cGBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : 2 * (cArgWord I).toNat + 1 < UInt256.size) :
    ExecTransitionBody cConfig Reuse.cContract evm (cArgStore I) Reuse.gTransition.body
      (.returned { contract := Reuse.cContract, locals := cGStoreAfterF I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ (cFResultWord I)) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  have hcall : ExecStmt cConfig { contract := Reuse.cContract, locals := cArgStore I } evm
      (.internalCall "f" [.var "v"] "r")
      (.ok { contract := Reuse.cContract, locals := cGStoreAfterF I } evm) := by
    refine
      ExecStmt.internalCallReturn
        (cfg := cConfig)
        (solm := { contract := Reuse.cContract, locals := cArgStore I })
        (evm := evm) (name := "f") (args := [.var "v"]) (retVar := "r")
        (argVals := [cArgValue I]) (callee := Reuse.fTransition.toCallable)
        (locals := cArgStore I)
        (calleeSolm := { contract := Reuse.cContract, locals := cArgStore I })
        (calleeEvm := evm) (value := some (cFResultValue I))
        (cEvalArgs_v evm I) cLookupF (cBindFArg I) ?_
    simpa [ExecTransitionBody, TransitionDecl.toCallable, cFResultValue] using
      cFBodyReturns evm I hwv hbound
  refine ExecBlock.consNormal hcall ?_
  exact ExecBlock.consNormal (ExecStmt.assign (cEvalR evm I) (cAssignS evm I)) ExecBlock.nil

theorem cGBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hover : UInt256.size ≤ 2 * (cArgWord I).toNat + 1) :
    ExecTransitionBody cConfig Reuse.cContract evm (cArgStore I) Reuse.gTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert <|
    ExecStmt.internalCallRevert (cEvalArgs_v evm I) cLookupF (cBindFArg I) <|
      by
        simpa [ExecTransitionBody, TransitionDecl.toCallable] using
          cFBodyReverts_overflow evm I hwv hover

theorem cUint256ReturnEncoding (I : ExecutionEnv) :
    encodeReturnValue? Reuse.uint256 (cFResultValue I) =
      some (UInt256.toByteArray (cFResultWord I)) := by
  simpa [Reuse.uint256, cFResultValue] using uint256ReturnEncoding (cFResultWord I)

/-! ## Top-level revert obligations -/

/-- No selector matches: the EVM falls through to the no-match revert and Solm does not dispatch. -/
theorem cNoDispatch {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 2 → (cSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor cConfig Reuse.cContract cA gh bl σ σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (cX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm).reEquivNoDispatch
      hcode (cDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (cX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch hcode
      (cDispatch_none_short hshort)

/-- Calldata shorter than a selector: the size guard reverts before dispatch. -/
theorem cShortRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor cConfig Reuse.cContract cA gh bl σ σ₀ g A I := by
  exact (cX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (cDispatch_none_short hsz)

/-- Non-zero callvalue: both Solm transition bodies and the bytecode revert as non-payable. -/
theorem cNonPayable {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor cConfig Reuse.cContract cA gh bl σ σ₀ g A I := by
  exact (cX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg Reuse.cContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ Reuse.cContract.transitions := by
          rw [dispatchMsg_eq_dispatchList] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldata (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (cBodyReverts_nonPayable t htmem (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Runtime equivalence when the global non-payable guard accepts the call. -/
theorem cReEquiv_callvalueZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) :
    runtimeEquivalenceFor cConfig Reuse.cContract cA gh bl σ σ₀ g A I := by
  by_cases hselShort : I.calldata.size < 4
  · exact cShortRevert hcode hsize hperm hwv hselShort
  · have hsz4 : 4 ≤ I.calldata.size := by omega
    by_cases hf : (cSelBytes 0 == I.calldata.extract 0 4) = true
    · have hd := cDispatch_f (cd := I.calldata) hf
      by_cases hsz36 : 36 ≤ I.calldata.size
      · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
        · have hdec := cDecode_f_ok (I := I) hsz36 hbig
          by_cases hbound : 2 * (cArgWord I).toNat + 1 < UInt256.size
          · have hbody := cFBodyReturns
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hbound
            exact (cX_f_success (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hf
                hbound).reEquivExecution hcode hd hdec hbody
              (returnEquiv_of_encode (cUint256ReturnEncoding I))
          · have hover : UInt256.size ≤ 2 * (cArgWord I).toNat + 1 := by omega
            have hbody := cFBodyReverts_overflow
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hover
            exact (cX_f_overflow (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hf
                hover).reEquivExecutionRevert hcode hd hdec hbody
        · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
          have hdec := cDecode_f_none_huge (I := I) hbigge
          exact (cX_f_hugearg (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hbigge
              hf).reEquivDecodingFailed hcode hd hdec
      · have hshort : I.calldata.size < 36 := by omega
        have hdec := cDecode_f_none_short (I := I) hshort
        exact (cX_f_shortarg (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hshort
            hf).reEquivDecodingFailed hcode hd hdec
    · rw [Bool.not_eq_true] at hf
      by_cases hg : (cSelBytes 1 == I.calldata.extract 0 4) = true
      · have hd := cDispatch_g (cd := I.calldata) hf hg
        by_cases hsz36 : 36 ≤ I.calldata.size
        · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
          · have hdec := cDecode_g_ok (I := I) hsz36 hbig
            by_cases hbound : 2 * (cArgWord I).toNat + 1 < UInt256.size
            · have hbody := cGBodyReturns
                (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hbound
              exact (cX_g_success (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize
                  hperm hf hg hbound).reEquivExecutionGen hcode hd hdec hbody
                (by
                  rw [storageStore_createdAccounts, storageStore_accountMap]
                  simp [initState])
                (returnEquiv.void rfl rfl rfl)
            · have hover : UInt256.size ≤ 2 * (cArgWord I).toNat + 1 := by omega
              have hbody := cGBodyReverts_overflow
                (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hover
              exact (cX_g_overflow (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize
                  hf hg hover).reEquivExecutionRevert hcode hd hdec hbody
          · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
            have hdec := cDecode_g_none_huge (I := I) hbigge
            exact (cX_g_hugearg (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hbigge
                hf hg).reEquivDecodingFailed hcode hd hdec
        · have hshort : I.calldata.size < 36 := by omega
          have hdec := cDecode_g_none_short (I := I) hshort
          exact (cX_g_shortarg (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hshort
              hf hg).reEquivDecodingFailed hcode hd hdec
      · rw [Bool.not_eq_true] at hg
        have hnm : ∀ i, i < 2 → (cSelBytes i == I.calldata.extract 0 4) = false := by
          intro i hi
          interval_cases i
          · exact hf
          · exact hg
        exact cNoDispatch hcode hsize hperm hwv hnm

/-- **Correctness of `C`.** -/
theorem cCorrect : runtimeEquivalence!?! cConfig cBytecode Reuse.cContract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize hperm => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact cReEquiv_callvalueZero hcode hsize hperm hwv
  · exact cNonPayable hcode hwv
