import Benchmarks.Dss.Vat.Trusted

/-!
# MakerDAO/Sky DSS Vat dispatcher facts

This file is the local home for Solm dispatch routing facts and shared dispatcher/revert proof
infrastructure. The first scaffold pass keeps the hard EVM reachability leaves as body stubs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vat

abbrev vatDispatchRevertPc : UInt256 := ⟨452⟩
abbrev vatDispatchBodyPc : UInt256 := ⟨18⟩
abbrev vatSelectorLoadPc : UInt256 := ⟨26⟩

abbrev vatRootSplitPc : UInt256 := ⟨32⟩
abbrev vatHighSplitPc : UInt256 := ⟨43⟩
abbrev vatHighHighSplitPc : UInt256 := ⟨54⟩
abbrev vatHighLowSplitPc : UInt256 := ⟨152⟩
abbrev vatLowSplitPc : UInt256 := ⟨250⟩
abbrev vatLowHighSplitPc : UInt256 := ⟨261⟩
abbrev vatLowLowSplitPc : UInt256 := ⟨359⟩

abbrev vatArms65FirstPc : UInt256 := ⟨65⟩
abbrev vatArms114FirstPc : UInt256 := ⟨114⟩
abbrev vatArms163FirstPc : UInt256 := ⟨163⟩
abbrev vatArms212FirstPc : UInt256 := ⟨212⟩
abbrev vatArms272FirstPc : UInt256 := ⟨272⟩
abbrev vatArms321FirstPc : UInt256 := ⟨321⟩
abbrev vatArms370FirstPc : UInt256 := ⟨370⟩
abbrev vatArms419FirstPc : UInt256 := ⟨419⟩

def vatArms65SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xdc, 0x4d, 0x20, 0xfa]⟩ -- nope(address)
  | 1 => ⟨#[0xf0, 0x59, 0x21, 0x2a]⟩ -- sin(address)
  | 2 => ⟨#[0xf2, 0x4e, 0x23, 0xeb]⟩ -- suck(address,address,uint256)
  | _ => ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩ -- heal(uint256)

def vatArms114SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xbb, 0x35, 0x78, 0x3b]⟩ -- move(address,address,uint256)
  | 1 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩ -- ilks(bytes32)

def vatArms163SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 1 => ⟨#[0xa3, 0xb2, 0x2f, 0xc4]⟩ -- hope(address)
  | 2 => ⟨#[0xb6, 0x53, 0x37, 0xdf]⟩ -- fold(bytes32,address,int256)
  | _ => ⟨#[0xba, 0xbe, 0x8a, 0x3f]⟩ -- Line()

def vatArms212SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x7c, 0xdd, 0x3f, 0xde]⟩ -- slip(bytes32,address,int256)
  | 1 => ⟨#[0x87, 0x0c, 0x61, 0x6d]⟩ -- fork(bytes32,address,address,int256,int256)
  | _ => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()

def vatArms272SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | 1 => ⟨#[0x6c, 0x25, 0xb3, 0x46]⟩ -- dai(address)
  | 2 => ⟨#[0x76, 0x08, 0x87, 0x03]⟩ -- frob(bytes32,address,address,address,int256,int256)
  | _ => ⟨#[0x7b, 0xab, 0x3f, 0x40]⟩ -- grab(bytes32,address,address,address,int256,int256)

def vatArms321SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x45, 0x38, 0xc4, 0xeb]⟩ -- can(address,address)
  | 1 => ⟨#[0x61, 0x11, 0xbe, 0x2e]⟩ -- flux(bytes32,address,address,uint256)
  | _ => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)

def vatArms370SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x24, 0x24, 0xbe, 0x5c]⟩ -- urns(bytes32,address)
  | 1 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 2 => ⟨#[0x2d, 0x61, 0xa3, 0x55]⟩ -- vice()
  | _ => ⟨#[0x3b, 0x66, 0x31, 0x95]⟩ -- init(bytes32)

def vatArms419SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x0d, 0xca, 0x59, 0xc1]⟩ -- debt()
  | 1 => ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩ -- file(bytes32,bytes32,uint256)
  | _ => ⟨#[0x21, 0x44, 0x14, 0xd5]⟩ -- gem(bytes32,address)

theorem vatSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    vatSelWord I = sel := by
  simpa [vatSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

attribute [local simp]
  LineSelectorBytes
  cageSelectorBytes
  canSelectorBytes
  daiSelectorBytes
  debtSelectorBytes
  denySelectorBytes
  fileIlkSelectorBytes
  fileLineSelectorBytes
  fluxSelectorBytes
  foldSelectorBytes
  forkSelectorBytes
  frobSelectorBytes
  gemSelectorBytes
  grabSelectorBytes
  healSelectorBytes
  hopeSelectorBytes
  ilksSelectorBytes
  initSelectorBytes
  liveSelectorBytes
  moveSelectorBytes
  nopeSelectorBytes
  relySelectorBytes
  sinSelectorBytes
  slipSelectorBytes
  suckSelectorBytes
  urnsSelectorBytes
  viceSelectorBytes
  wardsSelectorBytes

theorem vatDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList transitions cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp [transitions] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals
      simp [selectorOf]
      native_decide) h

theorem vatDispatchDebt {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 4)) :
    dispatchMsg contract I.calldata = some debtTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some debtTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem vatDispatchLine {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 0)) :
    dispatchMsg contract I.calldata = some LineTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some LineTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem vatDispatchDai {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 3)) :
    dispatchMsg contract I.calldata = some daiTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some daiTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem vatDispatchCan {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 2)) :
    dispatchMsg contract I.calldata = some canTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some canTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem vatDispatchSin {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 22)) :
    dispatchMsg contract I.calldata = some sinTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 22 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some sinTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem vatDispatchLive {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 18)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 18 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem vatDispatchVice {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 26)) :
    dispatchMsg contract I.calldata = some viceTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 26 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some viceTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem vatDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 27)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 27 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem vatDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 28 → (vatSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · rw [selectorOf, LineSelectorBytes]
    simpa [vatSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, cageSelectorBytes]
    simpa [vatSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, canSelectorBytes]
    simpa [vatSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, daiSelectorBytes]
    simpa [vatSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, debtSelectorBytes]
    simpa [vatSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [vatSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, fileIlkSelectorBytes]
    simpa [vatSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, fileLineSelectorBytes]
    simpa [vatSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, fluxSelectorBytes]
    simpa [vatSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, foldSelectorBytes]
    simpa [vatSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, forkSelectorBytes]
    simpa [vatSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, frobSelectorBytes]
    simpa [vatSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, gemSelectorBytes]
    simpa [vatSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, grabSelectorBytes]
    simpa [vatSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, healSelectorBytes]
    simpa [vatSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, hopeSelectorBytes]
    simpa [vatSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, ilksSelectorBytes]
    simpa [vatSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, initSelectorBytes]
    simpa [vatSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [vatSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, moveSelectorBytes]
    simpa [vatSelBytes] using hnm 19 (by omega)
  · rw [selectorOf, nopeSelectorBytes]
    simpa [vatSelBytes] using hnm 20 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [vatSelBytes] using hnm 21 (by omega)
  · rw [selectorOf, sinSelectorBytes]
    simpa [vatSelBytes] using hnm 22 (by omega)
  · rw [selectorOf, slipSelectorBytes]
    simpa [vatSelBytes] using hnm 23 (by omega)
  · rw [selectorOf, suckSelectorBytes]
    simpa [vatSelBytes] using hnm 24 (by omega)
  · rw [selectorOf, urnsSelectorBytes]
    simpa [vatSelBytes] using hnm 25 (by omega)
  · rw [selectorOf, viceSelectorBytes]
    simpa [vatSelBytes] using hnm 26 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [vatSelBytes] using hnm 27 (by omega)

theorem vatBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals exact bodyReverts_nonPayable h

theorem vatRootSplitWellFormed :
    selectorSplitWellFormed vatBytecode vatRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vatHighSplitWellFormed :
    selectorSplitWellFormed vatBytecode vatHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vatHighHighSplitWellFormed :
    selectorSplitWellFormed vatBytecode vatHighHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vatHighLowSplitWellFormed :
    selectorSplitWellFormed vatBytecode vatHighLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vatLowSplitWellFormed :
    selectorSplitWellFormed vatBytecode vatLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vatLowHighSplitWellFormed :
    selectorSplitWellFormed vatBytecode vatLowHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vatLowLowSplitWellFormed :
    selectorSplitWellFormed vatBytecode vatLowLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem vatArms65WellFormed :
    ∀ j, j ≤ 3 → armWellFormed vatBytecode
      (nthArmPc vatBytecode vatArms65FirstPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vatArms114WellFormed :
    ∀ j, j ≤ 2 → armWellFormed vatBytecode
      (nthArmPc vatBytecode vatArms114FirstPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vatArms163WellFormed :
    ∀ j, j ≤ 3 → armWellFormed vatBytecode
      (nthArmPc vatBytecode vatArms163FirstPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vatArms212WellFormed :
    ∀ j, j ≤ 2 → armWellFormed vatBytecode
      (nthArmPc vatBytecode vatArms212FirstPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vatArms272WellFormed :
    ∀ j, j ≤ 3 → armWellFormed vatBytecode
      (nthArmPc vatBytecode vatArms272FirstPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vatArms321WellFormed :
    ∀ j, j ≤ 2 → armWellFormed vatBytecode
      (nthArmPc vatBytecode vatArms321FirstPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vatArms370WellFormed :
    ∀ j, j ≤ 3 → armWellFormed vatBytecode
      (nthArmPc vatBytecode vatArms370FirstPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vatArms419WellFormed :
    ∀ j, j ≤ 2 → armWellFormed vatBytecode
      (nthArmPc vatBytecode vatArms419FirstPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem vatArms65Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc j))
        (vatSelWord I) =
      if (vatArms65SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vatArms114Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc j))
        (vatSelWord I) =
      if (vatArms114SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vatArms163Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc j))
        (vatSelWord I) =
      if (vatArms163SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vatArms212Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc j))
        (vatSelWord I) =
      if (vatArms212SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vatArms272Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc j))
        (vatSelWord I) =
      if (vatArms272SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vatArms321Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc j))
        (vatSelWord I) =
      if (vatArms321SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vatArms370Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc j))
        (vatSelWord I) =
      if (vatArms370SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vatArms419Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 3) :
    UInt256.eq
        (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc j))
        (vatSelWord I) =
      if (vatArms419SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vatJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode vatBytecode pc = some (.Push .PUSH2, some (vatDispatchRevertPc, 2)))
    (hjump : decode vatBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h452 := h.push2 vatDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h452 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem vatArms65NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) vatArms65FirstPc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc j))
        (vatSelWord I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (vatArms65WellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms65WellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms65WellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms65WellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact vatJumpToNoMatchRevert h109 (by native_decide) (by native_decide)

theorem vatArms114NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) vatArms114FirstPc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc j))
        (vatSelWord I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h147 := h
    |>.selectorArmNotTakenAuto (vatArms114WellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms114WellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms114WellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
  exact vatJumpToNoMatchRevert h147 (by native_decide) (by native_decide)

theorem vatArms163NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) vatArms163FirstPc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc j))
        (vatSelWord I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h207 := h
    |>.selectorArmNotTakenAuto (vatArms163WellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms163WellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms163WellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms163WellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact vatJumpToNoMatchRevert h207 (by native_decide) (by native_decide)

theorem vatArms212NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) vatArms212FirstPc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc j))
        (vatSelWord I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h245 := h
    |>.selectorArmNotTakenAuto (vatArms212WellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms212WellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms212WellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
  exact vatJumpToNoMatchRevert h245 (by native_decide) (by native_decide)

theorem vatArms272NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) vatArms272FirstPc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc j))
        (vatSelWord I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h316 := h
    |>.selectorArmNotTakenAuto (vatArms272WellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms272WellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms272WellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms272WellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact vatJumpToNoMatchRevert h316 (by native_decide) (by native_decide)

theorem vatArms321NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) vatArms321FirstPc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc j))
        (vatSelWord I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h354 := h
    |>.selectorArmNotTakenAuto (vatArms321WellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms321WellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms321WellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
  exact vatJumpToNoMatchRevert h354 (by native_decide) (by native_decide)

theorem vatArms370NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) vatArms370FirstPc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc j))
        (vatSelWord I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h414 := h
    |>.selectorArmNotTakenAuto (vatArms370WellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms370WellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms370WellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms370WellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
  exact vatJumpToNoMatchRevert h414 (by native_decide) (by native_decide)

theorem vatArms419NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) vatArms419FirstPc
      [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc j))
        (vatSelWord I) = ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h452 := h
    |>.selectorArmNotTakenAuto (vatArms419WellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms419WellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vatArms419WellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h452 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem vatReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatRootSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [vatRootSplitPc, vatSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := vatBytecode)
      (bodyPc := vatDispatchBodyPc) (loadPc := vatSelectorLoadPc)
      (firstPc := vatRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := vatDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

set_option maxHeartbeats 1000000 in
theorem vatReachArms419First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatArms419FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h249 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatRootSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 vatRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h250 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [vatLowSplitPc, vatRootSplitPc, armTgt, pushAt]
      using h249.jumpdest (by native_decide) (by simp)
  have h358 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatLowSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) :=
    RD.selectorSplitTakenAuto h250 vatLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h359 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatLowLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5 + 1) (C32 + 22 + 1 + 22 + 1) := by
    simpa [vatLowLowSplitPc, vatLowSplitPc, armTgt, pushAt]
      using h358.jumpdest (by native_decide) (by simp)
  have h418 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatLowLowSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5 + 1 + 5) (C32 + 22 + 1 + 22 + 1 + 22) :=
    RD.selectorSplitTakenAuto h359 vatLowLowSplitWellFormed hlowlow
      (by jump_dest) (by simp)
  have h419 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatArms419FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5 + 1 + 5 + 1)
      (C32 + 22 + 1 + 22 + 1 + 22 + 1) := by
    simpa [vatArms419FirstPc, vatLowLowSplitPc, armTgt, pushAt]
      using h418.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h419⟩

theorem vatReachArms419Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc j))
        (vatSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc i))
        (vatSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vatBytecode 0).contains bodyPC = true)
    (hbody : armTgt vatBytecode (nthArmPc vatBytecode vatArms419FirstPc i) = bodyPC) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vatReachArms419First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hlowlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vatArms419WellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

set_option maxHeartbeats 1000000 in
theorem vatReachArms163First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) = ⟨0⟩) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatArms163FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [vatHighSplitPc, vatRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 vatRootSplitWellFormed hroot (by simp)
  have h151 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatHighSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k32 + 5 + 5) (C32 + 22 + 22) :=
    RD.selectorSplitTakenAuto h43 vatHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h152 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatHighLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa [vatHighLowSplitPc, vatHighSplitPc, armTgt, pushAt]
      using h151.jumpdest (by native_decide) (by simp)
  have h163 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatArms163FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) := by
    simpa [vatArms163FirstPc, vatHighLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h152 vatHighLowSplitWellFormed hhighlow (by simp)
  exact ⟨_, _, h163⟩

theorem vatReachArms163Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc j))
        (vatSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc i))
        (vatSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vatBytecode 0).contains bodyPC = true)
    (hbody : armTgt vatBytecode (nthArmPc vatBytecode vatArms163FirstPc i) = bodyPC) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vatReachArms163First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vatArms163WellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

set_option maxHeartbeats 1000000 in
theorem vatReachArms212First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatArms212FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [vatHighSplitPc, vatRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 vatRootSplitWellFormed hroot (by simp)
  have h151 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatHighSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k32 + 5 + 5) (C32 + 22 + 22) :=
    RD.selectorSplitTakenAuto h43 vatHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h152 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatHighLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa [vatHighLowSplitPc, vatHighSplitPc, armTgt, pushAt]
      using h151.jumpdest (by native_decide) (by simp)
  have h211 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatHighLowSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) :=
    RD.selectorSplitTakenAuto h152 vatHighLowSplitWellFormed hhighlow
      (by jump_dest) (by simp)
  have h212 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatArms212FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 5 + 1 + 5 + 1) (C32 + 22 + 22 + 1 + 22 + 1) := by
    simpa [vatArms212FirstPc, vatHighLowSplitPc, armTgt, pushAt]
      using h211.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h212⟩

theorem vatReachArms212Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hhighlow :
      UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc j))
        (vatSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc i))
        (vatSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vatBytecode 0).contains bodyPC = true)
    (hbody : armTgt vatBytecode (nthArmPc vatBytecode vatArms212FirstPc i) = bodyPC) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vatReachArms212First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vatArms212WellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

set_option maxHeartbeats 1000000 in
theorem vatReachArms370First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) = ⟨0⟩) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatArms370FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h249 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatRootSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 vatRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h250 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [vatLowSplitPc, vatRootSplitPc, armTgt, pushAt]
      using h249.jumpdest (by native_decide) (by simp)
  have h358 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatLowSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) :=
    RD.selectorSplitTakenAuto h250 vatLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h359 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatLowLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5 + 1) (C32 + 22 + 1 + 22 + 1) := by
    simpa [vatLowLowSplitPc, vatLowSplitPc, armTgt, pushAt]
      using h358.jumpdest (by native_decide) (by simp)
  have h370 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatArms370FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5 + 1 + 5) (C32 + 22 + 1 + 22 + 1 + 22) := by
    simpa [vatArms370FirstPc, vatLowLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h359 vatLowLowSplitWellFormed hlowlow (by simp)
  exact ⟨_, _, h370⟩

theorem vatReachArms370Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc j))
        (vatSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc i))
        (vatSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vatBytecode 0).contains bodyPC = true)
    (hbody : armTgt vatBytecode (nthArmPc vatBytecode vatArms370FirstPc i) = bodyPC) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vatReachArms370First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hlowlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vatArms370WellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

set_option maxHeartbeats 1000000 in
theorem vatReachArms114First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatArms114FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [vatHighSplitPc, vatRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 vatRootSplitWellFormed hroot (by simp)
  have h54 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatHighHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [vatHighHighSplitPc, vatHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 vatHighSplitWellFormed hhigh (by simp)
  have h113 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatHighHighSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) :=
    RD.selectorSplitTakenAuto h54 vatHighHighSplitWellFormed hhighhigh
      (by jump_dest) (by simp)
  have h114 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatArms114FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 5 + 5 + 1) (C32 + 22 + 22 + 22 + 1) := by
    simpa [vatArms114FirstPc, vatHighHighSplitPc, armTgt, pushAt]
      using h113.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h114⟩

theorem vatReachArms114Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc j))
        (vatSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc i))
        (vatSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vatBytecode 0).contains bodyPC = true)
    (hbody : armTgt vatBytecode (nthArmPc vatBytecode vatArms114FirstPc i) = bodyPC) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vatReachArms114First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vatArms114WellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

set_option maxHeartbeats 1000000 in
theorem vatReachArms272First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩)
    (hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) = ⟨0⟩) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatArms272FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h249 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatRootSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 vatRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h250 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [vatLowSplitPc, vatRootSplitPc, armTgt, pushAt]
      using h249.jumpdest (by native_decide) (by simp)
  have h261 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatLowHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [vatLowHighSplitPc, vatLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h250 vatLowSplitWellFormed hlow (by simp)
  have h272 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatArms272FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
    simpa [vatArms272FirstPc, vatLowHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h261 vatLowHighSplitWellFormed hlowhigh (by simp)
  exact ⟨_, _, h272⟩

theorem vatReachArms272Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩)
    (hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc j))
        (vatSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc i))
        (vatSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vatBytecode 0).contains bodyPC = true)
    (hbody : armTgt vatBytecode (nthArmPc vatBytecode vatArms272FirstPc i) = bodyPC) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vatReachArms272First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hlowhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vatArms272WellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

set_option maxHeartbeats 1000000 in
theorem vatReachArms65First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) = ⟨0⟩) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatArms65FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [vatHighSplitPc, vatRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 vatRootSplitWellFormed hroot (by simp)
  have h54 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatHighHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [vatHighHighSplitPc, vatHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 vatHighSplitWellFormed hhigh (by simp)
  have h65 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatArms65FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
    simpa [vatArms65FirstPc, vatHighHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h54 vatHighHighSplitWellFormed hhighhigh (by simp)
  exact ⟨_, _, h65⟩

theorem vatReachArms65Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩)
    (hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc j))
        (vatSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc i))
        (vatSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vatBytecode 0).contains bodyPC = true)
    (hbody : armTgt vatBytecode (nthArmPc vatBytecode vatArms65FirstPc i) = bodyPC) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vatReachArms65First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh hhighhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vatArms65WellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

set_option maxHeartbeats 1000000 in
theorem vatReachArms321First {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩)
    (hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatArms321FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h249 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatRootSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 vatRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h250 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [vatLowSplitPc, vatRootSplitPc, armTgt, pushAt]
      using h249.jumpdest (by native_decide) (by simp)
  have h261 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatLowHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [vatLowHighSplitPc, vatLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h250 vatLowSplitWellFormed hlow (by simp)
  have h320 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vatBytecode vatLowHighSplitPc) [vatSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) :=
    RD.selectorSplitTakenAuto h261 vatLowHighSplitWellFormed hlowhigh
      (by jump_dest) (by simp)
  have h321 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
      vatArms321FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ)
      (k32 + 5 + 1 + 5 + 5 + 1) (C32 + 22 + 1 + 22 + 22 + 1) := by
    simpa [vatArms321FirstPc, vatLowHighSplitPc, armTgt, pushAt]
      using h320.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h321⟩

theorem vatReachArms321Body {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 2) (bodyPC : UInt256)
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩)
    (hlowhigh :
      UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc j))
        (vatSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc i))
        (vatSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vatBytecode 0).contains bodyPC = true)
    (hbody : armTgt vatBytecode (nthArmPc vatBytecode vatArms321FirstPc i) = bodyPC) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vatReachArms321First (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow hlowhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vatArms321WellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

set_option maxHeartbeats 3000000 in
theorem vatX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 28 → (vatSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq65 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vatArms65Eq I hsz 0 (by omega)]
      have hfalse : (vatArms65SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vatArms65SelBytes, vatSelBytes] using hnm 20 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms65Eq I hsz 1 (by omega)]
      have hfalse : (vatArms65SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vatArms65SelBytes, vatSelBytes] using hnm 22 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms65Eq I hsz 2 (by omega)]
      have hfalse : (vatArms65SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vatArms65SelBytes, vatSelBytes] using hnm 24 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms65Eq I hsz 3 (by omega)]
      have hfalse : (vatArms65SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vatArms65SelBytes, vatSelBytes] using hnm 14 (by omega)
      rw [hfalse]; rfl
  have heq114 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms114FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vatArms114Eq I hsz 0 (by omega)]
      have hfalse : (vatArms114SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vatArms114SelBytes, vatSelBytes] using hnm 19 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms114Eq I hsz 1 (by omega)]
      have hfalse : (vatArms114SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vatArms114SelBytes, vatSelBytes] using hnm 27 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms114Eq I hsz 2 (by omega)]
      have hfalse : (vatArms114SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vatArms114SelBytes, vatSelBytes] using hnm 16 (by omega)
      rw [hfalse]; rfl
  have heq163 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms163FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vatArms163Eq I hsz 0 (by omega)]
      have hfalse : (vatArms163SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vatArms163SelBytes, vatSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms163Eq I hsz 1 (by omega)]
      have hfalse : (vatArms163SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vatArms163SelBytes, vatSelBytes] using hnm 15 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms163Eq I hsz 2 (by omega)]
      have hfalse : (vatArms163SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vatArms163SelBytes, vatSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms163Eq I hsz 3 (by omega)]
      have hfalse : (vatArms163SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vatArms163SelBytes, vatSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
  have heq212 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms212FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vatArms212Eq I hsz 0 (by omega)]
      have hfalse : (vatArms212SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vatArms212SelBytes, vatSelBytes] using hnm 23 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms212Eq I hsz 1 (by omega)]
      have hfalse : (vatArms212SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vatArms212SelBytes, vatSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms212Eq I hsz 2 (by omega)]
      have hfalse : (vatArms212SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vatArms212SelBytes, vatSelBytes] using hnm 18 (by omega)
      rw [hfalse]; rfl
  have heq272 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms272FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vatArms272Eq I hsz 0 (by omega)]
      have hfalse : (vatArms272SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vatArms272SelBytes, vatSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms272Eq I hsz 1 (by omega)]
      have hfalse : (vatArms272SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vatArms272SelBytes, vatSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms272Eq I hsz 2 (by omega)]
      have hfalse : (vatArms272SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vatArms272SelBytes, vatSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms272Eq I hsz 3 (by omega)]
      have hfalse : (vatArms272SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vatArms272SelBytes, vatSelBytes] using hnm 13 (by omega)
      rw [hfalse]; rfl
  have heq321 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms321FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vatArms321Eq I hsz 0 (by omega)]
      have hfalse : (vatArms321SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vatArms321SelBytes, vatSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms321Eq I hsz 1 (by omega)]
      have hfalse : (vatArms321SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vatArms321SelBytes, vatSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms321Eq I hsz 2 (by omega)]
      have hfalse : (vatArms321SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vatArms321SelBytes, vatSelBytes] using hnm 21 (by omega)
      rw [hfalse]; rfl
  have heq370 : ∀ j, j < 4 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vatArms370Eq I hsz 0 (by omega)]
      have hfalse : (vatArms370SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vatArms370SelBytes, vatSelBytes] using hnm 25 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms370Eq I hsz 1 (by omega)]
      have hfalse : (vatArms370SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vatArms370SelBytes, vatSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms370Eq I hsz 2 (by omega)]
      have hfalse : (vatArms370SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vatArms370SelBytes, vatSelBytes] using hnm 26 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms370Eq I hsz 3 (by omega)]
      have hfalse : (vatArms370SelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vatArms370SelBytes, vatSelBytes] using hnm 17 (by omega)
      rw [hfalse]; rfl
  have heq419 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms419FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vatArms419Eq I hsz 0 (by omega)]
      have hfalse : (vatArms419SelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vatArms419SelBytes, vatSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms419Eq I hsz 1 (by omega)]
      have hfalse : (vatArms419SelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vatArms419SelBytes, vatSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [vatArms419Eq I hsz 2 (by omega)]
      have hfalse : (vatArms419SelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vatArms419SelBytes, vatSelBytes] using hnm 12 (by omega)
      rw [hfalse]; rfl
  obtain ⟨k32, C32, h32⟩ :=
    vatReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  by_cases hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩
  · have h249 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        (armTgt vatBytecode vatRootSplitPc) [vatSelWord I] solcFreePtrMem
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
      RD.selectorSplitTakenAuto h32 vatRootSplitWellFormed hroot (by jump_dest) (by simp)
    have h250 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
      simpa [vatLowSplitPc, vatRootSplitPc, armTgt, pushAt]
        using h249.jumpdest (by native_decide) (by simp)
    by_cases hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩
    · have h358 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
          (armTgt vatBytecode vatLowSplitPc) [vatSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) :=
        RD.selectorSplitTakenAuto h250 vatLowSplitWellFormed hlow (by jump_dest) (by simp)
      have h359 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
          vatLowLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
          ByteArray.empty (cA, σ)
          (k32 + 5 + 1 + 5 + 1) (C32 + 22 + 1 + 22 + 1) := by
        simpa [vatLowLowSplitPc, vatLowSplitPc, armTgt, pushAt]
          using h358.jumpdest (by native_decide) (by simp)
      by_cases hlowlow :
          UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) ≠ ⟨0⟩
      · have h418 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            (armTgt vatBytecode vatLowLowSplitPc) [vatSelWord I] solcFreePtrMem
            (UInt256.ofNat 3) ByteArray.empty (cA, σ)
            (k32 + 5 + 1 + 5 + 1 + 5) (C32 + 22 + 1 + 22 + 1 + 22) :=
          RD.selectorSplitTakenAuto h359 vatLowLowSplitWellFormed hlowlow
            (by jump_dest) (by simp)
        have h419 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            vatArms419FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
            ByteArray.empty (cA, σ)
            (k32 + 5 + 1 + 5 + 1 + 5 + 1)
            (C32 + 22 + 1 + 22 + 1 + 22 + 1) := by
          simpa [vatArms419FirstPc, vatLowLowSplitPc, armTgt, pushAt]
            using h418.jumpdest (by native_decide) (by simp)
        exact vatArms419NoMatchRevert h419 heq419
      · have hlowlow0 :
            UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
          by_contra hne
          exact hlowlow hne
        have h370 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            vatArms370FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
            ByteArray.empty (cA, σ)
            (k32 + 5 + 1 + 5 + 1 + 5) (C32 + 22 + 1 + 22 + 1 + 22) := by
          simpa [vatArms370FirstPc, vatLowLowSplitPc, selArmNextPc, armTgtWidth,
            selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
            RD.selectorSplitNotTakenAuto h359 vatLowLowSplitWellFormed hlowlow0 (by simp)
        exact vatArms370NoMatchRevert h370 heq370
    · have hlow0 : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hlow hne
      have h261 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
          vatLowHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
          ByteArray.empty (cA, σ)
          (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
        simpa [vatLowHighSplitPc, vatLowSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          RD.selectorSplitNotTakenAuto h250 vatLowSplitWellFormed hlow0 (by simp)
      by_cases hlowhigh :
          UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) ≠ ⟨0⟩
      · have h320 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            (armTgt vatBytecode vatLowHighSplitPc) [vatSelWord I] solcFreePtrMem
            (UInt256.ofNat 3) ByteArray.empty (cA, σ)
            (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) :=
          RD.selectorSplitTakenAuto h261 vatLowHighSplitWellFormed hlowhigh
            (by jump_dest) (by simp)
        have h321 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            vatArms321FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
            ByteArray.empty (cA, σ)
            (k32 + 5 + 1 + 5 + 5 + 1) (C32 + 22 + 1 + 22 + 22 + 1) := by
          simpa [vatArms321FirstPc, vatLowHighSplitPc, armTgt, pushAt]
            using h320.jumpdest (by native_decide) (by simp)
        exact vatArms321NoMatchRevert h321 heq321
      · have hlowhigh0 :
            UInt256.gt (armSelNat vatBytecode vatLowHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
          by_contra hne
          exact hlowhigh hne
        have h272 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            vatArms272FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
            ByteArray.empty (cA, σ)
            (k32 + 5 + 1 + 5 + 5) (C32 + 22 + 1 + 22 + 22) := by
          simpa [vatArms272FirstPc, vatLowHighSplitPc, selArmNextPc, armTgtWidth,
            selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
            RD.selectorSplitNotTakenAuto h261 vatLowHighSplitWellFormed hlowhigh0 (by simp)
        exact vatArms272NoMatchRevert h272 heq272
  · have hroot0 : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    have h43 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        vatHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
      simpa [vatHighSplitPc, vatRootSplitPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
        RD.selectorSplitNotTakenAuto h32 vatRootSplitWellFormed hroot0 (by simp)
    by_cases hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) ≠ ⟨0⟩
    · have h151 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
          (armTgt vatBytecode vatHighSplitPc) [vatSelWord I] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ)
          (k32 + 5 + 5) (C32 + 22 + 22) :=
        RD.selectorSplitTakenAuto h43 vatHighSplitWellFormed hhigh (by jump_dest) (by simp)
      have h152 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
          vatHighLowSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
          ByteArray.empty (cA, σ)
          (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
        simpa [vatHighLowSplitPc, vatHighSplitPc, armTgt, pushAt]
          using h151.jumpdest (by native_decide) (by simp)
      by_cases hhighlow :
          UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) ≠ ⟨0⟩
      · have h211 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            (armTgt vatBytecode vatHighLowSplitPc) [vatSelWord I] solcFreePtrMem
            (UInt256.ofNat 3) ByteArray.empty (cA, σ)
            (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) :=
          RD.selectorSplitTakenAuto h152 vatHighLowSplitWellFormed hhighlow
            (by jump_dest) (by simp)
        have h212 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            vatArms212FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
            ByteArray.empty (cA, σ)
            (k32 + 5 + 5 + 1 + 5 + 1) (C32 + 22 + 22 + 1 + 22 + 1) := by
          simpa [vatArms212FirstPc, vatHighLowSplitPc, armTgt, pushAt]
            using h211.jumpdest (by native_decide) (by simp)
        exact vatArms212NoMatchRevert h212 heq212
      · have hhighlow0 :
            UInt256.gt (armSelNat vatBytecode vatHighLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
          by_contra hne
          exact hhighlow hne
        have h163 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            vatArms163FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
            ByteArray.empty (cA, σ)
            (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) := by
          simpa [vatArms163FirstPc, vatHighLowSplitPc, selArmNextPc, armTgtWidth,
            selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
            RD.selectorSplitNotTakenAuto h152 vatHighLowSplitWellFormed hhighlow0 (by simp)
        exact vatArms163NoMatchRevert h163 heq163
    · have hhigh0 : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hhigh hne
      have h54 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
          vatHighHighSplitPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
          ByteArray.empty (cA, σ)
          (k32 + 5 + 5) (C32 + 22 + 22) := by
        simpa [vatHighHighSplitPc, vatHighSplitPc, selArmNextPc, armTgtWidth,
          selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
          RD.selectorSplitNotTakenAuto h43 vatHighSplitWellFormed hhigh0 (by simp)
      by_cases hhighhigh :
          UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) ≠ ⟨0⟩
      · have h113 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            (armTgt vatBytecode vatHighHighSplitPc) [vatSelWord I] solcFreePtrMem
            (UInt256.ofNat 3) ByteArray.empty (cA, σ)
            (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) :=
          RD.selectorSplitTakenAuto h54 vatHighHighSplitWellFormed hhighhigh
            (by jump_dest) (by simp)
        have h114 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            vatArms114FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
            ByteArray.empty (cA, σ)
            (k32 + 5 + 5 + 5 + 1) (C32 + 22 + 22 + 22 + 1) := by
          simpa [vatArms114FirstPc, vatHighHighSplitPc, armTgt, pushAt]
            using h113.jumpdest (by native_decide) (by simp)
        exact vatArms114NoMatchRevert h114 heq114
      · have hhighhigh0 :
            UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
          by_contra hne
          exact hhighhigh hne
        have h65 : RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
            vatArms65FirstPc [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3)
            ByteArray.empty (cA, σ)
            (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
          simpa [vatArms65FirstPc, vatHighHighSplitPc, selArmNextPc, armTgtWidth,
            selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
            RD.selectorSplitNotTakenAuto h54 vatHighHighSplitWellFormed hhighhigh0 (by simp)
        exact vatArms65NoMatchRevert h65 heq65

theorem vatX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem vatX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt vatBytecode)
    (opC := solcGuardTgtOp vatBytecode)
    (wC := solcGuardTgtWidth vatBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h452 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 vatDispatchRevertPc (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h452 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

end Benchmarks.Dss.Vat
