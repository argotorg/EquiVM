import Benchmarks.Dss.Flapper.Trusted

/-!
# MakerDAO/Sky DSS Flapper dispatcher facts

Solm dispatch routing facts and the shared dispatcher revert entry points.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper

attribute [local simp]
  begSelectorBytes
  bidsSelectorBytes
  cageSelectorBytes
  dealSelectorBytes
  denySelectorBytes
  fileSelectorBytes
  fillSelectorBytes
  gemSelectorBytes
  kickSelectorBytes
  kicksSelectorBytes
  lidSelectorBytes
  liveSelectorBytes
  relySelectorBytes
  tauSelectorBytes
  tendSelectorBytes
  tickSelectorBytes
  ttlSelectorBytes
  vatSelectorBytes
  wardsSelectorBytes
  yankSelectorBytes

theorem flapperDispatchBeg {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 0)) :
    dispatchMsg contract I.calldata = some begTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some begTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchBids {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 1)) :
    dispatchMsg contract I.calldata = some bidsTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some bidsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchCage {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 2)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchDeal {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 3)) :
    dispatchMsg contract I.calldata = some dealTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dealTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 4)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchFile {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 5)) :
    dispatchMsg contract I.calldata = some fileTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchFill {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 6)) :
    dispatchMsg contract I.calldata = some fillTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fillTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchGem {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 7)) :
    dispatchMsg contract I.calldata = some gemTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some gemTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchKick {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 8)) :
    dispatchMsg contract I.calldata = some kickTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some kickTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchKicks {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 9)) :
    dispatchMsg contract I.calldata = some kicksTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some kicksTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchLid {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 10)) :
    dispatchMsg contract I.calldata = some lidTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some lidTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchLive {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 11)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 12)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchTau {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 13)) :
    dispatchMsg contract I.calldata = some tauTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tauTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchTend {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 14)) :
    dispatchMsg contract I.calldata = some tendTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tendTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchTick {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 15)) :
    dispatchMsg contract I.calldata = some tickTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tickTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchTtl {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 16)) :
    dispatchMsg contract I.calldata = some ttlTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ttlTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchVat {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 17)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 17 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 18)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 18 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatchYank {I : ExecutionEnv}
    (hsel : selIs I (flapperSelBytes 19)) :
    dispatchMsg contract I.calldata = some yankTransition := by
  have hcd : I.calldata.extract 0 4 = flapperSelBytes 19 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some yankTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flapperDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [begTransition, bidsTransition, cageTransition, dealTransition, denyTransition,
      fileTransition, fillTransition, gemTransition, kickTransition, kicksTransition,
      lidTransition, liveTransition, relyTransition, tauTransition, tendTransition,
      tickTransition, ttlTransition, vatTransition, wardsTransition, yankTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, begSelectorBytes, bidsSelectorBytes, cageSelectorBytes,
        dealSelectorBytes, denySelectorBytes, fileSelectorBytes, fillSelectorBytes,
        gemSelectorBytes, kickSelectorBytes, kicksSelectorBytes, lidSelectorBytes,
        liveSelectorBytes, relySelectorBytes, tauSelectorBytes, tendSelectorBytes,
        tickSelectorBytes, ttlSelectorBytes, vatSelectorBytes, wardsSelectorBytes,
        yankSelectorBytes]
      native_decide) h

theorem flapperDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 20 → (flapperSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, begSelectorBytes]
    simpa [flapperSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, bidsSelectorBytes]
    simpa [flapperSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, cageSelectorBytes]
    simpa [flapperSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, dealSelectorBytes]
    simpa [flapperSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [flapperSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, fileSelectorBytes]
    simpa [flapperSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, fillSelectorBytes]
    simpa [flapperSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, gemSelectorBytes]
    simpa [flapperSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, kickSelectorBytes]
    simpa [flapperSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, kicksSelectorBytes]
    simpa [flapperSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, lidSelectorBytes]
    simpa [flapperSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [flapperSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [flapperSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, tauSelectorBytes]
    simpa [flapperSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, tendSelectorBytes]
    simpa [flapperSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, tickSelectorBytes]
    simpa [flapperSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, ttlSelectorBytes]
    simpa [flapperSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [flapperSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [flapperSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, yankSelectorBytes]
    simpa [flapperSelBytes] using hnm 19 (by omega)

theorem flapperBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-! ## Shared runtime dispatcher paths -/

abbrev flapperDispatchRevertPc : UInt256 := ⟨300⟩
abbrev flapperRootSplitPc : UInt256 := ⟨32⟩
abbrev flapperHighSplitPc : UInt256 := ⟨43⟩
abbrev flapperHighHighFirstArmPc : UInt256 := ⟨54⟩
abbrev flapperHighLowJumpdestPc : UInt256 := ⟨113⟩
abbrev flapperHighLowFirstArmPc : UInt256 := ⟨114⟩
abbrev flapperLowSplitJumpdestPc : UInt256 := ⟨173⟩
abbrev flapperLowSplitPc : UInt256 := ⟨174⟩
abbrev flapperLowHighFirstArmPc : UInt256 := ⟨185⟩
abbrev flapperLowLowJumpdestPc : UInt256 := ⟨244⟩
abbrev flapperLowLowFirstArmPc : UInt256 := ⟨245⟩
abbrev flapperDispatchBodyPc : UInt256 := ⟨18⟩
abbrev flapperSelectorLoadPc : UInt256 := ⟨26⟩

def flapperLowLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x26, 0xd2, 0xad, 0xdc]⟩ -- lid()
  | 1 => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ -- yank(uint256)
  | 2 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 3 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | _ => ⟨#[0x44, 0x23, 0xc5, 0xf1]⟩  -- bids(uint256)

def flapperLowHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x4b, 0x43, 0xed, 0x12]⟩ -- tend(uint256,uint256,uint256)
  | 1 => ⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩ -- ttl()
  | 2 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 3 => ⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ -- gem()
  | _ => ⟨#[0x7d, 0x78, 0x0d, 0x82]⟩  -- beg()

def flapperHighLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 1 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 2 => ⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩ -- cage(uint256)
  | 3 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩  -- deal(uint256)

def flapperHighHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xca, 0x40, 0xc4, 0x19]⟩ -- kick(uint256,uint256)
  | 1 => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau()
  | 2 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ -- kicks()
  | 3 => ⟨#[0xd9, 0xc5, 0x5c, 0xe1]⟩ -- fill()
  | _ => ⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩  -- tick(uint256)

theorem flapperRootSplitWellFormed :
    selectorSplitWellFormed flapperBytecode flapperRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem flapperHighSplitWellFormed :
    selectorSplitWellFormed flapperBytecode flapperHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem flapperLowSplitWellFormed :
    selectorSplitWellFormed flapperBytecode flapperLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem flapperLowLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flapperBytecode
      (nthArmPc flapperBytecode flapperLowLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem flapperLowHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flapperBytecode
      (nthArmPc flapperBytecode flapperLowHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem flapperHighLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flapperBytecode
      (nthArmPc flapperBytecode flapperHighLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem flapperHighHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flapperBytecode
      (nthArmPc flapperBytecode flapperHighHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem flapperLowLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowLowFirstArmPc j))
        (flapperSelWord I) =
      if (flapperLowLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem flapperLowHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc j))
        (flapperSelWord I) =
      if (flapperLowHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem flapperHighLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc j))
        (flapperSelWord I) =
      if (flapperHighLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem flapperHighHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc j))
        (flapperSelWord I) =
      if (flapperHighHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem flapperReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flapperRootSplitPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [flapperRootSplitPc, flapperSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := flapperBytecode)
      (bodyPc := flapperDispatchBodyPc) (loadPc := flapperSelectorLoadPc)
      (firstPc := flapperRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := flapperDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem flapperReachLowSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flapperLowSplitPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    flapperReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h173 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperLowSplitJumpdestPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [flapperRootSplitPc, flapperLowSplitJumpdestPc] using
      RD.selectorSplitTakenAuto h32 flapperRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h174 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperLowSplitPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [flapperLowSplitPc] using h173.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h174⟩

theorem flapperReachHighSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flapperHighSplitPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    flapperReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperHighSplitPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [flapperHighSplitPc, flapperRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 flapperRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem flapperReachLowLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flapperLowLowFirstArmPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k174, C174, h174⟩ :=
    flapperReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h244 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperLowLowJumpdestPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5) (C174 + 22) := by
    simpa [flapperLowSplitPc, flapperLowLowJumpdestPc] using
      RD.selectorSplitTakenAuto h174 flapperLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h245 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperLowLowFirstArmPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5 + 1) (C174 + 22 + 1) := by
    simpa [flapperLowLowFirstArmPc] using h244.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h245⟩

theorem flapperReachLowHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
      (flapperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flapperLowHighFirstArmPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k174, C174, h174⟩ :=
    flapperReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h185 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperLowHighFirstArmPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5) (C174 + 22) := by
    simpa [flapperLowHighFirstArmPc, flapperLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h174 flapperLowSplitWellFormed hlow (by simp)
  exact ⟨_, _, h185⟩

theorem flapperReachHighLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flapperHighLowFirstArmPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    flapperReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h113 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperHighLowJumpdestPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [flapperHighSplitPc, flapperHighLowJumpdestPc] using
      RD.selectorSplitTakenAuto h43 flapperHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h114 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperHighLowFirstArmPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [flapperHighLowFirstArmPc] using h113.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h114⟩

theorem flapperReachHighHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
      (flapperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flapperHighHighFirstArmPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    flapperReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flapperHighHighFirstArmPc [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [flapperHighHighFirstArmPc, flapperHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 flapperHighSplitWellFormed hhigh (by simp)
  exact ⟨_, _, h54⟩

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem flapperX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-- Calldata shorter than a selector reverts at the shared dispatcher revert block. -/
theorem flapperX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt flapperBytecode)
    (opC := solcGuardTgtOp flapperBytecode)
    (wC := solcGuardTgtWidth flapperBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h300 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 flapperDispatchRevertPc (by native_decide)
      (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h300 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-- A fallthrough `PUSH2 300; JUMP` reaches the shared revert block. -/
theorem flapperJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode flapperBytecode pc = some (.Push .PUSH2, some (flapperDispatchRevertPc, 2)))
    (hjump : decode flapperBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h300 := h.push2 flapperDispatchRevertPc hpush
      (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h300 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem flapperLowLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) flapperLowLowFirstArmPc
      [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h300 := h
    |>.selectorArmNotTakenAuto (flapperLowLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperLowLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperLowLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperLowLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperLowLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h300 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem flapperLowHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) flapperLowHighFirstArmPc
      [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h240 := h
    |>.selectorArmNotTakenAuto (flapperLowHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperLowHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperLowHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperLowHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperLowHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flapperJumpToNoMatchRevert h240 (by native_decide) (by native_decide)

theorem flapperHighLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) flapperHighLowFirstArmPc
      [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h169 := h
    |>.selectorArmNotTakenAuto (flapperHighLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperHighLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperHighLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperHighLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperHighLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flapperJumpToNoMatchRevert h169 (by native_decide) (by native_decide)

theorem flapperHighHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) flapperHighHighFirstArmPc
      [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (flapperHighHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperHighHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperHighHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperHighHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flapperHighHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flapperJumpToNoMatchRevert h109 (by native_decide) (by native_decide)

theorem flapperX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 20 → (flapperSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLowLow : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flapperLowLowArmEq I hsz 0 (by omega)]
      have hfalse : (flapperLowLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowLowSelBytes, flapperSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [flapperLowLowArmEq I hsz 1 (by omega)]
      have hfalse : (flapperLowLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowLowSelBytes, flapperSelBytes] using hnm 19 (by omega)
      rw [hfalse]; rfl
    · rw [flapperLowLowArmEq I hsz 2 (by omega)]
      have hfalse : (flapperLowLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowLowSelBytes, flapperSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [flapperLowLowArmEq I hsz 3 (by omega)]
      have hfalse : (flapperLowLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowLowSelBytes, flapperSelBytes] using hnm 17 (by omega)
      rw [hfalse]; rfl
    · rw [flapperLowLowArmEq I hsz 4 (by omega)]
      have hfalse : (flapperLowLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowLowSelBytes, flapperSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
  have heqLowHigh : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flapperLowHighArmEq I hsz 0 (by omega)]
      have hfalse : (flapperLowHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowHighSelBytes, flapperSelBytes] using hnm 14 (by omega)
      rw [hfalse]; rfl
    · rw [flapperLowHighArmEq I hsz 1 (by omega)]
      have hfalse : (flapperLowHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowHighSelBytes, flapperSelBytes] using hnm 16 (by omega)
      rw [hfalse]; rfl
    · rw [flapperLowHighArmEq I hsz 2 (by omega)]
      have hfalse : (flapperLowHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowHighSelBytes, flapperSelBytes] using hnm 12 (by omega)
      rw [hfalse]; rfl
    · rw [flapperLowHighArmEq I hsz 3 (by omega)]
      have hfalse : (flapperLowHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowHighSelBytes, flapperSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [flapperLowHighArmEq I hsz 4 (by omega)]
      have hfalse : (flapperLowHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flapperLowHighSelBytes, flapperSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
  have heqHighLow : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flapperHighLowArmEq I hsz 0 (by omega)]
      have hfalse : (flapperHighLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighLowSelBytes, flapperSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [flapperHighLowArmEq I hsz 1 (by omega)]
      have hfalse : (flapperHighLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighLowSelBytes, flapperSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [flapperHighLowArmEq I hsz 2 (by omega)]
      have hfalse : (flapperHighLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighLowSelBytes, flapperSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [flapperHighLowArmEq I hsz 3 (by omega)]
      have hfalse : (flapperHighLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighLowSelBytes, flapperSelBytes] using hnm 18 (by omega)
      rw [hfalse]; rfl
    · rw [flapperHighLowArmEq I hsz 4 (by omega)]
      have hfalse : (flapperHighLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighLowSelBytes, flapperSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
  have heqHighHigh : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperHighHighFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flapperHighHighArmEq I hsz 0 (by omega)]
      have hfalse : (flapperHighHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighHighSelBytes, flapperSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [flapperHighHighArmEq I hsz 1 (by omega)]
      have hfalse : (flapperHighHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighHighSelBytes, flapperSelBytes] using hnm 13 (by omega)
      rw [hfalse]; rfl
    · rw [flapperHighHighArmEq I hsz 2 (by omega)]
      have hfalse : (flapperHighHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighHighSelBytes, flapperSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [flapperHighHighArmEq I hsz 3 (by omega)]
      have hfalse : (flapperHighHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighHighSelBytes, flapperSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [flapperHighHighArmEq I hsz 4 (by omega)]
      have hfalse : (flapperHighHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flapperHighHighSelBytes, flapperSelBytes] using hnm 15 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩
  · by_cases hlow : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
        (flapperSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        flapperReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
      exact flapperLowLowNoMatchRevert hfirst heqLowLow
    · have hlow0 : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
        (flapperSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hlow hne
      obtain ⟨_, _, hfirst⟩ :=
        flapperReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow0
      exact flapperLowHighNoMatchRevert hfirst heqLowHigh
  · have hroot0 : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    by_cases hhigh : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
        (flapperSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        flapperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh
      exact flapperHighLowNoMatchRevert hfirst heqHighLow
    · have hhigh0 : UInt256.gt (armSelNat flapperBytecode flapperHighSplitPc)
        (flapperSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hhigh hne
      obtain ⟨_, _, hfirst⟩ :=
        flapperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh0
      exact flapperHighHighNoMatchRevert hfirst heqHighHigh

theorem flapperNoSelectorMatches {I : ExecutionEnv}
    (hbeg : ¬ selIs I (flapperSelBytes 0))
    (hbids : ¬ selIs I (flapperSelBytes 1))
    (hcage : ¬ selIs I (flapperSelBytes 2))
    (hdeal : ¬ selIs I (flapperSelBytes 3))
    (hdeny : ¬ selIs I (flapperSelBytes 4))
    (hfile : ¬ selIs I (flapperSelBytes 5))
    (hfill : ¬ selIs I (flapperSelBytes 6))
    (hgem : ¬ selIs I (flapperSelBytes 7))
    (hkick : ¬ selIs I (flapperSelBytes 8))
    (hkicks : ¬ selIs I (flapperSelBytes 9))
    (hlid : ¬ selIs I (flapperSelBytes 10))
    (hlive : ¬ selIs I (flapperSelBytes 11))
    (hrely : ¬ selIs I (flapperSelBytes 12))
    (htau : ¬ selIs I (flapperSelBytes 13))
    (htend : ¬ selIs I (flapperSelBytes 14))
    (htick : ¬ selIs I (flapperSelBytes 15))
    (httl : ¬ selIs I (flapperSelBytes 16))
    (hvat : ¬ selIs I (flapperSelBytes 17))
    (hwards : ¬ selIs I (flapperSelBytes 18))
    (hyank : ¬ selIs I (flapperSelBytes 19)) :
    ∀ i, i < 20 → (flapperSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, flapperSelBytes] using hbeg
  · simpa [selIs, flapperSelBytes] using hbids
  · simpa [selIs, flapperSelBytes] using hcage
  · simpa [selIs, flapperSelBytes] using hdeal
  · simpa [selIs, flapperSelBytes] using hdeny
  · simpa [selIs, flapperSelBytes] using hfile
  · simpa [selIs, flapperSelBytes] using hfill
  · simpa [selIs, flapperSelBytes] using hgem
  · simpa [selIs, flapperSelBytes] using hkick
  · simpa [selIs, flapperSelBytes] using hkicks
  · simpa [selIs, flapperSelBytes] using hlid
  · simpa [selIs, flapperSelBytes] using hlive
  · simpa [selIs, flapperSelBytes] using hrely
  · simpa [selIs, flapperSelBytes] using htau
  · simpa [selIs, flapperSelBytes] using htend
  · simpa [selIs, flapperSelBytes] using htick
  · simpa [selIs, flapperSelBytes] using httl
  · simpa [selIs, flapperSelBytes] using hvat
  · simpa [selIs, flapperSelBytes] using hwards
  · simpa [selIs, flapperSelBytes] using hyank

theorem flapperNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flapperX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (flapperBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

theorem flapperShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (flapperX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (flapperDispatch_none_short hsz)

theorem flapperNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 20 → (flapperSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (flapperX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (flapperDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (flapperX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (flapperDispatch_none_short hshort)

end Benchmarks.Dss.Flapper
