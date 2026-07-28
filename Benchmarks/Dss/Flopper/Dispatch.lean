import Benchmarks.Dss.Flopper.Trusted

/-!
# MakerDAO/Sky DSS Flopper dispatcher facts

Solm dispatch routing facts and the shared non-payable source result.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

attribute [local simp]
  begSelectorBytes
  bidsSelectorBytes
  cageSelectorBytes
  dealSelectorBytes
  dentSelectorBytes
  denySelectorBytes
  fileSelectorBytes
  gemSelectorBytes
  kickSelectorBytes
  kicksSelectorBytes
  liveSelectorBytes
  padSelectorBytes
  relySelectorBytes
  tauSelectorBytes
  tickSelectorBytes
  ttlSelectorBytes
  vatSelectorBytes
  vowSelectorBytes
  wardsSelectorBytes
  yankSelectorBytes

theorem flopperDispatchBeg {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 0)) :
    dispatchMsg contract I.calldata = some begTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some begTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchBids {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 1)) :
    dispatchMsg contract I.calldata = some bidsTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some bidsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchCage {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 2)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchDeal {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 3)) :
    dispatchMsg contract I.calldata = some dealTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dealTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchDent {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 4)) :
    dispatchMsg contract I.calldata = some dentTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dentTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 5)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchFile {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 6)) :
    dispatchMsg contract I.calldata = some fileTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchGem {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 7)) :
    dispatchMsg contract I.calldata = some gemTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some gemTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchKick {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 8)) :
    dispatchMsg contract I.calldata = some kickTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some kickTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchKicks {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 9)) :
    dispatchMsg contract I.calldata = some kicksTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some kicksTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchLive {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 10)) :
    dispatchMsg contract I.calldata = some liveTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some liveTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchPad {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 11)) :
    dispatchMsg contract I.calldata = some padTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some padTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 12)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchTau {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 13)) :
    dispatchMsg contract I.calldata = some tauTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tauTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchTick {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 14)) :
    dispatchMsg contract I.calldata = some tickTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tickTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchTtl {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 15)) :
    dispatchMsg contract I.calldata = some ttlTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ttlTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchVat {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 16)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchVow {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 17)) :
    dispatchMsg contract I.calldata = some vowTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 17 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vowTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 18)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 18 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatchYank {I : ExecutionEnv}
    (hsel : selIs I (flopperSelBytes 19)) :
    dispatchMsg contract I.calldata = some yankTransition := by
  have hcd : I.calldata.extract 0 4 = flopperSelBytes 19 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some yankTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  native_decide

theorem flopperDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [begTransition, bidsTransition, cageTransition, dealTransition, dentTransition,
      denyTransition, fileTransition, gemTransition, kickTransition, kicksTransition,
      liveTransition, padTransition, relyTransition, tauTransition, tickTransition,
      ttlTransition, vatTransition, vowTransition, wardsTransition, yankTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, begSelectorBytes, bidsSelectorBytes, cageSelectorBytes,
        dealSelectorBytes, dentSelectorBytes, denySelectorBytes, fileSelectorBytes,
        gemSelectorBytes, kickSelectorBytes, kicksSelectorBytes, liveSelectorBytes,
        padSelectorBytes, relySelectorBytes, tauSelectorBytes, tickSelectorBytes,
        ttlSelectorBytes, vatSelectorBytes, vowSelectorBytes, wardsSelectorBytes,
        yankSelectorBytes]
      native_decide) h

theorem flopperDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 20 → (flopperSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, begSelectorBytes]
    simpa [flopperSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, bidsSelectorBytes]
    simpa [flopperSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, cageSelectorBytes]
    simpa [flopperSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, dealSelectorBytes]
    simpa [flopperSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, dentSelectorBytes]
    simpa [flopperSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [flopperSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, fileSelectorBytes]
    simpa [flopperSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, gemSelectorBytes]
    simpa [flopperSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, kickSelectorBytes]
    simpa [flopperSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, kicksSelectorBytes]
    simpa [flopperSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [flopperSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, padSelectorBytes]
    simpa [flopperSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [flopperSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, tauSelectorBytes]
    simpa [flopperSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, tickSelectorBytes]
    simpa [flopperSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, ttlSelectorBytes]
    simpa [flopperSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [flopperSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, vowSelectorBytes]
    simpa [flopperSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [flopperSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, yankSelectorBytes]
    simpa [flopperSelBytes] using hnm 19 (by omega)

theorem flopperBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

/-! ## Shared runtime paths -/

abbrev flopperDispatchRevertPc : UInt256 := ⟨300⟩
abbrev flopperRootSplitPc : UInt256 := ⟨32⟩
abbrev flopperHighSplitPc : UInt256 := ⟨43⟩
abbrev flopperHighHighFirstArmPc : UInt256 := ⟨54⟩
abbrev flopperHighLowJumpdestPc : UInt256 := ⟨113⟩
abbrev flopperHighLowFirstArmPc : UInt256 := ⟨114⟩
abbrev flopperLowSplitJumpdestPc : UInt256 := ⟨173⟩
abbrev flopperLowSplitPc : UInt256 := ⟨174⟩
abbrev flopperLowHighFirstArmPc : UInt256 := ⟨185⟩
abbrev flopperLowLowJumpdestPc : UInt256 := ⟨244⟩
abbrev flopperLowLowFirstArmPc : UInt256 := ⟨245⟩
abbrev flopperDispatchBodyPc : UInt256 := ⟨18⟩
abbrev flopperSelectorLoadPc : UInt256 := ⟨26⟩

def flopperLowLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ -- yank(uint256)
  | 1 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 2 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 3 => ⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ -- bids(uint256)
  | _ => ⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩  -- ttl()

def flopperLowHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x5f, 0xf3, 0xa3, 0x82]⟩ -- dent(uint256,uint256,uint256)
  | 1 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow()
  | 2 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 3 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | _ => ⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩  -- gem()

def flopperHighLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x7d, 0x78, 0x0d, 0x82]⟩ -- beg()
  | 1 => ⟨#[0x93, 0x61, 0x26, 0x6c]⟩ -- pad()
  | 2 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 3 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | _ => ⟨#[0xb7, 0xe9, 0xcd, 0x24]⟩  -- kick(address,uint256,uint256)

def flopperHighHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | 1 => ⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩ -- deal(uint256)
  | 2 => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau()
  | 3 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ -- kicks()
  | _ => ⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩  -- tick(uint256)

theorem flopperRootSplitWellFormed :
    selectorSplitWellFormed flopperBytecode flopperRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem flopperHighSplitWellFormed :
    selectorSplitWellFormed flopperBytecode flopperHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem flopperLowSplitWellFormed :
    selectorSplitWellFormed flopperBytecode flopperLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem flopperLowLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flopperBytecode
      (nthArmPc flopperBytecode flopperLowLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem flopperLowHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flopperBytecode
      (nthArmPc flopperBytecode flopperLowHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem flopperHighLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flopperBytecode
      (nthArmPc flopperBytecode flopperHighLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem flopperHighHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flopperBytecode
      (nthArmPc flopperBytecode flopperHighHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem flopperLowLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc j))
        (flopperSelWord I) =
      if (flopperLowLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem flopperLowHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowHighFirstArmPc j))
        (flopperSelWord I) =
      if (flopperLowHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem flopperHighLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc j))
        (flopperSelWord I) =
      if (flopperHighLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem flopperHighHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc j))
        (flopperSelWord I) =
      if (flopperHighHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem flopperReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flopperRootSplitPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [flopperRootSplitPc, flopperSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := flopperBytecode)
      (bodyPc := flopperDispatchBodyPc) (loadPc := flopperSelectorLoadPc)
      (firstPc := flopperRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := flopperDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem flopperReachLowSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flopperLowSplitPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    flopperReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h173 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperLowSplitJumpdestPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [flopperRootSplitPc, flopperLowSplitJumpdestPc] using
      RD.selectorSplitTakenAuto h32 flopperRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h174 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperLowSplitPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [flopperLowSplitPc] using h173.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h174⟩

theorem flopperReachHighSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flopperHighSplitPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    flopperReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperHighSplitPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [flopperHighSplitPc, flopperRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 flopperRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem flopperReachLowLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flopperLowLowFirstArmPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k174, C174, h174⟩ :=
    flopperReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h244 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperLowLowJumpdestPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5) (C174 + 22) := by
    simpa [flopperLowSplitPc, flopperLowLowJumpdestPc] using
      RD.selectorSplitTakenAuto h174 flopperLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h245 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperLowLowFirstArmPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5 + 1) (C174 + 22 + 1) := by
    simpa [flopperLowLowFirstArmPc] using h244.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h245⟩

theorem flopperReachLowHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
      (flopperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flopperLowHighFirstArmPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k174, C174, h174⟩ :=
    flopperReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h185 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperLowHighFirstArmPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5) (C174 + 22) := by
    simpa [flopperLowHighFirstArmPc, flopperLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h174 flopperLowSplitWellFormed hlow (by simp)
  exact ⟨_, _, h185⟩

theorem flopperReachHighLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flopperHighLowFirstArmPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    flopperReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h113 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperHighLowJumpdestPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [flopperHighSplitPc, flopperHighLowJumpdestPc] using
      RD.selectorSplitTakenAuto h43 flopperHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h114 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperHighLowFirstArmPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [flopperHighLowFirstArmPc] using h113.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h114⟩

theorem flopperReachHighHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
      (flopperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flopperHighHighFirstArmPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    flopperReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flopperHighHighFirstArmPc [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [flopperHighHighFirstArmPc, flopperHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 flopperHighSplitWellFormed hhigh (by simp)
  exact ⟨_, _, h54⟩

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem flopperX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-- Calldata shorter than a selector reverts at the shared dispatcher revert block. -/
theorem flopperX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt flopperBytecode)
    (opC := solcGuardTgtOp flopperBytecode)
    (wC := solcGuardTgtWidth flopperBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h300 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 flopperDispatchRevertPc (by native_decide)
      (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h300 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

/-- A fallthrough `PUSH2 300; JUMP` reaches the shared revert block. -/
theorem flopperJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode flopperBytecode pc = some (.Push .PUSH2, some (flopperDispatchRevertPc, 2)))
    (hjump : decode flopperBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h300 := h.push2 flopperDispatchRevertPc hpush
      (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h300 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem flopperLowLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) flopperLowLowFirstArmPc
      [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h300 := h
    |>.selectorArmNotTakenAuto (flopperLowLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperLowLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperLowLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperLowLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperLowLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h300 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem flopperLowHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) flopperLowHighFirstArmPc
      [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h240 := h
    |>.selectorArmNotTakenAuto (flopperLowHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperLowHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperLowHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperLowHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperLowHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flopperJumpToNoMatchRevert h240 (by native_decide) (by native_decide)

theorem flopperHighLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) flopperHighLowFirstArmPc
      [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h169 := h
    |>.selectorArmNotTakenAuto (flopperHighLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperHighLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperHighLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperHighLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperHighLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flopperJumpToNoMatchRevert h169 (by native_decide) (by native_decide)

theorem flopperHighHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I) flopperHighHighFirstArmPc
      [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (flopperHighHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperHighHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperHighHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperHighHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flopperHighHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flopperJumpToNoMatchRevert h109 (by native_decide) (by native_decide)

theorem flopperX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 20 → (flopperSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev flopperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLowLow : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flopperLowLowArmEq I hsz 0 (by omega)]
      have hfalse : (flopperLowLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowLowSelBytes, flopperSelBytes] using hnm 19 (by omega)
      rw [hfalse]; rfl
    · rw [flopperLowLowArmEq I hsz 1 (by omega)]
      have hfalse : (flopperLowLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowLowSelBytes, flopperSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [flopperLowLowArmEq I hsz 2 (by omega)]
      have hfalse : (flopperLowLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowLowSelBytes, flopperSelBytes] using hnm 16 (by omega)
      rw [hfalse]; rfl
    · rw [flopperLowLowArmEq I hsz 3 (by omega)]
      have hfalse : (flopperLowLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowLowSelBytes, flopperSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [flopperLowLowArmEq I hsz 4 (by omega)]
      have hfalse : (flopperLowLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowLowSelBytes, flopperSelBytes] using hnm 15 (by omega)
      rw [hfalse]; rfl
  have heqLowHigh : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flopperLowHighArmEq I hsz 0 (by omega)]
      have hfalse : (flopperLowHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowHighSelBytes, flopperSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [flopperLowHighArmEq I hsz 1 (by omega)]
      have hfalse : (flopperLowHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowHighSelBytes, flopperSelBytes] using hnm 17 (by omega)
      rw [hfalse]; rfl
    · rw [flopperLowHighArmEq I hsz 2 (by omega)]
      have hfalse : (flopperLowHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowHighSelBytes, flopperSelBytes] using hnm 12 (by omega)
      rw [hfalse]; rfl
    · rw [flopperLowHighArmEq I hsz 3 (by omega)]
      have hfalse : (flopperLowHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowHighSelBytes, flopperSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [flopperLowHighArmEq I hsz 4 (by omega)]
      have hfalse : (flopperLowHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flopperLowHighSelBytes, flopperSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
  have heqHighLow : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flopperHighLowArmEq I hsz 0 (by omega)]
      have hfalse : (flopperHighLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighLowSelBytes, flopperSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
    · rw [flopperHighLowArmEq I hsz 1 (by omega)]
      have hfalse : (flopperHighLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighLowSelBytes, flopperSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [flopperHighLowArmEq I hsz 2 (by omega)]
      have hfalse : (flopperHighLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighLowSelBytes, flopperSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [flopperHighLowArmEq I hsz 3 (by omega)]
      have hfalse : (flopperHighLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighLowSelBytes, flopperSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [flopperHighLowArmEq I hsz 4 (by omega)]
      have hfalse : (flopperHighLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighLowSelBytes, flopperSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
  have heqHighHigh : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperHighHighFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flopperHighHighArmEq I hsz 0 (by omega)]
      have hfalse : (flopperHighHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighHighSelBytes, flopperSelBytes] using hnm 18 (by omega)
      rw [hfalse]; rfl
    · rw [flopperHighHighArmEq I hsz 1 (by omega)]
      have hfalse : (flopperHighHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighHighSelBytes, flopperSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
    · rw [flopperHighHighArmEq I hsz 2 (by omega)]
      have hfalse : (flopperHighHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighHighSelBytes, flopperSelBytes] using hnm 13 (by omega)
      rw [hfalse]; rfl
    · rw [flopperHighHighArmEq I hsz 3 (by omega)]
      have hfalse : (flopperHighHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighHighSelBytes, flopperSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [flopperHighHighArmEq I hsz 4 (by omega)]
      have hfalse : (flopperHighHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flopperHighHighSelBytes, flopperSelBytes] using hnm 14 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩
  · by_cases hlow : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
        (flopperSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        flopperReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
      exact flopperLowLowNoMatchRevert hfirst heqLowLow
    · have hlow0 : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
        (flopperSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hlow hne
      obtain ⟨_, _, hfirst⟩ :=
        flopperReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow0
      exact flopperLowHighNoMatchRevert hfirst heqLowHigh
  · have hroot0 : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    by_cases hhigh : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
        (flopperSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        flopperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh
      exact flopperHighLowNoMatchRevert hfirst heqHighLow
    · have hhigh0 : UInt256.gt (armSelNat flopperBytecode flopperHighSplitPc)
        (flopperSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hhigh hne
      obtain ⟨_, _, hfirst⟩ :=
        flopperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh0
      exact flopperHighHighNoMatchRevert hfirst heqHighHigh

/-- `callvalue ≠ 0` is equivalent to every Solm transition reverting on the non-payable guard. -/
theorem flopperNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (flopperX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (flopperBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than four bytes has no Solm dispatch and the EVM reverts. -/
theorem flopperShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (flopperX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (flopperDispatch_none_short hsz)

/-- `size ≥ 4` but no selector matches: no Solm dispatch and EVM fallthrough reverts. -/
theorem flopperNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 20 → (flopperSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (flopperX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (flopperDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (flopperX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (flopperDispatch_none_short hshort)

theorem flopperNoSelectorMatches {I : ExecutionEnv}
    (hbeg : ¬ selIs I (flopperSelBytes 0))
    (hbids : ¬ selIs I (flopperSelBytes 1))
    (hcage : ¬ selIs I (flopperSelBytes 2))
    (hdeal : ¬ selIs I (flopperSelBytes 3))
    (hdent : ¬ selIs I (flopperSelBytes 4))
    (hdeny : ¬ selIs I (flopperSelBytes 5))
    (hfile : ¬ selIs I (flopperSelBytes 6))
    (hgem : ¬ selIs I (flopperSelBytes 7))
    (hkick : ¬ selIs I (flopperSelBytes 8))
    (hkicks : ¬ selIs I (flopperSelBytes 9))
    (hlive : ¬ selIs I (flopperSelBytes 10))
    (hpad : ¬ selIs I (flopperSelBytes 11))
    (hrely : ¬ selIs I (flopperSelBytes 12))
    (htau : ¬ selIs I (flopperSelBytes 13))
    (htick : ¬ selIs I (flopperSelBytes 14))
    (httl : ¬ selIs I (flopperSelBytes 15))
    (hvat : ¬ selIs I (flopperSelBytes 16))
    (hvow : ¬ selIs I (flopperSelBytes 17))
    (hwards : ¬ selIs I (flopperSelBytes 18))
    (hyank : ¬ selIs I (flopperSelBytes 19)) :
    ∀ i, i < 20 → (flopperSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, flopperSelBytes] using hbeg
  · simpa [selIs, flopperSelBytes] using hbids
  · simpa [selIs, flopperSelBytes] using hcage
  · simpa [selIs, flopperSelBytes] using hdeal
  · simpa [selIs, flopperSelBytes] using hdent
  · simpa [selIs, flopperSelBytes] using hdeny
  · simpa [selIs, flopperSelBytes] using hfile
  · simpa [selIs, flopperSelBytes] using hgem
  · simpa [selIs, flopperSelBytes] using hkick
  · simpa [selIs, flopperSelBytes] using hkicks
  · simpa [selIs, flopperSelBytes] using hlive
  · simpa [selIs, flopperSelBytes] using hpad
  · simpa [selIs, flopperSelBytes] using hrely
  · simpa [selIs, flopperSelBytes] using htau
  · simpa [selIs, flopperSelBytes] using htick
  · simpa [selIs, flopperSelBytes] using httl
  · simpa [selIs, flopperSelBytes] using hvat
  · simpa [selIs, flopperSelBytes] using hvow
  · simpa [selIs, flopperSelBytes] using hwards
  · simpa [selIs, flopperSelBytes] using hyank

end Benchmarks.Dss.Flopper
