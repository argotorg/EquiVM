import Benchmarks.Dss.Flipper.Trusted
import Benchmarks.Dss.Flipper.CommonRoutines

/-!
# MakerDAO/Sky DSS Flipper dispatcher facts

Shared runtime-dispatch obligations for the optimized Flipper bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flipper

attribute [local simp]
  begSelectorBytes
  bidsSelectorBytes
  catSelectorBytes
  dealSelectorBytes
  dentSelectorBytes
  denySelectorBytes
  fileAddressSelectorBytes
  fileUintSelectorBytes
  ilkSelectorBytes
  kickSelectorBytes
  kicksSelectorBytes
  relySelectorBytes
  tauSelectorBytes
  tendSelectorBytes
  tickSelectorBytes
  ttlSelectorBytes
  vatSelectorBytes
  wardsSelectorBytes
  yankSelectorBytes

theorem flipperDispatchBeg {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 0)) :
    dispatchMsg contract I.calldata = some begTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some begTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchKicks {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 10)) :
    dispatchMsg contract I.calldata = some kicksTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some kicksTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchTau {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 12)) :
    dispatchMsg contract I.calldata = some tauTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 12 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tauTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchTtl {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 15)) :
    dispatchMsg contract I.calldata = some ttlTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 15 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ttlTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchCat {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 2)) :
    dispatchMsg contract I.calldata = some catTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 2 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some catTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchDeal {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 3)) :
    dispatchMsg contract I.calldata = some dealTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dealTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchDent {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 4)) :
    dispatchMsg contract I.calldata = some dentTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 4 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dentTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchVat {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 16)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 16 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some vatTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchIlk {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 8)) :
    dispatchMsg contract I.calldata = some ilkTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 8 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some ilkTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchKick {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 9)) :
    dispatchMsg contract I.calldata = some kickTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some kickTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchWards {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 17)) :
    dispatchMsg contract I.calldata = some wardsTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 17 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some wardsTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchRely {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 11)) :
    dispatchMsg contract I.calldata = some relyTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some relyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchDeny {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 5)) :
    dispatchMsg contract I.calldata = some denyTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 5 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some denyTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchTend {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 13)) :
    dispatchMsg contract I.calldata = some tendTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 13 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tendTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchFileAddress {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 6)) :
    dispatchMsg contract I.calldata = some fileAddressTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileAddressTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchFileUint {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 7)) :
    dispatchMsg contract I.calldata = some fileUintTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileUintTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchTick {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 14)) :
    dispatchMsg contract I.calldata = some tickTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some tickTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperDispatchYank {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 18)) :
    dispatchMsg contract I.calldata = some yankTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 18 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some yankTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd]
  decide +native

theorem flipperBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact bodyReverts_nonPayable h

theorem flipperX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
  have h12 := h0.push2 ⟨16⟩ (by decide +native) (by simp only [List.length]; omega)
    |>.jumpiNT (by decide +native) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h12 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length]; omega)

/-- `callvalue ≠ 0` makes the global non-payable guard revert before dispatch. -/
theorem flipperNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (flipperX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (flipperBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-! ## Runtime dispatcher reachability -/

abbrev flipperRootSplitPc : UInt256 := ⟨32⟩
abbrev flipperLowSplitPc : UInt256 := ⟨43⟩
abbrev flipperLowHighFirstArmPc : UInt256 := ⟨54⟩
abbrev flipperLowLowJumpdestPc : UInt256 := ⟨113⟩
abbrev flipperLowLowFirstArmPc : UInt256 := ⟨114⟩
abbrev flipperHighJumpdestPc : UInt256 := ⟨173⟩
abbrev flipperHighSplitPc : UInt256 := ⟨174⟩
abbrev flipperHighHighFirstArmPc : UInt256 := ⟨185⟩
abbrev flipperHighLowJumpdestPc : UInt256 := ⟨244⟩
abbrev flipperHighLowFirstArmPc : UInt256 := ⟨245⟩
abbrev flipperDispatchBodyPc : UInt256 := ⟨18⟩
abbrev flipperSelectorLoadPc : UInt256 := ⟨26⟩
abbrev flipperDispatchRevertPc : UInt256 := ⟨289⟩

def flipperLowHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau()
  | 1 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ -- kicks()
  | 2 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 3 => ⟨#[0xe4, 0x88, 0x18, 0x13]⟩ -- cat()
  | _ => ⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩  -- tick(uint256)

def flipperLowLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x7d, 0x78, 0x0d, 0x82]⟩  -- beg()
  | 1 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 2 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩  -- wards(address)
  | 3 => ⟨#[0xc5, 0xce, 0x28, 0x1e]⟩  -- ilk()
  | _ => ⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩  -- deal(uint256)

def flipperHighHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x44, 0x23, 0xc5, 0xf1]⟩ -- bids(uint256)
  | 1 => ⟨#[0x4b, 0x43, 0xed, 0x12]⟩ -- tend(uint256,uint256,uint256)
  | 2 => ⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩ -- ttl()
  | 3 => ⟨#[0x5f, 0xf3, 0xa3, 0x82]⟩ -- dent(uint256,uint256,uint256)
  | _ => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩  -- rely(address)

def flipperHighLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩ -- yank(uint256)
  | 1 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 2 => ⟨#[0x35, 0x1d, 0xe6, 0x00]⟩ -- kick(address,address,uint256,uint256,uint256)
  | _ => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩  -- vat()

theorem flipperSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    flipperSelWord I = sel := by
  simpa [flipperSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem flipperRootSplitWellFormed :
    selectorSplitWellFormed flipperBytecode flipperRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

theorem flipperLowSplitWellFormed :
    selectorSplitWellFormed flipperBytecode flipperLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

theorem flipperHighSplitWellFormed :
    selectorSplitWellFormed flipperBytecode flipperHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | decide +native

set_option maxHeartbeats 1000000 in
theorem flipperLowHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flipperBytecode
      (nthArmPc flipperBytecode flipperLowHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem flipperLowLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flipperBytecode
      (nthArmPc flipperBytecode flipperLowLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem flipperHighHighArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed flipperBytecode
      (nthArmPc flipperBytecode flipperHighHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem flipperHighLowArmsWellFormed :
    ∀ j, j ≤ 3 → armWellFormed flipperBytecode
      (nthArmPc flipperBytecode flipperHighLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | decide +native)

theorem flipperLowHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flipperBytecode (nthArmPc flipperBytecode flipperLowHighFirstArmPc j))
        (flipperSelWord I) =
      if (flipperLowHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide +native)

theorem flipperLowLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flipperBytecode (nthArmPc flipperBytecode flipperLowLowFirstArmPc j))
        (flipperSelWord I) =
      if (flipperLowLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide +native)

theorem flipperHighHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 5) :
    UInt256.eq
        (armSelNat flipperBytecode (nthArmPc flipperBytecode flipperHighHighFirstArmPc j))
        (flipperSelWord I) =
      if (flipperHighHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide +native)

theorem flipperHighLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 4) :
    UInt256.eq
        (armSelNat flipperBytecode (nthArmPc flipperBytecode flipperHighLowFirstArmPc j))
        (flipperSelWord I) =
      if (flipperHighLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide +native)

theorem flipperReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flipperRootSplitPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [flipperRootSplitPc, flipperSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := flipperBytecode)
      (bodyPc := flipperDispatchBodyPc) (loadPc := flipperSelectorLoadPc)
      (firstPc := flipperRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := flipperDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)

theorem flipperReachLowSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flipperLowSplitPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    flipperReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperLowSplitPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [flipperLowSplitPc, flipperRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 flipperRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem flipperReachHighSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flipperHighSplitPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    flipperReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h173 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperHighJumpdestPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [flipperRootSplitPc, flipperHighJumpdestPc] using
      RD.selectorSplitTakenAuto h32 flipperRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h174 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperHighSplitPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [flipperHighSplitPc] using h173.jumpdest (by decide +native) (by simp)
  exact ⟨_, _, h174⟩

theorem flipperReachLowHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩)
    (hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flipperLowHighFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    flipperReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperLowHighFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [flipperLowHighFirstArmPc, flipperLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 flipperLowSplitWellFormed hlow (by simp)
  exact ⟨_, _, h54⟩

theorem flipperReachHighLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flipperHighLowFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k174, C174, h174⟩ :=
    flipperReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h244 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperHighLowJumpdestPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5) (C174 + 22) := by
    simpa [flipperHighSplitPc, flipperHighLowJumpdestPc] using
      RD.selectorSplitTakenAuto h174 flipperHighSplitWellFormed hhigh (by jump_dest)
        (by simp)
  have h245 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperHighLowFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5 + 1) (C174 + 22 + 1) := by
    simpa [flipperHighLowFirstArmPc] using h244.jumpdest (by decide +native) (by simp)
  exact ⟨_, _, h245⟩

theorem flipperReachHighHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) = ⟨0⟩) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flipperHighHighFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k174, C174, h174⟩ :=
    flipperReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h185 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperHighHighFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k174 + 5) (C174 + 22) := by
    simpa [flipperHighHighFirstArmPc, flipperHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h174 flipperHighSplitWellFormed hhigh (by simp)
  exact ⟨_, _, h185⟩

theorem flipperReachLowLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩)
    (hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        flipperLowLowFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    flipperReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h113 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperLowLowJumpdestPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [flipperLowSplitPc, flipperLowLowJumpdestPc] using
      RD.selectorSplitTakenAuto h43 flipperLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h114 : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperLowLowFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [flipperLowLowFirstArmPc] using h113.jumpdest (by decide +native) (by simp)
  exact ⟨_, _, h114⟩

theorem flipperReachHighHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc i))
        (flipperSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J flipperBytecode 0).contains bodyPC = true)
    (hbody : armTgt flipperBytecode
      (nthArmPc flipperBytecode flipperHighHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    flipperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => flipperHighHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem flipperReachHighLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 3) (bodyPC : UInt256)
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc i))
        (flipperSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J flipperBytecode 0).contains bodyPC = true)
    (hbody : armTgt flipperBytecode
      (nthArmPc flipperBytecode flipperHighLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    flipperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => flipperHighLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem flipperReachLowHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩)
    (hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc i))
        (flipperSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J flipperBytecode 0).contains bodyPC = true)
    (hbody : armTgt flipperBytecode
      (nthArmPc flipperBytecode flipperLowHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    flipperReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => flipperLowHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem flipperReachLowLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 4) (bodyPC : UInt256)
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩)
    (hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc i))
        (flipperSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J flipperBytecode 0).contains bodyPC = true)
    (hbody : armTgt flipperBytecode
      (nthArmPc flipperBytecode flipperLowLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    flipperReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => flipperLowLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem flipperDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [begTransition, bidsTransition, catTransition, dealTransition, dentTransition,
      denyTransition, fileAddressTransition, fileUintTransition, ilkTransition,
      kickTransition, kicksTransition, relyTransition, tauTransition, tendTransition,
      tickTransition, ttlTransition, vatTransition, wardsTransition, yankTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, begSelectorBytes, bidsSelectorBytes, catSelectorBytes,
        dealSelectorBytes, dentSelectorBytes, denySelectorBytes, fileAddressSelectorBytes,
        fileUintSelectorBytes, ilkSelectorBytes, kickSelectorBytes, kicksSelectorBytes,
        relySelectorBytes, tauSelectorBytes, tendSelectorBytes, tickSelectorBytes,
        ttlSelectorBytes, vatSelectorBytes, wardsSelectorBytes, yankSelectorBytes]
      decide +native) h

theorem flipperDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 19 → (flipperSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, begSelectorBytes]
    simpa [flipperSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, bidsSelectorBytes]
    simpa [flipperSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, catSelectorBytes]
    simpa [flipperSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, dealSelectorBytes]
    simpa [flipperSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, dentSelectorBytes]
    simpa [flipperSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [flipperSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, fileAddressSelectorBytes]
    simpa [flipperSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, fileUintSelectorBytes]
    simpa [flipperSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, ilkSelectorBytes]
    simpa [flipperSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, kickSelectorBytes]
    simpa [flipperSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, kicksSelectorBytes]
    simpa [flipperSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [flipperSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, tauSelectorBytes]
    simpa [flipperSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, tendSelectorBytes]
    simpa [flipperSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, tickSelectorBytes]
    simpa [flipperSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, ttlSelectorBytes]
    simpa [flipperSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [flipperSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [flipperSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, yankSelectorBytes]
    simpa [flipperSelBytes] using hnm 18 (by omega)

theorem flipperJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode flipperBytecode pc =
      some (.Push .PUSH2, some (flipperDispatchRevertPc, 2)))
    (hjump : decode flipperBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h289 := h.push2 flipperDispatchRevertPc hpush
    (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by decide +native) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h289 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_singleton]; omega)

theorem flipperLowHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) flipperLowHighFirstArmPc
      [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (flipperLowHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperLowHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperLowHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperLowHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperLowHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flipperJumpToNoMatchRevert h109 (by decide +native) (by decide +native)

theorem flipperLowLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) flipperLowLowFirstArmPc
      [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h169 := h
    |>.selectorArmNotTakenAuto (flipperLowLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperLowLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperLowLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperLowLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperLowLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flipperJumpToNoMatchRevert h169 (by decide +native) (by decide +native)

theorem flipperHighHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
      flipperHighHighFirstArmPc [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h240 := h
    |>.selectorArmNotTakenAuto (flipperHighHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperHighHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperHighHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperHighHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperHighHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact flipperJumpToNoMatchRevert h240 (by decide +native) (by decide +native)

theorem flipperHighLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) flipperHighLowFirstArmPc
      [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h289 := h
    |>.selectorArmNotTakenAuto (flipperHighLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperHighLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperHighLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (flipperHighLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.jumpdest (by decide +native) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h289 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_singleton]; omega)

theorem flipperX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt flipperBytecode)
    (opC := solcGuardTgtOp flipperBytecode)
    (wC := solcGuardTgtWidth flipperBytecode) h0 hwv
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest)
  have h289 := h1.push1 ⟨4⟩ (by decide +native) (by simp only [List.length]; omega)
    |>.calldatasize (by decide +native) (by simp only [List.length]; omega)
    |>.lt (by decide +native) (by simp only [List.length]; omega)
    |>.push2 flipperDispatchRevertPc (by decide +native) (by simp only [List.length]; omega)
    |>.jumpiT (by decide +native) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by decide +native) (by simp only [List.length]; omega)
  exact RD.solcPush1Dup1Revert0 h289 (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length]; omega)

theorem flipperX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 19 → (flipperSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLowHigh : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flipperBytecode (nthArmPc flipperBytecode flipperLowHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flipperLowHighArmEq I hsz 0 (by omega)]
      have hfalse : (flipperLowHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowHighSelBytes, flipperSelBytes] using hnm 12 (by omega)
      rw [hfalse]; rfl
    · rw [flipperLowHighArmEq I hsz 1 (by omega)]
      have hfalse : (flipperLowHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowHighSelBytes, flipperSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [flipperLowHighArmEq I hsz 2 (by omega)]
      have hfalse : (flipperLowHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowHighSelBytes, flipperSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [flipperLowHighArmEq I hsz 3 (by omega)]
      have hfalse : (flipperLowHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowHighSelBytes, flipperSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [flipperLowHighArmEq I hsz 4 (by omega)]
      have hfalse : (flipperLowHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowHighSelBytes, flipperSelBytes] using hnm 14 (by omega)
      rw [hfalse]; rfl
  have heqLowLow : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flipperBytecode (nthArmPc flipperBytecode flipperLowLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flipperLowLowArmEq I hsz 0 (by omega)]
      have hfalse : (flipperLowLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowLowSelBytes, flipperSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
    · rw [flipperLowLowArmEq I hsz 1 (by omega)]
      have hfalse : (flipperLowLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowLowSelBytes, flipperSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [flipperLowLowArmEq I hsz 2 (by omega)]
      have hfalse : (flipperLowLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowLowSelBytes, flipperSelBytes] using hnm 17 (by omega)
      rw [hfalse]; rfl
    · rw [flipperLowLowArmEq I hsz 3 (by omega)]
      have hfalse : (flipperLowLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowLowSelBytes, flipperSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [flipperLowLowArmEq I hsz 4 (by omega)]
      have hfalse : (flipperLowLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flipperLowLowSelBytes, flipperSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
  have heqHighHigh : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat flipperBytecode (nthArmPc flipperBytecode flipperHighHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flipperHighHighArmEq I hsz 0 (by omega)]
      have hfalse : (flipperHighHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighHighSelBytes, flipperSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [flipperHighHighArmEq I hsz 1 (by omega)]
      have hfalse : (flipperHighHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighHighSelBytes, flipperSelBytes] using hnm 13 (by omega)
      rw [hfalse]; rfl
    · rw [flipperHighHighArmEq I hsz 2 (by omega)]
      have hfalse : (flipperHighHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighHighSelBytes, flipperSelBytes] using hnm 15 (by omega)
      rw [hfalse]; rfl
    · rw [flipperHighHighArmEq I hsz 3 (by omega)]
      have hfalse : (flipperHighHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighHighSelBytes, flipperSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [flipperHighHighArmEq I hsz 4 (by omega)]
      have hfalse : (flipperHighHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighHighSelBytes, flipperSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
  have heqHighLow : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat flipperBytecode (nthArmPc flipperBytecode flipperHighLowFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [flipperHighLowArmEq I hsz 0 (by omega)]
      have hfalse : (flipperHighLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighLowSelBytes, flipperSelBytes] using hnm 18 (by omega)
      rw [hfalse]; rfl
    · rw [flipperHighLowArmEq I hsz 1 (by omega)]
      have hfalse : (flipperHighLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighLowSelBytes, flipperSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [flipperHighLowArmEq I hsz 2 (by omega)]
      have hfalse : (flipperHighLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighLowSelBytes, flipperSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [flipperHighLowArmEq I hsz 3 (by omega)]
      have hfalse : (flipperHighLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [flipperHighLowSelBytes, flipperSelBytes] using hnm 16 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩
  · by_cases hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
        (flipperSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        flipperReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
      exact flipperHighLowNoMatchRevert hfirst heqHighLow
    · have hhigh0 : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
          (flipperSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hhigh hne
      obtain ⟨_, _, hfirst⟩ :=
        flipperReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh0
      exact flipperHighHighNoMatchRevert hfirst heqHighHigh
  · have hroot0 : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
        (flipperSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    by_cases hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
        (flipperSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        flipperReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hlow
      exact flipperLowLowNoMatchRevert hfirst heqLowLow
    · have hlow0 : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
          (flipperSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hlow hne
      obtain ⟨_, _, hfirst⟩ :=
        flipperReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hlow0
      exact flipperLowHighNoMatchRevert hfirst heqLowHigh

/-- The runtime dispatcher reverts if no 4-byte selector arm matches. -/
theorem flipperNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 19 → (flipperSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (flipperX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (flipperDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (flipperX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (flipperDispatch_none_short hshort)

end Benchmarks.Dss.Flipper
