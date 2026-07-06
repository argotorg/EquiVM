import Benchmarks.Dss.Dai.Constructor
import Benchmarks.Dss.Dai.Allowance
import Benchmarks.Dss.Dai.Approve
import Benchmarks.Dss.Dai.BalanceOf
import Benchmarks.Dss.Dai.Burn
import Benchmarks.Dss.Dai.Decimals
import Benchmarks.Dss.Dai.Deny
import Benchmarks.Dss.Dai.DomainSeparator
import Benchmarks.Dss.Dai.Mint
import Benchmarks.Dss.Dai.Move
import Benchmarks.Dss.Dai.Name
import Benchmarks.Dss.Dai.Nonces
import Benchmarks.Dss.Dai.Permit
import Benchmarks.Dss.Dai.PermitTypehash
import Benchmarks.Dss.Dai.Pull
import Benchmarks.Dss.Dai.Push
import Benchmarks.Dss.Dai.Rely
import Benchmarks.Dss.Dai.Symbol
import Benchmarks.Dss.Dai.TotalSupply
import Benchmarks.Dss.Dai.Transfer
import Benchmarks.Dss.Dai.TransferFrom
import Benchmarks.Dss.Dai.Version
import Benchmarks.Dss.Dai.Wards

/-!
# MakerDAO DSS Dai benchmark correctness scaffold

The top-level runtime theorem performs the shared Solidity dispatcher split: non-payable guard,
selector-size guard, and one branch per ABI selector.  Each matched branch delegates to that
function's `…BodyCore` lemma in its own file.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

attribute [local simp]
  daiAllowanceSelectorBytes
  daiApproveSelectorBytes
  daiBalanceOfSelectorBytes
  daiBurnSelectorBytes
  daiDecimalsSelectorBytes
  daiDenySelectorBytes
  daiDomainSeparatorSelectorBytes
  daiMintSelectorBytes
  daiMoveSelectorBytes
  daiNameSelectorBytes
  daiNoncesSelectorBytes
  daiPermitSelectorBytes
  daiPermitTypehashSelectorBytes
  daiPullSelectorBytes
  daiPushSelectorBytes
  daiRelySelectorBytes
  daiSymbolSelectorBytes
  daiTotalSupplySelectorBytes
  daiTransferSelectorBytes
  daiTransferFromSelectorBytes
  daiVersionSelectorBytes
  daiWardsSelectorBytes

theorem daiBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem daiX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h12 := h0
    |>.pushConst (⟨16⟩ : UInt256) (width := 2) (op := .PUSH2) (by native_decide)
        (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
        (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem daiX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt daiBytecode) (opC := solcGuardTgtOp daiBytecode)
    (wC := solcGuardTgtWidth daiBytecode) h0 hwv
    (by decide) (by decide) (by decide) (by decide) (by decide) (by jump_dest)
  have h322 := h1
    |>.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.pushConst (⟨322⟩ : UInt256) (width := 2) (op := .PUSH2) (by native_decide)
        (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
        (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h322 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem daiDispatch_none_short {cd : ByteArray} (hshort : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl) (by rfl)]
  exact dispatchList_none_short contract.transitions
    (by
      intro t ht
      simp [contract, transitions] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [selectorOf, daiAllowanceSelectorBytes]; rfl
      · rw [selectorOf, daiApproveSelectorBytes]; rfl
      · rw [selectorOf, daiBalanceOfSelectorBytes]; rfl
      · rw [selectorOf, daiBurnSelectorBytes]; rfl
      · rw [selectorOf, daiDecimalsSelectorBytes]; rfl
      · rw [selectorOf, daiDenySelectorBytes]; rfl
      · rw [selectorOf, daiDomainSeparatorSelectorBytes]; rfl
      · rw [selectorOf, daiMintSelectorBytes]; rfl
      · rw [selectorOf, daiMoveSelectorBytes]; rfl
      · rw [selectorOf, daiNameSelectorBytes]; rfl
      · rw [selectorOf, daiNoncesSelectorBytes]; rfl
      · rw [selectorOf, daiPermitSelectorBytes]; rfl
      · rw [selectorOf, daiPermitTypehashSelectorBytes]; rfl
      · rw [selectorOf, daiPullSelectorBytes]; rfl
      · rw [selectorOf, daiPushSelectorBytes]; rfl
      · rw [selectorOf, daiRelySelectorBytes]; rfl
      · rw [selectorOf, daiSymbolSelectorBytes]; rfl
      · rw [selectorOf, daiTotalSupplySelectorBytes]; rfl
      · rw [selectorOf, daiTransferSelectorBytes]; rfl
      · rw [selectorOf, daiTransferFromSelectorBytes]; rfl
      · rw [selectorOf, daiVersionSelectorBytes]; rfl
      · rw [selectorOf, daiWardsSelectorBytes]; rfl)
    hshort

theorem daiDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 22 → (daiSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl) (by rfl)]
  apply dispatchList_none_of_all_ne
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [selectorOf] using hnm 0 (by decide)
  · simpa [selectorOf] using hnm 1 (by decide)
  · simpa [selectorOf] using hnm 2 (by decide)
  · simpa [selectorOf] using hnm 3 (by decide)
  · simpa [selectorOf] using hnm 4 (by decide)
  · simpa [selectorOf] using hnm 5 (by decide)
  · simpa [selectorOf] using hnm 6 (by decide)
  · simpa [selectorOf] using hnm 7 (by decide)
  · simpa [selectorOf] using hnm 8 (by decide)
  · simpa [selectorOf] using hnm 9 (by decide)
  · simpa [selectorOf] using hnm 10 (by decide)
  · simpa [selectorOf] using hnm 11 (by decide)
  · simpa [selectorOf] using hnm 12 (by decide)
  · simpa [selectorOf] using hnm 13 (by decide)
  · simpa [selectorOf] using hnm 14 (by decide)
  · simpa [selectorOf] using hnm 15 (by decide)
  · simpa [selectorOf] using hnm 16 (by decide)
  · simpa [selectorOf] using hnm 17 (by decide)
  · simpa [selectorOf] using hnm 18 (by decide)
  · simpa [selectorOf] using hnm 19 (by decide)
  · simpa [selectorOf] using hnm 20 (by decide)
  · simpa [selectorOf] using hnm 21 (by decide)

theorem daiJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    {pc : UInt256}
    (h : RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) pc [daiSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode daiBytecode pc = some (.Push .PUSH2, some (⟨322⟩, 2)))
    (hjump : decode daiBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h322 := h.push2 ⟨322⟩ hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.uniswapPush1Dup1Revert0 h322 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem daiX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 22 → (daiSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hselectorNoMatch (i : ℕ) (hi : i < 22) (c0 c1 c2 c3 : UInt8) (sel : UInt256)
      (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
      (hbytes : daiSelBytes i = (⟨#[c0, c1, c2, c3]⟩ : ByteArray)) :
      UInt256.eq sel (daiSelWord I) = ⟨0⟩ := by
    dsimp [daiSelWord]
    rw [evmSelectorDecode hsz c0 c1 c2 c3 sel hsel]
    have hno := hnm i hi
    rw [hbytes] at hno
    simp [hno]
  have heqVeryHigh : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat daiBytecode (nthArmPc daiBytecode daiVeryHighFirstArmPc j))
        (daiSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 18 (by omega) 0xa9 0x05 0x9c 0xbb _ (by native_decide) rfl
    · exact hselectorNoMatch 14 (by omega) 0xb7 0x53 0xa9 0x8c _ (by native_decide) rfl
    · exact hselectorNoMatch 8 (by omega) 0xbb 0x35 0x78 0x3b _ (by native_decide) rfl
    · exact hselectorNoMatch 21 (by omega) 0xbf 0x35 0x3d 0xbb _ (by native_decide) rfl
    · exact hselectorNoMatch 0 (by omega) 0xdd 0x62 0xed 0x3e _ (by native_decide) rfl
    · exact hselectorNoMatch 13 (by omega) 0xf2 0xd5 0xd5 0x6b _ (by native_decide) rfl
  have heqHigh : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat daiBytecode (nthArmPc daiBytecode daiHighFirstArmPc j))
        (daiSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 10 (by omega) 0x7e 0xce 0xbe 0x00 _ (by native_decide) rfl
    · exact hselectorNoMatch 11 (by omega) 0x8f 0xcb 0xaf 0x0c _ (by native_decide) rfl
    · exact hselectorNoMatch 16 (by omega) 0x95 0xd8 0x9b 0x41 _ (by native_decide) rfl
    · exact hselectorNoMatch 5 (by omega) 0x9c 0x52 0xa7 0xf1 _ (by native_decide) rfl
    · exact hselectorNoMatch 3 (by omega) 0x9d 0xc2 0x9f 0xac _ (by native_decide) rfl
  have heqLow : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat daiBytecode (nthArmPc daiBytecode daiLowFirstArmPc j))
        (daiSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 4 (by omega) 0x31 0x3c 0xe5 0x67 _ (by native_decide) rfl
    · exact hselectorNoMatch 6 (by omega) 0x36 0x44 0xe5 0x15 _ (by native_decide) rfl
    · exact hselectorNoMatch 7 (by omega) 0x40 0xc1 0x0f 0x19 _ (by native_decide) rfl
    · exact hselectorNoMatch 20 (by omega) 0x54 0xfd 0x4d 0x50 _ (by native_decide) rfl
    · exact hselectorNoMatch 15 (by omega) 0x65 0xfa 0xe3 0x5e _ (by native_decide) rfl
    · exact hselectorNoMatch 2 (by omega) 0x70 0xa0 0x82 0x31 _ (by native_decide) rfl
  have heqVeryLow : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat daiBytecode (nthArmPc daiBytecode daiVeryLowFirstArmPc j))
        (daiSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 9 (by omega) 0x06 0xfd 0xde 0x03 _ (by native_decide) rfl
    · exact hselectorNoMatch 1 (by omega) 0x09 0x5e 0xa7 0xb3 _ (by native_decide) rfl
    · exact hselectorNoMatch 17 (by omega) 0x18 0x16 0x0d 0xdd _ (by native_decide) rfl
    · exact hselectorNoMatch 19 (by omega) 0x23 0xb8 0x72 0xdd _ (by native_decide) rfl
    · exact hselectorNoMatch 12 (by omega) 0x30 0xad 0xf8 0x1f _ (by native_decide) rfl
  by_cases hroot :
      UInt256.gt (armSelNat daiBytecode daiRootSplitPc) (daiSelWord I) = ⟨0⟩
  · by_cases hhigh :
        UInt256.gt (armSelNat daiBytecode daiHighSplitPc) (daiSelWord I) = ⟨0⟩
    · obtain ⟨_, _, h54⟩ := daiReachVeryHighFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hhigh
      have h124 := h54
        |>.selectorArmNotTakenAuto (daiVeryHighArmsWellFormed 0 (by omega))
            (heqVeryHigh 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryHighArmsWellFormed 1 (by omega))
            (heqVeryHigh 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryHighArmsWellFormed 2 (by omega))
            (heqVeryHigh 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryHighArmsWellFormed 3 (by omega))
            (heqVeryHigh 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryHighArmsWellFormed 4 (by omega))
            (heqVeryHigh 4 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryHighArmsWellFormed 5 (by omega))
            (heqVeryHigh 5 (by omega)) (by simp)
      exact daiJumpToNoMatchRevert h124 (by native_decide) (by native_decide)
    · obtain ⟨_, _, h125⟩ := daiReachHighFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hhigh
      have h181 := h125
        |>.selectorArmNotTakenAuto (daiHighArmsWellFormed 0 (by omega))
            (heqHigh 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiHighArmsWellFormed 1 (by omega))
            (heqHigh 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiHighArmsWellFormed 2 (by omega))
            (heqHigh 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiHighArmsWellFormed 3 (by omega))
            (heqHigh 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiHighArmsWellFormed 4 (by omega))
            (heqHigh 4 (by omega)) (by simp)
      exact daiJumpToNoMatchRevert h181 (by native_decide) (by native_decide)
  · by_cases hlow :
        UInt256.gt (armSelNat daiBytecode daiLowSplitPc) (daiSelWord I) = ⟨0⟩
    · obtain ⟨_, _, h196⟩ := daiReachLowFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hlow
      have h263 := h196
        |>.selectorArmNotTakenAuto (daiLowArmsWellFormed 0 (by omega))
            (heqLow 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiLowArmsWellFormed 1 (by omega))
            (heqLow 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiLowArmsWellFormed 2 (by omega))
            (heqLow 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiLowArmsWellFormed 3 (by omega))
            (heqLow 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiLowArmsWellFormed 4 (by omega))
            (heqLow 4 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiLowArmsWellFormed 5 (by omega))
            (heqLow 5 (by omega)) (by simp)
      exact daiJumpToNoMatchRevert h263 (by native_decide) (by native_decide)
    · obtain ⟨_, _, h267⟩ := daiReachVeryLowFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hlow
      have h322 := h267
        |>.selectorArmNotTakenAuto (daiVeryLowArmsWellFormed 0 (by omega))
            (heqVeryLow 0 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryLowArmsWellFormed 1 (by omega))
            (heqVeryLow 1 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryLowArmsWellFormed 2 (by omega))
            (heqVeryLow 2 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryLowArmsWellFormed 3 (by omega))
            (heqVeryLow 3 (by omega)) (by simp)
        |>.selectorArmNotTakenAuto (daiVeryLowArmsWellFormed 4 (by omega))
            (heqVeryLow 4 (by omega)) (by simp)
      have h323 := h322.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
      exact RD.uniswapPush1Dup1Revert0 h323 (by native_decide) (by native_decide)
        (by native_decide) (by simp only [List.length_singleton]; omega)

/-- `callvalue != 0` reverts on both sides for every Dai transition. -/
theorem daiNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (daiX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
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
            (daiBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
              (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than a selector reverts before runtime dispatch reaches a body. -/
theorem daiShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (daiX_short (g := Sat256.ofUInt256 g) hcode hwv hsz).reEquivNoDispatch hcode
    (daiDispatch_none_short hsz)

/-- No selector matches: Solm dispatch fails and the bytecode falls through to the revert stub. -/
theorem daiNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 22 → (daiSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (daiX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (daiDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (daiX_short (g := Sat256.ofUInt256 g) hcode hwv hshort).reEquivNoDispatch hcode
      (daiDispatch_none_short hshort)

theorem daiCorrect :
    runtimeEquivalence!?! config daiBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I (daiSelBytes 0)
      · exact daiAllowanceBodyCore hcode hsize hperm hwv h0 hAccounts
      · by_cases h1 : selIs I (daiSelBytes 1)
        · exact daiApproveBodyCore hcode hsize hperm hwv h1 hAccounts
        · by_cases h2 : selIs I (daiSelBytes 2)
          · exact daiBalanceOfBodyCore hcode hsize hperm hwv h2 hAccounts
          · by_cases h3 : selIs I (daiSelBytes 3)
            · exact daiBurnBodyCore hcode hsize hperm hwv h3 hAccounts
            · by_cases h4 : selIs I (daiSelBytes 4)
              · exact daiDecimalsBodyCore hcode hsize hperm hwv h4 hAccounts
              · by_cases h5 : selIs I (daiSelBytes 5)
                · exact daiDenyBodyCore hcode hsize hperm hwv h5 hAccounts
                · by_cases h6 : selIs I (daiSelBytes 6)
                  · exact daiDomainSeparatorBodyCore hcode hsize hperm hwv h6 hAccounts
                  · by_cases h7 : selIs I (daiSelBytes 7)
                    · exact daiMintBodyCore hcode hsize hperm hwv h7 hAccounts
                    · by_cases h8 : selIs I (daiSelBytes 8)
                      · exact daiMoveBodyCore hcode hsize hperm hwv h8 hAccounts
                      · by_cases h9 : selIs I (daiSelBytes 9)
                        · exact daiNameBodyCore hcode hsize hperm hwv h9 hAccounts
                        · by_cases h10 : selIs I (daiSelBytes 10)
                          · exact daiNoncesBodyCore hcode hsize hperm hwv h10 hAccounts
                          · by_cases h11 : selIs I (daiSelBytes 11)
                            · exact daiPermitBodyCore hcode hsize hperm hwv h11 hAccounts
                            · by_cases h12 : selIs I (daiSelBytes 12)
                              · exact daiPermitTypehashBodyCore hcode hsize hperm hwv h12 hAccounts
                              · by_cases h13 : selIs I (daiSelBytes 13)
                                · exact daiPullBodyCore hcode hsize hperm hwv h13 hAccounts
                                · by_cases h14 : selIs I (daiSelBytes 14)
                                  · exact daiPushBodyCore hcode hsize hperm hwv h14 hAccounts
                                  · by_cases h15 : selIs I (daiSelBytes 15)
                                    · exact daiRelyBodyCore hcode hsize hperm hwv h15 hAccounts
                                    · by_cases h16 : selIs I (daiSelBytes 16)
                                      · exact daiSymbolBodyCore hcode hsize hperm hwv h16 hAccounts
                                      · by_cases h17 : selIs I (daiSelBytes 17)
                                        · exact daiTotalSupplyBodyCore hcode hsize hperm hwv h17 hAccounts
                                        · by_cases h18 : selIs I (daiSelBytes 18)
                                          · exact daiTransferBodyCore hcode hsize hperm hwv h18 hAccounts
                                          · by_cases h19 : selIs I (daiSelBytes 19)
                                            · exact daiTransferFromBodyCore hcode hsize hperm hwv h19 hAccounts
                                            · by_cases h20 : selIs I (daiSelBytes 20)
                                              · exact daiVersionBodyCore hcode hsize hperm hwv h20 hAccounts
                                              · by_cases h21 : selIs I (daiSelBytes 21)
                                                · exact daiWardsBodyCore hcode hsize hperm hwv h21 hAccounts
                                                · refine daiNoDispatch hcode hsize hperm hwv ?_
                                                  intro i hi
                                                  interval_cases i
                                                  · simpa [selIs, daiSelBytes] using h0
                                                  · simpa [selIs, daiSelBytes] using h1
                                                  · simpa [selIs, daiSelBytes] using h2
                                                  · simpa [selIs, daiSelBytes] using h3
                                                  · simpa [selIs, daiSelBytes] using h4
                                                  · simpa [selIs, daiSelBytes] using h5
                                                  · simpa [selIs, daiSelBytes] using h6
                                                  · simpa [selIs, daiSelBytes] using h7
                                                  · simpa [selIs, daiSelBytes] using h8
                                                  · simpa [selIs, daiSelBytes] using h9
                                                  · simpa [selIs, daiSelBytes] using h10
                                                  · simpa [selIs, daiSelBytes] using h11
                                                  · simpa [selIs, daiSelBytes] using h12
                                                  · simpa [selIs, daiSelBytes] using h13
                                                  · simpa [selIs, daiSelBytes] using h14
                                                  · simpa [selIs, daiSelBytes] using h15
                                                  · simpa [selIs, daiSelBytes] using h16
                                                  · simpa [selIs, daiSelBytes] using h17
                                                  · simpa [selIs, daiSelBytes] using h18
                                                  · simpa [selIs, daiSelBytes] using h19
                                                  · simpa [selIs, daiSelBytes] using h20
                                                  · simpa [selIs, daiSelBytes] using h21
    · exact daiShortRevert hcode hsize hperm hwv (by omega)
  · exact daiNonPayable hcode hwv

theorem daiContractCorrect :
    contractEquivalence config daiCreationBytecode daiBytecode contract :=
  contractEquivalence.intro daiConstructorCorrect daiCorrect

end Benchmarks.Dss.Dai
