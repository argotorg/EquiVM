import Benchmarks.Dss.End.Trusted

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000

attribute [local simp]
  wardsSelectorBytes vatSelectorBytes catSelectorBytes dogSelectorBytes vowSelectorBytes
  potSelectorBytes spotSelectorBytes cureSelectorBytes liveSelectorBytes whenSelectorBytes
  waitSelectorBytes debtSelectorBytes tagSelectorBytes gapSelectorBytes ArtSelectorBytes
  fixSelectorBytes bagSelectorBytes outSelectorBytes relySelectorBytes denySelectorBytes
  fileAddressSelectorBytes fileUintSelectorBytes cageSelectorBytes cageIlkSelectorBytes
  snipSelectorBytes skipSelectorBytes skimSelectorBytes freeSelectorBytes thawSelectorBytes
  flowSelectorBytes packSelectorBytes cashSelectorBytes

def debtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨11⟩ σ I

theorem endDecode_debt {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (debtTransition.params.map Param.name)
      (transitionSignature debtTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endDispatchDebtLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 11)) :
    dispatchMsg contract I.calldata = some debtTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some debtTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, debtSelectorBytes]
  native_decide

set_option maxHeartbeats 5000000 in
theorem endReachDebtBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 11)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨501⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x0dca59c1⟩ :=
    endSelWord_eq_of_beq I hsz 0x0d 0xca 0x59 0xc1 ⟨0x0dca59c1⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot : UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h271 := RD.selectorSplitTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by jump_dest) (by simp)
  have h272 := h271.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h272gt : UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h391 := RD.selectorSplitTakenAuto h272
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h272gt (by jump_dest) (by simp)
  have h392 := h391.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h392gt : UInt256.gt (armSelNat endBytecode (⟨392⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h451 := RD.selectorSplitTakenAuto h392
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h392gt (by jump_dest) (by simp)
  have h452 := h451.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h452take : UInt256.eq (armSelNat endBytecode (⟨452⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h501 := h452.selectorArmTakenAuto
    (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
    h452take (by jump_dest) (by simp)
  exact ⟨_, _, h501⟩

theorem endDebtBodyCoreImpl
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some debtTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (debtTransition.params.map Param.name)
        (transitionSignature debtTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨501⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ debtTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (debtWord σ_solm I).toNat))])) := by
    simpa [debtTransition, debtWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endUint256GetterBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (ref := debtRef) (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (slot := ⟨11⟩)
        (by simp only [initState]; exact hwv) (by simp [debtRef])
        (by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (by decide) (by rfl)
  exact endUint256GetterBodyCore (entry := ⟨501⟩) (returnPc := ⟨509⟩)
    (routine := ⟨1309⟩) (slot := ⟨11⟩)
    hcode hdispatch hdecode hreach hAccounts
    (by unfold solcGetterEntryWf; repeat' first | apply And.intro | native_decide)
    (by unfold solcWordSlotGetterWf; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by jump_dest)
    (by unfold solcReturnWordFromMemWf; repeat' first | apply And.intro | native_decide)
    (by rfl) (by simpa [debtWord] using hbody)

theorem endDebtBodyCore : endBodyObligation 11 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 11) rfl hsel
  exact endDebtBodyCoreImpl hcode hwv (endDispatchDebtLocal hsel) (endDecode_debt hsz)
    (endReachDebtBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel) hAccounts

end Benchmarks.Dss.End
