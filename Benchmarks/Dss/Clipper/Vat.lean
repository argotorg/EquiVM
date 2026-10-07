import Reasoning.WordArithmetic
import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperVatSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 25)) :
    clipperSelWord I = clipperSelNat 25 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x36 0x56 0x9e 0x77 (clipperSelNat 25)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_vat {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 25)) :
    dispatchMsg contract I.calldata = some vatTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition, kickTransition,
        kicksTransition, listTransition, redoTransition, relyTransition, salesTransition,
        spotterTransition, stoppedTransition, tailTransition, takeTransition, tipTransition,
        upchostTransition])
    (post := [vowTransition, wardsTransition, yankTransition])
    (ti := vatTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, countSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, cuspSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, denySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, dogSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileUintSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileAddressSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, getStatusSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, ilkSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kickSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, listSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, redoSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, relySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, salesSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, spotterSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, stoppedSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, tailSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, takeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, tipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, upchostSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, vatSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_vat {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (vatTransition.params.map Param.name)
      (transitionSignature vatTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalVat (v : ClipperImmutables) (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm vatExpr =
      .ok (.address v.vat) := by
  exact evalExpr_vatExpr

theorem clipperVatBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals vatTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm (some [(.address v.vat)])) (immStore v) := by
  simpa [vatTransition] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h
      (clipperEvalVat v evm locals)

set_option maxHeartbeats 1000000 in
theorem clipperReachVatBody {σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 25)) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) (⟨744⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperVatSelectorWord hsz hsel
  have h260 := RD.selectorSplitTakenPush2 (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
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
        change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by native_decide))
    (by simp)
  have h272 := RD.selectorSplitNotTakenPush2 (pc := (⟨261⟩ : UInt256))
    (next := (⟨272⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by
          change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
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
        change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h331 := RD.selectorSplitTakenPush2 (pc := (⟨272⟩ : UInt256))
    (pivot := clipperSelNat 6) (tgt := (⟨331⟩ : UInt256)) h272
    (by
        change decode code (⟨272⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨272⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 6, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨272⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨272⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨331⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨272⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨331⟩ : UInt256) (by native_decide))
    (by simp)
  have h343 := RD.selectorArmNotTakenPush2 (pc := (⟨332⟩ : UInt256))
    (next := (⟨343⟩ : UInt256)) (sel := clipperSelNat 9)
    (tgt := (⟨673⟩ : UInt256))
    (h331.jumpdest
      (by
          change decode code (⟨331⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
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
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h354 := RD.selectorArmNotTakenPush2 (pc := (⟨343⟩ : UInt256))
    (next := (⟨354⟩ : UInt256)) (sel := clipperSelNat 19)
    (tgt := (⟨708⟩ : UInt256)) h343
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
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h744 := RD.selectorArmTakenPush2 (pc := (⟨354⟩ : UInt256)) (sel := clipperSelNat 25)
    (tgt := (⟨744⟩ : UInt256)) h354
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
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨744⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h744⟩

theorem clipperVatGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨744⟩ : UInt256) (⟨716⟩ : UInt256) (⟨3143⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperVatPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hwin : (lo, hi) ∈
      [(3143, 3144), (3144, 3144), (3144, 3145), (3177, 3178), (3178, 3178),
        (3178, 3179), (3179, 3179)]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : Reasoning.Theory.wordBytes? v.ilk
  · simp [hIlk] at hwin ⊢
  · simp [hIlk] at hwin ⊢
    omega

theorem clipperVatPatchPayload (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 3145 3177 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v with ⟨ilk, vat, hwf⟩
  rcases hwf with ⟨ilkBs, hilk, hlen⟩
  subst ilk
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian ilkBs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑vat : Nat))
  have hpost :
      PatchesWindowDisjoint32 3145 3177
        [(4318, vatBytes), (4441, vatBytes), (4751, vatBytes), (5115, vatBytes),
          (6295, vatBytes), (7936, vatBytes),
          (1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
          (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
          (8747, ilkBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | hfalse
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre := [(1463, vatBytes), (2437, vatBytes)])
    (post :=
      [(4318, vatBytes), (4441, vatBytes), (4751, vatBytes), (5115, vatBytes),
        (6295, vatBytes), (7936, vatBytes),
        (1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes)])
    (off := 3145) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, Reasoning.Theory.wordBytes?, valueToWord,
        List.lookup_cons, hlen, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperVatPush32Decode (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨3144⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  exact decode_push32_of_get?_extract'
    (pc := (⟨3144⟩ : UInt256)) (w := EVM.Word.ofNat (↑v.vat : Nat))
    (by
      rw [patchRuntime_get?_disjoint hpatch
        (by apply clipperVatPatchesWindowDisjoint32 v; native_decide)]
      native_decide)
    (by
      rw [show (⟨3144⟩ : UInt256).toNat + 1 = 3145 by native_decide]
      rw [show (⟨3144⟩ : UInt256).toNat + 33 = 3177 by native_decide]
      exact clipperVatPatchPayload v hpatch)

set_option maxHeartbeats 1000000 in
theorem clipperVatConstGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcConstGetterWf code (⟨3143⟩ : UInt256) (EVM.Word.ofNat (↑v.vat : Nat))
      32 .PUSH32 := by
  unfold solcConstGetterWf
  repeat' first | apply And.intro
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperVatPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperVatPatchesWindowDisjoint32 v; native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
  · decide
  · exact clipperVatPush32Decode v hpatch
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperVatPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperVatPatchesWindowDisjoint32 v; native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperVatPatchesWindowDisjoint32 v; native_decide)
      (by apply clipperVatPatchesWindowDisjoint32 v; native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperJumpDest3143 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3143⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : Reasoning.Theory.wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide


theorem clipperVatBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 25)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 25) (by native_decide) hsel
  have hvatAddr :
      AccountAddress.ofNat (EVM.Word.ofNat (↑v.vat : Nat)).toNat = v.vat :=
    addressOfWordOfNat v.vat
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ vatTransition.body
        (.returned { contract := contract, locals := ∅, immutables := immStore v }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (EVM.Word.ofNat (↑v.vat : Nat)).toNat))])) (immStore v) := by
    simpa [hvatAddr] using
      clipperVatBodyReturns v
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv)
  have hreach := clipperReachVatBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hroutine : (D_J code 0).contains (⟨3143⟩ : UInt256) = true := by
    exact clipperJumpDest3143 v hpatch
  exact clipperAddressConstGetterBodyCore (v := v) (code := code)
    (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (sel := clipperSelWord I) (transition := vatTransition)
    (entry := (⟨744⟩ : UInt256)) (routine := (⟨3143⟩ : UInt256))
    (returnPc := (⟨716⟩ : UInt256)) (val := EVM.Word.ofNat (↑v.vat : Nat))
    (width := 32) (op := .PUSH32) hcode (clipperDispatch_vat hsel)
    (clipperDecode_vat hsz) hreach (clipperVatGetterEntryWf v hpatch)
    (clipperVatConstGetterWf v hpatch) hroutine
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨716⟩ : UInt256) (by native_decide))
    (clipperReturnAddress716Wf v hpatch) (by rfl) hbody

end Benchmarks.Dss.Clipper
