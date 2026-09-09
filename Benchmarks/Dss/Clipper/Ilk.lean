import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperIlkSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 12)) :
    clipperSelWord I = clipperSelNat 12 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0xc5 0xce 0x28 0x1e (clipperSelNat 12)
      (by decide +native) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_ilk (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 12)) :
    dispatchMsg (contract v) I.calldata = some (ilkTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition])
    (post :=
      [kickTransition v, kicksTransition, listTransition, redoTransition v, relyTransition,
        salesTransition, spotterTransition, stoppedTransition, tailTransition, takeTransition v,
        tipTransition, upchostTransition v, vatTransition v, vowTransition, wardsTransition,
        yankTransition v])
    (ti := ilkTransition v) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, countSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, cuspSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, denySelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, dogSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, fileUintSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, fileAddressSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · rw [selectorOf, getStatusSelectorBytes, ← byteArray_eq_of_beq hsel]
      decide +native
    · cases hfalse
  · rw [selectorOf, ilkSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_ilk (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((ilkTransition v).params.map Param.name)
      (transitionSignature (ilkTransition v)).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperIlkBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm locals (ilkTransition v).body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.fixedBytes ⟨31, by decide⟩ bs)])) := by
  simpa [ilkTransition, ilkExpr, hilk] using
    nonpayableFixedBytesLiteralBodyReturns (cfg := config v) (contract := contract v)
      evm locals ⟨31, by decide⟩ bs h

set_option maxHeartbeats 1000000 in
theorem clipperReachIlkBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 12)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1349⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperIlkSelectorWord hsz hsel
  have h43 := clipperSplitNotTaken (pc := (⟨32⟩ : UInt256))
    (next := (⟨43⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by
        change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (⟨33⟩ : UInt256) =
          some (.Push .PUSH4, some (clipperSelNat 20, 4))
        clipper_decode)
    (by
        change decode code (⟨38⟩ : UInt256) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (⟨39⟩ : UInt256) =
          some (.Push .PUSH2, some (⟨260⟩, 2))
        clipper_decode)
    (by
        change decode code (⟨42⟩ : UInt256) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (by decide +native)
    (by simp)
  have h54 := clipperSplitNotTaken (pc := (⟨43⟩ : UInt256))
    (next := (⟨54⟩ : UInt256)) (pivot := clipperSelNat 3)
    (tgt := (⟨162⟩ : UInt256)) h43
    (by
        change decode code (⟨43⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (⟨44⟩ : UInt256) =
          some (.Push .PUSH4, some (clipperSelNat 3, 4))
        clipper_decode)
    (by
        change decode code (⟨49⟩ : UInt256) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (⟨50⟩ : UInt256) =
          some (.Push .PUSH2, some (⟨162⟩, 2))
        clipper_decode)
    (by
        change decode code (⟨53⟩ : UInt256) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (by decide +native)
    (by simp)
  have h65 := clipperSplitNotTaken (pc := (⟨54⟩ : UInt256))
    (next := (⟨65⟩ : UInt256)) (pivot := clipperSelNat 12)
    (tgt := (⟨113⟩ : UInt256)) h54
    (by
        change decode code (⟨54⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (⟨55⟩ : UInt256) =
          some (.Push .PUSH4, some (clipperSelNat 12, 4))
        clipper_decode)
    (by
        change decode code (⟨60⟩ : UInt256) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (⟨61⟩ : UInt256) =
          some (.Push .PUSH2, some (⟨113⟩, 2))
        clipper_decode)
    (by
        change decode code (⟨64⟩ : UInt256) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (by decide +native)
    (by simp)
  have h1349 := clipperArmTaken (pc := (⟨65⟩ : UInt256)) (sel := clipperSelNat 12)
    (tgt := (⟨1349⟩ : UInt256)) h65
    (by
        change decode code (⟨65⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (⟨66⟩ : UInt256) =
          some (.Push .PUSH4, some (clipperSelNat 12, 4))
        clipper_decode)
    (by
        change decode code (⟨71⟩ : UInt256) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (⟨72⟩ : UInt256) =
          some (.Push .PUSH2, some (⟨1349⟩, 2))
        clipper_decode)
    (by
        change decode code (⟨75⟩ : UInt256) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; decide +native)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1349⟩ : UInt256) (by decide +native))
    (by simp)
  exact ⟨_, _, h1349⟩

theorem clipperIlkGetterEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨1349⟩ : UInt256) (⟨476⟩ : UInt256)
      (⟨6798⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by decide +native)]
    decide +native

theorem clipperIlkPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hwin : (lo, hi) ∈
      [(6798, 6799), (6799, 6799), (6799, 6800), (6832, 6833), (6833, 6833),
        (6833, 6834), (6834, 6834)]) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk
  · simp [hIlk] at hwin ⊢
  · simp [hIlk] at hwin ⊢
    omega

theorem clipperIlkPatchPayload (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 6800 6832 =
      ({ data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray } :
        ByteArray) := by
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : ilkBytes.size = 32 := by
    simpa [ilkBytes] using
      word_toBytesBE_toByteArray_size (EVM.Word.ofNat (fromBytesBigEndian bs))
  have hpost :
      PatchesWindowDisjoint32 6800 6832
        [(8747, ilkBytes), (1463, vatBytes), (2437, vatBytes), (3145, vatBytes),
          (4318, vatBytes), (4441, vatBytes), (4751, vatBytes), (5115, vatBytes),
          (6295, vatBytes), (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
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
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes)])
    (post :=
      [(8747, ilkBytes), (1463, vatBytes), (2437, vatBytes), (3145, vatBytes),
        (4318, vatBytes), (4441, vatBytes), (4751, vatBytes), (5115, vatBytes),
        (6295, vatBytes), (7936, vatBytes)])
    (off := 6800) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk, hlen,
        List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperIlkPush32Decode (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨6799⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  exact decode_push32_of_get?_extract'
    (pc := (⟨6799⟩ : UInt256)) (w := EVM.Word.ofNat (fromBytesBigEndian bs))
    (by
      rw [patchRuntime_get?_disjoint hpatch
        (by apply clipperIlkPatchesWindowDisjoint32 v; decide +native)]
      decide +native)
    (by
      rw [show (⟨6799⟩ : UInt256).toNat + 1 = 6800 by decide +native]
      rw [show (⟨6799⟩ : UInt256).toNat + 33 = 6832 by decide +native]
      exact clipperIlkPatchPayload v hpatch hilk hlen)

set_option maxHeartbeats 1000000 in
theorem clipperIlkConstGetterWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    solcConstGetterWf code (⟨6798⟩ : UInt256)
      (EVM.Word.ofNat (fromBytesBigEndian bs)) 32 .PUSH32 := by
  unfold solcConstGetterWf
  repeat' first | apply And.intro
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperIlkPatchesWindowDisjoint32 v; decide +native)
      (by apply clipperIlkPatchesWindowDisjoint32 v; decide +native)
      (by decide +native)
      (by decide +native)
      (by decide +native)
  · decide
  · exact clipperIlkPush32Decode v hpatch hilk hlen
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperIlkPatchesWindowDisjoint32 v; decide +native)
      (by apply clipperIlkPatchesWindowDisjoint32 v; decide +native)
      (by decide +native)
      (by decide +native)
      (by decide +native)
  · exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperIlkPatchesWindowDisjoint32 v; decide +native)
      (by apply clipperIlkPatchesWindowDisjoint32 v; decide +native)
      (by decide +native)
      (by decide +native)
      (by decide +native)

theorem clipperJumpDest6798 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6798⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      decide +native
  | some bs =>
      simp [hIlk]
      decide +native

theorem clipperIlkBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 12))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 12) (by decide +native) hsel
  have htoBytes :
      EVM.Word.toBytesBE (EVM.Word.ofNat (fromBytesBigEndian ilkBs)) = ilkBs := by
    simpa [ABI.bytesToWord, fromByteArrayBigEndian, byteArray_toList_eq] using
      toBytesBE_bytesToWord_of_length hlen
  have hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ (ilkTransition v).body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes ⟨31, by decide⟩
            (EVM.Word.toBytesBE (EVM.Word.ofNat (fromBytesBigEndian ilkBs))))])) := by
    simpa [htoBytes] using
      clipperIlkBodyReturns v
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ hilk
        (by simp only [initState]; exact hwv)
  have hreach := clipperReachIlkBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (v := v) hpatch hcode hwv hsz hsize hsel
  have hroutine : (D_J code 0).contains (⟨6798⟩ : UInt256) = true := by
    exact clipperJumpDest6798 v hpatch
  exact clipperBytes32ConstGetterBodyCore (v := v) (code := code) (cA := cA)
    (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (sel := clipperSelWord I) (transition := ilkTransition v)
    (entry := (⟨1349⟩ : UInt256)) (routine := (⟨6798⟩ : UInt256))
    (returnPc := (⟨476⟩ : UInt256))
    (val := EVM.Word.ofNat (fromBytesBigEndian ilkBs)) (width := 32) (op := .PUSH32)
    hcode (clipperDispatch_ilk v hsel) (clipperDecode_ilk v hsz) hreach hAccounts
    (clipperIlkGetterEntryWf v hpatch) (clipperIlkConstGetterWf v hpatch hilk hlen)
    hroutine
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨476⟩ : UInt256) (by decide +native))
    (clipperReturnWord476Wf v hpatch) (by rfl) hbody

end Benchmarks.Dss.Clipper
