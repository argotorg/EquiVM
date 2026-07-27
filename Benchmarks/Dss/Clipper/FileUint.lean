import Benchmarks.Dss.Clipper.FileUintSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperFileUintPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : 2621 ≤ lo) (hhi : hi ≤ 3128) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      try omega
  | some bs =>
      simp [hIlk]
      try omega

theorem clipperFileUintDecodeMid (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 2621 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 3128)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperFileUintPatchesWindowDisjoint32 v pc.toNat (pc.toNat + 1) hlo (by omega))
    (clipperFileUintPatchesWindowDisjoint32 v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega) hhi)
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      exact Nat.lt_of_le_of_lt (Nat.le_trans hle hhi) (by norm_num))
    (by exact Nat.lt_of_le_of_lt hhi (by norm_num))

macro "clipper_file_uint_decode" : tactic =>
  `(tactic| first
    | clipper_decode
    | exact clipperFileUintDecodeMid _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide))

theorem clipperFileUintJumpDest2703 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2703⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintJumpDest2780 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2780⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintJumpDest2809 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2809⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintJumpDest2834 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2834⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintJumpDest2859 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2859⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintJumpDest2908 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2908⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintJumpDest2960 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2960⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintJumpDest2988 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2988⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintJumpDest3065 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨3065⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 3200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileUintBufWord :
    UInt256.shiftLeft (⟨3226291⟩ : UInt256) ⟨233⟩ =
      ABI.bytesToWord clipperFileUintBufBytes := by
  native_decide

theorem clipperFileUintTailWord :
    UInt256.shiftLeft (⟨488135259⟩ : UInt256) ⟨226⟩ =
      ABI.bytesToWord clipperFileUintTailBytes := by
  native_decide

theorem clipperFileUintCuspWord :
    UInt256.shiftLeft (⟨104290103⟩ : UInt256) ⟨228⟩ =
      ABI.bytesToWord clipperFileUintCuspBytes := by
  native_decide

theorem clipperFileUintChipParamWord :
    UInt256.shiftLeft (⟨104236695⟩ : UInt256) ⟨228⟩ =
      ABI.bytesToWord clipperFileUintChipBytes := by
  native_decide

theorem clipperFileUintTipParamWord :
    UInt256.shiftLeft (⟨476823⟩ : UInt256) ⟨236⟩ =
      ABI.bytesToWord clipperFileUintTipBytes := by
  native_decide

theorem clipperFileUintStoppedParamWord :
    UInt256.shiftLeft (⟨8124411074582873⟩ : UInt256) ⟨202⟩ =
      ABI.bytesToWord clipperFileUintStoppedBytes := by
  native_decide

theorem clipperFileUintShift64Word :
    UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩ = clipperFileUintShift64 := by
  native_decide

theorem clipperFileUintUint192MaskWord :
    UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩ =
      clipperFileUintUint192Mask := by
  native_decide

theorem clipperFileUintHigh64Mask_eq_lnot64 :
    UInt256.lnot clipperFileUintUint64Mask = clipperFileUintHigh64Mask := by
  native_decide

theorem clipperFileUintAuthHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperRelyAuthHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 3) * ⟨32⟩ then ⟨0⟩
      else
        UInt256.ofNat (fromByteArrayBigEndian
          ((clipperRelyAuthHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperRelyAuthHashMem_size]; decide)
    (by decide)
    (clipperRelyAuthHashMem_read64 I)

noncomputable abbrev clipperFileUintEventMem (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem (clipperRelyAuthHashMem I) (clipperFileUintData I)

theorem clipperFileUintEventMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperFileUintEventMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else
        UInt256.ofNat (fromByteArrayBigEndian
          ((clipperFileUintEventMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 (clipperFileUintData I)
    (clipperRelyAuthHashMem_size I) (clipperRelyAuthHashMem_read64 I)

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (h : RD code I g s0 ⟨2621⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2703⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd2626pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw caller (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2627 := rd2626pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2631pre := evm_run rd2627 with [
    raw push1 ⟨32⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2632 := rd2631pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2635pre := evm_run rd2632 with [
    raw push1 ⟨64⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2636 := rd2635pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2638, C2638, rd2638raw⟩ := rd2636.sload (by clipper_file_uint_decode) (by evm_ov)
  have rd2638 : RD code I g s0 ⟨2638⟩
      (clipperRelyAuthWord σ I :: clipperFileUintData I :: calldataWord I.calldata 4 ::
        ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2638 C2638 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd2638raw
  have rd2640pre := evm_run rd2638 with [
    raw push1 ⟨1⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw eq (by clipper_file_uint_decode) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd2640pre
  have rd2644 := rd2640pre.pushConst (⟨2703⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2644.jumpiT (by clipper_file_uint_decode) one_ne_zero_uint
    (clipperFileUintJumpDest2703 v hpatch) (by evm_ov)⟩

theorem clipperFileUintX_lockOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (h : RD code I g s0 ⟨2703⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2780⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2706pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨k2707, C2707, rd2707raw⟩ := rd2706pre.sload
    (by clipper_file_uint_decode) (by evm_ov)
  have rd2707 : RD code I g s0 ⟨2707⟩
      (solcSlotWord σ I ⟨13⟩ :: clipperFileUintData I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2707 C2707 := by
    simpa [solcSlotWord] using rd2707raw
  have rd2708 := rd2707.iszero (by clipper_file_uint_decode) (by evm_ov)
  have hcond : UInt256.isZero (solcSlotWord σ I ⟨13⟩) ≠ ⟨0⟩ := by
    rw [hlocked]
    native_decide
  have rd2711 := rd2708.pushConst (⟨2780⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2711.jumpiT (by clipper_file_uint_decode) hcond
    (clipperFileUintJumpDest2780 v hpatch) (by evm_ov)⟩

theorem clipperFileUintX_lockStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨2780⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2786⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) k' C' := by
  have rd2785pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨_, _, rd2786raw⟩ := rd2785pre.sstore hperm (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd2786raw⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_bufStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintBufBytes)
    (h : RD code I g s0 ⟨2786⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3065⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩ (clipperFileUintData I)) k' C' := by
  have rd2790 := h.pushConst (⟨3226291⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2793pre := evm_run rd2790 with [
    raw push1 ⟨233⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintBufWord, ← hwhat] at rd2793pre
  have rd2799pre := evm_run rd2793pre with [
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd2799pre
  have rd2799 := rd2799pre.pushConst (⟨2809⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2800 := rd2799.jumpiNT (by clipper_file_uint_decode) (by native_decide) (by evm_ov)
  have rd2804pre := evm_run rd2800 with [
    raw push1 ⟨5⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨_, _, rd2805raw⟩ := rd2804pre.sstore hperm (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2808 := rd2805raw.pushConst (⟨3065⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2808.jump (by clipper_file_uint_decode)
    (clipperFileUintJumpDest3065 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_bufSkip {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotBuf : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintBufBytes)
    (h : RD code I g s0 ⟨2786⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2809⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2790 := h.pushConst (⟨3226291⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2793pre := evm_run rd2790 with [
    raw push1 ⟨233⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintBufWord] at rd2793pre
  have rd2799pre := evm_run rd2793pre with [
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  have hbufEq :
      UInt256.eq (calldataWord I.calldata 4) (ABI.bytesToWord clipperFileUintBufBytes) =
        ⟨0⟩ := by
    exact u256_eq_of_ne hnotBuf
  rw [hbufEq] at rd2799pre
  have rd2799 := rd2799pre.pushConst (⟨2809⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2799.jumpiT (by clipper_file_uint_decode) (by native_decide)
    (clipperFileUintJumpDest2809 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_tailStoreFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintTailBytes)
    (h : RD code I g s0 ⟨2809⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3065⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩ (clipperFileUintData I)) k' C' := by
  have rd2819pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2816 := rd2819pre.pushConst (⟨488135259⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2818pre := evm_run rd2816 with [
    raw push1 ⟨226⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintTailWord, ← hwhat] at rd2818pre
  have rd2820pre := evm_run rd2818pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd2820pre
  have rd2824 := rd2820pre.pushConst (⟨2834⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2825 := rd2824.jumpiNT (by clipper_file_uint_decode) (by native_decide) (by evm_ov)
  have rd2829pre := evm_run rd2825 with [
    raw push1 ⟨6⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨_, _, rd2830raw⟩ := rd2829pre.sstore hperm (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2833 := rd2830raw.pushConst (⟨3065⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2833.jump (by clipper_file_uint_decode)
    (clipperFileUintJumpDest3065 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_tailSkipFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotTail : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTailBytes)
    (h : RD code I g s0 ⟨2809⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2834⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2819pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2816 := rd2819pre.pushConst (⟨488135259⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2818pre := evm_run rd2816 with [
    raw push1 ⟨226⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintTailWord] at rd2818pre
  have rd2820pre := evm_run rd2818pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  have htailEq :
      UInt256.eq (ABI.bytesToWord clipperFileUintTailBytes) (calldataWord I.calldata 4) =
        ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hnotTail hbad.symm)
  rw [htailEq] at rd2820pre
  have rd2824 := rd2820pre.pushConst (⟨2834⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2824.jumpiT (by clipper_file_uint_decode) (by native_decide)
    (clipperFileUintJumpDest2834 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_cuspStoreFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintCuspBytes)
    (h : RD code I g s0 ⟨2834⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3065⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨7⟩ (clipperFileUintData I)) k' C' := by
  have rd2844pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2841 := rd2844pre.pushConst (⟨104290103⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2843pre := evm_run rd2841 with [
    raw push1 ⟨228⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintCuspWord, ← hwhat] at rd2843pre
  have rd2845pre := evm_run rd2843pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd2845pre
  have rd2849 := rd2845pre.pushConst (⟨2859⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2850 := rd2849.jumpiNT (by clipper_file_uint_decode) (by native_decide) (by evm_ov)
  have rd2854pre := evm_run rd2850 with [
    raw push1 ⟨7⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨_, _, rd2855raw⟩ := rd2854pre.sstore hperm (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2858 := rd2855raw.pushConst (⟨3065⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2858.jump (by clipper_file_uint_decode)
    (clipperFileUintJumpDest3065 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_cuspSkipFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotCusp : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintCuspBytes)
    (h : RD code I g s0 ⟨2834⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2859⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2844pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2841 := rd2844pre.pushConst (⟨104290103⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2843pre := evm_run rd2841 with [
    raw push1 ⟨228⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintCuspWord] at rd2843pre
  have rd2845pre := evm_run rd2843pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  have hcuspEq :
      UInt256.eq (ABI.bytesToWord clipperFileUintCuspBytes) (calldataWord I.calldata 4) =
        ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hnotCusp hbad.symm)
  rw [hcuspEq] at rd2845pre
  have rd2849 := rd2845pre.pushConst (⟨2859⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2849.jumpiT (by clipper_file_uint_decode) (by native_decide)
    (clipperFileUintJumpDest2859 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_chipStoreFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintChipBytes)
    (h : RD code I g s0 ⟨2859⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3065⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨8⟩
        (clipperFileUintChipWord (solcSlotWord σ I ⟨8⟩) (clipperFileUintData I)))
      k' C' := by
  have rd2869pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2866 := rd2869pre.pushConst (⟨104236695⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2868pre := evm_run rd2866 with [
    raw push1 ⟨228⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintChipParamWord, ← hwhat] at rd2868pre
  have rd2870pre := evm_run rd2868pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd2870pre
  have rd2874 := rd2870pre.pushConst (⟨2908⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2875 := rd2874.jumpiNT (by clipper_file_uint_decode) (by native_decide) (by evm_ov)
  have rd2878pre := evm_run rd2875 with [
    raw push1 ⟨8⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup1 (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨k2879, C2879, rd2879raw⟩ := rd2878pre.sload
    (by clipper_file_uint_decode) (by evm_ov)
  have rd2879 : RD code I g s0 ⟨2879⟩
      (solcSlotWord σ I ⟨8⟩ :: ⟨8⟩ :: clipperFileUintData I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k2879 C2879 := by
    simpa [solcSlotWord] using rd2879raw
  have rd2888 := rd2879.pushConst clipperFileUintUint64Mask
    (width := 8) (op := .PUSH8) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2889 := rd2888.not (by clipper_file_uint_decode) (by evm_ov)
  rw [clipperFileUintHigh64Mask_eq_lnot64] at rd2889
  have rd2890 := rd2889.and (by clipper_file_uint_decode) (by evm_ov)
  have rd2899 := rd2890.pushConst clipperFileUintUint64Mask
    (width := 8) (op := .PUSH8) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2900 := rd2899.dup4 (by clipper_file_uint_decode) (by evm_ov)
  have rd2901 := rd2900.and (by clipper_file_uint_decode) (by evm_ov)
  have rd2902 := rd2901.lor (by clipper_file_uint_decode) (by evm_ov)
  rw [u256_lor_comm] at rd2902
  have rd2903 := rd2902.swap1 (by clipper_file_uint_decode) (by evm_ov)
  obtain ⟨_, _, rd2904raw⟩ := rd2903.sstore hperm (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2907 := rd2904raw.pushConst (⟨3065⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [clipperFileUintChipWord] using
      rd2907.jump (by clipper_file_uint_decode) (clipperFileUintJumpDest3065 v hpatch)
        (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_chipSkipFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotChip : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintChipBytes)
    (h : RD code I g s0 ⟨2859⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2908⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2869pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2866 := rd2869pre.pushConst (⟨104236695⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2868pre := evm_run rd2866 with [
    raw push1 ⟨228⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintChipParamWord] at rd2868pre
  have rd2870pre := evm_run rd2868pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  have hchipEq :
      UInt256.eq (ABI.bytesToWord clipperFileUintChipBytes) (calldataWord I.calldata 4) =
        ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hnotChip hbad.symm)
  rw [hchipEq] at rd2870pre
  have rd2874 := rd2870pre.pushConst (⟨2908⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2874.jumpiT (by clipper_file_uint_decode) (by native_decide)
    (clipperFileUintJumpDest2908 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_tipStoreFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintTipBytes)
    (h : RD code I g s0 ⟨2908⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3065⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨8⟩
        (clipperFileUintTipWord (solcSlotWord σ I ⟨8⟩) (clipperFileUintData I)))
      k' C' := by
  have rd2917pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2914 := rd2917pre.pushConst (⟨476823⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2916pre := evm_run rd2914 with [
    raw push1 ⟨236⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintTipParamWord, ← hwhat] at rd2916pre
  have rd2918pre := evm_run rd2916pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd2918pre
  have rd2922 := rd2918pre.pushConst (⟨2960⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2923 := rd2922.jumpiNT (by clipper_file_uint_decode) (by native_decide) (by evm_ov)
  have rd2926pre := evm_run rd2923 with [
    raw push1 ⟨8⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup1 (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨k2927, C2927, rd2927raw⟩ := rd2926pre.sload
    (by clipper_file_uint_decode) (by evm_ov)
  have rd2927 : RD code I g s0 ⟨2927⟩
      (solcSlotWord σ I ⟨8⟩ :: ⟨8⟩ :: clipperFileUintData I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k2927 C2927 := by
    simpa [solcSlotWord] using rd2927raw
  have rd2936 := rd2927.pushConst clipperFileUintUint64Mask
    (width := 8) (op := .PUSH8) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2937 := rd2936.and (by clipper_file_uint_decode) (by evm_ov)
  rw [u256_land_comm clipperFileUintUint64Mask (solcSlotWord σ I ⟨8⟩)] at rd2937
  have rd2941pre := evm_run rd2937 with [
    raw push1 ⟨1⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintShift64Word] at rd2941pre
  have rd2949pre := evm_run rd2941pre with [
    raw push1 ⟨1⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨192⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov),
    raw sub (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintUint192MaskWord] at rd2949pre
  have rd2950 := rd2949pre.dup5 (by clipper_file_uint_decode) (by evm_ov)
  have rd2951 := rd2950.and (by clipper_file_uint_decode) (by evm_ov)
  have rd2952 := rd2951.mul (by clipper_file_uint_decode) (by evm_ov)
  have rd2953 := rd2952.lor (by clipper_file_uint_decode) (by evm_ov)
  rw [u256_lor_comm] at rd2953
  have rd2954 := rd2953.swap1 (by clipper_file_uint_decode) (by evm_ov)
  obtain ⟨_, _, rd2956raw⟩ := rd2954.sstore hperm (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2959 := rd2956raw.pushConst (⟨3065⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [clipperFileUintTipWord] using
      rd2959.jump (by clipper_file_uint_decode) (clipperFileUintJumpDest3065 v hpatch)
        (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_tipSkipFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotTip : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTipBytes)
    (h : RD code I g s0 ⟨2908⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2960⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2917pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2914 := rd2917pre.pushConst (⟨476823⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2916pre := evm_run rd2914 with [
    raw push1 ⟨236⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintTipParamWord] at rd2916pre
  have rd2918pre := evm_run rd2916pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  have htipEq :
      UInt256.eq (ABI.bytesToWord clipperFileUintTipBytes) (calldataWord I.calldata 4) =
        ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hnotTip hbad.symm)
  rw [htipEq] at rd2918pre
  have rd2922 := rd2918pre.pushConst (⟨2960⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2922.jumpiT (by clipper_file_uint_decode) (by native_decide)
    (clipperFileUintJumpDest2960 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_stoppedStoreFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintStoppedBytes)
    (h : RD code I g s0 ⟨2960⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3065⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨14⟩ (clipperFileUintData I)) k' C' := by
  have rd2973pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2970 := rd2973pre.pushConst (⟨8124411074582873⟩ : UInt256)
    (width := 7) (op := .PUSH7) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2972pre := evm_run rd2970 with [
    raw push1 ⟨202⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintStoppedParamWord, ← hwhat] at rd2972pre
  have rd2974pre := evm_run rd2972pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd2974pre
  have rd2978 := rd2974pre.pushConst (⟨2988⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2979 := rd2978.jumpiNT (by clipper_file_uint_decode) (by native_decide) (by evm_ov)
  have rd2983pre := evm_run rd2979 with [
    raw push1 ⟨14⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨_, _, rd2984raw⟩ := rd2983pre.sstore hperm (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2987 := rd2984raw.pushConst (⟨3065⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2987.jump (by clipper_file_uint_decode)
    (clipperFileUintJumpDest3065 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_stoppedSkipFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotStopped : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintStoppedBytes)
    (h : RD code I g s0 ⟨2960⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2988⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd2973pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2970 := rd2973pre.pushConst (⟨8124411074582873⟩ : UInt256)
    (width := 7) (op := .PUSH7) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2972pre := evm_run rd2970 with [
    raw push1 ⟨202⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperFileUintStoppedParamWord] at rd2972pre
  have rd2974pre := evm_run rd2972pre with [
    raw eq (by clipper_file_uint_decode) (by evm_ov),
    raw iszero (by clipper_file_uint_decode) (by evm_ov)]
  have hstoppedEq :
      UInt256.eq (ABI.bytesToWord clipperFileUintStoppedBytes) (calldataWord I.calldata 4) =
        ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hnotStopped hbad.symm)
  rw [hstoppedEq] at rd2974pre
  have rd2978 := rd2974pre.pushConst (⟨2988⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  exact ⟨_, _, rd2978.jumpiT (by clipper_file_uint_decode) (by native_decide)
    (clipperFileUintJumpDest2988 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_successEpilogue {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨3065⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g s0 (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨0⟩) ByteArray.empty := by
  have rd3069 := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup1 (by clipper_file_uint_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost
      (clipperFileUintAuthHashMem_mload64 I) (by native_decide) (by evm_ov)]
  have rd3071pre := evm_run rd3069 with [
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd3072 := rd3071pre.mstore 6 (clipperFileUintEventMem I) (UInt256.ofNat 5)
    (by clipper_file_uint_decode)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := UInt256.ofNat 3) (off := (⟨128⟩ : UInt256))
        (val := clipperFileUintData I)
        (t := (⟨128⟩ : UInt256) :: (⟨64⟩ : UInt256) :: clipperFileUintData I ::
          calldataWord I.calldata 4 :: (⟨502⟩ : UInt256) :: [sel])
        haw hstk (by native_decide))
    (by rfl)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3074 := evm_run rd3072 with [
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by clipper_file_uint_decode) mem_cost
      (clipperFileUintEventMem_mload64 I) (by native_decide) (by evm_ov)]
  have rd3076 := evm_run rd3074 with [
    raw dup4 (by clipper_file_uint_decode) (by evm_ov),
    raw swap2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd3110 := rd3076.pushConst
    (⟨105627225169409785158710363763375725481095598661489361122320324215644262229191⟩ :
      UInt256)
    (op := .PUSH32) (width := 32) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd3119pre := evm_run rd3110 with [
    raw swap2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw sub (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  have rd3120 := RD.log2 0 (UInt256.ofNat 5) rd3119pre
    (by clipper_file_uint_decode) hperm mem_cost (by native_decide) (by evm_ov)
  have rd3126pre := evm_run rd3120 with [
    raw pop (by clipper_file_uint_decode) (by evm_ov),
    raw pop (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨_, _, rd3127raw⟩ := rd3126pre.sstore hperm (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd502 := rd3127raw.jump (by clipper_file_uint_decode) (clipperRelyReturnJumpDest v hpatch)
    (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_decode) (by evm_ov)
  exact RD.stop rd503 (by clipper_decode) (by evm_ov)

theorem clipperFileUintX_bufOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintBufBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2621⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨5⟩ (clipperFileUintData I))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd2621⟩ := hreach
  obtain ⟨_, _, rd2703⟩ := clipperFileUintX_authorized (v := v) hpatch hauth rd2621
  obtain ⟨_, _, rd2780⟩ := clipperFileUintX_lockOpen (v := v) hpatch hlocked rd2703
  obtain ⟨_, _, rd2786⟩ := clipperFileUintX_lockStore (v := v) hpatch hperm rd2780
  obtain ⟨_, _, rd3065⟩ := clipperFileUintX_bufStore (v := v) hpatch hperm hwhat rd2786
  exact clipperFileUintX_successEpilogue (v := v) hpatch hperm rd3065

theorem clipperFileUintX_tailOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintBufBytes)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintTailBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2621⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨6⟩ (clipperFileUintData I))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd2621⟩ := hreach
  obtain ⟨_, _, rd2703⟩ := clipperFileUintX_authorized (v := v) hpatch hauth rd2621
  obtain ⟨_, _, rd2780⟩ := clipperFileUintX_lockOpen (v := v) hpatch hlocked rd2703
  obtain ⟨_, _, rd2786⟩ := clipperFileUintX_lockStore (v := v) hpatch hperm rd2780
  obtain ⟨_, _, rd2809⟩ := clipperFileUintX_bufSkip (v := v) hpatch hnotBuf rd2786
  obtain ⟨_, _, rd3065⟩ := clipperFileUintX_tailStoreFrom (v := v) hpatch hperm hwhat rd2809
  exact clipperFileUintX_successEpilogue (v := v) hpatch hperm rd3065

theorem clipperFileUintX_cuspOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintBufBytes)
    (hnotTail : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTailBytes)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintCuspBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2621⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨7⟩ (clipperFileUintData I))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd2621⟩ := hreach
  obtain ⟨_, _, rd2703⟩ := clipperFileUintX_authorized (v := v) hpatch hauth rd2621
  obtain ⟨_, _, rd2780⟩ := clipperFileUintX_lockOpen (v := v) hpatch hlocked rd2703
  obtain ⟨_, _, rd2786⟩ := clipperFileUintX_lockStore (v := v) hpatch hperm rd2780
  obtain ⟨_, _, rd2809⟩ := clipperFileUintX_bufSkip (v := v) hpatch hnotBuf rd2786
  obtain ⟨_, _, rd2834⟩ := clipperFileUintX_tailSkipFrom (v := v) hpatch hnotTail rd2809
  obtain ⟨_, _, rd3065⟩ := clipperFileUintX_cuspStoreFrom (v := v) hpatch hperm hwhat rd2834
  exact clipperFileUintX_successEpilogue (v := v) hpatch hperm rd3065

theorem clipperFileUintX_chipOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintBufBytes)
    (hnotTail : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTailBytes)
    (hnotCusp : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintCuspBytes)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintChipBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2621⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨8⟩
            (clipperFileUintChipWord
              (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨8⟩)
              (clipperFileUintData I)))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd2621⟩ := hreach
  obtain ⟨_, _, rd2703⟩ := clipperFileUintX_authorized (v := v) hpatch hauth rd2621
  obtain ⟨_, _, rd2780⟩ := clipperFileUintX_lockOpen (v := v) hpatch hlocked rd2703
  obtain ⟨_, _, rd2786⟩ := clipperFileUintX_lockStore (v := v) hpatch hperm rd2780
  obtain ⟨_, _, rd2809⟩ := clipperFileUintX_bufSkip (v := v) hpatch hnotBuf rd2786
  obtain ⟨_, _, rd2834⟩ := clipperFileUintX_tailSkipFrom (v := v) hpatch hnotTail rd2809
  obtain ⟨_, _, rd2859⟩ := clipperFileUintX_cuspSkipFrom (v := v) hpatch hnotCusp rd2834
  obtain ⟨_, _, rd3065⟩ := clipperFileUintX_chipStoreFrom (v := v) hpatch hperm hwhat rd2859
  exact clipperFileUintX_successEpilogue (v := v) hpatch hperm rd3065

theorem clipperFileUintX_tipOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintBufBytes)
    (hnotTail : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTailBytes)
    (hnotCusp : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintCuspBytes)
    (hnotChip : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintChipBytes)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintTipBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2621⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨8⟩
            (clipperFileUintTipWord
              (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨8⟩)
              (clipperFileUintData I)))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd2621⟩ := hreach
  obtain ⟨_, _, rd2703⟩ := clipperFileUintX_authorized (v := v) hpatch hauth rd2621
  obtain ⟨_, _, rd2780⟩ := clipperFileUintX_lockOpen (v := v) hpatch hlocked rd2703
  obtain ⟨_, _, rd2786⟩ := clipperFileUintX_lockStore (v := v) hpatch hperm rd2780
  obtain ⟨_, _, rd2809⟩ := clipperFileUintX_bufSkip (v := v) hpatch hnotBuf rd2786
  obtain ⟨_, _, rd2834⟩ := clipperFileUintX_tailSkipFrom (v := v) hpatch hnotTail rd2809
  obtain ⟨_, _, rd2859⟩ := clipperFileUintX_cuspSkipFrom (v := v) hpatch hnotCusp rd2834
  obtain ⟨_, _, rd2908⟩ := clipperFileUintX_chipSkipFrom (v := v) hpatch hnotChip rd2859
  obtain ⟨_, _, rd3065⟩ := clipperFileUintX_tipStoreFrom (v := v) hpatch hperm hwhat rd2908
  exact clipperFileUintX_successEpilogue (v := v) hpatch hperm rd3065

theorem clipperFileUintX_stoppedOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotBuf : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintBufBytes)
    (hnotTail : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTailBytes)
    (hnotCusp : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintCuspBytes)
    (hnotChip : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintChipBytes)
    (hnotTip : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTipBytes)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintStoppedBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2621⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨14⟩ (clipperFileUintData I))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd2621⟩ := hreach
  obtain ⟨_, _, rd2703⟩ := clipperFileUintX_authorized (v := v) hpatch hauth rd2621
  obtain ⟨_, _, rd2780⟩ := clipperFileUintX_lockOpen (v := v) hpatch hlocked rd2703
  obtain ⟨_, _, rd2786⟩ := clipperFileUintX_lockStore (v := v) hpatch hperm rd2780
  obtain ⟨_, _, rd2809⟩ := clipperFileUintX_bufSkip (v := v) hpatch hnotBuf rd2786
  obtain ⟨_, _, rd2834⟩ := clipperFileUintX_tailSkipFrom (v := v) hpatch hnotTail rd2809
  obtain ⟨_, _, rd2859⟩ := clipperFileUintX_cuspSkipFrom (v := v) hpatch hnotCusp rd2834
  obtain ⟨_, _, rd2908⟩ := clipperFileUintX_chipSkipFrom (v := v) hpatch hnotChip rd2859
  obtain ⟨_, _, rd2960⟩ := clipperFileUintX_tipSkipFrom (v := v) hpatch hnotTip rd2908
  obtain ⟨_, _, rd3065⟩ := clipperFileUintX_stoppedStoreFrom (v := v) hpatch hperm hwhat rd2960
  exact clipperFileUintX_successEpilogue (v := v) hpatch hperm rd3065

theorem clipperFileUintWordPostState_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {slot data : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) slot data)
        ⟨13⟩ ⟨0⟩)
      (clipperFileUintWordPostState
        (initState cA gh bl σ_solm σ₀ g A I) slot data).accountMap := by
  simpa [clipperFileUintWordPostState, clipperFileUintLockedState, initState,
    storageStore_accountMap, storageStore_executionEnv] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨0⟩
      (accountMapEquiv_sstoreAccountMap I.codeOwner slot data
        (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccounts))

theorem clipperFileUintChipPostState_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {data : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨8⟩
            (clipperFileUintChipWord
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩)
              data))
        ⟨13⟩ ⟨0⟩)
      (clipperFileUintChipPostState (initState cA gh bl σ_solm σ₀ g A I) data).accountMap := by
  have hlockAccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
        (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccounts
  have hslot8 :
      solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩ =
        solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨8⟩ :=
    accountMapEquiv_storage_findD hlockAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hstore8 :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨8⟩
            (clipperFileUintChipWord
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩)
              data))
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) ⟨8⟩
            (clipperFileUintChipWord
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩)
              data)) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩
      (clipperFileUintChipWord
        (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩)
        data)
      hlockAccounts
  have hfinal := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨0⟩ hstore8
  simpa [clipperFileUintChipPostState, clipperFileUintLockedState, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, hslot8] using hfinal

theorem clipperFileUintTipPostState_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {data : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨8⟩
            (clipperFileUintTipWord
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩)
              data))
        ⟨13⟩ ⟨0⟩)
      (clipperFileUintTipPostState (initState cA gh bl σ_solm σ₀ g A I) data).accountMap := by
  have hlockAccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
        (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccounts
  have hslot8 :
      solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩ =
        solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I ⟨8⟩ :=
    accountMapEquiv_storage_findD hlockAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hstore8 :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨8⟩
            (clipperFileUintTipWord
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩)
              data))
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) ⟨8⟩
            (clipperFileUintTipWord
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩)
              data)) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩
      (clipperFileUintTipWord
        (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨8⟩)
        data)
      hlockAccounts
  have hfinal := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨0⟩ hstore8
  simpa [clipperFileUintTipPostState, clipperFileUintLockedState, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, hslot8] using hfinal

theorem clipperFileUintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨673⟩ : UInt256) [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := (⟨673⟩ : UInt256))
    (ret := (⟨502⟩ : UInt256)) (decoded := (⟨695⟩ : UInt256))
    (need := (⟨64⟩ : UInt256)) hreach
    (by change decode code (⟨673⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
    (by
      change decode code (⟨674⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨502⟩, 2))
      clipper_decode)
    (by
      change decode code (⟨677⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by change decode code (⟨679⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨680⟩ : UInt256) = some (.CALLDATASIZE, .none); clipper_decode)
    (by change decode code (⟨681⟩ : UInt256) = some (.SUB, .none); clipper_decode)
    (by
      change decode code (⟨682⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨64⟩, 1))
      clipper_decode)
    (by change decode code (⟨684⟩ : UInt256) = some (.DUP2, .none); clipper_decode)
    (by change decode code (⟨685⟩ : UInt256) = some (.LT, .none); clipper_decode)
    (by change decode code (⟨686⟩ : UInt256) = some (.ISZERO, .none); clipper_decode)
    (by
      change decode code (⟨687⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨695⟩, 2))
      clipper_decode)
    (by change decode code (⟨690⟩ : UInt256) = some (.JUMPI, .none); clipper_decode)
    (by
      change decode code (⟨691⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨0⟩, 1))
      clipper_decode)
    (by change decode code (⟨693⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨694⟩ : UInt256) = some (.REVERT, .none); clipper_decode)
    hlt

theorem clipperFileUintLockRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code (⟨2712⟩ : UInt256) ⟨21⟩
      ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ .PUSH21 21 := by
  unfold solcErrorStringRevertTailWf
  dsimp
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> (norm_num1; clipper_file_uint_decode)

theorem clipperFileUintLockedStringWord :
    UInt256.shiftLeft ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ =
      ⟨30496508052792062404420069455133111715513420844312188351800969105462834233344⟩ := by
  native_decide

theorem clipperFileUintUnrecognizedStringWord :
    UInt256.shiftLeft
        ⟨30496508052792062404099775245839162874297393920482488000238941594219156958464⟩
        ⟨0⟩ =
      ⟨0x436c69707065722f66696c652d756e7265636f676e697a65642d706172616d00⟩ := by
  native_decide

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_locked {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨2703⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd2706pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_file_uint_decode) (by evm_ov)]
  obtain ⟨k2707, C2707, rd2707raw⟩ := rd2706pre.sload
    (by clipper_file_uint_decode) (by evm_ov)
  have rd2707 : RD code I g s0 ⟨2707⟩
      (solcSlotWord σ I ⟨13⟩ :: clipperFileUintData I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2707 C2707 := by
    simpa [solcSlotWord] using rd2707raw
  have rd2708pre := rd2707.iszero (by clipper_file_uint_decode) (by evm_ov)
  rw [isZero_eq_zero_of_ne hlocked] at rd2708pre
  have rd2711 := rd2708pre.pushConst (⟨2780⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2712 := rd2711.jumpiNT (by clipper_file_uint_decode)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail rd2712
    (clipperFileUintLockRevertTailWf v hpatch)
    (by decide)
    clipperFileUintLockedStringWord
    (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD code I g s0 ⟨2621⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd2626pre := evm_run h with [
    raw jumpdest (by clipper_file_uint_decode) (by evm_ov),
    raw caller (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2627 := rd2626pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2631pre := evm_run rd2627 with [
    raw push1 ⟨32⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2632 := rd2631pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2635pre := evm_run rd2632 with [
    raw push1 ⟨64⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2636 := rd2635pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k2638, C2638, rd2638raw⟩ := rd2636.sload
    (by clipper_file_uint_decode) (by evm_ov)
  have rd2638 : RD code I g s0 ⟨2638⟩
      (clipperRelyAuthWord σ I :: clipperFileUintData I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k2638 C2638 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd2638raw
  have rd2640pre := evm_run rd2638 with [
    raw push1 ⟨1⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw eq (by clipper_file_uint_decode) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (clipperRelyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd2640pre
  have rd2644 := rd2640pre.pushConst (⟨2703⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2645 := rd2644.jumpiNT (by clipper_file_uint_decode) rfl (by evm_ov)
  have rd2648 := evm_run rd2645 with [
    raw push1 ⟨64⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup1 (by clipper_file_uint_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost
      (mloadFreePtrValue (by rw [clipperRelyAuthHashMem_size]; decide)
        (by decide) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rd2652 := rd2648.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2655 := evm_run rd2652 with [
    raw push1 ⟨229⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov)]
  rw [clipperRelyNotAuthorizedWord] at rd2655
  have rd2657pre := evm_run rd2655 with [
    raw dup2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2657 := rd2657pre.mstore 6
    (solcErrorStringMem0 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 5) (by clipper_file_uint_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2669pre := evm_run rd2657 with [
    raw push1 ⟨32⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov)]
  have rd2670 := rd2669pre.mstore 3
    (solcErrorStringMem1 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 6) (by clipper_file_uint_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd2681pre := evm_run rd2670 with [
    raw push1 ⟨22⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov),
    raw mstore 3 (clipperRelyErrorMem2 I)
      (UInt256.ofNat 7) (by clipper_file_uint_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup1 (by clipper_file_uint_decode) (by evm_ov),
    raw mload 0 (clipperRelySourceWord I) (UInt256.ofNat 7)
      (by clipper_file_uint_decode) mem_cost (clipperRelyErrorMem2_mload0 I)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_file_uint_decode) (by evm_ov)]
  have rd2680 := rd2681pre.pushConst (⟨9316⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_uint_decode) (by evm_ov)
  have rd2681pre2 := evm_run rd2680 with [
    raw dup4 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2682 := rd2681pre2.codecopy 0 (clipperRelyErrorCopiedMem code I)
    (UInt256.ofNat 7) (by clipper_file_uint_decode) mem_cost
    (by
      rw [show (⟨9316⟩ : UInt256).toNat = 9316 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rd2684 := evm_run rd2682 with [
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw mload 0 clipperRelyNotAuthorizedStringWord (UInt256.ofNat 7)
      (by clipper_file_uint_decode) mem_cost
      (by simpa [clipperRelyErrorCopiedMem, clipperRelyErrorMem2]
        using clipperRelyCodecopyMload0 v hpatch I)
      (by native_decide) (by evm_ov),
    raw swap2 (by clipper_file_uint_decode) (by evm_ov)]
  have rd2685 := rd2684.mstore 0 (clipperRelyErrorRestoredMem code I)
    (UInt256.ofNat 7) (by clipper_file_uint_decode) mem_cost
    (by simp [clipperRelyErrorRestoredMem, clipperRelyErrorCopiedMem])
    (by native_decide) (by evm_ov)
  have rd2689pre := evm_run rd2685 with [
    raw push1 ⟨68⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov)]
  have rd2690 := rd2689pre.mstore 3 (clipperRelyErrorStringMem code I)
    (UInt256.ofNat 8) (by clipper_file_uint_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 from by decide])
    (by native_decide) (by evm_ov)
  have rd2692 := evm_run rd2690 with [
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_file_uint_decode) mem_cost
      (clipperRelyErrorStringMem_mload64 v hpatch I)
      (by native_decide) (by evm_ov)]
  exact evm_run rd2692 with [
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw sub (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw rev 0 (by clipper_file_uint_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem clipperFileUintX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2988⟩
      [clipperFileUintData I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd2989 := h.jumpdest
    (by change decode code (⟨2988⟩ : UInt256) = some (.JUMPDEST, .none); clipper_file_uint_decode)
    (by simp)
  have rdMload := evm_run rd2989 with [
    raw push1 ⟨64⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup1 (by clipper_file_uint_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_file_uint_decode) mem_cost
      (mloadFreePtrValue (by rw [clipperRelyAuthHashMem_size]; decide)
        (by decide) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw shl (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (clipperRelyAuthHashMem I)) (UInt256.ofNat 5)
      (by clipper_file_uint_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (clipperRelyAuthHashMem I)) (UInt256.ofNat 6)
      (by clipper_file_uint_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨31⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨31⟩ : UInt256) (clipperRelyAuthHashMem I))
      (UInt256.ofNat 7) (by clipper_file_uint_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst
    (⟨30496508052792062404099775245839162874297393920482488000238941594219156958464⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by clipper_file_uint_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw dup3 (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨31⟩ : UInt256)
        ⟨30496508052792062404099775245839162874297393920482488000238941594219156958464⟩
        (clipperRelyAuthHashMem I))
      (UInt256.ofNat 8) (by clipper_file_uint_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_file_uint_decode) mem_cost
      (solcErrorStringMem3_mload64 (⟨31⟩ : UInt256)
        ⟨30496508052792062404099775245839162874297393920482488000238941594219156958464⟩
        (clipperRelyAuthHashMem_size I) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw dup2 (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw sub (by clipper_file_uint_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_file_uint_decode) (by evm_ov),
    raw add (by clipper_file_uint_decode) (by evm_ov),
    raw swap1 (by clipper_file_uint_decode) (by evm_ov),
    raw rev 0 (by clipper_file_uint_decode) mem_cost (by evm_ov)]

theorem clipperFileUintBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 9) (by native_decide) hsel
  have hdispatch := clipperDispatch_fileUint v hsel
  have hreachEntry :=
    clipperReachFileUintBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) v hpatch hcode hwv
      hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := clipperDecode_fileUint_ok v (I := I) hsz68
    have hreachBody :=
      clipperFileUintDecodedToBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) v hpatch hsz68
        hsize hreachEntry
    let data := clipperFileUintData I
    let locals := clipperFileUintLocals I
    have henc : returnEquiv ByteArray.empty none fileUintTransition.returnType := by
      rw [show fileUintTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
    have hauthWord : clipperRelyAuthWord σ_evm I = clipperRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (clipperRelyAuthStorageSlot I) ⟨0⟩
    have hlockWord : solcSlotWord σ_evm I ⟨13⟩ = solcSlotWord σ_solm I ⟨13⟩ :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨13⟩ ⟨0⟩
    by_cases hauthEvm : clipperRelyAuthWord σ_evm I = ⟨1⟩
    · have hauthSolm : clipperRelyAuthWord σ_solm I = ⟨1⟩ := by
        rw [← hauthWord]
        exact hauthEvm
      by_cases hlockedEvm : solcSlotWord σ_evm I ⟨13⟩ = ⟨0⟩
      · have hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ = ⟨0⟩ := by
          rw [← hlockWord]
          exact hlockedEvm
        by_cases hbuf : clipperFileUintWhat I = clipperFileUintBufBytes
        · have hbufWord :
              calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintBufBytes := by
            rw [← clipperFileUintWhatWord_eq (I := I) (by omega), hbuf]
          let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evm2 := clipperFileUintWordPostState evmSolm ⟨5⟩ data
          have hbody :
              ExecTransitionBody (config v) (contract v) evmSolm locals
                fileUintTransition.body
                (.returned { contract := contract v, locals := locals } evm2 none) := by
            simpa [evmSolm, evm2, locals, data] using
              (clipperFileUintBufSourceBody (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                hauthSolm hlockedSolm hbuf)
          have hret := clipperFileUintX_bufOk (v := v) hpatch hperm hauthEvm
            hlockedEvm hbufWord hreachBody
          have hcreated :
              (cA, sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨5⟩ data)
                    ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
            simp [evm2, evmSolm, data, clipperFileUintWordPostState,
              clipperFileUintLockedState, initState, storageStore_createdAccounts]
          have haccounts :
              accountMapEquiv
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨5⟩ data)
                  ⟨13⟩ ⟨0⟩)
                evm2.accountMap := by
            simpa [evm2, evmSolm, data] using
              (clipperFileUintWordPostState_accountMapEquiv
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) (slot := ⟨5⟩) (data := data) hAccounts)
          exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            hcreated haccounts henc
        · have hnotBufWord :
              calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintBufBytes :=
            clipperFileUintWhatWord_ne_of_bytes_ne (I := I)
              (bs := clipperFileUintBufBytes) (by omega) hbuf (by native_decide)
          by_cases htail : clipperFileUintWhat I = clipperFileUintTailBytes
          · have htailWord :
                calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintTailBytes := by
              rw [← clipperFileUintWhatWord_eq (I := I) (by omega), htail]
            let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            let evm2 := clipperFileUintWordPostState evmSolm ⟨6⟩ data
            have hbody :
                ExecTransitionBody (config v) (contract v) evmSolm locals
                  fileUintTransition.body
                  (.returned { contract := contract v, locals := locals } evm2 none) := by
              simpa [evmSolm, evm2, locals, data] using
                (clipperFileUintTailSourceBody (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                  hauthSolm hlockedSolm hbuf htail)
            have hret := clipperFileUintX_tailOk (v := v) hpatch hperm hauthEvm
              hlockedEvm hnotBufWord htailWord hreachBody
            have hcreated :
                (cA, sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner
                        (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨6⟩ data)
                      ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
              simp [evm2, evmSolm, data, clipperFileUintWordPostState,
                clipperFileUintLockedState, initState, storageStore_createdAccounts]
            have haccounts :
                accountMapEquiv
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨6⟩ data)
                    ⟨13⟩ ⟨0⟩)
                  evm2.accountMap := by
              simpa [evm2, evmSolm, data] using
                (clipperFileUintWordPostState_accountMapEquiv
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) (slot := ⟨6⟩) (data := data) hAccounts)
            exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              hcreated haccounts henc
          · have hnotTailWord :
                calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTailBytes :=
              clipperFileUintWhatWord_ne_of_bytes_ne (I := I)
                (bs := clipperFileUintTailBytes) (by omega) htail (by native_decide)
            by_cases hcusp : clipperFileUintWhat I = clipperFileUintCuspBytes
            · have hcuspWord :
                  calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintCuspBytes := by
                rw [← clipperFileUintWhatWord_eq (I := I) (by omega), hcusp]
              let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              let evm2 := clipperFileUintWordPostState evmSolm ⟨7⟩ data
              have hbody :
                  ExecTransitionBody (config v) (contract v) evmSolm locals
                    fileUintTransition.body
                    (.returned { contract := contract v, locals := locals } evm2 none) := by
                simpa [evmSolm, evm2, locals, data] using
                  (clipperFileUintCuspSourceBody (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                    hauthSolm hlockedSolm hbuf htail hcusp)
              have hret := clipperFileUintX_cuspOk (v := v) hpatch hperm hauthEvm
                hlockedEvm hnotBufWord hnotTailWord hcuspWord hreachBody
              have hcreated :
                  (cA, sstoreAccountMap I.codeOwner
                        (sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨7⟩ data)
                        ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
                simp [evm2, evmSolm, data, clipperFileUintWordPostState,
                  clipperFileUintLockedState, initState, storageStore_createdAccounts]
              have haccounts :
                  accountMapEquiv
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner
                        (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨7⟩ data)
                      ⟨13⟩ ⟨0⟩)
                    evm2.accountMap := by
                simpa [evm2, evmSolm, data] using
                  (clipperFileUintWordPostState_accountMapEquiv
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) (slot := ⟨7⟩) (data := data)
                    hAccounts)
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                hcreated haccounts henc
            · have hnotCuspWord :
                  calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintCuspBytes :=
                clipperFileUintWhatWord_ne_of_bytes_ne (I := I)
                  (bs := clipperFileUintCuspBytes) (by omega) hcusp (by native_decide)
              by_cases hchip : clipperFileUintWhat I = clipperFileUintChipBytes
              · have hchipWord :
                    calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintChipBytes := by
                  rw [← clipperFileUintWhatWord_eq (I := I) (by omega), hchip]
                let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                let evm2 := clipperFileUintChipPostState evmSolm data
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm locals
                      fileUintTransition.body
                      (.returned { contract := contract v, locals := locals } evm2 none) := by
                  simpa [evmSolm, evm2, locals, data] using
                    (clipperFileUintChipSourceBody (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                      hauthSolm hlockedSolm hbuf htail hcusp hchip)
                have hret := clipperFileUintX_chipOk (v := v) hpatch hperm hauthEvm
                  hlockedEvm hnotBufWord hnotTailWord hnotCuspWord hchipWord hreachBody
                have hcreated :
                    (cA, sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner
                            (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨8⟩
                              (clipperFileUintChipWord
                                (solcSlotWord
                                  (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                                  I ⟨8⟩) data))
                          ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
                  simp [evm2, evmSolm, data, clipperFileUintChipPostState,
                    clipperFileUintLockedState, initState, storageStore_createdAccounts]
                have haccounts :
                    accountMapEquiv
                      (sstoreAccountMap I.codeOwner
                        (sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨8⟩
                            (clipperFileUintChipWord
                              (solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                                I ⟨8⟩) data))
                        ⟨13⟩ ⟨0⟩)
                      evm2.accountMap := by
                  simpa [evm2, evmSolm, data] using
                    (clipperFileUintChipPostState_accountMapEquiv
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) (data := data) hAccounts)
                exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                  hcreated haccounts henc
              · have hnotChipWord :
                    calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintChipBytes :=
                  clipperFileUintWhatWord_ne_of_bytes_ne (I := I)
                    (bs := clipperFileUintChipBytes) (by omega) hchip (by native_decide)
                by_cases htip : clipperFileUintWhat I = clipperFileUintTipBytes
                · have htipWord :
                      calldataWord I.calldata 4 = ABI.bytesToWord clipperFileUintTipBytes := by
                    rw [← clipperFileUintWhatWord_eq (I := I) (by omega), htip]
                  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                  let evm2 := clipperFileUintTipPostState evmSolm data
                  have hbody :
                      ExecTransitionBody (config v) (contract v) evmSolm locals
                        fileUintTransition.body
                        (.returned { contract := contract v, locals := locals } evm2 none) := by
                    simpa [evmSolm, evm2, locals, data] using
                      (clipperFileUintTipSourceBody (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                        hauthSolm hlockedSolm hbuf htail hcusp hchip htip)
                  have hret := clipperFileUintX_tipOk (v := v) hpatch hperm hauthEvm
                    hlockedEvm hnotBufWord hnotTailWord hnotCuspWord hnotChipWord htipWord
                    hreachBody
                  have hcreated :
                      (cA, sstoreAccountMap I.codeOwner
                            (sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨8⟩
                                (clipperFileUintTipWord
                                  (solcSlotWord
                                    (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                                    I ⟨8⟩) data))
                            ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
                    simp [evm2, evmSolm, data, clipperFileUintTipPostState,
                      clipperFileUintLockedState, initState, storageStore_createdAccounts]
                  have haccounts :
                      accountMapEquiv
                        (sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner
                            (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨8⟩
                              (clipperFileUintTipWord
                                (solcSlotWord
                                  (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                                  I ⟨8⟩) data))
                          ⟨13⟩ ⟨0⟩)
                        evm2.accountMap := by
                    simpa [evm2, evmSolm, data] using
                      (clipperFileUintTipPostState_accountMapEquiv
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g) (data := data) hAccounts)
                  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode
                    hbody hcreated haccounts henc
                · have hnotTipWord :
                      calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileUintTipBytes :=
                    clipperFileUintWhatWord_ne_of_bytes_ne (I := I)
                      (bs := clipperFileUintTipBytes) (by omega) htip (by native_decide)
                  by_cases hstopped : clipperFileUintWhat I = clipperFileUintStoppedBytes
                  · have hstoppedWord :
                        calldataWord I.calldata 4 =
                          ABI.bytesToWord clipperFileUintStoppedBytes := by
                      rw [← clipperFileUintWhatWord_eq (I := I) (by omega), hstopped]
                    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                    let evm2 := clipperFileUintWordPostState evmSolm ⟨14⟩ data
                    have hbody :
                        ExecTransitionBody (config v) (contract v) evmSolm locals
                          fileUintTransition.body
                          (.returned { contract := contract v, locals := locals } evm2 none) := by
                      simpa [evmSolm, evm2, locals, data] using
                        (clipperFileUintStoppedSourceBody (cA := cA) (gh := gh)
                          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := g) v hwv hauthSolm hlockedSolm hbuf htail hcusp hchip
                          htip hstopped)
                    have hret := clipperFileUintX_stoppedOk (v := v) hpatch hperm
                      hauthEvm hlockedEvm hnotBufWord hnotTailWord hnotCuspWord
                      hnotChipWord hnotTipWord hstoppedWord hreachBody
                    have hcreated :
                        (cA, sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner
                                (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                                  ⟨14⟩ data)
                              ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
                      simp [evm2, evmSolm, data, clipperFileUintWordPostState,
                        clipperFileUintLockedState, initState, storageStore_createdAccounts]
                    have haccounts :
                        accountMapEquiv
                          (sstoreAccountMap I.codeOwner
                            (sstoreAccountMap I.codeOwner
                              (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                                ⟨14⟩ data)
                            ⟨13⟩ ⟨0⟩)
                          evm2.accountMap := by
                      simpa [evm2, evmSolm, data] using
                        (clipperFileUintWordPostState_accountMapEquiv
                          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := Sat256.ofUInt256 g) (slot := ⟨14⟩) (data := data)
                          hAccounts)
                    exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode
                      hbody hcreated haccounts henc
                  · have hnotStoppedWord :
                        calldataWord I.calldata 4 ≠
                          ABI.bytesToWord clipperFileUintStoppedBytes :=
                      clipperFileUintWhatWord_ne_of_bytes_ne (I := I)
                        (bs := clipperFileUintStoppedBytes) (by omega) hstopped
                        (by native_decide)
                    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                    have hbody :
                        ExecTransitionBody (config v) (contract v) evmSolm locals
                          fileUintTransition.body .reverted := by
                      simpa [evmSolm, locals] using
                        (clipperFileUintUnrecognizedSourceBody (cA := cA) (gh := gh)
                          (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := g) v hwv hauthSolm hlockedSolm hbuf htail hcusp hchip
                          htip hstopped)
                    obtain ⟨_, _, rd2621⟩ := hreachBody
                    obtain ⟨_, _, rd2703⟩ :=
                      clipperFileUintX_authorized (v := v) hpatch hauthEvm rd2621
                    obtain ⟨_, _, rd2780⟩ :=
                      clipperFileUintX_lockOpen (v := v) hpatch hlockedEvm rd2703
                    obtain ⟨_, _, rd2786⟩ :=
                      clipperFileUintX_lockStore (v := v) hpatch hperm rd2780
                    obtain ⟨_, _, rd2809⟩ :=
                      clipperFileUintX_bufSkip (v := v) hpatch hnotBufWord rd2786
                    obtain ⟨_, _, rd2834⟩ :=
                      clipperFileUintX_tailSkipFrom (v := v) hpatch hnotTailWord rd2809
                    obtain ⟨_, _, rd2859⟩ :=
                      clipperFileUintX_cuspSkipFrom (v := v) hpatch hnotCuspWord rd2834
                    obtain ⟨_, _, rd2908⟩ :=
                      clipperFileUintX_chipSkipFrom (v := v) hpatch hnotChipWord rd2859
                    obtain ⟨_, _, rd2960⟩ :=
                      clipperFileUintX_tipSkipFrom (v := v) hpatch hnotTipWord rd2908
                    obtain ⟨_, _, rd2988⟩ :=
                      clipperFileUintX_stoppedSkipFrom (v := v) hpatch hnotStoppedWord
                        rd2960
                    have hrev := clipperFileUintX_unrecognized (v := v) hpatch rd2988
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ ≠ ⟨0⟩ := by
          intro hsolm
          exact hlockedEvm (by rw [hlockWord, hsolm])
        let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody (config v) (contract v) evmSolm locals
              fileUintTransition.body .reverted := by
          simpa [evmSolm, locals] using
            (clipperFileUintLockedSourceReverts (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
              hauthSolm hlockedSolm)
        obtain ⟨_, _, rd2621⟩ := hreachBody
        obtain ⟨_, _, rd2703⟩ :=
          clipperFileUintX_authorized (v := v) hpatch hauthEvm rd2621
        have hrev := clipperFileUintX_locked (v := v) hpatch hlockedEvm rd2703
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : clipperRelyAuthWord σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hauthWord, hsolm])
      let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evmSolm locals
            fileUintTransition.body .reverted := by
        simpa [evmSolm, locals] using
          (clipperFileUintAuthSourceReverts (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv hauthSolm)
      obtain ⟨_, _, rd2621⟩ := hreachBody
      have hrev := clipperFileUintX_unauthorized (v := v) hpatch hauthEvm rd2621
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hrev := clipperFileUintX_shortarg (v := v) hpatch hsz4 hsize hshort hreachEntry
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (clipperDecode_fileUint_none_short v hsz4 hshort)


end Benchmarks.Dss.Clipper
