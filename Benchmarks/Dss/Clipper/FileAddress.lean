import Benchmarks.Dss.Clipper.FileAddressSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperFileAddressPatchesWindowDisjoint32 (v : ClipperImmutables) (lo hi : Nat)
    (hlo : 2988 ≤ lo) (hhi : hi ≤ 7261) (hgap : hi ≤ 3065 ∨ 6840 ≤ lo) :
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

theorem clipperFileAddressDecodeMid (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hlo : 2988 ≤ pc.toNat)
    (hhi : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 7261)
    (hgap :
      pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 3065 ∨
        6840 ≤ pc.toNat)
    (hdec : decode clipperBytecode pc = some res) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperFileAddressPatchesWindowDisjoint32 v pc.toNat (pc.toNat + 1) hlo (by omega)
      (by omega))
    (clipperFileAddressPatchesWindowDisjoint32 v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) (by omega) hhi
      (by omega))
    hdec
    (by
      have hle :
          pc.toNat + 1 ≤
            pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) := by
        omega
      exact Nat.lt_of_le_of_lt (Nat.le_trans hle hhi) (by norm_num))
    (by exact Nat.lt_of_le_of_lt hhi (by norm_num))

macro "clipper_file_address_decode" : tactic =>
  `(tactic| first
    | clipper_decode
    | exact clipperFileAddressDecodeMid _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide) (by native_decide))

theorem clipperFileAddressRoutineJumpDest (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6840⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileAddressJumpDest6922 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6922⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileAddressJumpDest6999 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨6999⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileAddressJumpDest7054 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7054⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileAddressJumpDest7100 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7100⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileAddressJumpDest7146 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7146⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileAddressJumpDest7189 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨7189⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileAddressJumpDest2988 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨2988⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 7200) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperFileAddressSpotterWord :
    UInt256.shiftLeft (⟨16246623159595705⟩ : UInt256) ⟨201⟩ =
      ABI.bytesToWord clipperFileAddressSpotterBytes := by
  native_decide

theorem clipperFileAddressDogWord :
    UInt256.shiftLeft (⟨6582119⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord clipperFileAddressDogBytes := by
  native_decide

theorem clipperFileAddressVowWord :
    UInt256.shiftLeft (⟨7761783⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord clipperFileAddressVowBytes := by
  native_decide

theorem clipperFileAddressCalcWord :
    UInt256.shiftLeft (⟨1667329123⟩ : UInt256) ⟨224⟩ =
      ABI.bytesToWord clipperFileAddressCalcBytes := by
  native_decide

noncomputable abbrev clipperFileAddressEventMem (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem (clipperRelyAuthHashMem I)
    (UInt256.land (clipperFileAddressDataMaskedWord I) solcAddrMask)

theorem clipperFileAddressAuthHashMem_mload64 (I : ExecutionEnv) :
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

theorem clipperFileAddressEventMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperFileAddressEventMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 5) * ⟨32⟩ then ⟨0⟩
      else
        UInt256.ofNat (fromByteArrayBigEndian
          ((clipperFileAddressEventMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact solcScratchReturnMem_mload64
    (UInt256.land (clipperFileAddressDataMaskedWord I) solcAddrMask)
    (clipperRelyAuthHashMem_size I) (clipperRelyAuthHashMem_read64 I)

theorem RD.clipperFileAddressDecodeToRoutine (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨1387⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J code 0).contains ⟨6840⟩ = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨6840⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd1388 := h.jumpdest (by clipper_file_address_decode) (by evm_ov)
  have rd1389 := rd1388.pop (by clipper_file_address_decode) (by evm_ov)
  have rd1390 := rd1389.dup1 (by clipper_file_address_decode) (by evm_ov)
  have rd1391 := rd1390.calldataload (by clipper_file_address_decode) (by evm_ov)
  have rd1392 := rd1391.swap1 (by clipper_file_address_decode) (by evm_ov)
  have rd1394 := rd1392.push1 ⟨32⟩ (by clipper_file_address_decode) (by evm_ov)
  have rd1395 := rd1394.add (by clipper_file_address_decode) (by evm_ov)
  have rd1396 := rd1395.calldataload (by clipper_file_address_decode) (by evm_ov)
  have rd1398 := rd1396.push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov)
  have rd1400 := rd1398.push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov)
  have rd1402 := rd1400.push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov)
  have rd1403 := rd1402.shl (by clipper_file_address_decode) (by evm_ov)
  have rd1404 := rd1403.sub (by clipper_file_address_decode) (by evm_ov)
  have rd1405 := rd1404.and (by clipper_file_address_decode) (by evm_ov)
  have rd1408 := rd1405.push2 ⟨6840⟩ (by clipper_file_address_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd1408.jump (by clipper_file_address_decode) hroutine (by evm_ov)⟩

theorem clipperFileAddressDecodedToBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    {sel : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (⟨1365⟩ : UInt256) [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨6840⟩ : UInt256)
      (clipperFileAddressDataMaskedWord I :: calldataWord I.calldata 4 :: ⟨502⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨1365⟩) (ret := ⟨502⟩)
    (decoded := ⟨1387⟩) hreach
    (by change decode code (⟨1365⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩) =
        some (.Push .PUSH2, some (⟨502⟩, 2))
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2) = some (.DUP1, .none)
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩) = some (.CALLDATASIZE, .none)
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.SUB, .none)
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1))
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.DUP2, .none)
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none)
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none)
      clipper_decode)
    (by
      change decode code ((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (⟨1387⟩, 2))
      clipper_decode)
    (by
      change decode code (((⟨1365⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) = some (.JUMPI, .none)
      clipper_decode)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1387⟩ : UInt256) (by native_decide))
    hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.clipperFileAddressDecodeToRoutine
    (ret := ⟨502⟩) (sel := sel) (R := []) v hpatch hdecoded
    (clipperFileAddressRoutineJumpDest v hpatch) (by simp)
  exact ⟨_, _, by simpa [clipperFileAddressDataMaskedWord, clipperFileAddressDataWord] using hroutine⟩

theorem clipperFileAddressX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD code I g
      (initState cA gh bl σ σ₀ g A I) (⟨1365⟩ : UInt256) [sel]
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
    (code := code) (sel := sel) (entry := (⟨1365⟩ : UInt256))
    (ret := (⟨502⟩ : UInt256)) (decoded := (⟨1387⟩ : UInt256))
    (need := (⟨64⟩ : UInt256)) hreach
    (by change decode code (⟨1365⟩ : UInt256) = some (.JUMPDEST, .none); clipper_decode)
    (by
      change decode code (⟨1366⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨502⟩, 2))
      clipper_decode)
    (by
      change decode code (⟨1369⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      clipper_decode)
    (by change decode code (⟨1371⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨1372⟩ : UInt256) = some (.CALLDATASIZE, .none); clipper_decode)
    (by change decode code (⟨1373⟩ : UInt256) = some (.SUB, .none); clipper_decode)
    (by
      change decode code (⟨1374⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨64⟩, 1))
      clipper_decode)
    (by change decode code (⟨1376⟩ : UInt256) = some (.DUP2, .none); clipper_decode)
    (by change decode code (⟨1377⟩ : UInt256) = some (.LT, .none); clipper_decode)
    (by change decode code (⟨1378⟩ : UInt256) = some (.ISZERO, .none); clipper_decode)
    (by
      change decode code (⟨1379⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨1387⟩, 2))
      clipper_decode)
    (by change decode code (⟨1382⟩ : UInt256) = some (.JUMPI, .none); clipper_decode)
    (by
      change decode code (⟨1383⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨0⟩, 1))
      clipper_decode)
    (by change decode code (⟨1385⟩ : UInt256) = some (.DUP1, .none); clipper_decode)
    (by change decode code (⟨1386⟩ : UInt256) = some (.REVERT, .none); clipper_decode)
    hlt

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (h : RD code I g s0 ⟨6840⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨6922⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd6845pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw caller (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd6847 := rd6845pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd6850pre := evm_run rd6847 with [
    raw push1 ⟨32⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  have rd6852 := rd6850pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd6855pre := evm_run rd6852 with [
    raw push1 ⟨64⟩ (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  have rd6856 := rd6855pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost hauthSlot
    (by native_decide) (by evm_ov)
  obtain ⟨k6857, C6857, rd6857raw⟩ := rd6856.sload
    (by clipper_file_address_decode) (by evm_ov)
  have rd6857 : RD code I g s0 ⟨6857⟩
      (clipperRelyAuthWord σ I :: clipperFileAddressDataMaskedWord I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6857 C6857 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd6857raw
  have rd6859pre := evm_run rd6857 with [
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw eq (by clipper_file_address_decode) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd6859pre
  have rd6863 := rd6859pre.pushConst (⟨6922⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode)
    (by evm_ov)
  exact ⟨_, _, rd6863.jumpiT (by clipper_file_address_decode) one_ne_zero_uint
    (clipperFileAddressJumpDest6922 v hpatch) (by evm_ov)⟩

theorem clipperFileAddressX_lockOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (h : RD code I g s0 ⟨6922⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨6999⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6925pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨k6926, C6926, rd6926raw⟩ := rd6925pre.sload
    (by clipper_file_address_decode) (by evm_ov)
  have rd6926 : RD code I g s0 ⟨6926⟩
      (solcSlotWord σ I ⟨13⟩ :: clipperFileAddressDataMaskedWord I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6926 C6926 := by
    simpa [solcSlotWord] using rd6926raw
  have rd6927 := rd6926.iszero (by clipper_file_address_decode) (by evm_ov)
  have hcond : UInt256.isZero (solcSlotWord σ I ⟨13⟩) ≠ ⟨0⟩ := by
    rw [hlocked]
    native_decide
  have rd6930 := rd6927.pushConst (⟨6999⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode)
    (by evm_ov)
  exact ⟨_, _, rd6930.jumpiT (by clipper_file_address_decode) hcond
    (clipperFileAddressJumpDest6999 v hpatch) (by evm_ov)⟩

theorem clipperFileAddressX_lockStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨6999⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨7005⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) k' C' := by
  have rd7004pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨_, _, rd7005raw⟩ := rd7004pre.sstore hperm (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd7005raw⟩

theorem clipperFileAddressSetWord_eq (old data : UInt256) :
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old data := by
  calc
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
        UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land old (UInt256.lnot solcAddrMask)) := by
          rw [u256_land_comm (UInt256.lnot solcAddrMask) old]
    _ = UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask))
          (UInt256.land data solcAddrMask) := by
          exact u256_lor_comm _ _
    _ = setAddressOffset0Word old data := by
          rfl

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_spotterStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressSpotterBytes)
    (h : RD code I g s0 ⟨7005⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨7189⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (clipperFileAddressDataMaskedWord I)))
      k' C' := by
  have rd7013 := h.pushConst (⟨16246623159595705⟩ : UInt256)
    (width := 7) (op := .PUSH7) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7015pre := evm_run rd7013 with [
    raw push1 ⟨201⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperFileAddressSpotterWord, ← hwhat] at rd7015pre
  have rd7019pre := evm_run rd7015pre with [
    raw dup3 (by clipper_file_address_decode) (by evm_ov),
    raw eq (by clipper_file_address_decode) (by evm_ov),
    raw iszero (by clipper_file_address_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd7019pre
  have rd7022 := rd7019pre.pushConst (⟨7054⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7023 := rd7022.jumpiNT (by clipper_file_address_decode) (by native_decide)
    (by evm_ov)
  have rd7026pre := evm_run rd7023 with [
    raw push1 ⟨3⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup1 (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨k7027, C7027, rd7027raw⟩ := rd7026pre.sload
    (by clipper_file_address_decode) (by evm_ov)
  have rd7027 : RD code I g s0 ⟨7027⟩
      (solcSlotWord σ I ⟨3⟩ :: ⟨3⟩ :: clipperFileAddressDataMaskedWord I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k7027 C7027 := by
    simpa [solcSlotWord] using rd7027raw
  have rd7048 := evm_run rd7027 with [
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw not (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw dup4 (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw lor (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨_, _, rd7050raw⟩ := rd7048.sstore hperm (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7053 := rd7050raw.pushConst (⟨7189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, clipperFileAddressSetWord_eq,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd7053.jump (by clipper_file_address_decode)
        (clipperFileAddressJumpDest7189 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_spotterSkip {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotSpotter : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressSpotterBytes)
    (h : RD code I g s0 ⟨7005⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨7054⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd7013 := h.pushConst (⟨16246623159595705⟩ : UInt256)
    (width := 7) (op := .PUSH7) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7015pre := evm_run rd7013 with [
    raw push1 ⟨201⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperFileAddressSpotterWord] at rd7015pre
  have rd7019pre := evm_run rd7015pre with [
    raw dup3 (by clipper_file_address_decode) (by evm_ov),
    raw eq (by clipper_file_address_decode) (by evm_ov),
    raw iszero (by clipper_file_address_decode) (by evm_ov)]
  have heq :
      UInt256.eq (calldataWord I.calldata 4)
          (ABI.bytesToWord clipperFileAddressSpotterBytes) = ⟨0⟩ := by
    exact u256_eq_of_ne hnotSpotter
  rw [heq] at rd7019pre
  have rd7022 := rd7019pre.pushConst (⟨7054⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  exact ⟨_, _, rd7022.jumpiT (by clipper_file_address_decode) (by native_decide)
    (clipperFileAddressJumpDest7054 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_dogStoreFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressDogBytes)
    (h : RD code I g s0 ⟨7054⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨7189⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨1⟩) (clipperFileAddressDataMaskedWord I)))
      k' C' := by
  have rd7056pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd7060 := rd7056pre.pushConst (⟨6582119⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7062pre := evm_run rd7060 with [
    raw push1 ⟨232⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperFileAddressDogWord, ← hwhat] at rd7062pre
  have rd7065pre := evm_run rd7062pre with [
    raw eq (by clipper_file_address_decode) (by evm_ov),
    raw iszero (by clipper_file_address_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd7065pre
  have rd7068 := rd7065pre.pushConst (⟨7100⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7069 := rd7068.jumpiNT (by clipper_file_address_decode) (by native_decide)
    (by evm_ov)
  have rd7072pre := evm_run rd7069 with [
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup1 (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨k7073, C7073, rd7073raw⟩ := rd7072pre.sload
    (by clipper_file_address_decode) (by evm_ov)
  have rd7073 : RD code I g s0 ⟨7073⟩
      (solcSlotWord σ I ⟨1⟩ :: ⟨1⟩ :: clipperFileAddressDataMaskedWord I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k7073 C7073 := by
    simpa [solcSlotWord] using rd7073raw
  have rd7094 := evm_run rd7073 with [
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw not (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw dup4 (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw lor (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨_, _, rd7096raw⟩ := rd7094.sstore hperm (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7099 := rd7096raw.pushConst (⟨7189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, clipperFileAddressSetWord_eq,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd7099.jump (by clipper_file_address_decode)
        (clipperFileAddressJumpDest7189 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_dogSkipFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotDog : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressDogBytes)
    (h : RD code I g s0 ⟨7054⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨7100⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd7056pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd7060 := rd7056pre.pushConst (⟨6582119⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7062pre := evm_run rd7060 with [
    raw push1 ⟨232⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperFileAddressDogWord] at rd7062pre
  have rd7065pre := evm_run rd7062pre with [
    raw eq (by clipper_file_address_decode) (by evm_ov),
    raw iszero (by clipper_file_address_decode) (by evm_ov)]
  have heq :
      UInt256.eq (ABI.bytesToWord clipperFileAddressDogBytes)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hnotDog hbad.symm)
  rw [heq] at rd7065pre
  have rd7068 := rd7065pre.pushConst (⟨7100⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  exact ⟨_, _, rd7068.jumpiT (by clipper_file_address_decode) (by native_decide)
    (clipperFileAddressJumpDest7100 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_vowStoreFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressVowBytes)
    (h : RD code I g s0 ⟨7100⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨7189⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (clipperFileAddressDataMaskedWord I)))
      k' C' := by
  have rd7102pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd7106 := rd7102pre.pushConst (⟨7761783⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7108pre := evm_run rd7106 with [
    raw push1 ⟨232⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperFileAddressVowWord, ← hwhat] at rd7108pre
  have rd7111pre := evm_run rd7108pre with [
    raw eq (by clipper_file_address_decode) (by evm_ov),
    raw iszero (by clipper_file_address_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd7111pre
  have rd7114 := rd7111pre.pushConst (⟨7146⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7115 := rd7114.jumpiNT (by clipper_file_address_decode) (by native_decide)
    (by evm_ov)
  have rd7118pre := evm_run rd7115 with [
    raw push1 ⟨2⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup1 (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨k7119, C7119, rd7119raw⟩ := rd7118pre.sload
    (by clipper_file_address_decode) (by evm_ov)
  have rd7119 : RD code I g s0 ⟨7119⟩
      (solcSlotWord σ I ⟨2⟩ :: ⟨2⟩ :: clipperFileAddressDataMaskedWord I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k7119 C7119 := by
    simpa [solcSlotWord] using rd7119raw
  have rd7140 := evm_run rd7119 with [
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw not (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw dup4 (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw lor (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨_, _, rd7142raw⟩ := rd7140.sstore hperm (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7145 := rd7142raw.pushConst (⟨7189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [solcSlotWord, clipperFileAddressSetWord_eq,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd7145.jump (by clipper_file_address_decode)
        (clipperFileAddressJumpDest7189 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_vowSkipFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotVow : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressVowBytes)
    (h : RD code I g s0 ⟨7100⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨7146⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd7102pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd7106 := rd7102pre.pushConst (⟨7761783⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7108pre := evm_run rd7106 with [
    raw push1 ⟨232⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperFileAddressVowWord] at rd7108pre
  have rd7111pre := evm_run rd7108pre with [
    raw eq (by clipper_file_address_decode) (by evm_ov),
    raw iszero (by clipper_file_address_decode) (by evm_ov)]
  have heq :
      UInt256.eq (ABI.bytesToWord clipperFileAddressVowBytes)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hnotVow hbad.symm)
  rw [heq] at rd7111pre
  have rd7114 := rd7111pre.pushConst (⟨7146⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  exact ⟨_, _, rd7114.jumpiT (by clipper_file_address_decode) (by native_decide)
    (clipperFileAddressJumpDest7146 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_calcStoreFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressCalcBytes)
    (h : RD code I g s0 ⟨7146⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨7189⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨4⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨4⟩) (clipperFileAddressDataMaskedWord I)))
      k' C' := by
  have rd7148pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd7153 := rd7148pre.pushConst (⟨1667329123⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7155pre := evm_run rd7153 with [
    raw push1 ⟨224⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperFileAddressCalcWord, ← hwhat] at rd7155pre
  have rd7158pre := evm_run rd7155pre with [
    raw eq (by clipper_file_address_decode) (by evm_ov),
    raw iszero (by clipper_file_address_decode) (by evm_ov)]
  rw [u256_eq_refl] at rd7158pre
  have rd7161 := rd7158pre.pushConst (⟨2988⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7162 := rd7161.jumpiNT (by clipper_file_address_decode) (by native_decide)
    (by evm_ov)
  have rd7165pre := evm_run rd7162 with [
    raw push1 ⟨4⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup1 (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨k7166, C7166, rd7166raw⟩ := rd7165pre.sload
    (by clipper_file_address_decode) (by evm_ov)
  have rd7166 : RD code I g s0 ⟨7166⟩
      (solcSlotWord σ I ⟨4⟩ :: ⟨4⟩ :: clipperFileAddressDataMaskedWord I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k7166 C7166 := by
    simpa [solcSlotWord] using rd7166raw
  have rd7187 := evm_run rd7166 with [
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw not (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw dup4 (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw lor (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨_, _, rd7189raw⟩ := rd7187.sstore hperm (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [solcSlotWord, clipperFileAddressSetWord_eq,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd7189raw⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_calcSkipFrom {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hnotCalc : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressCalcBytes)
    (h : RD code I g s0 ⟨7146⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨2988⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd7148pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd7153 := rd7148pre.pushConst (⟨1667329123⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7155pre := evm_run rd7153 with [
    raw push1 ⟨224⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperFileAddressCalcWord] at rd7155pre
  have rd7158pre := evm_run rd7155pre with [
    raw eq (by clipper_file_address_decode) (by evm_ov),
    raw iszero (by clipper_file_address_decode) (by evm_ov)]
  have heq :
      UInt256.eq (ABI.bytesToWord clipperFileAddressCalcBytes)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hnotCalc hbad.symm)
  rw [heq] at rd7158pre
  have rd7161 := rd7158pre.pushConst (⟨2988⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  exact ⟨_, _, rd7161.jumpiT (by clipper_file_address_decode) (by native_decide)
    (clipperFileAddressJumpDest2988 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_successEpilogue {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨7189⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g s0 (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨0⟩) ByteArray.empty := by
  have rd7193 := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup1 (by clipper_file_address_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost
      (clipperFileAddressAuthHashMem_mload64 I) (by native_decide) (by evm_ov)]
  have rd7204pre := evm_run rd7193 with [
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw dup4 (by clipper_file_address_decode) (by evm_ov),
    raw and (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by decide] at rd7204pre
  have rd7206 := rd7204pre.mstore 6 (clipperFileAddressEventMem I) (UInt256.ofNat 5)
    (by clipper_file_address_decode)
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := UInt256.ofNat 3) (off := (⟨128⟩ : UInt256))
        (val := UInt256.land (clipperFileAddressDataMaskedWord I) solcAddrMask)
        (t := (⟨128⟩ : UInt256) :: (⟨64⟩ : UInt256) :: clipperFileAddressDataMaskedWord I ::
          calldataWord I.calldata 4 :: (⟨502⟩ : UInt256) :: [sel])
        haw hstk (by native_decide))
    (by rfl)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd7208 := evm_run rd7206 with [
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by clipper_file_address_decode) mem_cost
      (clipperFileAddressEventMem_mload64 I) (by native_decide) (by evm_ov)]
  have rd7210 := evm_run rd7208 with [
    raw dup4 (by clipper_file_address_decode) (by evm_ov),
    raw swap2 (by clipper_file_address_decode) (by evm_ov)]
  have rd7243 := rd7210.pushConst
    (⟨65103624907084577414431664178121565314709747119730508611619433015502684841658⟩ :
      UInt256)
    (op := .PUSH32) (width := 32) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd7252pre := evm_run rd7243 with [
    raw swap2 (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  have rd7253 := RD.log2 0 (UInt256.ofNat 5) rd7252pre
    (by clipper_file_address_decode) hperm mem_cost (by native_decide) (by evm_ov)
  have rd7259pre := evm_run rd7253 with [
    raw pop (by clipper_file_address_decode) (by evm_ov),
    raw pop (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨_, _, rd7260raw⟩ := rd7259pre.sstore hperm (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd502 := rd7260raw.jump (by clipper_file_address_decode)
    (clipperRelyReturnJumpDest v hpatch) (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_decode) (by evm_ov)
  exact RD.stop rd503 (by clipper_decode) (by evm_ov)

theorem clipperFileAddressX_spotterOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressSpotterBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨6840⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨3⟩
            (setAddressOffset0Word
              (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨3⟩)
              (clipperFileAddressDataMaskedWord I)))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd6840⟩ := hreach
  obtain ⟨_, _, rd6922⟩ := clipperFileAddressX_authorized (v := v) hpatch hauth rd6840
  obtain ⟨_, _, rd6999⟩ := clipperFileAddressX_lockOpen (v := v) hpatch hlocked rd6922
  obtain ⟨_, _, rd7005⟩ := clipperFileAddressX_lockStore (v := v) hpatch hperm rd6999
  obtain ⟨_, _, rd7189⟩ :=
    clipperFileAddressX_spotterStore (v := v) hpatch hperm hwhat rd7005
  exact clipperFileAddressX_successEpilogue (v := v) hpatch hperm rd7189

theorem clipperFileAddressX_dogOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotSpotter : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressSpotterBytes)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressDogBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨6840⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨1⟩
            (setAddressOffset0Word
              (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨1⟩)
              (clipperFileAddressDataMaskedWord I)))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd6840⟩ := hreach
  obtain ⟨_, _, rd6922⟩ := clipperFileAddressX_authorized (v := v) hpatch hauth rd6840
  obtain ⟨_, _, rd6999⟩ := clipperFileAddressX_lockOpen (v := v) hpatch hlocked rd6922
  obtain ⟨_, _, rd7005⟩ := clipperFileAddressX_lockStore (v := v) hpatch hperm rd6999
  obtain ⟨_, _, rd7054⟩ := clipperFileAddressX_spotterSkip (v := v) hpatch
    hnotSpotter rd7005
  obtain ⟨_, _, rd7189⟩ :=
    clipperFileAddressX_dogStoreFrom (v := v) hpatch hperm hwhat rd7054
  exact clipperFileAddressX_successEpilogue (v := v) hpatch hperm rd7189

theorem clipperFileAddressX_vowOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotSpotter : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressSpotterBytes)
    (hnotDog : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressDogBytes)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressVowBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨6840⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨2⟩
            (setAddressOffset0Word
              (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨2⟩)
              (clipperFileAddressDataMaskedWord I)))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd6840⟩ := hreach
  obtain ⟨_, _, rd6922⟩ := clipperFileAddressX_authorized (v := v) hpatch hauth rd6840
  obtain ⟨_, _, rd6999⟩ := clipperFileAddressX_lockOpen (v := v) hpatch hlocked rd6922
  obtain ⟨_, _, rd7005⟩ := clipperFileAddressX_lockStore (v := v) hpatch hperm rd6999
  obtain ⟨_, _, rd7054⟩ := clipperFileAddressX_spotterSkip (v := v) hpatch
    hnotSpotter rd7005
  obtain ⟨_, _, rd7100⟩ :=
    clipperFileAddressX_dogSkipFrom (v := v) hpatch hnotDog rd7054
  obtain ⟨_, _, rd7189⟩ :=
    clipperFileAddressX_vowStoreFrom (v := v) hpatch hperm hwhat rd7100
  exact clipperFileAddressX_successEpilogue (v := v) hpatch hperm rd7189

theorem clipperFileAddressX_calcOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (hnotSpotter : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressSpotterBytes)
    (hnotDog : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressDogBytes)
    (hnotVow : calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressVowBytes)
    (hwhat : calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressCalcBytes)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨6840⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) ⟨4⟩
            (setAddressOffset0Word
              (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨4⟩)
              (clipperFileAddressDataMaskedWord I)))
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rd6840⟩ := hreach
  obtain ⟨_, _, rd6922⟩ := clipperFileAddressX_authorized (v := v) hpatch hauth rd6840
  obtain ⟨_, _, rd6999⟩ := clipperFileAddressX_lockOpen (v := v) hpatch hlocked rd6922
  obtain ⟨_, _, rd7005⟩ := clipperFileAddressX_lockStore (v := v) hpatch hperm rd6999
  obtain ⟨_, _, rd7054⟩ := clipperFileAddressX_spotterSkip (v := v) hpatch
    hnotSpotter rd7005
  obtain ⟨_, _, rd7100⟩ :=
    clipperFileAddressX_dogSkipFrom (v := v) hpatch hnotDog rd7054
  obtain ⟨_, _, rd7146⟩ :=
    clipperFileAddressX_vowSkipFrom (v := v) hpatch hnotVow rd7100
  obtain ⟨_, _, rd7189⟩ :=
    clipperFileAddressX_calcStoreFrom (v := v) hpatch hperm hwhat rd7146
  exact clipperFileAddressX_successEpilogue (v := v) hpatch hperm rd7189

theorem clipperFileAddressPostState_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256} {slot data : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) slot
            (setAddressOffset0Word
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I slot)
              data))
        ⟨13⟩ ⟨0⟩)
      (clipperFileAddressPostState
        (initState cA gh bl σ_solm σ₀ g A I) slot data).accountMap := by
  have hlockAccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
        (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨1⟩ hAccounts
  have hslot :
      solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I slot =
        solcSlotWord (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) I slot :=
    accountMapEquiv_storage_findD hlockAccounts I.codeOwner slot ⟨0⟩
  have hstore :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) slot
            (setAddressOffset0Word
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I slot)
              data))
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm ⟨13⟩ ⟨1⟩) slot
            (setAddressOffset0Word
              (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I slot)
              data)) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner slot
      (setAddressOffset0Word
        (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I slot) data)
      hlockAccounts
  have hfinal := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨13⟩ ⟨0⟩ hstore
  simpa [clipperFileAddressPostState, clipperFileAddressLockedState, initState,
    storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
    State.lookupAccount, hslot] using hfinal

theorem clipperFileAddressLockRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code (⟨6931⟩ : UInt256) ⟨21⟩
      ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ .PUSH21 21 := by
  unfold solcErrorStringRevertTailWf
  dsimp
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> (norm_num1; clipper_file_address_decode)

theorem clipperFileAddressLockedStringWord :
    UInt256.shiftLeft ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ =
      ⟨30496508052792062404420069455133111715513420844312188351800969105462834233344⟩ := by
  native_decide

theorem clipperFileAddressUnrecognizedStringWord :
    UInt256.shiftLeft
        ⟨30496508052792062404099775245839162874297393920482488000238941594219156958464⟩
        ⟨0⟩ =
      ⟨0x436c69707065722f66696c652d756e7265636f676e697a65642d706172616d00⟩ := by
  native_decide

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_locked {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨6922⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd6925pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_file_address_decode) (by evm_ov)]
  obtain ⟨k6926, C6926, rd6926raw⟩ := rd6925pre.sload
    (by clipper_file_address_decode) (by evm_ov)
  have rd6926 : RD code I g s0 ⟨6926⟩
      (solcSlotWord σ I ⟨13⟩ :: clipperFileAddressDataMaskedWord I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6926 C6926 := by
    simpa [solcSlotWord] using rd6926raw
  have rd6927pre := rd6926.iszero (by clipper_file_address_decode) (by evm_ov)
  rw [isZero_eq_zero_of_ne hlocked] at rd6927pre
  have rd6930 := rd6927pre.pushConst (⟨6999⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd6931 := rd6930.jumpiNT (by clipper_file_address_decode)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail rd6931
    (clipperFileAddressLockRevertTailWf v hpatch)
    (by decide)
    clipperFileAddressLockedStringWord
    (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD code I g s0 ⟨6840⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd6845pre := evm_run h with [
    raw jumpdest (by clipper_file_address_decode) (by evm_ov),
    raw caller (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd6847 := rd6845pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6850pre := evm_run rd6847 with [
    raw push1 ⟨32⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  have rd6852 := rd6850pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6855pre := evm_run rd6852 with [
    raw push1 ⟨64⟩ (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov)]
  have rd6856 := rd6855pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k6857, C6857, rd6857raw⟩ := rd6856.sload
    (by clipper_file_address_decode) (by evm_ov)
  have rd6857 : RD code I g s0 ⟨6857⟩
      (clipperRelyAuthWord σ I :: clipperFileAddressDataMaskedWord I ::
        calldataWord I.calldata 4 :: ⟨502⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k6857 C6857 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd6857raw
  have rd6859pre := evm_run rd6857 with [
    raw push1 ⟨1⟩ (by clipper_file_address_decode) (by evm_ov),
    raw eq (by clipper_file_address_decode) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (clipperRelyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd6859pre
  have rd6863 := rd6859pre.pushConst (⟨6922⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd6864 := rd6863.jumpiNT (by clipper_file_address_decode) rfl (by evm_ov)
  have rd6868 := evm_run rd6864 with [
    raw push1 ⟨64⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup1 (by clipper_file_address_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost
      (mloadFreePtrValue (by rw [clipperRelyAuthHashMem_size]; decide)
        (by decide) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rd6872 := rd6868.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6874 := evm_run rd6872 with [
    raw push1 ⟨229⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov)]
  rw [clipperRelyNotAuthorizedWord] at rd6874
  have rd6876pre := evm_run rd6874 with [
    raw dup2 (by clipper_file_address_decode) (by evm_ov)]
  have rd6877 := rd6876pre.mstore 6
    (solcErrorStringMem0 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 5) (by clipper_file_address_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6889pre := evm_run rd6877 with [
    raw push1 ⟨32⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup3 (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov)]
  have rd6884 := rd6889pre.mstore 3
    (solcErrorStringMem1 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 6) (by clipper_file_address_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd6894pre := evm_run rd6884 with [
    raw push1 ⟨22⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup3 (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov),
    raw mstore 3 (clipperRelyErrorMem2 I)
      (UInt256.ofNat 7) (by clipper_file_address_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup1 (by clipper_file_address_decode) (by evm_ov),
    raw mload 0 (clipperRelySourceWord I) (UInt256.ofNat 7)
      (by clipper_file_address_decode) mem_cost (clipperRelyErrorMem2_mload0 I)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_file_address_decode) (by evm_ov)]
  have rd6897 := rd6894pre.pushConst (⟨9316⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_file_address_decode) (by evm_ov)
  have rd6900pre := evm_run rd6897 with [
    raw dup4 (by clipper_file_address_decode) (by evm_ov)]
  have rd6902 := rd6900pre.codecopy 0 (clipperRelyErrorCopiedMem code I)
    (UInt256.ofNat 7) (by clipper_file_address_decode) mem_cost
    (by
      rw [show (⟨9316⟩ : UInt256).toNat = 9316 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rd6904 := evm_run rd6902 with [
    raw dup2 (by clipper_file_address_decode) (by evm_ov),
    raw mload 0 clipperRelyNotAuthorizedStringWord (UInt256.ofNat 7)
      (by clipper_file_address_decode) mem_cost
      (by simpa [clipperRelyErrorCopiedMem, clipperRelyErrorMem2]
        using clipperRelyCodecopyMload0 v hpatch I)
      (by native_decide) (by evm_ov),
    raw swap2 (by clipper_file_address_decode) (by evm_ov)]
  have rd6905 := rd6904.mstore 0 (clipperRelyErrorRestoredMem code I)
    (UInt256.ofNat 7) (by clipper_file_address_decode) mem_cost
    (by simp [clipperRelyErrorRestoredMem, clipperRelyErrorCopiedMem])
    (by native_decide) (by evm_ov)
  have rd6909pre := evm_run rd6905 with [
    raw push1 ⟨68⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup3 (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov)]
  have rd6911 := rd6909pre.mstore 3 (clipperRelyErrorStringMem code I)
    (UInt256.ofNat 8) (by clipper_file_address_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 from by decide])
    (by native_decide) (by evm_ov)
  have rd6913 := evm_run rd6911 with [
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_file_address_decode) mem_cost
      (clipperRelyErrorStringMem_mload64 v hpatch I)
      (by native_decide) (by evm_ov)]
  exact evm_run rd6913 with [
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw rev 0 (by clipper_file_address_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem clipperFileAddressX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2988⟩
      [clipperFileAddressDataMaskedWord I, calldataWord I.calldata 4, ⟨502⟩, sel]
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd2989 := h.jumpdest
    (by change decode code (⟨2988⟩ : UInt256) = some (.JUMPDEST, .none); clipper_file_address_decode)
    (by simp)
  have rdMload := evm_run rd2989 with [
    raw push1 ⟨64⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup1 (by clipper_file_address_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_file_address_decode) mem_cost
      (mloadFreePtrValue (by rw [clipperRelyAuthHashMem_size]; decide)
        (by decide) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_file_address_decode) (by evm_ov),
    raw shl (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (clipperRelyAuthHashMem I)) (UInt256.ofNat 5)
      (by clipper_file_address_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup3 (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (clipperRelyAuthHashMem I)) (UInt256.ofNat 6)
      (by clipper_file_address_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨31⟩ (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup3 (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 (⟨31⟩ : UInt256) (clipperRelyAuthHashMem I))
      (UInt256.ofNat 7) (by clipper_file_address_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst
    (⟨30496508052792062404099775245839162874297393920482488000238941594219156958464⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by clipper_file_address_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_file_address_decode) (by evm_ov),
    raw dup3 (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 (⟨31⟩ : UInt256)
        ⟨30496508052792062404099775245839162874297393920482488000238941594219156958464⟩
        (clipperRelyAuthHashMem I))
      (UInt256.ofNat 8) (by clipper_file_address_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_file_address_decode) mem_cost
      (solcErrorStringMem3_mload64 (⟨31⟩ : UInt256)
        ⟨30496508052792062404099775245839162874297393920482488000238941594219156958464⟩
        (clipperRelyAuthHashMem_size I) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw dup2 (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw sub (by clipper_file_address_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_file_address_decode) (by evm_ov),
    raw add (by clipper_file_address_decode) (by evm_ov),
    raw swap1 (by clipper_file_address_decode) (by evm_ov),
    raw rev 0 (by clipper_file_address_decode) mem_cost (by evm_ov)]

theorem clipperFileAddressBody (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (clipperSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (clipperSelBytes 10) (by native_decide) hsel
  have hdispatch := clipperDispatch_fileAddress v hsel
  have hreachEntry :=
    clipperReachFileAddressBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) v hpatch hcode hwv
      hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := clipperDecode_fileAddress_ok v (I := I) hsz68
    have hreachBody :=
      clipperFileAddressDecodedToBody (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        v hpatch hsz68 hsize hreachEntry
    let data := clipperFileAddressDataMaskedWord I
    let locals := clipperFileAddressLocals I
    have henc : returnEquiv ByteArray.empty none fileAddressTransition.returnType := by
      rw [show fileAddressTransition.returnType = [] by rfl]
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
        by_cases hspotter : clipperFileAddressWhat I = clipperFileAddressSpotterBytes
        · have hspotterWord :
              calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressSpotterBytes := by
            rw [← clipperFileAddressWhatWord_eq (I := I) (by omega), hspotter]
          let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evm2 := clipperFileAddressPostState evmSolm ⟨3⟩ data
          have hbody :
              ExecTransitionBody (config v) (contract v) evmSolm locals
                fileAddressTransition.body
                (.returned { contract := contract v, locals := locals } evm2 none) := by
            simpa [evmSolm, evm2, locals, data] using
              (clipperFileAddressSpotterSourceBody (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                hauthSolm hlockedSolm hspotter)
          have hret := clipperFileAddressX_spotterOk (v := v) hpatch hperm hauthEvm
            hlockedEvm hspotterWord hreachBody
          have hcreated :
              (cA, sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨3⟩
                    (setAddressOffset0Word
                      (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                        I ⟨3⟩) data))
                ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
            simp [evm2, evmSolm, data, clipperFileAddressPostState,
              clipperFileAddressLockedState, initState, storageStore_createdAccounts]
          have haccounts :
              accountMapEquiv
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨3⟩
                      (setAddressOffset0Word
                        (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                          I ⟨3⟩) data))
                  ⟨13⟩ ⟨0⟩)
                evm2.accountMap := by
            simpa [evm2, evmSolm, data] using
              (clipperFileAddressPostState_accountMapEquiv
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := Sat256.ofUInt256 g) (slot := ⟨3⟩) (data := data) hAccounts)
          exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            hcreated haccounts henc
        · have hnotSpotterWord :
              calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressSpotterBytes :=
            clipperFileAddressWhatWord_ne_of_bytes_ne (I := I)
              (bs := clipperFileAddressSpotterBytes) (by omega) hspotter (by native_decide)
          by_cases hdog : clipperFileAddressWhat I = clipperFileAddressDogBytes
          · have hdogWord :
                calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressDogBytes := by
              rw [← clipperFileAddressWhatWord_eq (I := I) (by omega), hdog]
            let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            let evm2 := clipperFileAddressPostState evmSolm ⟨1⟩ data
            have hbody :
                ExecTransitionBody (config v) (contract v) evmSolm locals
                  fileAddressTransition.body
                  (.returned { contract := contract v, locals := locals } evm2 none) := by
              simpa [evmSolm, evm2, locals, data] using
                (clipperFileAddressDogSourceBody (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                  hauthSolm hlockedSolm hspotter hdog)
            have hret := clipperFileAddressX_dogOk (v := v) hpatch hperm hauthEvm
              hlockedEvm hnotSpotterWord hdogWord hreachBody
            have hcreated :
                (cA, sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨1⟩
                      (setAddressOffset0Word
                        (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                          I ⟨1⟩) data))
                  ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
              simp [evm2, evmSolm, data, clipperFileAddressPostState,
                clipperFileAddressLockedState, initState, storageStore_createdAccounts]
            have haccounts :
                accountMapEquiv
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨1⟩
                        (setAddressOffset0Word
                          (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                            I ⟨1⟩) data))
                    ⟨13⟩ ⟨0⟩)
                  evm2.accountMap := by
              simpa [evm2, evmSolm, data] using
                (clipperFileAddressPostState_accountMapEquiv
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g) (slot := ⟨1⟩) (data := data) hAccounts)
            exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              hcreated haccounts henc
          · have hnotDogWord :
                calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressDogBytes :=
              clipperFileAddressWhatWord_ne_of_bytes_ne (I := I)
                (bs := clipperFileAddressDogBytes) (by omega) hdog (by native_decide)
            by_cases hvow : clipperFileAddressWhat I = clipperFileAddressVowBytes
            · have hvowWord :
                  calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressVowBytes := by
                rw [← clipperFileAddressWhatWord_eq (I := I) (by omega), hvow]
              let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              let evm2 := clipperFileAddressPostState evmSolm ⟨2⟩ data
              have hbody :
                  ExecTransitionBody (config v) (contract v) evmSolm locals
                    fileAddressTransition.body
                    (.returned { contract := contract v, locals := locals } evm2 none) := by
                simpa [evmSolm, evm2, locals, data] using
                  (clipperFileAddressVowSourceBody (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                    hauthSolm hlockedSolm hspotter hdog hvow)
              have hret := clipperFileAddressX_vowOk (v := v) hpatch hperm hauthEvm
                hlockedEvm hnotSpotterWord hnotDogWord hvowWord hreachBody
              have hcreated :
                  (cA, sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨2⟩
                        (setAddressOffset0Word
                          (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩)
                            I ⟨2⟩) data))
                    ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
                simp [evm2, evmSolm, data, clipperFileAddressPostState,
                  clipperFileAddressLockedState, initState, storageStore_createdAccounts]
              have haccounts :
                  accountMapEquiv
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner
                        (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨2⟩
                          (setAddressOffset0Word
                            (solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨2⟩)
                            data))
                      ⟨13⟩ ⟨0⟩)
                    evm2.accountMap := by
                simpa [evm2, evmSolm, data] using
                  (clipperFileAddressPostState_accountMapEquiv
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                    (g := Sat256.ofUInt256 g) (slot := ⟨2⟩) (data := data)
                    hAccounts)
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                hcreated haccounts henc
            · have hnotVowWord :
                  calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressVowBytes :=
                clipperFileAddressWhatWord_ne_of_bytes_ne (I := I)
                  (bs := clipperFileAddressVowBytes) (by omega) hvow (by native_decide)
              by_cases hcalc : clipperFileAddressWhat I = clipperFileAddressCalcBytes
              · have hcalcWord :
                    calldataWord I.calldata 4 = ABI.bytesToWord clipperFileAddressCalcBytes := by
                  rw [← clipperFileAddressWhatWord_eq (I := I) (by omega), hcalc]
                let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                let evm2 := clipperFileAddressPostState evmSolm ⟨4⟩ data
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm locals
                      fileAddressTransition.body
                      (.returned { contract := contract v, locals := locals } evm2 none) := by
                  simpa [evmSolm, evm2, locals, data] using
                    (clipperFileAddressCalcSourceBody (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
                      hauthSolm hlockedSolm hspotter hdog hvow hcalc)
                have hret := clipperFileAddressX_calcOk (v := v) hpatch hperm hauthEvm
                  hlockedEvm hnotSpotterWord hnotDogWord hnotVowWord hcalcWord hreachBody
                have hcreated :
                    (cA, sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner
                        (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨4⟩
                          (setAddressOffset0Word
                            (solcSlotWord
                              (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨4⟩)
                            data))
                      ⟨13⟩ ⟨0⟩).1 = evm2.createdAccounts := by
                  simp [evm2, evmSolm, data, clipperFileAddressPostState,
                    clipperFileAddressLockedState, initState, storageStore_createdAccounts]
                have haccounts :
                    accountMapEquiv
                      (sstoreAccountMap I.codeOwner
                        (sstoreAccountMap I.codeOwner
                          (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) ⟨4⟩
                            (setAddressOffset0Word
                              (solcSlotWord
                                (sstoreAccountMap I.codeOwner σ_evm ⟨13⟩ ⟨1⟩) I ⟨4⟩)
                              data))
                        ⟨13⟩ ⟨0⟩)
                      evm2.accountMap := by
                  simpa [evm2, evmSolm, data] using
                    (clipperFileAddressPostState_accountMapEquiv
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g) (slot := ⟨4⟩) (data := data)
                      hAccounts)
                exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode
                  hbody hcreated haccounts henc
              · have hnotCalcWord :
                    calldataWord I.calldata 4 ≠ ABI.bytesToWord clipperFileAddressCalcBytes :=
                  clipperFileAddressWhatWord_ne_of_bytes_ne (I := I)
                    (bs := clipperFileAddressCalcBytes) (by omega) hcalc (by native_decide)
                let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm locals
                      fileAddressTransition.body .reverted := by
                  simpa [evmSolm, locals] using
                    (clipperFileAddressUnrecognizedSourceBody (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) v hwv hauthSolm hlockedSolm hspotter hdog hvow hcalc)
                obtain ⟨_, _, rd6840⟩ := hreachBody
                obtain ⟨_, _, rd6922⟩ :=
                  clipperFileAddressX_authorized (v := v) hpatch hauthEvm rd6840
                obtain ⟨_, _, rd6999⟩ :=
                  clipperFileAddressX_lockOpen (v := v) hpatch hlockedEvm rd6922
                obtain ⟨_, _, rd7005⟩ :=
                  clipperFileAddressX_lockStore (v := v) hpatch hperm rd6999
                obtain ⟨_, _, rd7054⟩ :=
                  clipperFileAddressX_spotterSkip (v := v) hpatch hnotSpotterWord rd7005
                obtain ⟨_, _, rd7100⟩ :=
                  clipperFileAddressX_dogSkipFrom (v := v) hpatch hnotDogWord rd7054
                obtain ⟨_, _, rd7146⟩ :=
                  clipperFileAddressX_vowSkipFrom (v := v) hpatch hnotVowWord rd7100
                obtain ⟨_, _, rd2988⟩ :=
                  clipperFileAddressX_calcSkipFrom (v := v) hpatch hnotCalcWord rd7146
                have hrev := clipperFileAddressX_unrecognized (v := v) hpatch rd2988
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hlockedSolm : solcSlotWord σ_solm I ⟨13⟩ ≠ ⟨0⟩ := by
          intro hsolm
          exact hlockedEvm (by rw [hlockWord, hsolm])
        let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody (config v) (contract v) evmSolm locals
              fileAddressTransition.body .reverted := by
          simpa [evmSolm, locals] using
            (clipperFileAddressLockedSourceReverts (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv
              hauthSolm hlockedSolm)
        obtain ⟨_, _, rd6840⟩ := hreachBody
        obtain ⟨_, _, rd6922⟩ :=
          clipperFileAddressX_authorized (v := v) hpatch hauthEvm rd6840
        have hrev := clipperFileAddressX_locked (v := v) hpatch hlockedEvm rd6922
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : clipperRelyAuthWord σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hauthWord, hsolm])
      let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evmSolm locals
            fileAddressTransition.body .reverted := by
        simpa [evmSolm, locals] using
          (clipperFileAddressAuthSourceReverts (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hwv hauthSolm)
      obtain ⟨_, _, rd6840⟩ := hreachBody
      have hrev := clipperFileAddressX_unauthorized (v := v) hpatch hauthEvm rd6840
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hrev := clipperFileAddressX_shortarg (v := v) hpatch hsz4 hsize hshort hreachEntry
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (clipperDecode_fileAddress_none_short v hsz4 hshort)

end Benchmarks.Dss.Clipper
