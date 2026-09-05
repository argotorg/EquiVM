import Benchmarks.Dss.Clipper.KickBase
import Benchmarks.Dss.Clipper.Arithmetic
import Benchmarks.Dss.Clipper.Guards

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

macro "clipper_kick_jumpdest " v:term : tactic =>
  `(tactic|
    (apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9500) (by assumption)
     unfold patches patchesFrom offsets immValues
     simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
     cases hIlk : wordBytes? ($v).ilk with
     | none =>
         simp [hIlk]
         native_decide
     | some bs =>
         simp [hIlk]
         native_decide))

theorem clipperKickJumpDest5443 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5443⟩ : UInt256) = true := by
  clipper_kick_jumpdest v

theorem clipperKickJumpDest5520 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5520⟩ : UInt256) = true := by
  clipper_kick_jumpdest v

theorem clipperKickJumpDest5609 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5609⟩ : UInt256) = true := by
  clipper_kick_jumpdest v

theorem clipperKickJumpDest5681 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5681⟩ : UInt256) = true := by
  clipper_kick_jumpdest v

theorem clipperKickJumpDest5753 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5753⟩ : UInt256) = true := by
  clipper_kick_jumpdest v

theorem clipperKickJumpDest5831 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5831⟩ : UInt256) = true := by
  clipper_kick_jumpdest v

theorem clipperKickJumpDest5913 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5913⟩ : UInt256) = true := by
  clipper_kick_jumpdest v

theorem clipperKickJumpDest8728 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8728⟩ : UInt256) = true := by
  clipper_kick_jumpdest v

set_option maxHeartbeats 1500000 in
theorem clipperKickX_authCheck {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (_hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨5361⟩
      (clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨5381⟩
      (UInt256.eq ⟨1⟩ (clipperRelyAuthWord σ I) :: ⟨0⟩ ::
        clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperRelyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (clipperRelySourceWord I) ⟨0⟩ := by
    simpa [clipperRelyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (clipperRelySourceWord I)
        solcFreePtrMem_size
  have rd5367pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw caller (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5368 := rd5367pre.mstore 0
    (wordAt0Mem (clipperRelySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5372pre := evm_run rd5368 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd5373 := rd5372pre.mstore 0 (clipperRelyAuthHashMem I)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5376pre := evm_run rd5373 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5377 := rd5376pre.keccak256 0 (mapSlot (clipperRelySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k5378, C5378, rd5378raw⟩ := rd5377.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd5378 : RD code I g s0 ⟨5378⟩
      (clipperRelyAuthWord σ I :: ⟨0⟩ :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I :: clipperKickTabWord I ::
        ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k5378 C5378 := by
    simpa [clipperRelyAuthWord, solcSlotWord,
      clipperRelyAuthStorageSlot_eq_mapSlot_source I] using rd5378raw
  have rd5381 := evm_run rd5378 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd5381⟩

theorem clipperKickX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I = ⟨1⟩)
    (h : RD code I g s0 ⟨5361⟩
      (clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨5443⟩
      (⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd5381⟩ := clipperKickX_authCheck v hpatch h
  rw [hauth, u256_eq_refl] at rd5381
  have rd5384 := rd5381.pushConst (⟨5443⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, rd5384.jumpiT (by clipper_runtime_decode) one_ne_zero_uint
    (clipperKickJumpDest5443 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperKickX_lockOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (h : RD code I g s0 ⟨5443⟩
      (⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨5520⟩
      (⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd5446 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k5447, C5447, rd5447raw⟩ := rd5446.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd5447 : RD code I g s0 ⟨5447⟩
      (solcSlotWord σ I ⟨13⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I :: clipperKickTabWord I ::
        ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k5447 C5447 := by
    simpa [solcSlotWord] using rd5447raw
  have rd5448 := rd5447.iszero (by clipper_runtime_decode) (by evm_ov)
  have hcond : UInt256.isZero (solcSlotWord σ I ⟨13⟩) ≠ ⟨0⟩ := by
    rw [hlocked]
    native_decide
  have rd5451 := rd5448.pushConst (⟨5520⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, rd5451.jumpiT (by clipper_runtime_decode) hcond
    (clipperKickJumpDest5520 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperKickX_lockAndStoppedOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hstopped : (solcSlotWord
      (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat < 1)
    (h : RD code I g s0 ⟨5520⟩
      (⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨5609⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) k' C' := by
  have rd5527pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5528⟩ := rd5527pre.sstore hperm
    (by clipper_runtime_decode) (by evm_ov)
  have rd5530 := rd5528.pushConst (⟨14⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  obtain ⟨k5531, C5531, rd5531raw⟩ := rd5530.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd5531 : RD code I g s0 ⟨5531⟩
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩ ::
        ⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) k5531 C5531 := by
    simpa [solcSlotWord] using rd5531raw
  have rd5532 := rd5531.dup2 (by clipper_runtime_decode) (by evm_ov)
  have rd5533 := rd5532.gt (by clipper_runtime_decode) (by evm_ov)
  have hgt :
      UInt256.gt (⟨1⟩ : UInt256)
        (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩) =
        ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
    exact hstopped
  rw [hgt] at rd5533
  have rd5536 := rd5533.pushConst (⟨5609⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, rd5536.jumpiT (by clipper_runtime_decode) one_ne_zero_uint
    (clipperKickJumpDest5609 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1500000 in
theorem clipperKickX_tabPositive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (htab : 0 < (clipperKickTabWord I).toNat)
    (h : RD code I g s0 ⟨5609⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨5681⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have htabGt : UInt256.gt (clipperKickTabWord I) ⟨0⟩ = ⟨1⟩ :=
    ugt_one (by simpa using htab)
  have rd5617 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov)]
  rw [htabGt] at rd5617
  have rd5681 := (rd5617.push2 ⟨5681⟩ (by clipper_runtime_decode) (by evm_ov)).jumpiT
    (by clipper_runtime_decode) one_ne_zero_uint
    (clipperKickJumpDest5681 v hpatch) (by evm_ov)
  exact ⟨_, _, rd5681⟩

private theorem clipperKickX_lotPositiveCore {code : ByteArray} {I : ExecutionEnv}
    {g : Sat256} {s0 : State} {k C : ℕ} {one zero kpr usr lot : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code I g s0 ⟨5681⟩ (one :: zero :: kpr :: usr :: lot :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hlotGt : UInt256.gt lot ⟨0⟩ = ⟨1⟩)
    (hov : R.length + 7 ≤ 1024)
    (hd5681 : decode code ⟨5681⟩ = some (.JUMPDEST, .none))
    (hd5682 : decode code ⟨5682⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd5684 : decode code ⟨5684⟩ = some (.DUP6, .none))
    (hd5685 : decode code ⟨5685⟩ = some (.GT, .none))
    (hd5686 : decode code ⟨5686⟩ = some (.Push .PUSH2, some (⟨5753⟩, 2)))
    (hd5689 : decode code ⟨5689⟩ = some (.JUMPI, .none))
    (hjump : (D_J code 0).contains (⟨5753⟩ : UInt256) = true) :
    ∃ k' C', RD code I g s0 ⟨5753⟩ (one :: zero :: kpr :: usr :: lot :: R)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
  have rd5689 := evm_run h with [
    raw jumpdest hd5681 (by evm_ov),
    raw push1 ⟨0⟩ hd5682 (by evm_ov),
    raw dup6 hd5684 (by evm_ov),
    raw gt hd5685 (by evm_ov)]
  rw [hlotGt] at rd5689
  have rd5753 := (rd5689.push2 ⟨5753⟩
    hd5686 (by evm_ov)).jumpiT hd5689 one_ne_zero_uint hjump (by evm_ov)
  exact ⟨_, _, rd5753⟩

set_option maxHeartbeats 1500000 in
theorem clipperKickX_lotPositive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlot : 0 < (clipperKickLotWord I).toNat)
    (h : RD code I g s0 ⟨5681⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨5753⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hlotGt : UInt256.gt (clipperKickLotWord I) ⟨0⟩ = ⟨1⟩ :=
    ugt_one (by simpa using hlot)
  apply clipperKickX_lotPositiveCore h hlotGt (by simp)
  · exact clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  · exact clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  · exact clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  · exact clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  · exact clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  · exact clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  · exact clipperKickJumpDest5753 v hpatch

set_option maxHeartbeats 1500000 in
theorem clipperKickX_usrPositive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (husr : clipperKickUsrMaskedWord I ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨5753⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨5831⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by native_decide
  have husrCanonical :
      (clipperKickUsrMaskedWord I).toNat < EVM.addressModulus := by
    simpa [clipperKickUsrMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (clipperKickUsrWord I)
  have rd5764 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov)]
  rw [hmask, solcAddrMask_clean husrCanonical] at rd5764
  have rd5767 := rd5764.push2 ⟨5831⟩ (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, rd5767.jumpiT (by clipper_runtime_decode) husr
    (clipperKickJumpDest5831 v hpatch) (by evm_ov)⟩

end Benchmarks.Dss.Clipper
