import Benchmarks.Dss.Clipper.KickSourceReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

macro "kick_error_tail" : tactic =>
  `(tactic|
    (unfold solcErrorStringRevertTailWf
     dsimp
     refine
       ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩ <;> (norm_num1; clipper_runtime_decode)))

theorem clipperKickLockRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨5452⟩ ⟨21⟩
      ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩ .PUSH21 21 := by
  kick_error_tail

theorem clipperKickStoppedRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨5537⟩ ⟨25⟩
      ⟨105806016908988270734738552397420409440386134862091135834333⟩ ⟨58⟩
      .PUSH25 25 := by
  kick_error_tail

theorem clipperKickTabRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨5618⟩ ⟨16⟩
      ⟨44810591169829335862402008347737469105⟩ ⟨129⟩ .PUSH16 16 := by
  kick_error_tail

theorem clipperKickLotRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨5690⟩ ⟨16⟩
      ⟨22405295584914667931201004173868604381⟩ ⟨130⟩ .PUSH16 16 := by
  kick_error_tail

theorem clipperKickUsrRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨5768⟩ ⟨16⟩
      ⟨44810591169829335862402008347737504185⟩ ⟨129⟩ .PUSH16 16 := by
  kick_error_tail

theorem clipperKickOverflowRevertTailWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨5850⟩ ⟨16⟩
      ⟨89621182339658671724016153955851333495⟩ ⟨128⟩ .PUSH16 16 := by
  kick_error_tail

set_option maxHeartbeats 1500000

set_option maxHeartbeats 1500000 in
theorem clipperKickX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hauth : clipperRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD code I g s0 ⟨5361⟩
      (clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd5381⟩ := clipperKickX_authCheck v hpatch h
  have heq : UInt256.eq ⟨1⟩ (clipperRelyAuthWord σ I) = ⟨0⟩ :=
    u256_eq_of_ne (by intro he; exact hauth he.symm)
  rw [heq] at rd5381
  have rd5385 := (rd5381.push2 ⟨5443⟩ (by clipper_runtime_decode) (by evm_ov)).jumpiNT
    (by clipper_runtime_decode) rfl (by evm_ov)
  have rd5389 := evm_run rd5385 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost
      (mloadFreePtrValue (by rw [clipperRelyAuthHashMem_size]; decide)
        (by decide) (clipperRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov)]
  have rd5393 := rd5389.pushConst ⟨4594637⟩ (width := 3) (op := .PUSH3)
    (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd5396 := evm_run rd5393 with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [clipperRelyNotAuthorizedWord] at rd5396
  have rd5398pre := rd5396.dup2 (by clipper_runtime_decode) (by evm_ov)
  have rd5398 := rd5398pre.mstore 6 (solcErrorStringMem0 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 5) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5405pre := evm_run rd5398 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have rd5405 := rd5405pre.mstore 3 (solcErrorStringMem1 (clipperRelyAuthHashMem I))
    (UInt256.ofNat 6) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd5416pre := evm_run rd5405 with [
    raw push1 ⟨22⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (clipperRelyErrorMem2 I) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperRelySourceWord I) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (clipperRelyErrorMem2_mload0 I)
      (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd5421 := rd5416pre.push2 ⟨9316⟩ (by clipper_runtime_decode) (by evm_ov)
  have rd5423pre := rd5421.dup4 (by clipper_runtime_decode) (by evm_ov)
  have rd5423 := rd5423pre.codecopy 0 (clipperRelyErrorCopiedMem code I)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by rw [show (⟨9316⟩ : UInt256).toNat = 9316 by decide,
      show (⟨32⟩ : UInt256).toNat = 32 by decide]; rfl)
    (by native_decide) (by evm_ov)
  have rd5427 := evm_run rd5423 with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 clipperRelyNotAuthorizedStringWord (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost
      (by simpa [clipperRelyErrorCopiedMem, clipperRelyErrorMem2] using
        clipperRelyCodecopyMload0 v hpatch I)
      (by native_decide) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5427 := rd5427.mstore 0 (clipperRelyErrorRestoredMem code I)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by simp [clipperRelyErrorRestoredMem, clipperRelyErrorCopiedMem])
    (by native_decide) (by evm_ov)
  have rd5432pre := evm_run rd5427 with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have rd5432 := rd5432pre.mstore 3 (clipperRelyErrorStringMem code I)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by decide])
    (by native_decide) (by evm_ov)
  have rd5435 := evm_run rd5432 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
      (clipperRelyErrorStringMem_mload64 v hpatch I)
      (by native_decide) (by evm_ov)]
  exact evm_run rd5435 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem clipperKickX_locked {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨5443⟩
      (⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd5446pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5447raw⟩ := rd5446pre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd5447 := show RD code I g s0 ⟨5447⟩
      (solcSlotWord σ I ⟨13⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I :: clipperKickTabWord I ::
        ⟨476⟩ :: [sel]) (clipperRelyAuthHashMem I) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) _ _ from by simpa [solcSlotWord] using rd5447raw
  have rd5452 := (rd5447.iszero (by clipper_runtime_decode) (by evm_ov)).push2 ⟨5520⟩
    (by clipper_runtime_decode) (by evm_ov) |>.jumpiNT
      (by clipper_runtime_decode) (isZero_eq_zero_of_ne hlocked) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (word := UInt256.shiftLeft
      ⟨24634883019371952566956220926897864252907853633881⟩ ⟨90⟩)
    rd5452 (clipperKickLockRevertTailWf v hpatch)
    (by decide) (by native_decide) (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I) (by simp)

set_option maxHeartbeats 1000000 in
theorem clipperKickX_stopped {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hstopped : 1 ≤ (solcSlotWord
      (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩).toNat)
    (h : RD code I g s0 ⟨5520⟩
      (⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd5527pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5528⟩ := rd5527pre.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  have rd5530 := rd5528.push1 ⟨14⟩ (by clipper_runtime_decode) (by evm_ov)
  obtain ⟨_, _, rd5531raw⟩ := rd5530.sload (by clipper_runtime_decode) (by evm_ov)
  have rd5531 := show RD code I g s0 ⟨5531⟩
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩ ::
        ⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) _ _ from by
    simpa [solcSlotWord] using rd5531raw
  have hgt : UInt256.gt ⟨1⟩
      (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) I ⟨14⟩) = ⟨0⟩ :=
    ugt_zero (by simpa using hstopped)
  have rd5537 := evm_run rd5531 with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5609⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hgt] at rd5537
  have rd5537 := rd5537.jumpiNT (by clipper_runtime_decode) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (word := UInt256.shiftLeft
      ⟨105806016908988270734738552397420409440386134862091135834333⟩ ⟨58⟩)
    rd5537 (clipperKickStoppedRevertTailWf v hpatch)
    (by decide) (by native_decide) (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I) (by simp)

theorem clipperKickX_tabZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (htab : ¬ 0 < (clipperKickTabWord I).toNat)
    (h : RD code I g s0 ⟨5609⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have hgt : UInt256.gt (clipperKickTabWord I) ⟨0⟩ = ⟨0⟩ :=
    ugt_zero (by simpa using Nat.eq_zero_of_not_pos htab)
  have rd5618 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5681⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [hgt] at rd5618
  have rd5618 := rd5618.jumpiNT (by clipper_runtime_decode) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (word := UInt256.shiftLeft ⟨44810591169829335862402008347737469105⟩ ⟨129⟩)
    rd5618 (clipperKickTabRevertTailWf v hpatch)
    (by decide) (by native_decide) (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I) (by simp)

private theorem clipperKickX_lotZeroRaw {code : ByteArray} {I : ExecutionEnv}
    {g : Sat256} {s0 : State} {k C : ℕ} {one zero kpr usr lot : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code I g s0 ⟨5681⟩ (one :: zero :: kpr :: usr :: lot :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hgt : UInt256.gt lot ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024)
    (hd5681 : decode code ⟨5681⟩ = some (.JUMPDEST, .none))
    (hd5682 : decode code ⟨5682⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd5684 : decode code ⟨5684⟩ = some (.DUP6, .none))
    (hd5685 : decode code ⟨5685⟩ = some (.GT, .none))
    (hd5686 : decode code ⟨5686⟩ = some (.Push .PUSH2, some (⟨5753⟩, 2)))
    (hd5689 : decode code ⟨5689⟩ = some (.JUMPI, .none)) :
    ∃ k' C', RD code I g s0 ⟨5690⟩ (one :: zero :: kpr :: usr :: lot :: R)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
  have rd5689 := evm_run h with [
    raw jumpdest hd5681 (by evm_ov),
    raw push1 ⟨0⟩ hd5682 (by evm_ov),
    raw dup6 hd5684 (by evm_ov),
    raw gt hd5685 (by evm_ov)]
  rw [hgt] at rd5689
  have rd5689 := rd5689.push2 ⟨5753⟩ hd5686 hov
  exact ⟨_, _, rd5689.jumpiNT hd5689 rfl (by evm_ov)⟩

theorem clipperKickX_lotZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlot : ¬ 0 < (clipperKickLotWord I).toNat)
    (h : RD code I g s0 ⟨5681⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have hgt : UInt256.gt (clipperKickLotWord I) ⟨0⟩ = ⟨0⟩ :=
    ugt_zero (by simpa using Nat.eq_zero_of_not_pos hlot)
  obtain ⟨_, _, rd5690⟩ := clipperKickX_lotZeroRaw h hgt (by simp)
    (clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide))
    (clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide))
    (clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide))
    (clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide))
    (clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide))
    (clipperRuntimeDecodeDisjoint v hpatch
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide))
  exact RD.solcErrorStringRevertTail
    (word := UInt256.shiftLeft ⟨22405295584914667931201004173868604381⟩ ⟨130⟩)
    rd5690 (clipperKickLotRevertTailWf v hpatch)
    (by decide) (by native_decide) (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I) (by simp)

theorem clipperKickX_usrZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (husr : clipperKickUsrMaskedWord I = ⟨0⟩)
    (h : RD code I g s0 ⟨5753⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd5768 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5831⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask by native_decide, u256_land_comm, husr] at rd5768
  have rd5768 := rd5768.jumpiNT (by clipper_runtime_decode) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (word := UInt256.shiftLeft ⟨44810591169829335862402008347737504185⟩ ⟨129⟩)
    rd5768 (clipperKickUsrRevertTailWf v hpatch)
    (by decide) (by native_decide) (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I) (by simp)

set_option maxHeartbeats 1000000 in
theorem clipperKickX_idZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true) (hid : clipperKickIdWord σ I = ⟨0⟩)
    (h : RD code I g s0 ⟨5831⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd5835 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨10⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5836raw⟩ := rd5835.sload (by clipper_runtime_decode) (by evm_ov)
  have rd5836 := show RD code I g s0 ⟨5836⟩
      (solcSlotWord σ I ⟨10⟩ :: ⟨10⟩ :: ⟨1⟩ :: ⟨0⟩ ::
        clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ from by
    simpa [solcSlotWord] using rd5836raw
  have rd5842pre := evm_run rd5836 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5843⟩ := rd5842pre.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  have rd5850 := evm_run rd5843 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5913⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [show ⟨1⟩ + solcSlotWord σ I ⟨10⟩ = clipperKickIdWord σ I by
    rfl, hid] at rd5850
  have rd5850 := rd5850.jumpiNT (by clipper_runtime_decode) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (word := UInt256.shiftLeft ⟨89621182339658671724016153955851333495⟩ ⟨128⟩)
    rd5850 (clipperKickOverflowRevertTailWf v hpatch)
    (by decide) (by native_decide) (clipperRelyAuthHashMem_size I)
    (clipperRelyAuthHashMem_read64 I) (by simp)

end Benchmarks.Dss.Clipper
