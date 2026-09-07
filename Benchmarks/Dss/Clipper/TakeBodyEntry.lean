import Benchmarks.Dss.Clipper.Arithmetic
import Benchmarks.Dss.Clipper.GetStatus
import Benchmarks.Dss.Clipper.GetStatusEVM
import Benchmarks.Dss.Clipper.GetStatusEVMReverts
import Benchmarks.Dss.Clipper.GetStatusReverts
import Benchmarks.Dss.Clipper.Guards
import Benchmarks.Dss.Clipper.Sales
import Benchmarks.Dss.Clipper.StatusPriceCall
import Benchmarks.Dss.Clipper.Take
import Benchmarks.Dss.Clipper.TakeOweVatMoveSource
import Benchmarks.Dss.Clipper.TakePostDogRemoveSource
import Benchmarks.Dss.Clipper.TakeStatus
import Benchmarks.Dss.Clipper.TakeDogDigs
import Benchmarks.Dss.Clipper.TakeCallbackEquiv
import Benchmarks.Dss.Clipper.TakeDynamicPostDog
import Benchmarks.Dss.Clipper.TakeDynamicRemove

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem clipperTakeX_decode_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hoffMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataOffsetWord I).toNat)
    (hlenMax : ¬ solcMaxLen DecodeMode.legacySolc05 < (clipperTakeDataLenWord I).toNat)
    (hpayloadGt :
      UInt256.gt
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) +
          UInt256.mul (clipperTakeDataLenWord I) ⟨1⟩))
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨0⟩)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1012⟩ : UInt256)
      (((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I) ::
        ((⟨4⟩ : UInt256) + (⟨160⟩ : UInt256)) :: (⟨4⟩ : UInt256) ::
        ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨3527⟩ : UInt256)
      (clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1012⟩ := hreach
  have hload := clipperTakeDataLenLoad_eq (I := I) hoffMax
  have hlenGt := clipperTakeDataLenGt_zero (I := I) hlenMax
  have rd1028 := evm_run rd1012 with [
    raw jumpdest
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw calldataload
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw mul
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have hd1028 : decode code (⟨1028⟩ : UInt256) =
      some (.Push .PUSH5, some ((⟨4294967296⟩ : UInt256), 5)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨1028⟩ : UInt256) (by native_decide)]
    native_decide
  have rd1034 := rd1028.pushConst (⟨4294967296⟩ : UInt256)
    (width := 5) (op := .PUSH5) (by decide) hd1028 (by evm_ov)
  have rd1041 := evm_run rd1034 with [
    raw dup4
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw gt
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw or
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw iszero
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨1046⟩
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd1046 := rd1041.jumpiT
    (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
    (by rw [hload, hlenGt, hpayloadGt]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨1046⟩ : UInt256) (by native_decide))
    (by evm_ov)
  have rd1053 := evm_run rd1046 with [
    raw jumpdest
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
      (by evm_ov)]
  have hd1053 : decode code (⟨1053⟩ : UInt256) =
      some (.Push .PUSH2, some ((⟨3527⟩ : UInt256), 2)) := by
    rw [clipperDecodeBeforeFirstPatch v hpatch (⟨1053⟩ : UInt256) (by native_decide)]
    native_decide
  have rd1056 := rd1053.pushConst (⟨3527⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) hd1053 (by evm_ov)
  have rd3527 := rd1056.jump
    (by rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]; native_decide)
    (clipperTakeJumpDest3527 v hpatch)
    (by evm_ov)
  rw [hload] at rd3527
  exact ⟨_, _, rd3527⟩

set_option maxHeartbeats 1000000 in
theorem clipperTakeX_locked {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨3527⟩
      (clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd3530pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k3531, C3531, rd3531raw⟩ := rd3530pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd3531 : RD code I g s0 ⟨3531⟩
      (solcSlotWord σ I ⟨13⟩ :: clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3531 C3531 := by
    simpa [solcSlotWord] using rd3531raw
  have rd3532pre := rd3531.iszero (by clipper_runtime_decode) (by evm_ov)
  rw [isZero_eq_zero_of_ne hlocked] at rd3532pre
  have rd3535 := rd3532pre.pushConst (⟨3604⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd3536 := rd3535.jumpiNT (by clipper_runtime_decode)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail rd3536
    (clipperTakeLockRevertTailWf v hpatch)
    (by decide)
    clipperTakeLockedStringWord
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by norm_num [List.length])

set_option maxHeartbeats 1000000 in
theorem clipperTakeX_lockOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hlocked : solcSlotWord σ I ⟨13⟩ = ⟨0⟩)
    (h : RD code I g s0 ⟨3527⟩
      (clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3604⟩
      (clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3530pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k3531, C3531, rd3531raw⟩ := rd3530pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd3531 : RD code I g s0 ⟨3531⟩
      (solcSlotWord σ I ⟨13⟩ :: clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3531 C3531 := by
    simpa [solcSlotWord] using rd3531raw
  have rd3532 := rd3531.iszero (by clipper_runtime_decode) (by evm_ov)
  have hcond : UInt256.isZero (solcSlotWord σ I ⟨13⟩) ≠ ⟨0⟩ := by
    rw [hlocked]
    native_decide
  have rd3535 := rd3532.pushConst (⟨3604⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, rd3535.jumpiT (by clipper_runtime_decode) hcond
    (clipperTakeJumpDest3604 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperTakeX_lockStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨3604⟩
      (clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3610⟩
      (clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨13⟩ ⟨1⟩) k' C' := by
  have rd3609pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd3610raw⟩ := rd3609pre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd3610raw⟩

set_option maxHeartbeats 1000000 in
theorem clipperTakeX_stoppedClosed {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hstopped : 3 ≤ (solcSlotWord σ I ⟨14⟩).toNat)
    (h : RD code I g s0 ⟨3610⟩
      (clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rd3612pre := h.pushConst (⟨14⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  obtain ⟨k3613, C3613, rd3613raw⟩ := rd3612pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd3613 : RD code I g s0 ⟨3613⟩
      (solcSlotWord σ I ⟨14⟩ :: clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3613 C3613 := by
    simpa [solcSlotWord] using rd3613raw
  have rd3615 := rd3613.pushConst (⟨3⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd3616 := rd3615.swap1 (by clipper_runtime_decode) (by evm_ov)
  have rd3617 := rd3616.dup2 (by clipper_runtime_decode) (by evm_ov)
  have rd3618 := rd3617.gt (by clipper_runtime_decode) (by evm_ov)
  have hgt : UInt256.gt (⟨3⟩ : UInt256) (solcSlotWord σ I ⟨14⟩) = ⟨0⟩ := by
    exact ugt_zero (by simpa using hstopped)
  rw [hgt] at rd3618
  have rd3621 := rd3618.pushConst (⟨3694⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd3622 := rd3621.jumpiNT (by clipper_runtime_decode)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail rd3622
    (clipperTakeStoppedRevertTailWf v hpatch)
    (by decide)
    clipperTakeStoppedStringWord
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by norm_num [List.length])

set_option maxHeartbeats 1000000 in
theorem clipperTakeX_stoppedOpen {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hstopped : (solcSlotWord σ I ⟨14⟩).toNat < 3)
    (h : RD code I g s0 ⟨3610⟩
      (clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3694⟩
      ((⟨3⟩ : UInt256) :: clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3612pre := h.pushConst (⟨14⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  obtain ⟨k3613, C3613, rd3613raw⟩ := rd3612pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd3613 : RD code I g s0 ⟨3613⟩
      (solcSlotWord σ I ⟨14⟩ :: clipperTakeDataLenWord I ::
        (((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        ((clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I ::
        (⟨502⟩ : UInt256) :: [sel]))
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3613 C3613 := by
    simpa [solcSlotWord] using rd3613raw
  have rd3615 := rd3613.pushConst (⟨3⟩ : UInt256)
    (width := 1) (op := .PUSH1) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd3616 := rd3615.swap1 (by clipper_runtime_decode) (by evm_ov)
  have rd3617 := rd3616.dup2 (by clipper_runtime_decode) (by evm_ov)
  have rd3618 := rd3617.gt (by clipper_runtime_decode) (by evm_ov)
  have hgt : UInt256.gt (⟨3⟩ : UInt256) (solcSlotWord σ I ⟨14⟩) = ⟨1⟩ := by
    exact ugt_one (by
      rw [show (⟨3⟩ : UInt256).toNat = 3 from by decide]
      exact hstopped)
  rw [hgt] at rd3618
  have rd3621 := rd3618.pushConst (⟨3694⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, rd3621.jumpiT (by clipper_runtime_decode)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (clipperTakeJumpDest3694 v hpatch) (by evm_ov)⟩

abbrev clipperTakeNotRunningAuctionWord : UInt256 :=
  ⟨0x436c69707065722f6e6f742d72756e6e696e672d61756374696f6e0000000000⟩

set_option maxHeartbeats 1000000 in
theorem clipperTakeX_inactiveAuctionTail {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {stk : List UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hstk : stk.length + 8 < 1024)
    (h : RD code I g s0 ⟨3745⟩ stk
      (clipperTakeSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_runtime_decode)
      mem_cost
      (mloadFreePtrValue (by rw [clipperTakeSalesHashMem_size I]; decide)
        (by decide) (clipperTakeSalesHashMem_read64 I))
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 (clipperTakeSalesHashMem I))
      (UInt256.ofNat 5) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 (clipperTakeSalesHashMem I))
      (UInt256.ofNat 6) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ (clipperTakeSalesHashMem I))
      (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst clipperTakeNotRunningAuctionWord
    (width := 32) (op := .PUSH32) (by decide) (by clipper_runtime_decode)
    (by evm_ov)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3
      (solcErrorStringMem3 ⟨27⟩ clipperTakeNotRunningAuctionWord
        (clipperTakeSalesHashMem I))
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ clipperTakeNotRunningAuctionWord
        (clipperTakeSalesHashMem_size I) (clipperTakeSalesHashMem_read64 I))
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem clipperTakeX_usrZero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (husr : clipperTakeSalesUsrWord σ I = ⟨0⟩)
    (h : RD code I g s0 ⟨3694⟩
      [(⟨3⟩ : UInt256), clipperTakeDataLenWord I,
        (⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I),
        (clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩),
        clipperTakeMaxWord I, clipperTakeAmtWord I, clipperTakeIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev code g s0 := by
  let base : UInt256 := solcMappingSlot ⟨12⟩ (clipperTakeIdWord I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperTakeSalesHashMem I).readWithPadding 0 64))) =
        base := by
    simpa [clipperTakeSalesHashMem, base] using
      twoWordHashMem_solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) solcFreePtrMem_size
  have rd3698pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd3699 := rd3698pre.mstore 0
    (wordAt0Mem (clipperTakeIdWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3704pre := evm_run rd3699 with [
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd3705 := rd3704pre.mstore 0 (clipperTakeSalesHashMem I)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3708pre := evm_run rd3705 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd3709 := rd3708pre.keccak256 0 base
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd3712pre := evm_run rd3709 with [
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [u256_add_comm ⟨3⟩ base] at rd3712pre
  have hpackedSlot : base + ⟨3⟩ = clipperTakeSalesPackedSlot I := by
    change base + ⟨3⟩ = clipperTakeSalesBaseSlot I + ⟨3⟩
    rw [clipperTakeSalesBaseSlot_eq I]
  rw [hpackedSlot] at rd3712pre
  obtain ⟨k3713, C3713, rd3713raw⟩ := rd3712pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd3713 : RD code I g s0 ⟨3713⟩
      (solcSlotWord σ I (clipperTakeSalesPackedSlot I) :: ⟨3⟩ ::
        clipperTakeDataLenWord I ::
        ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        (clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I :: ⟨502⟩ ::
        [sel])
      (clipperTakeSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k3713 C3713 := by
    simpa [clipperTakeSalesPackedSlot, solcSlotWord] using rd3713raw
  have rd3741pre := evm_run rd3713 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd3741pre
  have rd3744 := rd3741pre.pushConst (⟨3821⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have husrStack :
      UInt256.land (solcSlotWord σ I (clipperTakeSalesPackedSlot I)) solcAddrMask =
        ⟨0⟩ := by
    simpa [clipperTakeSalesUsrWord, u256_land_comm] using husr
  have rd3745 := rd3744.jumpiNT (by clipper_runtime_decode) husrStack (by evm_ov)
  exact clipperTakeX_inactiveAuctionTail (v := v) hpatch
    (by norm_num [List.length]) rd3745

set_option maxHeartbeats 2000000 in
theorem clipperTakeX_usrNonzero {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (husr : clipperTakeSalesUsrWord σ I ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨3694⟩
      [(⟨3⟩ : UInt256), clipperTakeDataLenWord I,
        (⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I),
        (clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩),
        clipperTakeMaxWord I, clipperTakeAmtWord I, clipperTakeIdWord I, ⟨502⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨3821⟩
      [clipperTakeSalesTicStackWord σ I,
        (solcSlotWord σ I (clipperTakeSalesPackedSlot I)).land solcAddrMask, ⟨3⟩,
        clipperTakeDataLenWord I,
        (⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I),
        (clipperTakeWhoWord I).land solcAddrMask, clipperTakeMaxWord I, clipperTakeAmtWord I,
        clipperTakeIdWord I, ⟨502⟩, sel]
      (clipperTakeSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let base : UInt256 := solcMappingSlot ⟨12⟩ (clipperTakeIdWord I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperTakeSalesHashMem I).readWithPadding 0 64))) =
        base := by
    simpa [clipperTakeSalesHashMem, base] using
      twoWordHashMem_solcMappingSlot ⟨12⟩ (clipperTakeIdWord I) solcFreePtrMem_size
  have rd3698pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd3699 := rd3698pre.mstore 0
    (wordAt0Mem (clipperTakeIdWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3704pre := evm_run rd3699 with [
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd3705 := rd3704pre.mstore 0 (clipperTakeSalesHashMem I)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3708pre := evm_run rd3705 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd3709 := rd3708pre.keccak256 0 base
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd3712pre := evm_run rd3709 with [
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [u256_add_comm ⟨3⟩ base] at rd3712pre
  have hpackedSlot : base + ⟨3⟩ = clipperTakeSalesPackedSlot I := by
    change base + ⟨3⟩ = clipperTakeSalesBaseSlot I + ⟨3⟩
    rw [clipperTakeSalesBaseSlot_eq I]
  rw [hpackedSlot] at rd3712pre
  obtain ⟨k3713, C3713, rd3713raw⟩ := rd3712pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd3713 : RD code I g s0 ⟨3713⟩
      (solcSlotWord σ I (clipperTakeSalesPackedSlot I) :: ⟨3⟩ ::
        clipperTakeDataLenWord I ::
        ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
        (clipperTakeWhoWord I).land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) ::
        clipperTakeMaxWord I :: clipperTakeAmtWord I :: clipperTakeIdWord I :: ⟨502⟩ ::
        [sel])
      (clipperTakeSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k3713 C3713 := by
    simpa [clipperTakeSalesPackedSlot, solcSlotWord] using rd3713raw
  have rd3741pre := evm_run rd3713 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd3741pre
  have rd3744 := rd3741pre.pushConst (⟨3821⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have husrStack :
      UInt256.land (solcSlotWord σ I (clipperTakeSalesPackedSlot I)) solcAddrMask ≠
        ⟨0⟩ := by
    simpa [clipperTakeSalesUsrWord, u256_land_comm] using husr
  have rd3821 := rd3744.jumpiT (by clipper_runtime_decode) husrStack
    (clipperTakeJumpDest3821 v hpatch) (by evm_ov)
  exact ⟨_, _, rd3821⟩

set_option maxHeartbeats 2000000 in
theorem clipperTakeX_enterStatus {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨3821⟩
      [clipperTakeSalesTicStackWord σ I,
        (solcSlotWord σ I (clipperTakeSalesPackedSlot I)).land solcAddrMask, ⟨3⟩,
        clipperTakeDataLenWord I,
        (⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I),
        (clipperTakeWhoWord I).land solcAddrMask, clipperTakeMaxWord I, clipperTakeAmtWord I,
        clipperTakeIdWord I, ⟨502⟩, sel]
      (clipperTakeSalesHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨8460⟩
      [clipperTakeSalesTopWord σ I, clipperTakeSalesTicStackWord σ I, ⟨3852⟩, ⟨0⟩,
        ⟨0⟩, clipperTakeSalesTicStackWord σ I,
        (solcSlotWord σ I (clipperTakeSalesPackedSlot I)).land solcAddrMask, ⟨3⟩,
        clipperTakeDataLenWord I,
        (⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I),
        (clipperTakeWhoWord I).land solcAddrMask, clipperTakeMaxWord I, clipperTakeAmtWord I,
        clipperTakeIdWord I, ⟨502⟩, sel]
      (clipperTakeSalesTopHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let base : UInt256 := solcMappingSlot ⟨12⟩ (clipperTakeIdWord I)
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperTakeSalesTopHashMem I).readWithPadding 0 64))) =
        base := by
    have hmem : 64 ≤ (clipperTakeSalesHashMem I).size := by
      rw [clipperTakeSalesHashMem_size I]
      norm_num
    simpa [clipperTakeSalesTopHashMem, base] using
      twoWordHashMem_solcMappingSlot_of_ge ⟨12⟩ (clipperTakeIdWord I)
        (mem := clipperTakeSalesHashMem I) hmem
  have rd3826pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup10 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd3827 := rd3826pre.mstore 0
    (wordAt0Mem (clipperTakeIdWord I) (clipperTakeSalesHashMem I))
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3831pre := evm_run rd3827 with [
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd3832 := rd3831pre.mstore 0 (clipperTakeSalesTopHashMem I)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd3835 := evm_run rd3832 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost hslot
      (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [u256_add_comm ⟨4⟩ base] at rd3835
  have htopSlot : base + ⟨4⟩ = clipperTakeSalesTopSlot I := by
    change base + ⟨4⟩ = clipperTakeSalesBaseSlot I + ⟨4⟩
    rw [clipperTakeSalesBaseSlot_eq I]
  rw [htopSlot] at rd3835
  obtain ⟨k3840, C3840, rd3840raw⟩ := rd3835.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd3840 : RD code I g s0 ⟨3840⟩
      (clipperTakeSalesTopWord σ I :: ⟨0⟩ :: clipperTakeSalesTicStackWord σ I ::
        (solcSlotWord σ I (clipperTakeSalesPackedSlot I)).land solcAddrMask :: ⟨3⟩ ::
        clipperTakeDataLenWord I ::
        ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + clipperTakeDataOffsetWord I)) ::
      (clipperTakeWhoWord I).land solcAddrMask :: clipperTakeMaxWord I ::
      clipperTakeAmtWord I :: clipperTakeIdWord I :: ⟨502⟩ :: [sel])
      (clipperTakeSalesTopHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k3840 C3840 := by
    simpa [clipperTakeSalesTopWord, solcSlotWord] using rd3840raw
  have rd8460pre := evm_run rd3840 with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨3852⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8460⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd8460pre.jump (by clipper_runtime_decode)
    (clipperJumpDest8460 v hpatch) (by evm_ov)⟩

end Benchmarks.Dss.Clipper
