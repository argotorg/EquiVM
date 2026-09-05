import Benchmarks.Dss.Clipper.KickPrefixEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

abbrev clipperKickIdWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  ⟨1⟩ + solcSlotWord σ I ⟨10⟩

abbrev clipperKickIdMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨10⟩ (clipperKickIdWord σ I)

abbrev clipperKickActiveLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord (clipperKickIdMap σ I) I ⟨11⟩

abbrev clipperKickActiveLengthMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (clipperKickIdMap σ I) ⟨11⟩
    (clipperKickActiveLengthWord σ I + ⟨1⟩)

abbrev clipperKickActiveElemSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  clipperKickActiveLengthWord σ I + activeDataSlot

abbrev clipperKickActiveMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (clipperKickActiveLengthMap σ I)
    (clipperKickActiveElemSlot σ I) (clipperKickIdWord σ I)

/-- The length observed after the element store. Keeping this as an actual storage read makes the
    proof valid even in the abstract model's pathological case where the hashed element slot
    aliases the array-length slot. -/
abbrev clipperKickPostPushLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord (clipperKickActiveMap σ I) I ⟨11⟩

abbrev clipperKickActivePosWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  clipperKickPostPushLengthWord σ I + UInt256.lnot ⟨0⟩

abbrev clipperKickSalesBaseSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨12⟩ (clipperKickIdWord σ I)

abbrev clipperKickSalesPosMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (clipperKickActiveMap σ I)
    (clipperKickSalesBaseSlot σ I) (clipperKickActivePosWord σ I)

abbrev clipperKickSalesTabMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (clipperKickSalesPosMap σ I)
    (clipperKickSalesBaseSlot σ I + ⟨1⟩) (clipperKickTabWord I)

abbrev clipperKickSalesLotMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (clipperKickSalesTabMap σ I)
    (clipperKickSalesBaseSlot σ I + ⟨2⟩) (clipperKickLotWord I)

abbrev clipperKickUint96Mask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩

abbrev clipperKickPackedSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  ⟨3⟩ + clipperKickSalesBaseSlot σ I

abbrev clipperKickPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.land clipperKickUint96Mask (UInt256.ofNat I.header.timestamp))
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
    (UInt256.land
      (UInt256.lor
        (UInt256.land solcAddrMask (clipperKickUsrMaskedWord I))
        (UInt256.land (UInt256.lnot solcAddrMask)
          (solcSlotWord (clipperKickSalesLotMap σ I) I (clipperKickPackedSlot σ I))))
      solcAddrMask)

abbrev clipperKickInitializedMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (clipperKickSalesLotMap σ I)
    (clipperKickPackedSlot σ I) (clipperKickPackedWord σ I)

noncomputable abbrev clipperKickSalesHashMem
    (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (clipperKickIdWord σ I) ⟨12⟩ (clipperRelyAuthHashMem I)

theorem clipperKickSalesHashMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (clipperKickSalesHashMem σ I).size = 96 := by
  simpa [clipperKickSalesHashMem] using
    twoWordHashMem_size_96 (clipperKickIdWord σ I) (⟨12⟩ : UInt256)
      (clipperRelyAuthHashMem_size I)

theorem clipperKickSalesHashMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (clipperKickSalesHashMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [clipperKickSalesHashMem,
    twoWordHashMem_read64 _ _ (clipperRelyAuthHashMem_size I)]
  exact clipperRelyAuthHashMem_read64 I

set_option maxHeartbeats 1500000 in
theorem clipperKickX_idPositive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (hid : clipperKickIdWord σ I ≠ ⟨0⟩)
    (h : RD code I g s0 ⟨5831⟩
      (⟨1⟩ :: ⟨0⟩ :: clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD code I g s0 ⟨5913⟩
      (⟨1⟩ :: clipperKickIdWord σ I :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I :: clipperKickTabWord I ::
        ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, clipperKickIdMap σ I) k' C' := by
  have rd5835 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨10⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k5836, C5836, rd5836raw⟩ := rd5835.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd5836 : RD code I g s0 ⟨5836⟩
      (solcSlotWord σ I ⟨10⟩ :: ⟨10⟩ :: ⟨1⟩ :: ⟨0⟩ ::
        clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k5836 C5836 := by
    simpa [solcSlotWord] using rd5836raw
  have rd5842pre := evm_run rd5836 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5843⟩ := rd5842pre.sstore hperm
    (by clipper_runtime_decode) (by evm_ov)
  have rd5845 := evm_run rd5843 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5849 := rd5845.push2 ⟨5913⟩ (by clipper_runtime_decode) (by evm_ov)
  exact ⟨_, _, by
    simpa [clipperKickIdMap, clipperKickIdWord] using rd5849.jumpiT
      (by clipper_runtime_decode) hid (clipperKickJumpDest5913 v hpatch) (by evm_ov)⟩

set_option maxHeartbeats 4000000 in
theorem clipperKickX_initializeAuction {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hperm : I.perm = true)
    (h : RD code I g s0 ⟨5913⟩
      (⟨1⟩ :: clipperKickIdWord σ I :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I :: clipperKickTabWord I ::
        ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, clipperKickIdMap σ I) k C) :
    ∃ k' C', RD code I g s0 ⟨8728⟩
      (⟨6061⟩ :: ⟨6069⟩ :: ⟨0⟩ :: ⟨1⟩ :: clipperKickIdWord σ I ::
        clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I ::
        clipperKickLotWord I :: clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperKickSalesHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, clipperKickInitializedMap σ I) k' C' := by
  have rd5917 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k5918, C5918, rd5918raw⟩ := rd5917.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd5918 : RD code I g s0 ⟨5918⟩
      (clipperKickActiveLengthWord σ I :: ⟨11⟩ :: ⟨1⟩ ::
        clipperKickIdWord σ I :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I :: clipperKickTabWord I ::
        ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, clipperKickIdMap σ I) k5918 C5918 := by
    simpa [clipperKickActiveLengthWord, solcSlotWord] using rd5918raw
  have rd5924pre := evm_run rd5918 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5925⟩ := rd5924pre.sstore hperm
    (by clipper_runtime_decode) (by evm_ov)
  have rd5958 := rd5925.pushConst activeDataSlot (width := 32)
    (by decide : Operation.POp.PUSH32 ≠ .PUSH0)
    (by rw [activeDataSlot_eq]; clipper_runtime_decode) (by evm_ov)
  have rd5963pre := evm_run rd5958 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5964⟩ := rd5963pre.sstore hperm
    (by clipper_runtime_decode) (by evm_ov)
  have rd5965 := rd5964.swap1 (by clipper_runtime_decode) (by evm_ov)
  obtain ⟨k5966, C5966, rd5966raw⟩ := rd5965.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd5966 : RD code I g s0 ⟨5966⟩
      (clipperKickPostPushLengthWord σ I :: ⟨1⟩ :: ⟨1⟩ ::
        clipperKickIdWord σ I :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I :: clipperKickTabWord I ::
        ⟨476⟩ :: [sel])
      (clipperRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, clipperKickActiveMap σ I) k5966 C5966 := by
    simpa [clipperKickPostPushLengthWord, solcSlotWord] using rd5966raw
  have rd5970pre := evm_run rd5966 with [
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5971 := rd5970pre.mstore 0
    (wordAt0Mem (clipperKickIdWord σ I) (clipperRelyAuthHashMem I))
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd5975 := evm_run rd5971 with [
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd5976 := rd5975.mstore 0 (clipperKickSalesHashMem σ I)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have hsalesSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((clipperKickSalesHashMem σ I).readWithPadding 0 64))) =
        clipperKickSalesBaseSlot σ I := by
    simpa [clipperKickSalesHashMem, clipperKickSalesBaseSlot] using
      twoWordHashMem_solcMappingSlot (⟨12⟩ : UInt256) (clipperKickIdWord σ I)
        (clipperRelyAuthHashMem_size I)
  have rd5979pre := evm_run rd5976 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5980 := rd5979pre.keccak256 0 (clipperKickSalesBaseSlot σ I)
    (UInt256.ofNat 3) (by clipper_runtime_decode) mem_cost hsalesSlot
    (by native_decide) (by evm_ov)
  have rd5987pre := evm_run rd5980 with [
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw not (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5988⟩ := rd5987pre.sstore hperm
    (by clipper_runtime_decode) (by evm_ov)
  change RD code I g s0 _ _ _ _ _ (cA, clipperKickSalesPosMap σ I) _ _ at rd5988
  have rd5993pre := evm_run rd5988 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup9 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5994⟩ := rd5993pre.sstore hperm
    (by clipper_runtime_decode) (by evm_ov)
  change RD code I g s0 _ _ _ _ _ (cA, clipperKickSalesTabMap σ I) _ _ at rd5994
  have rd6000pre := evm_run rd5994 with [
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd6001⟩ := rd6000pre.sstore hperm
    (by clipper_runtime_decode) (by evm_ov)
  change RD code I g s0 _ _ _ _ _ (cA, clipperKickSalesLotMap σ I) _ _ at rd6001
  have rd6004 := evm_run rd6001 with [
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k6006, C6006, rd6006⟩ := rd6004.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd6006' : RD code I g s0 ⟨6006⟩
      (solcSlotWord (clipperKickSalesLotMap σ I) I (clipperKickPackedSlot σ I) ::
        clipperKickPackedSlot σ I :: ⟨0⟩ :: ⟨1⟩ :: clipperKickIdWord σ I ::
        clipperKickKprMaskedWord I :: clipperKickUsrMaskedWord I :: clipperKickLotWord I ::
        clipperKickTabWord I :: ⟨476⟩ :: [sel])
      (clipperKickSalesHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, clipperKickSalesLotMap σ I) k6006 C6006 := by
    simpa [clipperKickPackedSlot, solcSlotWord] using rd6006
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by native_decide
  have hmask96 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩ =
        clipperKickUint96Mask := by rfl
  have rd6050pre := evm_run rd6006' with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw not (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw or (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw timestamp (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw mul (by clipper_runtime_decode) (by evm_ov),
    raw or (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [hmask160, hmask96] at rd6050pre
  obtain ⟨k6051, C6051, rd6051⟩ := rd6050pre.sstore hperm
    (by clipper_runtime_decode) (by evm_ov)
  have hpacked :
      UInt256.lor
          (UInt256.mul
            (UInt256.land clipperKickUint96Mask (UInt256.ofNat I.header.timestamp))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))
          (UInt256.land
            (UInt256.lor
              (UInt256.land solcAddrMask (clipperKickUsrMaskedWord I))
              (UInt256.land (UInt256.lnot solcAddrMask)
                (solcSlotWord (clipperKickSalesLotMap σ I) I
                  (clipperKickPackedSlot σ I))))
            solcAddrMask) =
        clipperKickPackedWord σ I := by
    rfl
  rw [hpacked] at rd6051
  have rd6051' : RD code I g s0 ⟨6051⟩
      (⟨0⟩ :: ⟨1⟩ :: clipperKickIdWord σ I :: clipperKickKprMaskedWord I ::
        clipperKickUsrMaskedWord I :: clipperKickLotWord I :: clipperKickTabWord I ::
        ⟨476⟩ :: [sel])
      (clipperKickSalesHashMem σ I) (UInt256.ofNat 3) ByteArray.empty
      (cA, clipperKickInitializedMap σ I) k6051 C6051 := by
    simpa only [clipperKickInitializedMap] using rd6051
  have rd6060 := evm_run rd6051' with [
    raw push2 ⟨6069⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨6061⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8728⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd6060.jump (by clipper_runtime_decode) (clipperKickJumpDest8728 v hpatch)
    (by evm_ov)⟩

end Benchmarks.Dss.Clipper
