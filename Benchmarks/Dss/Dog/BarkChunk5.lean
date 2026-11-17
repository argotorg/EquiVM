import Benchmarks.Dss.Dog.BarkChunk4

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogBarkKickReturnDecodeShortReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem out : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4404 : RD code I g s0 ⟨4404⟩ (d0 :: d1 :: d2 :: R)
      mem (UInt256.ofNat 19) out acc k C)
    (hshort : out.size < 32) (hout : out.size < UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop rd4404
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rdMload64 := RD.mload 0 ⟨384⟩ (UInt256.ofNat 19) rdPush64
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost hmload64 (by decide) (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rdIszero := RD.iszero rdLt
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨4424⟩
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hcond
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkKickReturnDecodeOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem out : ByteArray} {k C : ℕ} {retWord d0 d1 d2 : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4404 : RD code I g s0 ⟨4404⟩ (d0 :: d1 :: d2 :: R)
      mem (UInt256.ofNat 19) out acc k C)
    (hlong : 32 ≤ out.size) (hout : out.size < UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩)
    (hmload384 :
      (if (⟨384⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨384⟩ : UInt256).toNat 32))) =
        retWord)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4427⟩ (retWord :: R)
      mem (UInt256.ofNat 19) out acc k' C' := by
  have rdPop0 := RD.pop rd4404
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rdMload64 := RD.mload 0 ⟨384⟩ (UInt256.ofNat 19) rdPush64
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost hmload64 (by decide) (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' out.size hout]
    exact hlong
  have rdIszero := RD.iszero rdLt
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨4424⟩
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd4424 := RD.jumpiT rdPushOk
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd4425 := RD.jumpdest rd4424
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4426 := RD.pop rd4425
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4427 := RD.mload 0 retWord (UInt256.ofNat 19) rd4426
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
      mem_cost hmload384 (by decide) (by omega)
  exact ⟨_, _, rd4427⟩

theorem RD.dogBarkKickDecodedToPublicReturn {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem out : ByteArray} {k C : ℕ} {σMem : AccountMap}
    {id tab due dink dust rate dart art ink ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4427 : RD code I g s0 ⟨4427⟩
      (id :: tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art ::
        ink :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: [])
      mem (UInt256.ofNat 19) out acc k C)
    (hret : (D_J code 0).contains ret = true)
    (hperm : I.perm = true)
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hmload256 :
      (if (⟨256⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
        barkIlksClipWord σMem I) :
    ∃ k' C', RD code I g s0 ret (id :: sel :: [])
      (barkBarkLogMem mem dink dart due (barkIlksClipWord σMem I))
      (UInt256.ofNat 19) out acc k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
  have hmload64Log :=
    barkBarkLogMem_mload64 (mem := mem) (dink := dink) (dart := dart)
      (due := due) (clip := barkIlksClipWord σMem I) hmem hread64
  have haddrMaskWord :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hclipCanon : (barkIlksClipWord σMem I).toNat < EVM.addressModulus := by
    simpa [barkIlksClipWord, u256_land_comm] using
      solcAddrMask_result_canonical (solcSlotWord σMem I (barkIlksSlot I))
  have hclipCleanL :
      UInt256.land solcAddrMask (barkIlksClipWord σMem I) = barkIlksClipWord σMem I :=
    solcAddrMask_clean_left hclipCanon
  have hclipCleanR :
      UInt256.land (barkIlksClipWord σMem I) solcAddrMask = barkIlksClipWord σMem I := by
    rw [u256_land_comm]
    exact hclipCleanL
  have hurnCanon : (barkUrnKey I).toNat < EVM.addressModulus := by
    simpa [barkUrnKey, u256_land_comm] using
      solcAddrMask_result_canonical (barkUrnWord I)
  have hurnCleanL :
      UInt256.land solcAddrMask (barkUrnKey I) = barkUrnKey I :=
    solcAddrMask_clean_left hurnCanon
  have hurnCleanR :
      UInt256.land (barkUrnKey I) solcAddrMask = barkUrnKey I := by
    rw [u256_land_comm]
    exact hurnCleanL
  have rdLogMem := evm_run rd4427 with [
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 (barkIlksClipWord σMem I) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload256 (by decide) (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkBarkLogDinkMem mem dink) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup11
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkBarkLogDartMem mem dink dart) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ((⟨384⟩ : UInt256) + ⟨32⟩).toNat = 416 by native_decide]
        rfl)
      (by decide) (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkBarkLogDueMem mem dink dart due) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ((⟨64⟩ : UInt256) + ⟨384⟩).toNat = 448 by native_decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨96⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkBarkLogMem mem dink dart due (barkIlksClipWord σMem I))
      (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ((⟨384⟩ : UInt256) + ⟨96⟩).toNat = 480 by native_decide]
        simp [barkBarkLogMem, Reasoning.Theory.writeWord, haddrMaskWord,
          hclipCleanL, hclipCleanR])
      (by decide) (by evm_ov)]
  have rdLogPrep := evm_run rdLogMem with [
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64Log (by decide) (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap13
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup13
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup15
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup16
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdTopic := rdLogPrep.pushConst dogBarkLogTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons, List.length_nil]; norm_num)
  have rdLogStack := evm_run rdTopic with [
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨128⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdLog := RD.log4 0 (UInt256.ofNat 19) rdLogStack
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; norm_num)
  have rdTail := evm_run rdLog with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, rdTail.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hret (by evm_ov)⟩

theorem RD.dogBarkPublicReturnId {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem memout out : ByteArray} {k C : ℕ} {id sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd448 : RD code I g s0 ⟨448⟩ (id :: sel :: [])
      mem (UInt256.ofNat 19) out acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩)
    (hmemout : (UInt256.toByteArray id).write 0 mem 384 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩)
    (hread384 : memout.readWithPadding 384 32 = UInt256.toByteArray id) :
    RDret code g s0 acc (UInt256.toByteArray id) := by
  exact evm_run rd448 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by rw [show (⟨384⟩ : UInt256).toNat = 384 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmemoutLoad64 (by decide) (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw ret 0 (UInt256.toByteArray id)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show (⟨384⟩ : UInt256).toNat = 384 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨384⟩ : UInt256) ⟨384⟩).toNat = 32
            from by decide]
        exact hread384)
      (by evm_ov)]

theorem RD.dogBarkLiquidationLimitHitReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hfitInk : ink.toNat * spot.toNat < UInt256.size)
    (hsafe : (ink * spot).toNat < (art * rate).toNat)
    (hlimitFalse :
      ¬ ((solcSlotWordAt ⟨5⟩ σ I).toNat < (solcSlotWordAt ⟨4⟩ σ I).toNat ∧
        (barkIlksDirtWord σMem I).toNat < (barkIlksHoleWord σMem I).toNat))
    (hmload320 :
      (if (⟨320⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
        barkIlksHoleWord σMem I)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        barkIlksDirtWord σMem I)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 28 ≤ 1024) :
    RDrev code g s0 := by
  have htail : dogPostIlksErrorStringFullWordTailWf code ⟨3436⟩ ⟨25⟩
      (UInt256.shiftLeft dogLiquidationLimitHitRawWord ⟨56⟩) := by
    unfold dogPostIlksErrorStringFullWordTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
  obtain ⟨_, _, rd3405⟩ :=
    RD.dogBarkSafeToLimitGuard (v := v) (code := code) (ret := ret) (sel := sel)
      (R := R) hpatch hspot hfitArt hfitInk hsafe rd3308 hov
  have rd3408 := evm_run rd3405 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3409, C3409, rd3409raw⟩ := rd3408.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3409 : RD code I g s0 ⟨3409⟩
      (solcSlotWordAt ⟨5⟩ σ I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k3409 C3409 := by
    simpa [solcSlotWordAt, solcSlotWord] using rd3409raw
  have rd3411 := evm_run rd3409 with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3412, C3412, rd3412raw⟩ := rd3411.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3412 : RD code I g s0 ⟨3412⟩
      (solcSlotWordAt ⟨4⟩ σ I :: solcSlotWordAt ⟨5⟩ σ I :: spot :: dust :: rate ::
        ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k3412 C3412 := by
    simpa [solcSlotWordAt, solcSlotWord] using rd3412raw
  by_cases hglobal :
      (solcSlotWordAt ⟨5⟩ σ I).toNat < (solcSlotWordAt ⟨4⟩ σ I).toNat
  · have hgtGlobal :
        UInt256.gt (solcSlotWordAt ⟨4⟩ σ I) (solcSlotWordAt ⟨5⟩ σ I) = ⟨1⟩ :=
      Reasoning.Theory.ugt_one hglobal
    have rd3413raw := evm_run rd3412 with [
      raw gt
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3413 := rd3413raw
    rw [hgtGlobal] at rd3413
    have rd3418raw := evm_run rd3413 with [
      raw dup1
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw iszero
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨3431⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3418 := rd3418raw
    rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3418
    have rd3419 := rd3418.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by rfl) (by evm_ov)
    have rd3423 := evm_run rd3419 with [
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup5
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push1 ⟨96⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3424raw := RD.add rd3423
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)
    have hadd352 : (⟨96⟩ : UInt256) + ⟨256⟩ = ⟨352⟩ := by
      native_decide
    have rd3424 := by
      simpa [hadd352] using rd3424raw
    have rd3425 := evm_run rd3424 with [
      raw mload 0 (barkIlksDirtWord σMem I) (UInt256.ofNat 17)
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        mem_cost hmload352 (by decide) (by evm_ov)]
    have rd3428 := evm_run rd3425 with [
      raw dup6
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push1 ⟨64⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3429raw := RD.add rd3428
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)
    have hadd320 : (⟨64⟩ : UInt256) + ⟨256⟩ = ⟨320⟩ := by
      native_decide
    have rd3429 := by
      simpa [hadd320] using rd3429raw
    have rd3430 := evm_run rd3429 with [
      raw mload 0 (barkIlksHoleWord σMem I) (UInt256.ofNat 17)
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        mem_cost hmload320 (by decide) (by evm_ov)]
    have hmilkNot :
        ¬ (barkIlksDirtWord σMem I).toNat < (barkIlksHoleWord σMem I).toNat := by
      intro hmilk
      exact hlimitFalse ⟨hglobal, hmilk⟩
    have hgtMilk : UInt256.gt (barkIlksHoleWord σMem I) (barkIlksDirtWord σMem I) = ⟨0⟩ :=
      Reasoning.Theory.ugt_zero (by omega)
    have rd3431raw := evm_run rd3430 with [
      raw gt
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3431 := rd3431raw
    rw [hgtMilk] at rd3431
    have rd3435 := evm_run rd3431 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨3512⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3436raw := rd3435.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by rfl) (by evm_ov)
    have hpc3436 :
        (⟨3412⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 3 + ⟨1⟩ = ⟨3436⟩ := by
      native_decide
    have rd3436 := rd3436raw
    rw [hpc3436] at rd3436
    exact RD.dogBarkPostIlksErrorStringRevertTailFullWord
      (pc := ⟨3436⟩) (len := ⟨25⟩)
      (word := UInt256.shiftLeft dogLiquidationLimitHitRawWord ⟨56⟩)
      rd3436 htail hmem hread64
      (by simp only [List.length_cons]; omega)
  · have hgtGlobal :
        UInt256.gt (solcSlotWordAt ⟨4⟩ σ I) (solcSlotWordAt ⟨5⟩ σ I) = ⟨0⟩ :=
      Reasoning.Theory.ugt_zero (by omega)
    have rd3413raw := evm_run rd3412 with [
      raw gt
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3413 := rd3413raw
    rw [hgtGlobal] at rd3413
    have rd3418raw := evm_run rd3413 with [
      raw dup1
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw iszero
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨3431⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3418 := rd3418raw
    rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3418
    have rd3431 := rd3418.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd3435 := evm_run rd3431 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨3512⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3436raw := rd3435.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by rfl) (by evm_ov)
    have hpc3436 : (⟨3431⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨3436⟩ := by
      native_decide
    have rd3436 := rd3436raw
    rw [hpc3436] at rd3436
    exact RD.dogBarkPostIlksErrorStringRevertTailFullWord
      (pc := ⟨3436⟩) (len := ⟨25⟩)
      (word := UInt256.shiftLeft dogLiquidationLimitHitRawWord ⟨56⟩)
      rd3436 htail hmem hread64
      (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatUrnsStaticcallDepthLimitRevert {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : Sat256} {ret sel : UInt256} {R : List UInt256}
    {k C : ℕ} {mem rdata : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g (initState σ σ₀ g A I) ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata σ k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 24 ≤ 1024) :
    RDrev code g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd3007⟩ :=
    RD.dogBarkVatUrnsToStaticcall hpatch h hmem hread64 hcodeSize hov
  obtain ⟨_, _, rd3008raw⟩ :=
    RD.solcStaticcallDepthLimit rd3007
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  have hmin : (min (⟨64⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  obtain ⟨_, _, rd3008⟩ : ∃ k' C',
      RD code I g (initState σ σ₀ g A I) ⟨3008⟩
        (⟨0⟩ :: ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
          ret :: sel :: R)
        (barkVatUrnsCallMem I mem) (UInt256.ofNat 7) ByteArray.empty σ k' C' := by
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat) = UInt256.ofNat 7 := by
      native_decide
    exact ⟨_, _, by simpa [hmin, byteArray_write_len_zero] using haw ▸ rd3008raw⟩
  exact RD.dogBarkVatUrnsCallFailure hpatch rd3008 (by native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkLiveOk {v : DogImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State} {stk : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g s0 ⟨2813⟩ stk solcFreePtrMem
      (UInt256.ofNat 3) rdata σ k C)
    (hlive : solcSlotWord σ I ⟨3⟩ = ⟨1⟩)
    (hov : stk.length + 6 ≤ 1024) :
    ∃ k C, RD code I g s0 ⟨2885⟩ (⟨0⟩ :: stk) solcFreePtrMem
      (UInt256.ofNat 3) rdata σ k C := by
  obtain ⟨_, _, h⟩ := hreach
  have rd1 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rd3 := rd1.push1 ⟨0⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rd5 := rd3.push1 ⟨3⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd6⟩ := rd5.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨1⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd9₀ := rd8.eq
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hraw :
      (σ.get? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.getD ⟨3⟩ ⟨0⟩)) =
        ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have rd9 := rd9₀
  rw [hraw, uInt256_eq_self] at rd9
  have rd12 := rd9.push2 ⟨2885⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa using rd12.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      one_ne_zero_uint
      (dogPatchedJumpDest hpatch (by native_decide))
      (by simp only [List.length_cons]; omega)⟩

theorem RD.dogBarkLiveRevert {v : DogImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State} {stk : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g s0 ⟨2813⟩ stk solcFreePtrMem
      (UInt256.ofNat 3) rdata σ k C)
    (hlive : solcSlotWord σ I ⟨3⟩ ≠ ⟨1⟩)
    (hov : stk.length + 6 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, h⟩ := hreach
  have htail : solcErrorStringRevertTailWf code ⟨2826⟩ ⟨12⟩
      dogNotLiveRawWord ⟨160⟩ .PUSH12 12 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]; native_decide)
  have rd1 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rd3 := rd1.push1 ⟨0⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rd5 := rd3.push1 ⟨3⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd6⟩ := rd5.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨1⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd9₀ := rd8.eq
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hraw :
      (σ.get? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.getD ⟨3⟩ ⟨0⟩)) ≠
        ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.get? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.getD ⟨3⟩ ⟨0⟩)) =
          ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hraw h1.symm)
  have rd9 := rd9₀
  rw [heq0] at rd9
  have rd12 := rd9.push2 ⟨2885⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdTail := rd12.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2826⟩) (len := ⟨12⟩) (rawWord := dogNotLiveRawWord)
    (shift := ⟨160⟩) (word := UInt256.shiftLeft dogNotLiveRawWord ⟨160⟩)
    (op := .PUSH12) (width := 12) rdTail htail
    (by decide) (by rfl) solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons]; omega)

theorem dogBarkBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some barkTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨785⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨785⟩) (ret := ⟨448⟩)
    (decoded := ⟨807⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_bark_none_short hsz4 hshort)

theorem dogBarkBodyCore {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 2)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some barkTransition :=
    dogDispatchBark hsel
  have hreach := dogReachBarkBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode :
        config.externalABI.decodeCalldata?
          (barkTransition.params.map Param.name)
          (transitionSignature barkTransition).paramTypes I.calldata =
            some (barkLocals I) :=
      dogDecode_bark_ok hsz100
    have hbodyReach := RD.dogBarkDecodeToBody hpatch hsize hsz100 hreach
    by_cases hliveEvm : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩
    · have hslotWord :
          solcSlotWordAt ⟨3⟩ σ I = solcSlotWordAt ⟨3⟩ σ I :=
        rfl
      have hliveStele : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩ := by
        rw [← hslotWord]
        exact hliveEvm
      have hliveSolc : solcSlotWord σ I ⟨3⟩ = ⟨1⟩ := by
        simpa [solcSlotWordAt] using hliveEvm
      obtain ⟨_, _, h2885⟩ := RD.dogBarkLiveOk hpatch hbodyReach hliveSolc
        (by simp only [List.length_cons, List.length_nil]; omega)
      by_cases hvatCodeSize :
          Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) = ⟨0⟩
      · have hrev := RD.dogBarkVatUrnsNoCodeRevert
          (v := v) (code := code) (ret := ⟨448⟩) (sel := solcSelectorWord I) (R := [])
          hpatch h2885 solcFreePtrMem_size solcFreePtrMem_read64 hvatCodeSize
          (by simp)
        have hvatCodeSizeStele :
            Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) = ⟨0⟩ :=
          hvatCodeSize
        have hvatNoCode :
            (UInt256.ofNat
              (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (AccountAddress.ofNat v.vat.toNat)).option 0
                  (fun acc => acc.code.size))).toNat = 0 :=
          barkVatCode_zero_of_codeSize_zero (v := v)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hvatCodeSizeStele
        let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody config contract evm0 (barkLocals I)
              barkTransition.body .reverted (immStore v) := by
          simpa [evm0] using
            (dogBarkVatUrnsNoCodeSourceBody (v := v)
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hliveStele hvatNoCode)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hvatCodeSizeNe :
            Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩ :=
          hvatCodeSize
        have hvatCodeSizeSteleNe :
            Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩ :=
          hvatCodeSizeNe
        have hvatCode :
            0 < (UInt256.ofNat
              (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (AccountAddress.ofNat v.vat.toNat)).option 0
                  (fun acc => acc.code.size))).toNat :=
          barkVatCode_pos_of_codeSize_ne (v := v)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hvatCodeSizeSteleNe
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨σ', z, out, A', _k', _C', rd3008, hcallEvmRaw, hosz⟩ :=
            RD.dogBarkVatUrnsPostStaticcall
              (v := v) (code := code) (ret := ⟨448⟩) (sel := solcSelectorWord I)
              (R := []) hpatch h2885 hsz100 solcFreePtrMem_size solcFreePtrMem_read64
              hvatCodeSizeNe hdepthLt (by simp)
          let evmEvm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let evmStele := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let evmPostEvm :=
            { evmEvm with accountMap := σ', substate := A' }
          have hcallEvm :
              typedCallViaEVM config evmEvm
                (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
                [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
                (z, evmPostEvm, out) false := by
            simpa [evmEvm, evmPostEvm] using hcallEvmRaw
          let evmPostStele :=
            { evmStele with
              accountMap := evmPostEvm.accountMap, substate := evmPostEvm.substate }
          have hcallStele :
              typedCallViaEVM config evmStele
                (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
                [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
                (z, evmPostStele, out) false := by
            simpa [evmPostStele, evmStele, evmEvm] using hcallEvm
          cases z
          · simp only [Bool.false_eq_true, if_false] at rd3008 hcallStele
            have hrev := RD.dogBarkVatUrnsCallFailure hpatch rd3008 hosz (by simp)
            have hbody :
                ExecTransitionBody config contract evmStele (barkLocals I)
                  barkTransition.body .reverted (immStore v) := by
              simpa [evmStele] using
                (dogBarkVatUrnsCallFailureSourceBody (v := v)
                  (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) (evmCall := evmPostStele) (out := out)
                  hwv hliveStele hvatCode hcallStele)
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · simp only [Bool.true_eq_false, if_true] at rd3008 hcallStele
            obtain ⟨_, _, rd3026⟩ :=
              RD.dogBarkVatUrnsCallSuccessToDecode hpatch rd3008
                (by simp only [List.length_cons, List.length_nil]; omega)
            by_cases hretLong : 64 ≤ out.size
            · have hdecUrns : config.externalABI.decode? "urns" out =
                  some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
                    .int (Int.ofNat (barkVatUrnsArtWord out).toNat)] :=
                barkVatUrnsDecode_ok hretLong
              obtain ⟨_, _, rd3061⟩ :=
                RD.dogBarkVatUrnsReturnDecodeOk hpatch rd3026
                  solcFreePtrMem_size solcFreePtrMem_read64 hretLong hosz
                  (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨_, _, rd3070⟩ :=
                RD.dogBarkVatUrnsMaterializeTuple hpatch rd3061
                  solcFreePtrMem_size solcFreePtrMem_read64 hretLong hosz
                  (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨_, _, rd3139⟩ :=
                RD.dogBarkLoadIlkFields hpatch rd3070
                  solcFreePtrMem_size hretLong hosz
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hStateCall : EVMStateEquiv evmPostEvm evmPostStele := ⟨rfl, rfl⟩
              by_cases hvatIlksCodeSize :
                  Reasoning.Theory.extCodeSizeWord σ' (barkVatWord v) = ⟨0⟩
              · have hrev := RD.dogBarkVatIlksNoCodeRevert hpatch rd3139
                  solcFreePtrMem_size hretLong hosz hvatIlksCodeSize
                  (by simp only [List.length_cons, List.length_nil]; omega)
                have hvatIlksCodeSizeEvm :
                    Reasoning.Theory.extCodeSizeWord evmPostEvm.accountMap
                      (barkVatWord v) = ⟨0⟩ := by
                  simpa [evmPostEvm] using hvatIlksCodeSize
                have hvatIlksCodeSizeStele :
                    Reasoning.Theory.extCodeSizeWord evmPostStele.accountMap
                      (barkVatWord v) = ⟨0⟩ :=
                  hStateCall.accountMap ▸ hvatIlksCodeSizeEvm
                have hvatNoCode :
                    (UInt256.ofNat
                      ((evmPostStele.lookupAccount
                        (AccountAddress.ofNat v.vat.toNat)).option 0
                          (fun acc => acc.code.size))).toNat = 0 :=
                  barkVatCode_zero_of_state_codeSize_zero (v := v) (evm := evmPostStele)
                    hvatIlksCodeSizeStele
                have hbody :
                    ExecTransitionBody config contract evmStele (barkLocals I)
                      barkTransition.body .reverted (immStore v) := by
                  simpa [evmStele] using
                    (dogBarkVatIlksNoCodeSourceBody (v := v)
                      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) (evmUrns := evmPostStele) (out := out)
                      hwv hliveStele hvatCode hcallStele hdecUrns hvatNoCode hsz100)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · obtain ⟨σ'', zIlks, outIlks, A'', _k'', _C'', rd3245,
                    hcallIlksEvmRaw, hoszIlks⟩ :=
                  RD.dogBarkVatIlksPostStaticcall
                    (v := v) (code := code) (s0 := evmEvm) (evm := evmPostEvm)
                    (ret := ⟨448⟩) (sel := solcSelectorWord I) (R := [])
                    hpatch rd3139 hsz100 solcFreePtrMem_size hretLong hosz
                    hvatIlksCodeSize
                    (by simp [evmPostEvm, evmEvm, initState])
                    (by simp [evmPostEvm, evmEvm])
                    (by simp [evmPostEvm, evmEvm, initState])
                    hdepthLt
                    (by simp only [List.length_nil]; omega)
                let evmIlksPostEvm :=
                  { evmPostEvm with
                    accountMap := σ'', substate := A'' }
                have hcallIlksEvm :
                    typedCallViaEVM config evmPostEvm
                      (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
                      [.fixedBytes bytes32Width (barkIlkBytes I)]
                      (zIlks, evmIlksPostEvm, outIlks) false := by
                  simpa [evmIlksPostEvm] using hcallIlksEvmRaw
                obtain ⟨σIlksStelePost, AIlksStelePost, hcallIlksSteleRaw,
                    hAccountsIlks⟩ :=
                  Reasoning.Theory.typedCallViaEVM_sameInputs
                    (evm_stele := evmPostStele) hcallIlksEvm
                    hStateCall.accountMap
                    (by simp [evmPostEvm, evmPostStele, evmEvm, evmStele, initState])
                    (by simpa [evmPostEvm, evmPostStele] using hStateCall.executionEnv.symm)
                let evmIlksPostStele :=
                  { evmPostStele with
                    accountMap := σIlksStelePost, substate := AIlksStelePost }
                have hcallIlksStele :
                    typedCallViaEVM config evmPostStele
                      (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
                      [.fixedBytes bytes32Width (barkIlkBytes I)]
                      (zIlks, evmIlksPostStele, outIlks) false := by
                  simpa [evmIlksPostEvm, evmIlksPostStele] using hcallIlksSteleRaw
                cases zIlks
                · simp only [Bool.false_eq_true, if_false] at rd3245 hcallIlksEvm
                  simp only [Bool.false_eq_true, if_false] at hcallIlksStele
                  have hrev := RD.dogBarkVatIlksCallFailure hpatch rd3245 hoszIlks
                    (by simp only [List.length_cons, List.length_nil]; omega)
                  have hvatIlksCodeSizeEvmNe :
                      Reasoning.Theory.extCodeSizeWord evmPostEvm.accountMap
                        (barkVatWord v) ≠ ⟨0⟩ := by
                    simpa [evmPostEvm] using hvatIlksCodeSize
                  have hvatIlksCodeSizeSteleNe :
                      Reasoning.Theory.extCodeSizeWord evmPostStele.accountMap
                        (barkVatWord v) ≠ ⟨0⟩ :=
                    hStateCall.accountMap ▸ hvatIlksCodeSizeEvmNe
                  have hvatIlksCode :
                      0 < (UInt256.ofNat
                        ((evmPostStele.lookupAccount
                          (AccountAddress.ofNat v.vat.toNat)).option 0
                            (fun acc => acc.code.size))).toNat :=
                    barkVatCode_pos_of_state_codeSize_ne (v := v) (evm := evmPostStele)
                      hvatIlksCodeSizeSteleNe
                  have hbody :
                      ExecTransitionBody config contract evmStele (barkLocals I)
                        barkTransition.body .reverted (immStore v) := by
                    simpa [evmStele] using
                      (dogBarkVatIlksCallFailureSourceBody (v := v)
                        (σ := σ) (σ₀ := σ₀) (A := A)
                        (I := I) (g := g) (evmUrns := evmPostStele)
                        (evmIlks := evmIlksPostStele) (out := out) (outIlks := outIlks)
                        hwv hliveStele hvatCode hcallStele hdecUrns hvatIlksCode
                        hcallIlksStele hsz100)
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · simp only [Bool.true_eq_false, if_true] at rd3245 hcallIlksEvm
                  simp only [Bool.true_eq_false, if_true] at hcallIlksStele
                  obtain ⟨_, _, rd3263⟩ :=
                    RD.dogBarkVatIlksCallSuccessToDecode hpatch rd3245
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have hvatIlksCodeSizeEvmNe :
                      Reasoning.Theory.extCodeSizeWord evmPostEvm.accountMap
                        (barkVatWord v) ≠ ⟨0⟩ := by
                    simpa [evmPostEvm] using hvatIlksCodeSize
                  have hvatIlksCodeSizeSteleNe :
                      Reasoning.Theory.extCodeSizeWord evmPostStele.accountMap
                        (barkVatWord v) ≠ ⟨0⟩ :=
                    hStateCall.accountMap ▸ hvatIlksCodeSizeEvmNe
                  have hvatIlksCode :
                      0 < (UInt256.ofNat
                        ((evmPostStele.lookupAccount
                          (AccountAddress.ofNat v.vat.toNat)).option 0
                            (fun acc => acc.code.size))).toNat :=
                    barkVatCode_pos_of_state_codeSize_ne (v := v) (evm := evmPostStele)
                      hvatIlksCodeSizeSteleNe
                  by_cases hretIlksLong : 160 ≤ outIlks.size
                  · have hdecIlks :
                        config.externalABI.decode? "ilks" outIlks =
                          some (barkVatIlksReturnValues outIlks) :=
                      barkVatIlksDecode_ok hretIlksLong
                    obtain ⟨_, _, rd3308⟩ :=
                      RD.dogBarkVatIlksReturnDecodeOkToSpotGuard hpatch rd3263
                        solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    by_cases hoverInk :
                        UInt256.size ≤
                          (barkVatUrnsInkWord out).toNat *
                            (barkVatIlksSpotWord outIlks).toNat
                    · have hspotNe : barkVatIlksSpotWord outIlks ≠ ⟨0⟩ := by
                        intro hspotZero
                        have hprod0 :
                            (barkVatUrnsInkWord out).toNat *
                                (barkVatIlksSpotWord outIlks).toNat = 0 := by
                          simp [hspotZero]
                        have hsizePos : 0 < UInt256.size := by
                          norm_num [UInt256.size]
                        omega
                      have hbody :
                          ExecTransitionBody config contract evmStele (barkLocals I)
                            barkTransition.body .reverted (immStore v) := by
                        simpa [evmStele] using
                          (dogBarkVatIlksInkSpotOverflowSourceBody (v := v)
                            (σ := σ) (σ₀ := σ₀) (A := A)
                            (I := I) (g := g) (evmUrns := evmPostStele)
                            (evmIlks := evmIlksPostStele) (out := out)
                            (outIlks := outIlks) hwv hliveStele hvatCode hcallStele
                            hdecUrns hvatIlksCode hcallIlksStele hdecIlks hoverInk hsz100)
                      by_cases hoverArt :
                          UInt256.size ≤
                            (barkVatUrnsArtWord out).toNat *
                              (barkVatIlksRateWord outIlks).toNat
                      · have hrev := RD.dogBarkArtRateOverflowReverts
                          (v := v) (code := code) (ret := ⟨448⟩)
                          (sel := solcSelectorWord I) (R := []) hpatch hspotNe hoverArt
                          rd3308 (by simp)
                        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have hfitArt :
                            (barkVatUrnsArtWord out).toNat *
                                (barkVatIlksRateWord outIlks).toNat < UInt256.size :=
                          Nat.lt_of_not_ge hoverArt
                        have hrev := RD.dogBarkInkSpotOverflowReverts
                          (v := v) (code := code) (ret := ⟨448⟩)
                          (sel := solcSelectorWord I) (R := []) hpatch hspotNe hfitArt
                          hoverInk rd3308 (by simp)
                        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hfitInk :
                          (barkVatUrnsInkWord out).toNat *
                              (barkVatIlksSpotWord outIlks).toNat < UInt256.size :=
                        Nat.lt_of_not_ge hoverInk
                      by_cases hoverArt :
                          UInt256.size ≤
                            (barkVatUrnsArtWord out).toNat *
                              (barkVatIlksRateWord outIlks).toNat
                      · have hbody :
                            ExecTransitionBody config contract evmStele (barkLocals I)
                              barkTransition.body .reverted (immStore v) := by
                          simpa [evmStele] using
                            (dogBarkVatIlksArtRateOverflowSourceBody (v := v)
                              (σ := σ) (σ₀ := σ₀) (A := A)
                              (I := I) (g := g) (evmUrns := evmPostStele)
                              (evmIlks := evmIlksPostStele) (out := out)
                              (outIlks := outIlks) hwv hliveStele hvatCode hcallStele
                              hdecUrns hvatIlksCode hcallIlksStele hdecIlks hfitInk
                              hoverArt hsz100)
                        by_cases hspotZero : barkVatIlksSpotWord outIlks = ⟨0⟩
                        · have hpostMemSize :
                              (barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks).size =
                                544 :=
                            barkVatIlksPostCallMem_size_long (σ := σ') (I := I)
                              solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                          have hpostMemRead64 :
                              ((barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks).readWithPadding
                                64 32) =
                                UInt256.toByteArray ⟨384⟩ :=
                            barkVatIlksPostCallMem_read64_long (σ := σ') (I := I)
                              solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                          have hrev := RD.dogBarkSpotZeroReverts
                            (v := v) (code := code) (ret := ⟨448⟩)
                            (sel := solcSelectorWord I) (R := []) hpatch hspotZero
                            hpostMemSize hpostMemRead64 rd3308 (by simp)
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · have hrev := RD.dogBarkArtRateOverflowReverts
                            (v := v) (code := code) (ret := ⟨448⟩)
                            (sel := solcSelectorWord I) (R := []) hpatch hspotZero
                            hoverArt rd3308 (by simp)
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have hfitArt :
                            (barkVatUrnsArtWord out).toNat *
                                (barkVatIlksRateWord outIlks).toNat < UInt256.size :=
                          Nat.lt_of_not_ge hoverArt
                        have hpostMemSize :
                            (barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks).size =
                              544 :=
                          barkVatIlksPostCallMem_size_long (σ := σ') (I := I)
                            solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                        have hpostMemRead64 :
                            ((barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks).readWithPadding
                              64 32) =
                              UInt256.toByteArray ⟨384⟩ :=
                          barkVatIlksPostCallMem_read64_long (σ := σ') (I := I)
                            solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                        by_cases hspotZero : barkVatIlksSpotWord outIlks = ⟨0⟩
                        · have hnotSafe :
                              ¬ (0 < (barkVatIlksSpotWord outIlks).toNat ∧
                                (barkInkSpotWord out outIlks).toNat <
                                  (barkArtRateUnsafeWord out outIlks).toNat) := by
                            intro hsafe
                            have hspotNat : (barkVatIlksSpotWord outIlks).toNat = 0 := by
                              simp [hspotZero]
                            omega
                          have hbody :
                              ExecTransitionBody config contract evmStele
                                (barkLocals I) barkTransition.body .reverted (immStore v) := by
                            simpa [evmStele] using
                              (dogBarkVatIlksNotUnsafeSourceBody (v := v)
                                (σ := σ) (σ₀ := σ₀)
                                (A := A) (I := I) (g := g) (evmUrns := evmPostStele)
                                (evmIlks := evmIlksPostStele) (out := out)
                                (outIlks := outIlks) hwv hliveStele hvatCode hcallStele
                                hdecUrns hvatIlksCode hcallIlksStele hdecIlks hfitInk
                                hfitArt hnotSafe hsz100)
                          have hrev := RD.dogBarkSpotZeroReverts
                            (v := v) (code := code) (ret := ⟨448⟩)
                            (sel := solcSelectorWord I) (R := []) hpatch hspotZero
                            hpostMemSize hpostMemRead64 rd3308 (by simp)
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · by_cases hsafeLt :
                              (barkInkSpotWord out outIlks).toNat <
                                (barkArtRateUnsafeWord out outIlks).toNat
                          · by_cases hlimit :
                              (solcSlotWordAt ⟨5⟩ σ'' I).toNat <
                                  (solcSlotWordAt ⟨4⟩ σ'' I).toNat ∧
                                (barkIlksDirtWord σ' I).toNat <
                                  (barkIlksHoleWord σ' I).toNat
                            · have hspotPos :
                                  0 < (barkVatIlksSpotWord outIlks).toNat := by
                                have hnatNe :
                                    (barkVatIlksSpotWord outIlks).toNat ≠ 0 := by
                                  intro hnat
                                  exact hspotZero (uint256_toNat_eq_zero hnat)
                                exact Nat.pos_of_ne_zero hnatNe
                              have hsafeEvm :
                                  ((barkVatUrnsInkWord out) *
                                      (barkVatIlksSpotWord outIlks)).toNat <
                                    ((barkVatUrnsArtWord out) *
                                      (barkVatIlksRateWord outIlks)).toNat := by
                                simpa [barkInkSpotWord, barkArtRateUnsafeWord] using
                                  hsafeLt
                              have hrateNe : barkVatIlksRateWord outIlks ≠ ⟨0⟩ := by
                                intro hrateZero
                                have hartRateZero :
                                    (barkArtRateUnsafeWord out outIlks).toNat = 0 := by
                                  rw [barkArtRateUnsafeWord, hrateZero, u256_mul_op_toNat]
                                  simp
                                have hltZero :
                                    (barkInkSpotWord out outIlks).toNat < 0 := by
                                  simpa [hartRateZero] using hsafeLt
                                omega
                              have hartNe : barkVatUrnsArtWord out ≠ ⟨0⟩ := by
                                intro hartZero
                                have hartRateZero :
                                    (barkArtRateUnsafeWord out outIlks).toNat = 0 := by
                                  rw [barkArtRateUnsafeWord, hartZero, u256_mul_op_toNat]
                                  simp
                                have hltZero :
                                    (barkInkSpotWord out outIlks).toNat < 0 := by
                                  simpa [hartRateZero] using hsafeLt
                                omega
                              have hmload288 :=
                                barkVatIlksPostCallMem_mload288_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              have hmload320 :=
                                barkVatIlksPostCallMem_mload320_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              have hmload352 :=
                                barkVatIlksPostCallMem_mload352_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              obtain ⟨_, _, rd3512⟩ :=
                                RD.dogBarkLimitGuardOk
                                  (v := v) (code := code) (ret := ⟨448⟩)
                                  (sel := solcSelectorWord I) (R := [])
                                  (σ := σ'') (σMem := σ')
                                  hpatch hspotZero hfitArt hfitInk hsafeEvm hlimit
                                  hmload320 hmload352 rd3308 (by simp)
                              obtain ⟨_, _, rd3543⟩ :=
                                RD.dogBarkComputeRoom
                                  (v := v) (code := code) (ret := ⟨448⟩)
                                  (sel := solcSelectorWord I) (R := [])
                                  (σ := σ'') (σMem := σ')
                                  hpatch hmload320 hmload352 rd3512 (by simp)
                              have _traceProgress : True := by
                                by_cases hfitRoom :
                                    (barkRoomWord σ'' σ' I).toNat * dogWadWord.toNat <
                                      UInt256.size
                                · by_cases hchopNe : barkIlksChopWord σ' I ≠ ⟨0⟩
                                  · obtain ⟨_, _, rd3594⟩ :=
                                      RD.dogBarkComputeDart
                                        (v := v) (code := code) (ret := ⟨448⟩)
                                        (sel := solcSelectorWord I) (R := [])
                                        (σ := σ'') (σMem := σ')
                                        hpatch hfitRoom hrateNe hchopNe hmload288 rd3543
                                        (by simp)
                                    by_cases hnoLeftover :
                                        (barkVatUrnsArtWord out).toNat ≤
                                          (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                            (barkVatIlksRateWord outIlks)
                                            (barkIlksChopWord σ' I)).toNat
                                    · obtain ⟨_, _, rd3700⟩ :=
                                        RD.dogBarkNoLeftoverToDinkEntry
                                          (v := v) (code := code) (ret := ⟨448⟩)
                                          (sel := solcSelectorWord I) (R := [])
                                          (σ := σ'') hpatch hnoLeftover rd3594 (by simp)
                                      by_cases hfitInkDart :
                                          (barkVatUrnsInkWord out).toNat *
                                            (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                              (barkVatIlksRateWord outIlks)
                                              (barkIlksChopWord σ' I)).toNat <
                                            UInt256.size
                                      · obtain ⟨_, _, rd3726⟩ :=
                                          RD.dogBarkComputeDink
                                            (v := v) (code := code) (ret := ⟨448⟩)
                                            (sel := solcSelectorWord I) (R := [])
                                            (σ := σ'') hpatch hfitInkDart hartNe rd3700
                                            (by simp)
                                        by_cases hdinkPos :
                                            0 < (barkDinkWord (barkVatUrnsInkWord out)
                                              (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                                (barkVatIlksRateWord outIlks)
                                                (barkIlksChopWord σ' I))
                                              (barkVatUrnsArtWord out)).toNat
                                        · obtain ⟨_, _, rd3797⟩ :=
                                            RD.dogBarkDinkGuardOk
                                              (v := v) (code := code) (ret := ⟨448⟩)
                                              (sel := solcSelectorWord I) (R := [])
                                              hpatch hdinkPos rd3726 (by simp)
                                          by_cases hdartBound :
                                              (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                                (barkVatIlksRateWord outIlks)
                                                (barkIlksChopWord σ' I)).toNat ≤
                                                dogInt256LimitWord.toNat
                                          · by_cases hdinkBound :
                                                (barkDinkWord (barkVatUrnsInkWord out)
                                                  (barkDartWord σ'' σ' I
                                                    (barkVatUrnsArtWord out)
                                                    (barkVatIlksRateWord outIlks)
                                                    (barkIlksChopWord σ' I))
                                                  (barkVatUrnsArtWord out)).toNat ≤
                                                  dogInt256LimitWord.toNat
                                            · obtain ⟨_, _, _rd3885⟩ :=
                                                RD.dogBarkInt256GuardOk
                                                  (v := v) (code := code) (ret := ⟨448⟩)
                                                  (sel := solcSelectorWord I) (R := [])
                                                  hpatch hdartBound hdinkBound rd3797
                                                  (by simp)
                                              exact True.intro
                                            · exact True.intro
                                          · exact True.intro
                                        · exact True.intro
                                      · exact True.intro
                                    · have hleftover :
                                          (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                            (barkVatIlksRateWord outIlks)
                                            (barkIlksChopWord σ' I)).toNat <
                                            (barkVatUrnsArtWord out).toNat := by
                                        omega
                                      by_cases hfitLeftoverDue :
                                          (barkLeftoverArtWord (barkVatUrnsArtWord out)
                                            (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                              (barkVatIlksRateWord outIlks)
                                              (barkIlksChopWord σ' I))).toNat *
                                            (barkVatIlksRateWord outIlks).toNat <
                                            UInt256.size
                                      · by_cases hdusty :
                                            (barkLeftoverDueWord (barkVatUrnsArtWord out)
                                              (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                                (barkVatIlksRateWord outIlks)
                                                (barkIlksChopWord σ' I))
                                              (barkVatIlksRateWord outIlks)).toNat <
                                              (barkVatIlksDustWord outIlks).toNat
                                        · obtain ⟨_, _, rd3700⟩ :=
                                            RD.dogBarkDustyLeftoverToDinkEntry
                                              (v := v) (code := code) (ret := ⟨448⟩)
                                              (sel := solcSelectorWord I) (R := [])
                                              (σ := σ'') hpatch hleftover hfitLeftoverDue
                                              hdusty rd3594 (by simp)
                                          by_cases hfitInkDart :
                                              (barkVatUrnsInkWord out).toNat *
                                                (barkVatUrnsArtWord out).toNat <
                                                UInt256.size
                                          · obtain ⟨_, _, rd3726⟩ :=
                                              RD.dogBarkComputeDink
                                                (v := v) (code := code) (ret := ⟨448⟩)
                                                (sel := solcSelectorWord I) (R := [])
                                                (σ := σ'') hpatch hfitInkDart hartNe rd3700
                                                (by simp)
                                            by_cases hdinkPos :
                                                0 < (barkDinkWord (barkVatUrnsInkWord out)
                                                  (barkVatUrnsArtWord out)
                                                  (barkVatUrnsArtWord out)).toNat
                                            · obtain ⟨_, _, rd3797⟩ :=
                                                RD.dogBarkDinkGuardOk
                                                  (v := v) (code := code) (ret := ⟨448⟩)
                                                  (sel := solcSelectorWord I) (R := [])
                                                  hpatch hdinkPos rd3726 (by simp)
                                              by_cases hdartBound :
                                                  (barkVatUrnsArtWord out).toNat ≤
                                                    dogInt256LimitWord.toNat
                                              · by_cases hdinkBound :
                                                    (barkDinkWord (barkVatUrnsInkWord out)
                                                      (barkVatUrnsArtWord out)
                                                      (barkVatUrnsArtWord out)).toNat ≤
                                                      dogInt256LimitWord.toNat
                                                · obtain ⟨_, _, _rd3885⟩ :=
                                                    RD.dogBarkInt256GuardOk
                                                      (v := v) (code := code) (ret := ⟨448⟩)
                                                      (sel := solcSelectorWord I) (R := [])
                                                      hpatch hdartBound hdinkBound rd3797
                                                      (by simp)
                                                  exact True.intro
                                                · exact True.intro
                                              · exact True.intro
                                            · exact True.intro
                                          · exact True.intro
                                        · have hnotDusty :
                                              (barkVatIlksDustWord outIlks).toNat ≤
                                                (barkLeftoverDueWord (barkVatUrnsArtWord out)
                                                  (barkDartWord σ'' σ' I
                                                    (barkVatUrnsArtWord out)
                                                    (barkVatIlksRateWord outIlks)
                                                    (barkIlksChopWord σ' I))
                                                  (barkVatIlksRateWord outIlks)).toNat := by
                                            omega
                                          by_cases hfitPartialDue :
                                              (barkDartWord σ'' σ' I
                                                (barkVatUrnsArtWord out)
                                                (barkVatIlksRateWord outIlks)
                                                (barkIlksChopWord σ' I)).toNat *
                                                (barkVatIlksRateWord outIlks).toNat <
                                                UInt256.size
                                          · by_cases hpartialDueOk :
                                                (barkVatIlksDustWord outIlks).toNat ≤
                                                  (barkPartialDueWord
                                                    (barkDartWord σ'' σ' I
                                                      (barkVatUrnsArtWord out)
                                                      (barkVatIlksRateWord outIlks)
                                                      (barkIlksChopWord σ' I))
                                                    (barkVatIlksRateWord outIlks)).toNat
                                            · obtain ⟨_, _, rd3700⟩ :=
                                                RD.dogBarkPartialLeftoverToDinkEntry
                                                  (v := v) (code := code) (ret := ⟨448⟩)
                                                  (sel := solcSelectorWord I) (R := [])
                                                  (σ := σ'') hpatch hleftover hfitLeftoverDue
                                                  hnotDusty hfitPartialDue hpartialDueOk
                                                  rd3594 (by simp)
                                              by_cases hfitInkDart :
                                                  (barkVatUrnsInkWord out).toNat *
                                                    (barkDartWord σ'' σ' I
                                                      (barkVatUrnsArtWord out)
                                                      (barkVatIlksRateWord outIlks)
                                                      (barkIlksChopWord σ' I)).toNat <
                                                    UInt256.size
                                              · obtain ⟨_, _, rd3726⟩ :=
                                                  RD.dogBarkComputeDink
                                                    (v := v) (code := code) (ret := ⟨448⟩)
                                                    (sel := solcSelectorWord I) (R := [])
                                                    (σ := σ'') hpatch hfitInkDart hartNe rd3700
                                                    (by simp)
                                                by_cases hdinkPos :
                                                    0 < (barkDinkWord (barkVatUrnsInkWord out)
                                                      (barkDartWord σ'' σ' I
                                                        (barkVatUrnsArtWord out)
                                                        (barkVatIlksRateWord outIlks)
                                                        (barkIlksChopWord σ' I))
                                                      (barkVatUrnsArtWord out)).toNat
                                                · obtain ⟨_, _, rd3797⟩ :=
                                                    RD.dogBarkDinkGuardOk
                                                      (v := v) (code := code) (ret := ⟨448⟩)
                                                      (sel := solcSelectorWord I) (R := [])
                                                      hpatch hdinkPos rd3726 (by simp)
                                                  by_cases hdartBound :
                                                      (barkDartWord σ'' σ' I
                                                        (barkVatUrnsArtWord out)
                                                        (barkVatIlksRateWord outIlks)
                                                        (barkIlksChopWord σ' I)).toNat ≤
                                                        dogInt256LimitWord.toNat
                                                  · by_cases hdinkBound :
                                                        (barkDinkWord (barkVatUrnsInkWord out)
                                                          (barkDartWord σ'' σ' I
                                                            (barkVatUrnsArtWord out)
                                                            (barkVatIlksRateWord outIlks)
                                                            (barkIlksChopWord σ' I))
                                                          (barkVatUrnsArtWord out)).toNat ≤
                                                          dogInt256LimitWord.toNat
                                                    · obtain ⟨_, _, _rd3885⟩ :=
                                                        RD.dogBarkInt256GuardOk
                                                          (v := v) (code := code) (ret := ⟨448⟩)
                                                          (sel := solcSelectorWord I) (R := [])
                                                          hpatch hdartBound hdinkBound rd3797
                                                          (by simp)
                                                      exact True.intro
                                                    · exact True.intro
                                                  · exact True.intro
                                                · exact True.intro
                                              · exact True.intro
                                            · exact True.intro
                                          · exact True.intro
                                      · exact True.intro
                                  · exact True.intro
                                · exact True.intro
                              by_cases hfitRoom :
                                  (barkRoomWord σ'' σ' I).toNat * dogWadWord.toNat <
                                    UInt256.size
                              · by_cases hchopNe : barkIlksChopWord σ' I ≠ ⟨0⟩
                                · have hslot5 :
                                      solcSlotWordAt ⟨5⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv =
                                        solcSlotWordAt ⟨5⟩ σ'' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt ⟨5⟩ m I) hAccountsIlks
                                    simpa [evmIlksPostStele, evmPostStele, evmStele, initState]
                                      using h.symm
                                  have hslot4 :
                                      solcSlotWordAt ⟨4⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv =
                                        solcSlotWordAt ⟨4⟩ σ'' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt ⟨4⟩ m I) hAccountsIlks
                                    simpa [evmIlksPostStele, evmPostStele, evmStele, initState]
                                      using h.symm
                                  have hAccountsUrns :
                                      Eq σ' evmPostStele.accountMap := by
                                    simpa [evmPostEvm] using hStateCall.accountMap
                                  have hmilkDirt :
                                      solcSlotWordAt (barkIlksDirtSlotFor I)
                                          evmPostStele.accountMap evmPostStele.executionEnv =
                                        barkIlksDirtWord σ' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt (barkIlksDirtSlotFor I) m I) hAccountsUrns
                                    rw [barkIlksDirtWord_eq_slotFor (σ := σ') (I := I)
                                      hsz100]
                                    simpa [evmPostStele, evmStele, initState] using h.symm
                                  have hmilkHole :
                                      solcSlotWordAt (barkIlksHoleSlotFor I)
                                          evmPostStele.accountMap evmPostStele.executionEnv =
                                        barkIlksHoleWord σ' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt (barkIlksHoleSlotFor I) m I) hAccountsUrns
                                    rw [barkIlksHoleWord_eq_slotFor (σ := σ') (I := I)
                                      hsz100]
                                    simpa [evmPostStele, evmStele, initState] using h.symm
                                  have hmilkChop :
                                      solcSlotWordAt (barkIlksChopSlotFor I)
                                          evmPostStele.accountMap evmPostStele.executionEnv =
                                        barkIlksChopWord σ' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt (barkIlksChopSlotFor I) m I) hAccountsUrns
                                    rw [barkIlksChopWord_eq_slotFor (σ := σ') (I := I)
                                      hsz100]
                                    simpa [evmPostStele, evmStele, initState] using h.symm
                                  have hmilkClip :
                                      solcAddressSlotWord (barkIlksClipSlotFor I)
                                          evmPostStele.accountMap evmPostStele.executionEnv =
                                        barkIlksClipWord σ' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt (barkIlksClipSlotFor I) m I) hAccountsUrns
                                    rw [barkIlksClipWord_eq_slotFor (σ := σ') (I := I)
                                      hsz100]
                                    simpa [solcAddressSlotWord, evmPostStele, evmStele,
                                      initState] using
                                      congrArg (fun word => UInt256.land word solcAddrMask)
                                        h.symm
                                  have hlimitSource :
                                      (solcSlotWordAt ⟨5⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv).toNat <
                                        (solcSlotWordAt ⟨4⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv).toNat ∧
                                      (solcSlotWordAt (barkIlksDirtSlotFor I)
                                          evmPostStele.accountMap
                                          evmPostStele.executionEnv).toNat <
                                        (solcSlotWordAt (barkIlksHoleSlotFor I)
                                          evmPostStele.accountMap
                                          evmPostStele.executionEnv).toNat := by
                                    exact
                                      ⟨by simpa [hslot5, hslot4] using hlimit.1,
                                        by simpa [hmilkDirt, hmilkHole] using hlimit.2⟩
                                  have hglobalRoom :
                                      barkSourceGlobalRoomWord evmIlksPostStele =
                                        barkGlobalRoomWord σ'' I := by
                                    simp [barkSourceGlobalRoomWord, barkGlobalRoomWord, hslot4,
                                      hslot5]
                                  have hilkRoom :
                                      barkSourceIlkRoomWord evmPostStele I =
                                        barkIlkRoomWord σ' I := by
                                    simp [barkSourceIlkRoomWord, barkIlkRoomWord, hmilkHole,
                                      hmilkDirt]
                                  have hroom :
                                      barkSourceRoomWord evmPostStele evmIlksPostStele I =
                                        barkRoomWord σ'' σ' I := by
                                    simp [barkSourceRoomWord, barkRoomWord, hglobalRoom, hilkRoom]
                                  have hfitRoomSource :
                                      (barkSourceRoomWord evmPostStele evmIlksPostStele I).toNat *
                                          dogWadWord.toNat <
                                        UInt256.size := by
                                    simpa [hroom] using hfitRoom
                                  have hchopNeSource :
                                      barkSourceMilkChopWord evmPostStele I ≠ ⟨0⟩ := by
                                    simpa [barkSourceMilkChopWord, hmilkChop] using hchopNe
                                  obtain ⟨k3594Base, C3594Base, rd3594⟩ :=
                                    RD.dogBarkComputeDart
                                      (v := v) (code := code) (ret := ⟨448⟩)
                                      (sel := solcSelectorWord I) (R := [])
                                      (σ := σ'') (σMem := σ')
                                      hpatch hfitRoom hrateNe hchopNe hmload288 rd3543
                                      (by simp)
                                  have hdartSource :
                                      barkSourceDartWord evmPostStele evmIlksPostStele I out
                                          outIlks =
                                        barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                          (barkVatIlksRateWord outIlks)
                                          (barkIlksChopWord σ' I) := by
                                    simp [barkSourceDartWord, barkSourceDartCandidateWord,
                                      barkSourceDartByRateWord, barkSourceRoomWadWord,
                                      barkDartWord, barkDartCandidateWord, barkDartByRateWord,
                                      barkRoomWadWord, hroom, barkSourceMilkChopWord,
                                      hmilkChop]
                                  have hbodyBlockOfTail {result : ExecResult}
                                      (htail :
                                        ExecBlock config
                                          { contract := contract,
                                            locals :=
                                              barkLocalsDart evmPostStele evmIlksPostStele I
                                                out outIlks, immutables := immStore v }
                                          evmIlksPostStele
                                          ([ .ite
                                              (.binary .gt (.var "art") (.var "dart"))
                                              (checkedSubUintInto "leftoverArt" (.var "art")
                                                  (.var "dart") ++
                                                checkedMulUintInto "leftoverDue"
                                                  (.var "leftoverArt") (.var "rate") ++
                                                [ .ite
                                                    (.binary .lt (.var "leftoverDue")
                                                      (.var "dust"))
                                                    [ .assign .localVar (varRef "dart")
                                                        (.var "art") ]
                                                    (checkedMulUintInto "partialDue"
                                                        (.var "dart") (.var "rate") ++
                                                      [ .require
                                                          (.binary .ge (.var "partialDue")
                                                            (.var "dust")) ]) ])
                                              [] ] ++
                                            checkedMulUintInto "inkDart" (.var "ink")
                                              (.var "dart") ++
                                            [ .letDecl "dink" (some uint256)
                                                (.binary .div (.var "inkDart") (.var "art")),
                                              .require (.binary .gt (.var "dink") (.intLit 0)),
                                              .require
                                                (.binary .and
                                                  (.binary .le (.var "dart")
                                                    (.intLit int256Limit))
                                                  (.binary .le (.var "dink")
                                                    (.intLit int256Limit))) ] ++
                                            checkedExternalCallStmts vatExpr "grab"
                                              (.intLit 0)
                                              [ .var "ilk", .var "urn", .var "milkClip",
                                                vowAddr,
                                                asInt256 (.unary .neg (asInt256 (.var "dink"))),
                                                asInt256 (.unary .neg (asInt256 (.var "dart"))) ]
                                              "_grabRet" ++
                                            checkedMulUintInto "due" (.var "dart")
                                              (.var "rate") ++
                                            checkedExternalCallStmts vowAddr "fess"
                                              (.intLit 0) [.var "due"] "_fessRet" ++
                                            checkedMulUintInto "tabBase" (.var "due")
                                              (.var "milkChop") ++
                                            [ .letDecl "tab" (some uint256)
                                                (.binary .div (.var "tabBase")
                                                  (.intLit WAD)) ] ++
                                            checkedAddUintInto "DirtNew" (.storage DirtRef)
                                              (.var "tab") ++
                                            [ .assign .storage DirtRef (.var "DirtNew") ] ++
                                            checkedAddUintInto "ilkDirtNew" (.var "milkDirt")
                                              (.var "tab") ++
                                            [ .assign .storage (ilksF (.var "ilk") "dirt")
                                                (.var "ilkDirtNew") ] ++
                                            checkedExternalCallStmts (.var "milkClip") "kick"
                                              (.intLit 0)
                                              [.var "tab", .var "dink", .var "urn",
                                                .var "kpr"]
                                              "id" ++
                                            [ .return [.var "id"] ])
                                          result) :
                                      ExecBlock config
                                        { contract := contract, locals := barkLocals I, immutables := immStore v }
                                        evmStele barkTransition.body result := by
                                    have hblock :=
                                      dogBarkVatIlksDartTailSourceBlock (v := v)
                                        (σ := σ) (σ₀ := σ₀)
                                        (A := A) (I := I) (g := g)
                                        (evmUrns := evmPostStele)
                                        (evmIlks := evmIlksPostStele) (out := out)
                                        (outIlks := outIlks) hwv hliveStele hvatCode
                                        hcallStele hdecUrns hvatIlksCode hcallIlksStele
                                        hdecIlks hfitInk hfitArt hspotPos hsafeLt
                                        hlimitSource hfitRoomSource hrateNe hchopNeSource
                                        hsz100 htail
                                    simpa [evmStele] using hblock
                                  have hbodyRevertOfTail := fun htail ↦
                                    ExecFuncBody.execBlockRevert
                                      (hbodyBlockOfTail (result := .reverted) htail)
                                  have hbodyReturnOfTail {cs evmRet retVal} := fun htail ↦
                                    ExecFuncBody.execBlockRet
                                      (hbodyBlockOfTail
                                        (result := .returned cs evmRet retVal) htail)
                                  have hbodyStaticOfTail := fun htail ↦
                                    ExecFuncBody.execBlockStatic
                                      (hbodyBlockOfTail (result := .staticViolation) htail)
                                  let art := barkVatUrnsArtWord out
                                  let ink := barkVatUrnsInkWord out
                                  let rate := barkVatIlksRateWord outIlks
                                  let dust := barkVatIlksDustWord outIlks
                                  let spot := barkVatIlksSpotWord outIlks
                                  let room := barkRoomWord σ'' σ' I
                                  let milkChop := barkIlksChopWord σ' I
                                  let mem0 := barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks
                                  let dart0 := barkDartWord σ'' σ' I art rate milkChop
                                  have hrd3594Local :
                                      ∃ k C,
                                      RD code I (Sat256.ofUInt256 g) evmEvm ⟨3594⟩
                                        (room :: spot :: dust :: rate :: dart0 :: ⟨256⟩ ::
                                          art :: ink :: ⟨0⟩ :: barkKprKey I ::
                                          barkUrnKey I :: barkIlkWord I :: ⟨448⟩ ::
                                          solcSelectorWord I :: [])
                                        mem0 (UInt256.ofNat 17) outIlks σ'' k C := by
                                    refine ⟨k3594Base, C3594Base, ?_⟩
                                    simpa [room, spot, dust, rate, dart0, art, ink, milkChop,
                                      mem0] using rd3594
                                  obtain ⟨k3594, C3594, rd3594Local⟩ := hrd3594Local
                                  have hdartSourceLocal :
                                      barkSourceDartWord evmPostStele evmIlksPostStele I out
                                          outIlks = dart0 := by
                                    simpa [dart0, art, rate, milkChop] using hdartSource
                                  have finishFromDartEntry (dart : UInt256)
                                      (localsAfter : Store)
                                      (hleftover :
                                        ExecBlock config
                                          { contract := contract,
                                            locals :=
                                              barkLocalsDart evmPostStele evmIlksPostStele I
                                                out outIlks, immutables := immStore v }
                                          evmIlksPostStele
                                          [ .ite
                                              (.binary .gt (.var "art") (.var "dart"))
                                              (checkedSubUintInto "leftoverArt" (.var "art")
                                                  (.var "dart") ++
                                                checkedMulUintInto "leftoverDue"
                                                  (.var "leftoverArt") (.var "rate") ++
                                                [ .ite
                                                    (.binary .lt (.var "leftoverDue")
                                                      (.var "dust"))
                                                    [ .assign .localVar (varRef "dart")
                                                        (.var "art") ]
                                                    (checkedMulUintInto "partialDue"
                                                        (.var "dart") (.var "rate") ++
                                                      [ .require
                                                          (.binary .ge (.var "partialDue")
                                                            (.var "dust")) ]) ])
                                              [] ]
                                          (.ok { contract := contract, locals := localsAfter, immutables := immStore v }
                                            evmIlksPostStele))
                                      (hink :
                                        localsAfter.get? "ink" =
                                          some (.int (Int.ofNat ink.toNat)))
                                      (hdart :
                                        localsAfter.get? "dart" =
                                          some (.int (Int.ofNat dart.toNat)))
                                      (hart :
                                        localsAfter.get? "art" =
                                          some (.int (Int.ofNat art.toNat)))
                                      (hrateAfter :
                                        localsAfter.get? "rate" =
                                          some (.int (Int.ofNat rate.toNat)))
                                      (hmilkClipAfter :
                                        localsAfter.get? "milkClip" =
                                          some (.address (AccountAddress.ofNat
                                            (barkIlksClipWord σ' I).toNat)))
                                      (hmilkChopAfter :
                                        localsAfter.get? "milkChop" =
                                          some (.int (Int.ofNat milkChop.toNat)))
                                      (hmilkDirtAfter :
                                        localsAfter.get? "milkDirt" =
                                          some (.int (Int.ofNat
                                            (barkIlksDirtWord σ' I).toNat)))
                                      (hilkAfter :
                                        localsAfter.get? "ilk" =
                                          some (.fixedBytes bytes32Width (barkIlkBytes I)))
                                      (hurnAfter :
                                        localsAfter.get? "urn" =
                                          some (.address (barkUrn I)))
                                      (hkprAfter :
                                        localsAfter.get? "kpr" =
                                          some (.address (barkKpr I)))
                                      (hvowAfter : localsAfter.get? "vow" = none)
                                      (hDirtAfter : localsAfter.get? "Dirt" = none)
                                      (hilksAfter : localsAfter.get? "ilks" = none)
                                      (hdartLeArt : dart.toNat ≤ art.toNat)
                                      {k3700 C3700 : ℕ}
                                      (rd3700 :
                                        RD code I (Sat256.ofUInt256 g) evmEvm ⟨3700⟩
                                          (room :: spot :: dust :: rate :: dart :: ⟨256⟩ ::
                                            art :: ink :: ⟨0⟩ :: barkKprKey I ::
                                            barkUrnKey I :: barkIlkWord I :: ⟨448⟩ ::
                                          solcSelectorWord I :: [])
                                        mem0 (UInt256.ofNat 17) outIlks σ''
                                          k3700 C3700) :
                                      runtimeRefinementFor config contract
                                        σ σ₀ g A I (immStore v) := by
                                    let afterIntGuard : List Stmt :=
                                      checkedExternalCallStmts vatExpr "grab"
                                        (.intLit 0)
                                        [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
                                          asInt256 (.unary .neg (asInt256 (.var "dink"))),
                                          asInt256 (.unary .neg (asInt256 (.var "dart"))) ]
                                        "_grabRet" ++
                                      checkedMulUintInto "due" (.var "dart") (.var "rate") ++
                                      checkedExternalCallStmts vowAddr "fess" (.intLit 0)
                                        [.var "due"] "_fessRet" ++
                                      checkedMulUintInto "tabBase" (.var "due")
                                        (.var "milkChop") ++
                                      [ .letDecl "tab" (some uint256)
                                          (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
                                      checkedAddUintInto "DirtNew" (.storage DirtRef)
                                        (.var "tab") ++
                                      [ .assign .storage DirtRef (.var "DirtNew") ] ++
                                      checkedAddUintInto "ilkDirtNew" (.var "milkDirt")
                                        (.var "tab") ++
                                      [ .assign .storage (ilksF (.var "ilk") "dirt")
                                          (.var "ilkDirtNew") ] ++
                                      checkedExternalCallStmts (.var "milkClip") "kick"
                                        (.intLit 0)
                                        [.var "tab", .var "dink", .var "urn", .var "kpr"]
                                        "id" ++
                                      [ .return [.var "id"] ]
                                    let afterDinkGuard : List Stmt :=
                                      [ .require
                                          (.binary .and
                                            (.binary .le (.var "dart") (.intLit int256Limit))
                                            (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
                                      afterIntGuard
                                    let afterInkDart : List Stmt :=
                                      [ .letDecl "dink" (some uint256)
                                          (.binary .div (.var "inkDart") (.var "art")),
                                        .require (.binary .gt (.var "dink") (.intLit 0)),
                                        .require
                                          (.binary .and
                                            (.binary .le (.var "dart") (.intLit int256Limit))
                                            (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
                                      afterIntGuard
                                    by_cases hfitInkDart :
                                        ink.toNat * dart.toNat < UInt256.size
                                    · obtain ⟨_, _, rd3726⟩ :=
                                        RD.dogBarkComputeDink
                                          (v := v) (code := code) (ret := ⟨448⟩)
                                          (sel := solcSelectorWord I) (R := [])
                                          (room := room) (spot := spot) (dust := dust)
                                          (rate := rate) (dart := dart) (art := art)
                                          (ink := ink) hpatch hfitInkDart hartNe rd3700
                                          (by simp)
                                      let dink := barkDinkWord ink dart art
                                      let localsDink :=
                                        barkLocalsDink
                                          (barkLocalsInkDart localsAfter
                                            (barkInkDartWord ink dart)) dink
                                      have hdinkGet :
                                          localsDink.get? "dink" =
                                            some (.int (Int.ofNat dink.toNat)) := by
                                        simpa [localsDink, dink] using
                                          barkLocalsDink_get_dink
                                            (barkLocalsInkDart localsAfter
                                              (barkInkDartWord ink dart))
                                            (barkDinkWord ink dart art)
                                      have hdartDinkGet :
                                          localsDink.get? "dart" =
                                            some (.int (Int.ofNat dart.toNat)) := by
                                        simpa [localsDink, dink] using
                                          barkLocalsDink_get_preserved
                                            (locals :=
                                              barkLocalsInkDart localsAfter
                                                (barkInkDartWord ink dart))
                                            (dink := barkDinkWord ink dart art) (name := "dart")
                                            (value := .int (Int.ofNat dart.toNat)) (by decide)
                                            (barkLocalsInkDart_get_preserved
                                              (locals := localsAfter)
                                              (inkDart := barkInkDartWord ink dart)
                                              (name := "dart")
                                              (value := .int (Int.ofNat dart.toNat))
                                              (by decide) hdart)
                                      by_cases hdinkPos : 0 < dink.toNat
                                      · obtain ⟨_, _, rd3797⟩ :=
                                          RD.dogBarkDinkGuardOk
                                            (v := v) (code := code) (ret := ⟨448⟩)
                                            (sel := solcSelectorWord I) (R := [])
                                            hpatch (by simpa [dink] using hdinkPos) rd3726
                                            (by simp)
                                        by_cases hdartBound :
                                            dart.toNat ≤ dogInt256LimitWord.toNat
                                        · by_cases hdinkBound :
                                              dink.toNat ≤ dogInt256LimitWord.toNat
                                          · obtain ⟨_, _, rd3885⟩ :=
                                              RD.dogBarkInt256GuardOk
                                                (v := v) (code := code) (ret := ⟨448⟩)
                                                (sel := solcSelectorWord I) (R := [])
                                                hpatch hdartBound
                                                (by simpa [dink] using hdinkBound) rd3797
                                                (by simp)
                                            have hprefixOk :=
                                              dogBarkPostLeftoverIntGuardOkSource (v := v)
                                                evmIlksPostStele hink hdart hart hfitInkDart
                                                hartNe (by simpa [dink] using hdinkPos)
                                                hdartBound (by simpa [dink] using hdinkBound)
                                            have _hprefixFull :=
                                              execBlock_append hleftover hprefixOk
                                            have hpresDink {name : Ident} {value : Value}
                                                (hdinkName : ("dink" == name) = false)
                                                (hinkDartName : ("inkDart" == name) = false)
                                                (hget : localsAfter.get? name = some value) :
                                                localsDink.get? name = some value := by
                                              simpa [localsDink, dink] using
                                                barkLocalsDink_get_preserved
                                                  (locals :=
                                                    barkLocalsInkDart localsAfter
                                                      (barkInkDartWord ink dart))
                                                  (dink := barkDinkWord ink dart art)
                                                  (name := name) (value := value) hdinkName
                                                  (barkLocalsInkDart_get_preserved
                                                    (locals := localsAfter)
                                                    (inkDart := barkInkDartWord ink dart)
                                                    (name := name) (value := value)
                                                    hinkDartName hget)
                                            have hpresDinkNone {name : Ident}
                                                (hdinkName : ("dink" == name) = false)
                                                (hinkDartName : ("inkDart" == name) = false)
                                                (hget : localsAfter.get? name = none) :
                                                localsDink.get? name = none := by
                                              change (barkLocalsDink
                                                (barkLocalsInkDart localsAfter
                                                  (barkInkDartWord ink dart))
                                                (barkDinkWord ink dart art)).get? name = none
                                              rw [barkLocalsDink,
                                                store_get_ne _
                                                  (.int (Int.ofNat
                                                    (barkDinkWord ink dart art).toNat))
                                                  hdinkName,
                                                barkLocalsInkDart,
                                                store_get_ne _
                                                  (.int (Int.ofNat
                                                    (barkInkDartWord ink dart).toNat))
                                                  hinkDartName]
                                              exact hget
                                            have hrateDink :
                                                localsDink.get? "rate" =
                                                  some (.int (Int.ofNat rate.toNat)) :=
                                              hpresDink (by decide) (by decide) hrateAfter
                                            have hmilkClipDink :
                                                localsDink.get? "milkClip" =
                                                  some (.address (AccountAddress.ofNat
                                                    (barkIlksClipWord σ' I).toNat)) :=
                                              hpresDink (by decide) (by decide) hmilkClipAfter
                                            have hmilkChopDink :
                                                localsDink.get? "milkChop" =
                                                  some (.int (Int.ofNat milkChop.toNat)) :=
                                              hpresDink (by decide) (by decide) hmilkChopAfter
                                            have hmilkDirtDink :
                                                localsDink.get? "milkDirt" =
                                                  some (.int (Int.ofNat
                                                    (barkIlksDirtWord σ' I).toNat)) :=
                                              hpresDink (by decide) (by decide) hmilkDirtAfter
                                            have hilkDink :
                                                localsDink.get? "ilk" =
                                                  some (.fixedBytes bytes32Width
                                                    (barkIlkBytes I)) :=
                                              hpresDink (by decide) (by decide) hilkAfter
                                            have hurnDink :
                                                localsDink.get? "urn" =
                                                  some (.address (barkUrn I)) :=
                                              hpresDink (by decide) (by decide) hurnAfter
                                            have hkprDink :
                                                localsDink.get? "kpr" =
                                                  some (.address (barkKpr I)) :=
                                              hpresDink (by decide) (by decide) hkprAfter
                                            have hvowDink : localsDink.get? "vow" = none :=
                                              hpresDinkNone (by decide) (by decide) hvowAfter
                                            have hDirtDink : localsDink.get? "Dirt" = none :=
                                              hpresDinkNone (by decide) (by decide) hDirtAfter
                                            have hilksDink : localsDink.get? "ilks" = none :=
                                              hpresDinkNone (by decide) (by decide) hilksAfter
                                            let afterGrab : List Stmt :=
                                              checkedMulUintInto "due" (.var "dart")
                                                (.var "rate") ++
                                              checkedExternalCallStmts vowAddr "fess"
                                                (.intLit 0) [.var "due"] "_fessRet" ++
                                              checkedMulUintInto "tabBase" (.var "due")
                                                (.var "milkChop") ++
                                              [ .letDecl "tab" (some uint256)
                                                  (.binary .div (.var "tabBase")
                                                    (.intLit WAD)) ] ++
                                              checkedAddUintInto "DirtNew" (.storage DirtRef)
                                                (.var "tab") ++
                                              [ .assign .storage DirtRef (.var "DirtNew") ] ++
                                              checkedAddUintInto "ilkDirtNew" (.var "milkDirt")
                                                (.var "tab") ++
                                              [ .assign .storage
                                                  (ilksF (.var "ilk") "dirt")
                                                  (.var "ilkDirtNew") ] ++
                                              checkedExternalCallStmts (.var "milkClip") "kick"
                                                (.intLit 0)
                                                [.var "tab", .var "dink", .var "urn",
                                                  .var "kpr"]
                                                "id" ++
                                              [ .return [.var "id"] ]
                                            have hmload256Grab :
                                                (if (⟨256⟩ : UInt256).toNat ≥ mem0.size then ⟨0⟩
                                                 else UInt256.ofNat
                                                  (fromByteArrayBigEndian
                                                    (mem0.readWithPadding
                                                      (⟨256⟩ : UInt256).toNat 32))) =
                                                  barkIlksClipWord σ' I := by
                                              simpa [mem0] using
                                                barkVatIlksPostCallMem_mload256_long
                                                  (σ := σ') (I := I) solcFreePtrMem_size
                                                  hretLong hosz hretIlksLong hoszIlks
                                            by_cases hvatGrabCodeZero :
                                                Reasoning.Theory.extCodeSizeWord σ''
                                                  (barkVatWord v) = ⟨0⟩
                                            · obtain ⟨_, _, rd4023⟩ :=
                                                RD.dogBarkVatGrabExtcodesizeGuard
                                                  (v := v) (code := code) (ret := ⟨448⟩)
                                                  (sel := solcSelectorWord I) (R := [])
                                                  (σ := σ'') (σMem := σ')
                                                  hpatch
                                                  (by simpa [mem0] using hpostMemSize)
                                                  (by simpa [mem0] using hpostMemRead64)
                                                  hmload256Grab rd3885 (by simp)
                                              have hvatGrabZeroStele :
                                                  Reasoning.Theory.extCodeSizeWord
                                                    evmIlksPostStele.accountMap
                                                    (barkVatWord v) = ⟨0⟩ := by
                                                simpa [evmIlksPostEvm, evmIlksPostStele,
                                                  ← hAccountsIlks] using hvatGrabCodeZero
                                              have hvatNoCode :
                                                  (UInt256.ofNat
                                                    ((evmIlksPostStele.lookupAccount
                                                      (AccountAddress.ofNat v.vat.toNat)).option
                                                        0 (fun acc => acc.code.size))).toNat =
                                                    0 :=
                                                barkVatCode_zero_of_state_codeSize_zero
                                                  (v := v) (evm := evmIlksPostStele)
                                                  hvatGrabZeroStele
                                              have hvatExpr :
                                                  evalExpr? config
                                                    { contract := contract,
                                                      locals := localsDink, immutables := immStore v }
                                                    evmIlksPostStele vatExpr =
                                                    .ok (.address
                                                      (AccountAddress.ofNat v.vat.toNat)) :=
                                                evalExpr_barkVat_state (v := v)
                                                  (evm := evmIlksPostStele)
                                                  (locals := localsDink)
                                              have hguardFalse :
                                                  evalExpr? config
                                                    { contract := contract,
                                                      locals := localsDink, immutables := immStore v }
                                                    evmIlksPostStele
                                                    (.binary .gt (.extCodeSize vatExpr)
                                                      (.intLit 0)) = .ok (.bool false) :=
                                                evalExpr_barkVatCodeGuard_false (v := v)
                                                  (locals := localsDink) hvatExpr hvatNoCode
                                              have hgrabRev :=
                                                dogBarkVatGrabNoCodeBlock (v := v)
                                                  (evm := evmIlksPostStele)
                                                  (locals := localsDink) hguardFalse
                                              have htailPrefix :=
                                                execBlock_append hprefixOk hgrabRev
                                              have htailBody :
                                                  ExecTransitionBody config contract
                                                    evmStele (barkLocals I)
                                                    barkTransition.body .reverted (immStore v) := by
                                                apply hbodyRevertOfTail
                                                refine dogBarkDartTailFromLeftoverBlock
                                                  hleftover ?_
                                                simpa only [afterIntGuard, afterGrab, localsDink,
                                                  dink, List.append_assoc] using
                                                  execBlock_append_term (s2 := afterGrab)
                                                    htailPrefix
                                                    (by intro f e h; cases h)
                                              have hrev :=
                                                RD.dogBarkVatGrabNoCodeRevert
                                                  (v := v) (code := code) hpatch rd4023
                                                  hvatGrabCodeZero (by simp)
                                              exact hrev.reEquivExecutionRevert hcode
                                                hdispatch hdecode htailBody
                                            · obtain ⟨σGrab, zGrab, outGrab, AGrab,
                                                  _, _, rd4039, hcallGrabEvmRaw,
                                                  houtGrabSize⟩ :=
                                                RD.dogBarkVatGrabPostCall
                                                  (v := v) (code := code) (s0 := evmEvm)
                                                  (evm := evmIlksPostEvm) (ret := ⟨448⟩)
                                                  (sel := solcSelectorWord I) (R := [])
                                                  hpatch rd3885 hsz100
                                                  (by simpa [mem0] using hpostMemSize)
                                                  (by simpa [mem0] using hpostMemRead64)
                                                  hmload256Grab hvatGrabCodeZero
                                                  (by simp [evmIlksPostEvm, evmPostEvm,
                                                    evmEvm, initState])
                                                  (by simp [evmIlksPostEvm])
                                                  (by simp [evmIlksPostEvm, evmPostEvm,
                                                    evmEvm, initState])
                                                  hdepthLt
                                                  (by simpa [dink] using hdinkBound)
                                                  hdartBound (by simp)
                                              let evmGrabEvm :=
                                                { evmIlksPostEvm with accountMap := σGrab, substate := AGrab }
                                              have hcallGrabEvm :
                                                  typedCallViaEVM config evmIlksPostEvm
                                                    (EVM.address
                                                      (AccountAddress.ofNat v.vat.toNat))
                                                    "grab" 0
                                                    [.fixedBytes bytes32Width (barkIlkBytes I),
                                                      .address (barkUrn I),
                                                      .address (AccountAddress.ofNat
                                                        (barkIlksClipWord σ' I).toNat),
                                                      .address (AccountAddress.ofNat
                                                        (barkVowWord σ'' I).toNat),
                                                      .int (-(Int.ofNat dink.toNat)),
                                                      .int (-(Int.ofNat dart.toNat))]
                                                    (zGrab, evmGrabEvm, outGrab) true := by
                                                simpa [evmGrabEvm] using hcallGrabEvmRaw
                                              have hvowWordIlks :
                                                  barkVowWord evmIlksPostStele.accountMap
                                                      evmIlksPostStele.executionEnv =
                                                    barkVowWord σ'' I := by
                                                have hslot :=
                                                  congrArg (fun m => solcSlotWordAt ⟨2⟩ m I) hAccountsIlks
                                                simpa [barkVowWord, evmIlksPostStele,
                                                  evmPostStele, evmStele, initState] using
                                                  congrArg
                                                    (fun word => UInt256.land solcAddrMask word)
                                                    hslot.symm
                                              obtain ⟨σGrabStele, AGrabStele,
                                                  hcallGrabSteleRaw, hAccountsGrabRaw⟩ :=
                                                Reasoning.Theory.typedCallViaEVM_sameInputs
                                                  (evm_stele := evmIlksPostStele)
                                                  hcallGrabEvm
                                                  (by simpa [evmIlksPostEvm] using
                                                    hAccountsIlks)
                                                  (by simp [evmIlksPostEvm,
                                                    evmIlksPostStele, evmPostEvm, evmPostStele,
                                                    evmEvm, evmStele, initState])
                                                  (by simp [evmIlksPostEvm,
                                                    evmIlksPostStele, evmPostEvm, evmPostStele,
                                                    evmEvm, evmStele, initState])
                                              let evmGrabStele :=
                                                { evmIlksPostStele with
                                                  accountMap := σGrabStele,
                                                  substate := AGrabStele }
                                              have hcallGrabStele :
                                                  typedCallViaEVM config evmIlksPostStele
                                                    (EVM.address
                                                      (AccountAddress.ofNat v.vat.toNat))
                                                    "grab" 0
                                                    [.fixedBytes bytes32Width (barkIlkBytes I),
                                                      .address (barkUrn I),
                                                      .address (AccountAddress.ofNat
                                                        (barkIlksClipWord σ' I).toNat),
                                                      .address (AccountAddress.ofNat
                                                        (barkVowWord evmIlksPostStele.accountMap
                                                          evmIlksPostStele.executionEnv).toNat),
                                                      .int (-(Int.ofNat dink.toNat)),
                                                      .int (-(Int.ofNat dart.toNat))]
                                                    (zGrab, evmGrabStele, outGrab) true := by
                                                simpa [evmGrabStele, hvowWordIlks] using
                                                  hcallGrabSteleRaw
                                              have hvatGrabNonzeroStele :
                                                  Reasoning.Theory.extCodeSizeWord
                                                    evmIlksPostStele.accountMap
                                                    (barkVatWord v) ≠ ⟨0⟩ := by
                                                simpa [evmIlksPostEvm, evmIlksPostStele,
                                                  ← hAccountsIlks] using hvatGrabCodeZero
                                              have hvatCodePosStele :
                                                  0 < (UInt256.ofNat
                                                    ((evmIlksPostStele.lookupAccount
                                                      (AccountAddress.ofNat v.vat.toNat)).option
                                                        0 (fun acc => acc.code.size))).toNat :=
                                                barkVatCode_pos_of_state_codeSize_ne (v := v)
                                                  (evm := evmIlksPostStele)
                                                  hvatGrabNonzeroStele
                                              have hvatExpr :
                                                  evalExpr? config
                                                    { contract := contract,
                                                      locals := localsDink, immutables := immStore v }
                                                    evmIlksPostStele vatExpr =
                                                    .ok (.address
                                                      (AccountAddress.ofNat v.vat.toNat)) :=
                                                evalExpr_barkVat_state (v := v)
                                                  (evm := evmIlksPostStele)
                                                  (locals := localsDink)
                                              have hguardTrue :
                                                  evalExpr? config
                                                    { contract := contract,
                                                      locals := localsDink, immutables := immStore v }
                                                    evmIlksPostStele
                                                    (.binary .gt (.extCodeSize vatExpr)
                                                      (.intLit 0)) = .ok (.bool true) :=
                                                evalExpr_barkVatCodeGuard_true (v := v)
                                                  (locals := localsDink) hvatExpr
                                                  hvatCodePosStele
                                              cases zGrab
                                              · simp only [Bool.false_eq_true, if_false] at rd4039 hcallGrabEvm hcallGrabStele
                                                have hgrabRev :=
                                                  dogBarkVatGrabCallFailureBlock (v := v)
                                                    (evm := evmIlksPostStele)
                                                    (evm' := evmGrabStele)
                                                    (locals := localsDink) (I := I)
                                                    (outGrab := outGrab)
                                                    (milkClip := barkIlksClipWord σ' I)
                                                    (dink := dink) (dart := dart)
                                                    hguardTrue hilkDink hurnDink
                                                    hmilkClipDink hvowDink hdinkGet
                                                    hdartDinkGet hdinkBound hdartBound
                                                    hcallGrabStele
                                                have htailPrefix :=
                                                  execBlock_append hprefixOk hgrabRev
                                                have htailBody :
                                                    ExecTransitionBody config contract
                                                      evmStele (barkLocals I)
                                                      barkTransition.body .reverted (immStore v) := by
                                                  apply hbodyRevertOfTail
                                                  refine dogBarkDartTailFromLeftoverBlock
                                                    hleftover ?_
                                                  simpa only [afterIntGuard, afterGrab, localsDink,
                                                    dink, List.append_assoc] using
                                                    execBlock_append_term (s2 := afterGrab)
                                                      htailPrefix
                                                      (by intro f e h; cases h)
                                                have hrev :=
                                                  RD.dogBarkVatGrabCallFailure hpatch rd4039
                                                    houtGrabSize (by simp)
                                                exact hrev.reEquivExecutionRevert hcode
                                                  hdispatch hdecode htailBody
                                              · simp only [Bool.true_eq_false, if_true] at rd4039 hcallGrabEvm hcallGrabStele
                                                obtain ⟨_, _, rd4057⟩ :=
                                                  RD.dogBarkVatGrabCallSuccess hpatch rd4039
                                                    (by simp)
                                                have hgrabOk :=
                                                  dogBarkVatGrabCallSuccessBlock (v := v)
                                                    (evm := evmIlksPostStele)
                                                    (evm' := evmGrabStele)
                                                    (locals := localsDink) (I := I)
                                                    (outGrab := outGrab)
                                                    (milkClip := barkIlksClipWord σ' I)
                                                    (dink := dink) (dart := dart)
                                                    hguardTrue hilkDink hurnDink
                                                    hmilkClipDink hvowDink hdinkGet
                                                    hdartDinkGet hdinkBound hdartBound
                                                    hcallGrabStele
                                                have _hprefixGrab :=
                                                  execBlock_append _hprefixFull hgrabOk
                                                have _hprefixGrabTail :=
                                                  execBlock_append hprefixOk hgrabOk
                                                let localsGrab := barkLocalsGrabRet localsDink
                                                have hpresGrab {name : Ident} {value : Value}
                                                    (hgrabName : ("_grabRet" == name) = false)
                                                    (hget : localsDink.get? name = some value) :
                                                    localsGrab.get? name = some value := by
                                                  simpa [localsGrab] using
                                                    barkLocalsGrabRet_get_preserved
                                                      (locals := localsDink) (name := name)
                                                      (value := value) hgrabName hget
                                                have hpresGrabNone {name : Ident}
                                                    (hgrabName : ("_grabRet" == name) = false)
                                                    (hget : localsDink.get? name = none) :
                                                    localsGrab.get? name = none := by
                                                  change (barkLocalsGrabRet localsDink).get? name =
                                                    none
                                                  rw [barkLocalsGrabRet,
                                                    store_get_ne _ .unit hgrabName]
                                                  exact hget
                                                have hdartGrab :
                                                    localsGrab.get? "dart" =
                                                      some (.int (Int.ofNat dart.toNat)) :=
                                                  hpresGrab (by decide) hdartDinkGet
                                                have hrateGrab :
                                                    localsGrab.get? "rate" =
                                                      some (.int (Int.ofNat rate.toNat)) :=
                                                  hpresGrab (by decide) hrateDink
                                                have hmilkChopGrab :
                                                    localsGrab.get? "milkChop" =
                                                      some (.int (Int.ofNat milkChop.toNat)) :=
                                                  hpresGrab (by decide) hmilkChopDink
                                                have hvowGrab : localsGrab.get? "vow" = none :=
                                                  hpresGrabNone (by decide) hvowDink
                                                have hDirtGrab : localsGrab.get? "Dirt" = none :=
                                                  hpresGrabNone (by decide) hDirtDink
                                                have hfitDue :
                                                    dart.toNat * rate.toNat < UInt256.size := by
                                                  exact barkPartialDue_fit_of_dart_le_art
                                                    hdartLeArt (by simpa [art, rate] using hfitArt)
                                                obtain ⟨_, _, rd4071⟩ :=
                                                  RD.dogBarkDueCheckedMulOk hpatch hfitDue
                                                    rd4057 (by simp)
                                                let due := barkDueWord dart rate
                                                let localsDue := barkLocalsDue localsGrab due
                                                have hdueGet :
                                                    localsDue.get? "due" =
                                                      some (.int (Int.ofNat due.toNat)) := by
                                                  simpa [localsDue, due] using
                                                    barkLocalsDue_get_due localsGrab
                                                      (barkDueWord dart rate)
                                                have hmilkChopDue :
                                                    localsDue.get? "milkChop" =
                                                      some (.int (Int.ofNat milkChop.toNat)) := by
                                                  simpa [localsDue, due] using
                                                    barkLocalsDue_get_preserved
                                                      (locals := localsGrab)
                                                      (due := barkDueWord dart rate)
                                                      (name := "milkChop")
                                                      (value := .int (Int.ofNat milkChop.toNat))
                                                      (by decide) hmilkChopGrab
                                                have hvowDue : localsDue.get? "vow" = none := by
                                                  change (barkLocalsDue localsGrab
                                                    (barkDueWord dart rate)).get? "vow" = none
                                                  rw [barkLocalsDue,
                                                    store_get_ne _
                                                      (.int (Int.ofNat
                                                        (barkDueWord dart rate).toNat))
                                                      (by decide)]
                                                  exact hvowGrab
                                                have hDirtDue : localsDue.get? "Dirt" = none := by
                                                  change (barkLocalsDue localsGrab
                                                    (barkDueWord dart rate)).get? "Dirt" = none
                                                  rw [barkLocalsDue,
                                                    store_get_ne _
                                                      (.int (Int.ofNat
                                                        (barkDueWord dart rate).toNat))
                                                      (by decide)]
                                                  exact hDirtGrab
                                                have hdueOk :=
                                                  dogBarkDueCheckedMulOkSource (v := v)
                                                    evmGrabStele hdartGrab hrateGrab hfitDue
                                                have hAccountsGrab :
                                                    Eq σGrab
                                                      evmGrabStele.accountMap := by
                                                  simpa [evmGrabEvm, evmGrabStele] using
                                                    hAccountsGrabRaw
                                                have hvowWordGrab :
                                                    barkVowWord evmGrabStele.accountMap
                                                        evmGrabStele.executionEnv =
                                                      barkVowWord σGrab I := by
                                                  have hslot :=
                                                    congrArg (fun m => solcSlotWordAt ⟨2⟩ m I) hAccountsGrab
                                                  simpa [barkVowWord, evmGrabStele,
                                                    evmIlksPostStele, evmPostStele, evmStele,
                                                    initState] using
                                                    congrArg
                                                      (fun word =>
                                                        UInt256.land solcAddrMask word)
                                                      hslot.symm
                                                have hmemGrabSize :
                                                    (barkVatGrabPostCallMem σ'' σ' I mem0
                                                      outGrab dink dart).size = 580 := by
                                                  exact barkVatGrabPostCallMem_size
                                                    (σ := σ'') (σMem := σ') (I := I)
                                                    (mem := mem0) (out := outGrab)
                                                    (dink := dink) (dart := dart)
                                                    (by simpa [mem0] using hpostMemSize)
                                                have hmemGrabRead64 :
                                                    (barkVatGrabPostCallMem σ'' σ' I mem0
                                                      outGrab dink dart).readWithPadding 64 32 =
                                                      UInt256.toByteArray ⟨384⟩ := by
                                                  exact barkVatGrabPostCallMem_read64
                                                    (σ := σ'') (σMem := σ') (I := I)
                                                    (mem := mem0) (out := outGrab)
                                                    (dink := dink) (dart := dart)
                                                    (by simpa [mem0] using hpostMemSize)
                                                    (by simpa [mem0] using hpostMemRead64)
                                                let afterFess : List Stmt :=
                                                  checkedMulUintInto "tabBase" (.var "due")
                                                    (.var "milkChop") ++
                                                  [ .letDecl "tab" (some uint256)
                                                      (.binary .div (.var "tabBase")
                                                        (.intLit WAD)) ] ++
                                                  checkedAddUintInto "DirtNew"
                                                    (.storage DirtRef) (.var "tab") ++
                                                  [ .assign .storage DirtRef (.var "DirtNew") ] ++
                                                  checkedAddUintInto "ilkDirtNew"
                                                    (.var "milkDirt") (.var "tab") ++
                                                  [ .assign .storage
                                                      (ilksF (.var "ilk") "dirt")
                                                      (.var "ilkDirtNew") ] ++
                                                  checkedExternalCallStmts (.var "milkClip")
                                                    "kick" (.intLit 0)
                                                    [.var "tab", .var "dink", .var "urn",
                                                      .var "kpr"]
                                                    "id" ++
                                                  [ .return [.var "id"] ]
                                                by_cases hvowCodeZero :
                                                    Reasoning.Theory.extCodeSizeWord
                                                      σGrab (barkVowWord σGrab I) = ⟨0⟩
                                                · obtain ⟨_, _, rd4139⟩ :=
                                                    RD.dogBarkFessExtcodesizeGuard
                                                      (v := v) (code := code)
                                                      (g := Sat256.ofUInt256 g) (s0 := evmEvm)
                                                      (I := I) (ret := ⟨448⟩)
                                                      (sel := solcSelectorWord I) (R := [])
                                                      (σ := σGrab)
                                                      hpatch hmemGrabSize hmemGrabRead64
                                                      rd4071 (by simp)
                                                  have hvowCodeZeroStele :
                                                      Reasoning.Theory.extCodeSizeWord
                                                        evmGrabStele.accountMap
                                                        (barkVowWord evmGrabStele.accountMap
                                                          evmGrabStele.executionEnv) = ⟨0⟩ := by
                                                    have hzero :
                                                        Reasoning.Theory.extCodeSizeWord
                                                          evmGrabStele.accountMap
                                                          (barkVowWord σGrab I) = ⟨0⟩ := by
                                                      simpa only [← hAccountsGrab] using
                                                        hvowCodeZero
                                                    simpa [hvowWordGrab] using hzero
                                                  have hvowNoCode :
                                                      (UInt256.ofNat
                                                        ((evmGrabStele.lookupAccount
                                                          (AccountAddress.ofNat
                                                            (barkVowWord
                                                              evmGrabStele.accountMap
                                                              evmGrabStele.executionEnv).toNat)).option
                                                            0 (fun acc => acc.code.size))).toNat =
                                                        0 :=
                                                    code_zero_of_state_codeSize_zero
                                                      hvowCodeZeroStele
                                                  have hvowReceiver :=
                                                    evalExpr_barkStorageVow (v := v)
                                                      (evm := evmGrabStele)
                                                      (locals := localsDue) hvowDue
                                                  have hfessGuardFalse :
                                                      evalExpr? config
                                                        { contract := contract,
                                                          locals := localsDue, immutables := immStore v }
                                                        evmGrabStele
                                                        (.binary .gt (.extCodeSize vowAddr)
                                                          (.intLit 0)) = .ok (.bool false) :=
                                                    evalExpr_barkAddressCodeGuard_false
                                                      hvowReceiver hvowNoCode
                                                  have hfessRev :=
                                                    dogBarkVowFessNoCodeBlock (v := v)
                                                      (evm := evmGrabStele)
                                                      (locals := localsDue) hfessGuardFalse
                                                  have htailPrefix :=
                                                    execBlock_append
                                                      (execBlock_append _hprefixGrabTail hdueOk)
                                                      hfessRev
                                                  have htailBody :
                                                      ExecTransitionBody config
                                                        contract evmStele (barkLocals I)
                                                        barkTransition.body .reverted (immStore v) := by
                                                    apply hbodyRevertOfTail
                                                    refine dogBarkDartTailFromLeftoverBlock
                                                      hleftover ?_
                                                    simpa only [afterIntGuard, afterGrab, afterFess,
                                                      localsDink, localsGrab, localsDue, due,
                                                      dink, List.append_assoc] using
                                                      execBlock_append_term (s2 := afterFess)
                                                        htailPrefix
                                                        (by intro f e h; cases h)
                                                  have hrev :=
                                                    RD.dogBarkFessNoCodeRevert
                                                      (v := v) (code := code) hpatch rd4139
                                                      hvowCodeZero (by simp)
                                                  exact hrev.reEquivExecutionRevert hcode
                                                    hdispatch hdecode htailBody
                                                · obtain ⟨σFess, zFess, outFess,
                                                    AFess, _, _, rd4155, hcallFessEvmRaw,
                                                    houtFessSize⟩ :=
                                                    RD.dogBarkFessPostCall
                                                      (v := v) (code := code) (s0 := evmEvm)
                                                      (evm := evmGrabEvm) (I := I)
                                                      (ret := ⟨448⟩)
                                                      (sel := solcSelectorWord I) (R := [])
                                                      hpatch rd4071 hmemGrabSize
                                                      hmemGrabRead64 hvowCodeZero
                                                      (by simp [evmGrabEvm,
                                                        evmIlksPostEvm, evmPostEvm, evmEvm,
                                                        initState])
                                                      (by simp [evmGrabEvm])
                                                      (by simp [evmGrabEvm,
                                                        evmIlksPostEvm, evmPostEvm, evmEvm,
                                                        initState])
                                                      hdepthLt (by simp)
                                                  let evmFessEvm :=
                                                    { evmGrabEvm with accountMap := σFess, substate := AFess }
                                                  have hcallFessEvm :
                                                      typedCallViaEVM config evmGrabEvm
                                                        (EVM.address
                                                          (AccountAddress.ofNat
                                                            (barkVowWord σGrab I).toNat))
                                                        "fess" 0
                                                        [.int (Int.ofNat due.toNat)]
                                                        (zFess, evmFessEvm, outFess)
                                                        true := by
                                                    simpa [evmFessEvm] using hcallFessEvmRaw
                                                  obtain ⟨σFessStele, AFessStele,
                                                      hcallFessSteleRaw,
                                                      hAccountsFessRaw⟩ :=
                                                    Reasoning.Theory.typedCallViaEVM_sameInputs
                                                      (evm_stele := evmGrabStele)
                                                      hcallFessEvm
                                                      (by simpa [evmGrabEvm, evmGrabStele] using
                                                        hAccountsGrab)
                                                      (by simp [evmGrabEvm, evmGrabStele,
                                                        evmIlksPostEvm, evmIlksPostStele,
                                                        evmPostEvm, evmPostStele, evmEvm,
                                                        evmStele, initState])
                                                      (by simp [evmGrabEvm, evmGrabStele,
                                                        evmIlksPostEvm, evmIlksPostStele,
                                                        evmPostEvm, evmPostStele, evmEvm,
                                                        evmStele, initState])
                                                  let evmFessStele :=
                                                    { evmGrabStele with
                                                      accountMap := σFessStele,
                                                      substate := AFessStele }
                                                  have hcallFessStele :
                                                      typedCallViaEVM config evmGrabStele
                                                        (EVM.address
                                                          (AccountAddress.ofNat
                                                            (barkVowWord
                                                              evmGrabStele.accountMap
                                                              evmGrabStele.executionEnv).toNat))
                                                        "fess" 0
                                                        [.int (Int.ofNat due.toNat)]
                                                        (zFess, evmFessStele, outFess)
                                                        true := by
                                                    simpa [evmFessEvm, evmFessStele,
                                                      hvowWordGrab] using hcallFessSteleRaw
                                                  have hAccountsFess :
                                                      Eq σFess
                                                        evmFessStele.accountMap := by
                                                    simpa [evmFessEvm, evmFessStele] using
                                                      hAccountsFessRaw
                                                  have hvowCodeNonzeroStele :
                                                      Reasoning.Theory.extCodeSizeWord
                                                        evmGrabStele.accountMap
                                                        (barkVowWord
                                                          evmGrabStele.accountMap
                                                          evmGrabStele.executionEnv) ≠
                                                          ⟨0⟩ := by
                                                    have hne :
                                                        Reasoning.Theory.extCodeSizeWord
                                                          evmGrabStele.accountMap
                                                          (barkVowWord σGrab I) ≠ ⟨0⟩ := by
                                                      simpa only [← hAccountsGrab] using
                                                        hvowCodeZero
                                                    simpa [hvowWordGrab] using hne
                                                  have hvowCodePosStele :
                                                      0 < (UInt256.ofNat
                                                        ((evmGrabStele.lookupAccount
                                                          (AccountAddress.ofNat
                                                            (barkVowWord
                                                              evmGrabStele.accountMap
                                                              evmGrabStele.executionEnv).toNat)).option
                                                            0 (fun acc => acc.code.size))).toNat :=
                                                    code_pos_of_state_codeSize_ne
                                                      hvowCodeNonzeroStele
                                                  have hvowReceiver :=
                                                    evalExpr_barkStorageVow (v := v)
                                                      (evm := evmGrabStele)
                                                      (locals := localsDue) hvowDue
                                                  have hfessGuardTrue :
                                                      evalExpr? config
                                                        { contract := contract,
                                                          locals := localsDue, immutables := immStore v }
                                                        evmGrabStele
                                                        (.binary .gt (.extCodeSize vowAddr)
                                                          (.intLit 0)) = .ok (.bool true) :=
                                                    evalExpr_barkAddressCodeGuard_true
                                                      hvowReceiver hvowCodePosStele
                                                  cases zFess
                                                  · simp only [Bool.false_eq_true, if_false] at rd4155 hcallFessEvm hcallFessStele
                                                    have hfessRev :=
                                                      dogBarkVowFessCallFailureBlock (v := v)
                                                        (evm := evmGrabStele)
                                                        (evm' := evmFessStele)
                                                        (locals := localsDue)
                                                        (outFess := outFess)
                                                        (due := due)
                                                        hfessGuardTrue hvowDue hdueGet
                                                        hcallFessStele
                                                    have htailPrefix :=
                                                      execBlock_append
                                                        (execBlock_append _hprefixGrabTail hdueOk)
                                                        hfessRev
                                                    have htailBody :
                                                        ExecTransitionBody config
                                                          contract evmStele (barkLocals I)
                                                          barkTransition.body .reverted (immStore v) := by
                                                      apply hbodyRevertOfTail
                                                      refine dogBarkDartTailFromLeftoverBlock
                                                        hleftover ?_
                                                      simpa only [afterIntGuard, afterGrab,
                                                        afterFess, localsDink, localsGrab,
                                                        localsDue, due, dink,
                                                        List.append_assoc] using
                                                        execBlock_append_term (s2 := afterFess)
                                                          htailPrefix
                                                          (by intro f e h; cases h)
                                                    have hrev :=
                                                      RD.dogBarkFessCallFailure hpatch rd4155
                                                        houtFessSize (by simp)
                                                    exact hrev.reEquivExecutionRevert hcode
                                                      hdispatch hdecode htailBody
                                                  · simp only [Bool.true_eq_false, if_true] at rd4155 hcallFessEvm hcallFessStele
                                                    obtain ⟨_, _, rd4176⟩ :=
                                                      RD.dogBarkFessCallSuccess hpatch rd4155
                                                        (by simp)
                                                    have hfessOk :=
                                                      dogBarkVowFessCallSuccessBlock (v := v)
                                                        (evm := evmGrabStele)
                                                        (evm' := evmFessStele)
                                                        (locals := localsDue)
                                                        (outFess := outFess)
                                                        (due := due)
                                                        hfessGuardTrue hvowDue hdueGet
                                                        hcallFessStele
                                                    have _hprefixFess :=
                                                      execBlock_append
                                                        (execBlock_append _hprefixGrab hdueOk)
                                                        hfessOk
                                                    have _hprefixFessTail :=
                                                      execBlock_append
                                                        (execBlock_append _hprefixGrabTail hdueOk)
                                                        hfessOk
                                                    let localsFess :=
                                                      barkLocalsFessRet localsDue
                                                    have hpresDue {name : Ident} {value : Value}
                                                        (hdueName : ("due" == name) = false)
                                                        (hget :
                                                          localsGrab.get? name = some value) :
                                                        localsDue.get? name = some value := by
                                                      simpa [localsDue, due] using
                                                        barkLocalsDue_get_preserved
                                                          (locals := localsGrab)
                                                          (due := barkDueWord dart rate)
                                                          (name := name) (value := value)
                                                          hdueName hget
                                                    have hpresDueNone {name : Ident}
                                                        (hdueName : ("due" == name) = false)
                                                        (hget : localsGrab.get? name = none) :
                                                        localsDue.get? name = none := by
                                                      change (barkLocalsDue localsGrab
                                                        (barkDueWord dart rate)).get? name = none
                                                      rw [barkLocalsDue,
                                                        store_get_ne _
                                                          (.int (Int.ofNat
                                                            (barkDueWord dart rate).toNat))
                                                          hdueName]
                                                      exact hget
                                                    have hdinkGrab :
                                                        localsGrab.get? "dink" =
                                                          some (.int (Int.ofNat dink.toNat)) :=
                                                      hpresGrab (by decide) hdinkGet
                                                    have hmilkClipGrab :
                                                        localsGrab.get? "milkClip" =
                                                          some (.address (AccountAddress.ofNat
                                                            (barkIlksClipWord σ' I).toNat)) :=
                                                      hpresGrab (by decide) hmilkClipDink
                                                    have hmilkDirtGrab :
                                                        localsGrab.get? "milkDirt" =
                                                          some (.int (Int.ofNat
                                                            (barkIlksDirtWord σ' I).toNat)) :=
                                                      hpresGrab (by decide) hmilkDirtDink
                                                    have hilkGrab :
                                                        localsGrab.get? "ilk" =
                                                          some (.fixedBytes bytes32Width
                                                            (barkIlkBytes I)) :=
                                                      hpresGrab (by decide) hilkDink
                                                    have hurnGrab :
                                                        localsGrab.get? "urn" =
                                                          some (.address (barkUrn I)) :=
                                                      hpresGrab (by decide) hurnDink
                                                    have hkprGrab :
                                                        localsGrab.get? "kpr" =
                                                          some (.address (barkKpr I)) :=
                                                      hpresGrab (by decide) hkprDink
                                                    have hilksGrab :
                                                        localsGrab.get? "ilks" = none :=
                                                      hpresGrabNone (by decide) hilksDink
                                                    have hdinkDue :
                                                        localsDue.get? "dink" =
                                                          some (.int (Int.ofNat dink.toNat)) :=
                                                      hpresDue (by decide) hdinkGrab
                                                    have hmilkClipDue :
                                                        localsDue.get? "milkClip" =
                                                          some (.address (AccountAddress.ofNat
                                                            (barkIlksClipWord σ' I).toNat)) :=
                                                      hpresDue (by decide) hmilkClipGrab
                                                    have hmilkDirtDue :
                                                        localsDue.get? "milkDirt" =
                                                          some (.int (Int.ofNat
                                                            (barkIlksDirtWord σ' I).toNat)) :=
                                                      hpresDue (by decide) hmilkDirtGrab
                                                    have hilkDue :
                                                        localsDue.get? "ilk" =
                                                          some (.fixedBytes bytes32Width
                                                            (barkIlkBytes I)) :=
                                                      hpresDue (by decide) hilkGrab
                                                    have hurnDue :
                                                        localsDue.get? "urn" =
                                                          some (.address (barkUrn I)) :=
                                                      hpresDue (by decide) hurnGrab
                                                    have hkprDue :
                                                        localsDue.get? "kpr" =
                                                          some (.address (barkKpr I)) :=
                                                      hpresDue (by decide) hkprGrab
                                                    have hilksDue :
                                                        localsDue.get? "ilks" = none :=
                                                      hpresDueNone (by decide) hilksGrab
                                                    have hpresFess {name : Ident} {value : Value}
                                                        (hfessName :
                                                          ("_fessRet" == name) = false)
                                                        (hget :
                                                          localsDue.get? name = some value) :
                                                        localsFess.get? name = some value := by
                                                      simpa [localsFess] using
                                                        barkLocalsFessRet_get_preserved
                                                          (locals := localsDue)
                                                          (name := name) (value := value)
                                                          hfessName hget
                                                    have hpresFessNone {name : Ident}
                                                        (hfessName :
                                                          ("_fessRet" == name) = false)
                                                        (hget : localsDue.get? name = none) :
                                                        localsFess.get? name = none := by
                                                      change (barkLocalsFessRet localsDue).get?
                                                        name = none
                                                      rw [barkLocalsFessRet,
                                                        store_get_ne _ .unit hfessName]
                                                      exact hget
                                                    have hdueFess :
                                                        localsFess.get? "due" =
                                                          some (.int (Int.ofNat due.toNat)) :=
                                                      hpresFess (by decide) hdueGet
                                                    have hmilkChopFess :
                                                        localsFess.get? "milkChop" =
                                                          some (.int
                                                            (Int.ofNat milkChop.toNat)) :=
                                                      hpresFess (by decide) hmilkChopDue
                                                    have hDirtFess :
                                                        localsFess.get? "Dirt" = none :=
                                                      hpresFessNone (by decide) hDirtDue
                                                    have hmload288Grab :
                                                        (if (⟨288⟩ : UInt256).toNat ≥
                                                              (barkVatGrabPostCallMem σ'' σ' I
                                                                mem0 outGrab dink dart).size
 then ⟨0⟩
                                                         else UInt256.ofNat
                                                          (fromByteArrayBigEndian
                                                            ((barkVatGrabPostCallMem σ'' σ' I
                                                              mem0 outGrab dink dart).readWithPadding
                                                                (⟨288⟩ : UInt256).toNat 32))) =
                                                          milkChop := by
                                                      exact barkVatGrabPostCallMem_mload288
                                                        (σ := σ'') (σMem := σ') (I := I)
                                                        (mem := mem0) (out := outGrab)
                                                        (dink := dink) (dart := dart)
                                                        (by simpa [mem0] using hpostMemSize)
                                                        (by simpa [mem0, milkChop] using
                                                          hmload288)
                                                    have hmload288FessDue :
                                                        (if (⟨288⟩ : UInt256).toNat ≥
                                                              (barkVowFessDueMem
                                                                (barkVatGrabPostCallMem σ'' σ' I
                                                                  mem0 outGrab dink dart)
                                                                due).size
 then ⟨0⟩
                                                         else UInt256.ofNat
                                                          (fromByteArrayBigEndian
                                                            ((barkVowFessDueMem
                                                              (barkVatGrabPostCallMem σ'' σ' I
                                                                mem0 outGrab dink dart)
                                                              due).readWithPadding
                                                                (⟨288⟩ : UInt256).toNat 32))) =
                                                          milkChop := by
                                                      exact barkVowFessDueMem_mload288
                                                        hmemGrabSize hmload288Grab
                                                    have hmload288Fess :
                                                        (if (⟨288⟩ : UInt256).toNat ≥
                                                              (barkVowFessPostCallMem
                                                                (barkVatGrabPostCallMem σ'' σ' I
                                                                  mem0 outGrab dink dart)
                                                                outFess due).size
 then ⟨0⟩
                                                         else UInt256.ofNat
                                                          (fromByteArrayBigEndian
                                                            ((barkVowFessPostCallMem
                                                              (barkVatGrabPostCallMem σ'' σ' I
                                                                mem0 outGrab dink dart)
                                                              outFess due).readWithPadding
                                                                (⟨288⟩ : UInt256).toNat 32))) =
                                                          milkChop :=
                                                      barkVowFessPostCallMem_mload288
                                                        hmload288FessDue
                                                    let afterTabBase : List Stmt :=
                                                      [ .letDecl "tab" (some uint256)
                                                          (.binary .div (.var "tabBase")
                                                            (.intLit WAD)) ] ++
                                                      checkedAddUintInto "DirtNew"
                                                        (.storage DirtRef) (.var "tab") ++
                                                      [ .assign .storage DirtRef
                                                          (.var "DirtNew") ] ++
                                                      checkedAddUintInto "ilkDirtNew"
                                                        (.var "milkDirt") (.var "tab") ++
                                                      [ .assign .storage
                                                          (ilksF (.var "ilk") "dirt")
                                                          (.var "ilkDirtNew") ] ++
                                                      checkedExternalCallStmts (.var "milkClip")
                                                        "kick" (.intLit 0)
                                                        [.var "tab", .var "dink", .var "urn",
                                                          .var "kpr"]
                                                        "id" ++
                                                      [ .return [.var "id"] ]
                                                    by_cases hfitTabBase :
                                                        due.toNat * milkChop.toNat <
                                                          UInt256.size
                                                    · obtain ⟨_, _, rd4200⟩ :=
                                                        RD.dogBarkTabBaseCheckedMulOk
                                                          hpatch hfitTabBase hmload288Fess
                                                          rd4176 (by simp)
                                                      have htabBaseOk :=
                                                        dogBarkTabBaseCheckedMulOkSource
                                                          (v := v) evmFessStele hdueFess
                                                          hmilkChopFess hfitTabBase
                                                      have _hprefixTabBase :=
                                                        execBlock_append _hprefixFess
                                                          htabBaseOk
                                                      have _hprefixTabBaseTail :=
                                                        execBlock_append _hprefixFessTail
                                                          htabBaseOk
                                                      let tabBase :=
                                                        barkTabBaseWord due milkChop
                                                      let localsTabBase :=
                                                        barkLocalsTabBase localsFess tabBase
                                                      have htabBaseGet :
                                                          localsTabBase.get? "tabBase" =
                                                            some (.int
                                                              (Int.ofNat tabBase.toNat)) := by
                                                        simpa [localsTabBase, tabBase] using
                                                          barkLocalsTabBase_get_tabBase
                                                            localsFess
                                                            (barkTabBaseWord due milkChop)
                                                      have hpresTabBase {name : Ident}
                                                          {value : Value}
                                                          (htabBaseName :
                                                            ("tabBase" == name) = false)
                                                          (hget :
                                                            localsFess.get? name =
                                                              some value) :
                                                          localsTabBase.get? name =
                                                            some value := by
                                                        simpa [localsTabBase, tabBase] using
                                                          barkLocalsTabBase_get_preserved
                                                            (locals := localsFess)
                                                            (tabBase :=
                                                              barkTabBaseWord due milkChop)
                                                            (name := name) (value := value)
                                                            htabBaseName hget
                                                      have hpresTabBaseNone {name : Ident}
                                                          (htabBaseName :
                                                            ("tabBase" == name) = false)
                                                          (hget :
                                                            localsFess.get? name = none) :
                                                          localsTabBase.get? name = none := by
                                                        change (barkLocalsTabBase localsFess
                                                          (barkTabBaseWord due milkChop)).get?
                                                          name = none
                                                        rw [barkLocalsTabBase,
                                                          store_get_ne _
                                                            (.int (Int.ofNat
                                                              (barkTabBaseWord due milkChop).toNat))
                                                            htabBaseName]
                                                        exact hget
                                                      obtain ⟨_, _, rd4211⟩ :=
                                                        RD.dogBarkTabDivOk hpatch rd4200
                                                          (by simp)
                                                      have htabOk :=
                                                        dogBarkTabLetOk (v := v) evmFessStele
                                                          htabBaseGet
                                                      have _hprefixTab :=
                                                        execBlock_append _hprefixTabBase htabOk
                                                      have _hprefixTabTail :=
                                                        execBlock_append _hprefixTabBaseTail htabOk
                                                      let tab := barkTabWord tabBase
                                                      let localsTab :=
                                                        barkLocalsTab localsTabBase tab
                                                      have htabGet :
                                                          localsTab.get? "tab" =
                                                            some (.int (Int.ofNat tab.toNat)) := by
                                                        simpa [localsTab, tab] using
                                                          barkLocalsTab_get_tab localsTabBase
                                                            (barkTabWord tabBase)
                                                      have hpresTab {name : Ident}
                                                          {value : Value}
                                                          (htabName : ("tab" == name) = false)
                                                          (hget :
                                                            localsTabBase.get? name =
                                                              some value) :
                                                          localsTab.get? name = some value := by
                                                        simpa [localsTab, tab] using
                                                          barkLocalsTab_get_preserved
                                                            (locals := localsTabBase)
                                                            (tab := barkTabWord tabBase)
                                                            (name := name) (value := value)
                                                            htabName hget
                                                      have hpresTabNone {name : Ident}
                                                          (htabName : ("tab" == name) = false)
                                                          (hget :
                                                            localsTabBase.get? name = none) :
                                                          localsTab.get? name = none := by
                                                        change (barkLocalsTab localsTabBase
                                                          (barkTabWord tabBase)).get? name = none
                                                        rw [barkLocalsTab,
                                                          store_get_ne _
                                                            (.int (Int.ofNat
                                                              (barkTabWord tabBase).toNat))
                                                            htabName]
                                                        exact hget
                                                      have hDirtTab :
                                                          localsTab.get? "Dirt" = none :=
                                                        hpresTabNone (by decide)
                                                          (hpresTabBaseNone (by decide)
                                                            hDirtFess)
                                                      have hmilkDirtFess :
                                                          localsFess.get? "milkDirt" =
                                                            some (.int (Int.ofNat
                                                              (barkIlksDirtWord σ' I).toNat)) :=
                                                        hpresFess (by decide) hmilkDirtDue
                                                      have hmilkDirtTab :
                                                          localsTab.get? "milkDirt" =
                                                            some (.int (Int.ofNat
                                                              (barkIlksDirtWord σ' I).toNat)) :=
                                                        hpresTab (by decide)
                                                          (hpresTabBase (by decide)
                                                            hmilkDirtFess)
                                                      have hilkFess :
                                                          localsFess.get? "ilk" =
                                                            some (.fixedBytes bytes32Width
                                                              (barkIlkBytes I)) :=
                                                        hpresFess (by decide) hilkDue
                                                      have hilkTab :
                                                          localsTab.get? "ilk" =
                                                            some (.fixedBytes bytes32Width
                                                              (barkIlkBytes I)) :=
                                                        hpresTab (by decide)
                                                          (hpresTabBase (by decide) hilkFess)
                                                      have hilksFess :
                                                          localsFess.get? "ilks" = none :=
                                                        hpresFessNone (by decide) hilksDue
                                                      have hilksTab :
                                                          localsTab.get? "ilks" = none :=
                                                        hpresTabNone (by decide)
                                                          (hpresTabBaseNone (by decide)
                                                            hilksFess)
                                                      have hDirtSlotFess :
                                                          solcSlotWordAt ⟨5⟩
                                                              evmFessStele.accountMap
                                                              evmFessStele.executionEnv =
                                                            solcSlotWordAt ⟨5⟩ σFess I := by
                                                        have hslot :=
                                                          congrArg (fun m => solcSlotWordAt ⟨5⟩ m I) hAccountsFess
                                                        simpa [evmFessStele, evmGrabStele,
                                                          evmIlksPostStele, evmPostStele,
                                                          evmStele, initState] using hslot.symm
                                                      let afterTab : List Stmt :=
                                                        checkedAddUintInto "DirtNew"
                                                          (.storage DirtRef) (.var "tab") ++
                                                        [ .assign .storage DirtRef
                                                            (.var "DirtNew") ] ++
                                                        checkedAddUintInto "ilkDirtNew"
                                                          (.var "milkDirt") (.var "tab") ++
                                                        [ .assign .storage
                                                            (ilksF (.var "ilk") "dirt")
                                                            (.var "ilkDirtNew") ] ++
                                                        checkedExternalCallStmts
                                                          (.var "milkClip") "kick"
                                                          (.intLit 0)
                                                          [.var "tab", .var "dink", .var "urn",
                                                            .var "kpr"]
                                                          "id" ++
                                                        [ .return [.var "id"] ]
                                                      let afterDirtNew : List Stmt :=
                                                        [ .assign .storage DirtRef
                                                            (.var "DirtNew") ] ++
                                                        checkedAddUintInto "ilkDirtNew"
                                                          (.var "milkDirt") (.var "tab") ++
                                                        [ .assign .storage
                                                            (ilksF (.var "ilk") "dirt")
                                                            (.var "ilkDirtNew") ] ++
                                                        checkedExternalCallStmts
                                                          (.var "milkClip") "kick"
                                                          (.intLit 0)
                                                          [.var "tab", .var "dink", .var "urn",
                                                            .var "kpr"]
                                                          "id" ++
                                                        [ .return [.var "id"] ]
                                                      by_cases hfitDirt :
                                                          (solcSlotWordAt ⟨5⟩ σFess I).toNat +
                                                              tab.toNat <
                                                            UInt256.size
                                                      · obtain ⟨_, _, rd4222⟩ :=
                                                          RD.dogBarkDirtAddOk hpatch hfitDirt
                                                            rd4211 (by simp)
                                                        have hfitDirtStele :
                                                            (solcSlotWordAt ⟨5⟩
                                                                  evmFessStele.accountMap
                                                                  evmFessStele.executionEnv).toNat +
                                                                tab.toNat <
                                                              UInt256.size := by
                                                          simpa [hDirtSlotFess] using hfitDirt
                                                        have hdirtAddOk :=
                                                          dogBarkDirtAddOkSource (v := v)
                                                            evmFessStele hDirtTab htabGet
                                                            hfitDirtStele
                                                        have _hprefixDirtNew :=
                                                          execBlock_append _hprefixTab
                                                            hdirtAddOk
                                                        have _hprefixDirtNewTail :=
                                                          execBlock_append _hprefixTabTail
                                                            hdirtAddOk
                                                        let dirtNew :=
                                                          barkDirtNewWord
                                                            (solcSlotWordAt ⟨5⟩
                                                              evmFessStele.accountMap
                                                              evmFessStele.executionEnv) tab
                                                        let dirtNewEvm :=
                                                          barkDirtNewWord
                                                            (solcSlotWordAt ⟨5⟩ σFess I) tab
                                                        have hdirtNew_eq :
                                                            dirtNew = dirtNewEvm := by
                                                          simp [dirtNew, dirtNewEvm,
                                                            hDirtSlotFess]
                                                        let localsDirtNew :=
                                                          barkLocalsDirtNew localsTab dirtNew
                                                        have hDirtNewGet :
                                                            localsDirtNew.get? "DirtNew" =
                                                              some (.int
                                                                (Int.ofNat dirtNew.toNat)) := by
                                                          simpa [localsDirtNew, dirtNew] using
                                                            barkLocalsDirtNew_get_DirtNew
                                                              localsTab
                                                              (barkDirtNewWord
                                                                (solcSlotWordAt ⟨5⟩
                                                                  evmFessStele.accountMap
                                                                  evmFessStele.executionEnv)
                                                                tab)
                                                        have hDirtDirtNew :
                                                            localsDirtNew.get? "Dirt" = none := by
                                                          change (barkLocalsDirtNew localsTab
                                                            dirtNew).get? "Dirt" = none
                                                          rw [barkLocalsDirtNew,
                                                            store_get_ne _
                                                              (.int (Int.ofNat dirtNew.toNat))
                                                              (by decide)]
                                                          exact hDirtTab
                                                        have hstoreSplit :=
                                                          RD.dogBarkStoreDirtSplit hpatch
                                                            rd4222 (by simp)
                                                        have hsourceSplit :=
                                                          dogBarkDirtAssignOkSourceSplit
                                                            (v := v) evmFessStele
                                                            hDirtDirtNew hDirtNewGet
                                                        by_cases _hperm : I.perm = true
                                                        swap
                                                        · have hpf : I.perm = false := by
                                                            simpa using _hperm
                                                          have hdirtStatic := hsourceSplit.2
                                                            (by simpa [evmFessStele,
                                                              evmGrabStele, evmIlksPostStele,
                                                              evmPostStele, evmStele, initState]
                                                              using hpf)
                                                          have htailPrefix := execBlock_append
                                                            _hprefixDirtNewTail hdirtStatic
                                                          have hbodyStatic :
                                                              ExecTransitionBody config
                                                                contract evmStele
                                                                (barkLocals I)
                                                                barkTransition.body
                                                                .staticViolation (immStore v) := by
                                                            apply hbodyStaticOfTail
                                                            refine dogBarkDartTailFromLeftoverBlock
                                                              hleftover ?_
                                                            simpa only [afterIntGuard, afterGrab,
                                                              afterFess, afterTabBase, afterTab,
                                                              afterDirtNew, localsDink, localsGrab,
                                                              localsDue, localsFess, localsTabBase,
                                                              localsTab, localsDirtNew, due, dink,
                                                              tabBase, tab, dirtNew,
                                                              List.append_assoc,
                                                              List.drop_succ_cons, List.drop_zero,
                                                              List.cons_append, List.nil_append]
                                                              using execBlock_append_term
                                                                (s2 := afterDirtNew.drop 1)
                                                                htailPrefix
                                                                (by intro f e h; cases h)
                                                          have hs :=
                                                            permSplit_false hpf hstoreSplit
                                                          exact hs.reEquivStaticHalt
                                                            hcode hdispatch hdecode hbodyStatic
                                                        obtain ⟨_, _, rd4226⟩ :=
                                                          permSplit_true _hperm hstoreSplit
                                                        have hdirtAssignOk := hsourceSplit.1 (by
                                                          simpa [evmFessStele, evmGrabStele,
                                                            evmIlksPostStele, evmPostStele,
                                                            evmStele, initState] using _hperm)
                                                        have _hprefixDirtStore :=
                                                          execBlock_append _hprefixDirtNew
                                                            hdirtAssignOk
                                                        have _hprefixDirtStoreTail :=
                                                          execBlock_append _hprefixDirtNewTail
                                                            hdirtAssignOk
                                                        let σDirt :=
                                                          sstoreAccountMap I.codeOwner σFess
                                                            ⟨5⟩ dirtNewEvm
                                                        let evmDirtEvm :=
                                                          { evmFessEvm with accountMap := σDirt }
                                                        let evmDirtStele :=
                                                          Stele.EVM.storageStore evmFessStele
                                                            evmFessStele.executionEnv.codeOwner
                                                            ⟨5⟩ dirtNew
                                                        have hAccountsDirt :
                                                            Eq σDirt
                                                              evmDirtStele.accountMap := by
                                                          simpa [σDirt, evmDirtStele,
                                                            hdirtNew_eq,
                                                            evmFessStele, evmGrabStele,
                                                            evmIlksPostStele, evmPostStele,
                                                            evmStele, initState,
                                                            storageStore_accountMap,
                                                            storageStore_executionEnv] using
                                                            congrArg
                                                              (fun m => sstoreAccountMap
                                                                I.codeOwner m ⟨5⟩ dirtNewEvm)
                                                              hAccountsFess
                                                        have hmilkDirtDirtNew :
                                                            localsDirtNew.get? "milkDirt" =
                                                              some (.int (Int.ofNat
                                                                (barkIlksDirtWord σ' I).toNat)) := by
                                                          simpa [localsDirtNew, dirtNew] using
                                                            barkLocalsDirtNew_get_preserved
                                                              (locals := localsTab)
                                                              (dirtNew := dirtNew)
                                                              (name := "milkDirt")
                                                              (value := .int (Int.ofNat
                                                                (barkIlksDirtWord σ' I).toNat))
                                                              (by decide) hmilkDirtTab
                                                        have htabDirtNew :
                                                            localsDirtNew.get? "tab" =
                                                              some (.int
                                                                (Int.ofNat tab.toNat)) := by
                                                          simpa [localsDirtNew, dirtNew] using
                                                            barkLocalsDirtNew_get_preserved
                                                              (locals := localsTab)
                                                              (dirtNew := dirtNew)
                                                              (name := "tab")
                                                              (value := .int
                                                                (Int.ofNat tab.toNat))
                                                              (by decide) htabGet
                                                        let afterDirtAssign : List Stmt :=
                                                          checkedAddUintInto "ilkDirtNew"
                                                            (.var "milkDirt") (.var "tab") ++
                                                          [ .assign .storage
                                                              (ilksF (.var "ilk") "dirt")
                                                              (.var "ilkDirtNew") ] ++
                                                          checkedExternalCallStmts
                                                            (.var "milkClip") "kick"
                                                            (.intLit 0)
                                                            [.var "tab", .var "dink",
                                                              .var "urn", .var "kpr"]
                                                            "id" ++
                                                          [ .return [.var "id"] ]
                                                        let afterIlkDirtNew : List Stmt :=
                                                          [ .assign .storage
                                                              (ilksF (.var "ilk") "dirt")
                                                              (.var "ilkDirtNew") ] ++
                                                          checkedExternalCallStmts
                                                            (.var "milkClip") "kick"
                                                            (.intLit 0)
                                                            [.var "tab", .var "dink",
                                                              .var "urn", .var "kpr"]
                                                            "id" ++
                                                          [ .return [.var "id"] ]
                                                        have hmload352Grab :
                                                            (if (⟨352⟩ : UInt256).toNat ≥
                                                                  (barkVatGrabPostCallMem σ'' σ' I
                                                                    mem0 outGrab dink dart).size
 then ⟨0⟩
                                                             else UInt256.ofNat
                                                              (fromByteArrayBigEndian
                                                                ((barkVatGrabPostCallMem σ'' σ' I
                                                                  mem0 outGrab dink dart).readWithPadding
                                                                    (⟨352⟩ : UInt256).toNat 32))) =
                                                              barkIlksDirtWord σ' I := by
                                                          exact barkVatGrabPostCallMem_mload352
                                                            (σ := σ'') (σMem := σ') (I := I)
                                                            (mem := mem0) (out := outGrab)
                                                            (dink := dink) (dart := dart)
                                                            (by simpa [mem0] using hpostMemSize)
                                                            (by simpa [mem0] using hmload352)
                                                        have hmload352FessDue :
                                                            (if (⟨352⟩ : UInt256).toNat ≥
                                                                  (barkVowFessDueMem
                                                                    (barkVatGrabPostCallMem σ'' σ' I
                                                                      mem0 outGrab dink dart)
                                                                    due).size
 then ⟨0⟩
                                                             else UInt256.ofNat
                                                              (fromByteArrayBigEndian
                                                                ((barkVowFessDueMem
                                                                  (barkVatGrabPostCallMem σ'' σ' I
                                                                    mem0 outGrab dink dart)
                                                                  due).readWithPadding
                                                                    (⟨352⟩ : UInt256).toNat 32))) =
                                                              barkIlksDirtWord σ' I := by
                                                          exact barkVowFessDueMem_mload352
                                                            hmemGrabSize hmload352Grab
                                                        have hmload352Fess :
                                                            (if (⟨352⟩ : UInt256).toNat ≥
                                                                  (barkVowFessPostCallMem
                                                                    (barkVatGrabPostCallMem σ'' σ' I
                                                                      mem0 outGrab dink dart)
                                                                    outFess due).size
 then ⟨0⟩
                                                             else UInt256.ofNat
                                                              (fromByteArrayBigEndian
                                                                ((barkVowFessPostCallMem
                                                                  (barkVatGrabPostCallMem σ'' σ' I
                                                                    mem0 outGrab dink dart)
                                                                  outFess due).readWithPadding
                                                                    (⟨352⟩ : UInt256).toNat 32))) =
                                                              barkIlksDirtWord σ' I :=
                                                          barkVowFessPostCallMem_mload352
                                                            hmload352FessDue
                                                        by_cases hfitIlkDirt :
                                                            (barkIlksDirtWord σ' I).toNat +
                                                                tab.toNat <
                                                              UInt256.size
                                                        · obtain ⟨_, _, rd4240⟩ :=
                                                            RD.dogBarkIlkDirtAddOk
                                                              hpatch hmload352Fess
                                                              hfitIlkDirt rd4226 (by simp)
                                                          have hilkDirtAddOk :=
                                                            dogBarkIlkDirtAddOkSource
                                                              (v := v) evmDirtStele
                                                              hmilkDirtDirtNew htabDirtNew
                                                              hfitIlkDirt
                                                          have _hprefixIlkDirtNew :=
                                                            execBlock_append
                                                              _hprefixDirtStore
                                                              hilkDirtAddOk
                                                          have _hprefixIlkDirtNewTail :=
                                                            execBlock_append
                                                              _hprefixDirtStoreTail
                                                              hilkDirtAddOk
                                                          let ilkDirtNew :=
                                                            barkIlkDirtNewWord
                                                              (barkIlksDirtWord σ' I) tab
                                                          let localsIlkDirtNew :=
                                                            barkLocalsIlkDirtNew
                                                              localsDirtNew ilkDirtNew
                                                          have hIlkDirtNewGet :
                                                              localsIlkDirtNew.get?
                                                                  "ilkDirtNew" =
                                                                some (.int (Int.ofNat
                                                                  ilkDirtNew.toNat)) := by
                                                            simpa [localsIlkDirtNew,
                                                              ilkDirtNew] using
                                                              barkLocalsIlkDirtNew_get_ilkDirtNew
                                                                localsDirtNew
                                                                (barkIlkDirtNewWord
                                                                  (barkIlksDirtWord σ' I) tab)
                                                          have hpresDirtNew {name : Ident}
                                                              {value : Value}
                                                              (hname :
                                                                ("DirtNew" == name) = false)
                                                              (hget :
                                                                localsTab.get? name =
                                                                  some value) :
                                                              localsDirtNew.get? name =
                                                                some value := by
                                                            simpa [localsDirtNew, dirtNew] using
                                                              barkLocalsDirtNew_get_preserved
                                                                (locals := localsTab)
                                                                (dirtNew := dirtNew)
                                                                (name := name) (value := value)
                                                                hname hget
                                                          have hpresDirtNewNone {name : Ident}
                                                              (hname :
                                                                ("DirtNew" == name) = false)
                                                              (hget :
                                                                localsTab.get? name = none) :
                                                              localsDirtNew.get? name = none := by
                                                            change (barkLocalsDirtNew localsTab
                                                              dirtNew).get? name = none
                                                            rw [barkLocalsDirtNew,
                                                              store_get_ne _
                                                                (.int (Int.ofNat dirtNew.toNat))
                                                                hname]
                                                            exact hget
                                                          have hpresIlkDirtNew {name : Ident}
                                                              {value : Value}
                                                              (hname :
                                                                ("ilkDirtNew" == name) = false)
                                                              (hget :
                                                                localsDirtNew.get? name =
                                                                  some value) :
                                                              localsIlkDirtNew.get? name =
                                                                some value := by
                                                            simpa [localsIlkDirtNew,
                                                              ilkDirtNew] using
                                                              barkLocalsIlkDirtNew_get_preserved
                                                                (locals := localsDirtNew)
                                                                (ilkDirtNew := ilkDirtNew)
                                                                (name := name) (value := value)
                                                                hname hget
                                                          have hpresIlkDirtNewNone
                                                              {name : Ident}
                                                              (hname :
                                                                ("ilkDirtNew" == name) = false)
                                                              (hget :
                                                                localsDirtNew.get? name =
                                                                  none) :
                                                              localsIlkDirtNew.get? name =
                                                                none := by
                                                            change (barkLocalsIlkDirtNew
                                                              localsDirtNew ilkDirtNew).get?
                                                              name = none
                                                            rw [barkLocalsIlkDirtNew,
                                                              store_get_ne _
                                                                (.int (Int.ofNat
                                                                  ilkDirtNew.toNat))
                                                                hname]
                                                            exact hget
                                                          have hilksDirtNew :
                                                              localsDirtNew.get? "ilks" = none :=
                                                            hpresDirtNewNone (by decide)
                                                              hilksTab
                                                          have hilksIlkDirtNew :
                                                              localsIlkDirtNew.get? "ilks" =
                                                                none :=
                                                            hpresIlkDirtNewNone (by decide)
                                                              hilksDirtNew
                                                          have hilkDirtNew :
                                                              localsDirtNew.get? "ilk" =
                                                                some (.fixedBytes bytes32Width
                                                                  (barkIlkBytes I)) :=
                                                            hpresDirtNew (by decide) hilkTab
                                                          have hilkIlkDirtNew :
                                                              localsIlkDirtNew.get? "ilk" =
                                                                some (barkIlkValue I) := by
                                                            simpa [barkIlkValue] using
                                                              hpresIlkDirtNew (by decide)
                                                                hilkDirtNew
                                                          obtain ⟨_, _, rd4267⟩ :=
                                                            RD.dogBarkStoreIlkDirt
                                                              hpatch hsz100 _hperm
                                                              (barkVowFessPostCallMem_size
                                                                hmemGrabSize)
                                                              rd4240
                                                              (by
                                                                simp only [List.length_nil]
                                                                omega)
                                                          have hilkDirtAssignOk :=
                                                            dogBarkIlkDirtAssignOkSource (hperm := by simpa [evmDirtStele, storageStore_executionEnv, evmFessStele, evmGrabStele, evmIlksPostStele, evmPostStele, evmStele, initState] using _hperm)
                                                              (v := v) evmDirtStele hsz100
                                                              hilksIlkDirtNew hilkIlkDirtNew
                                                              hIlkDirtNewGet
                                                          have _hprefixIlkDirtStore :=
                                                            execBlock_append
                                                              _hprefixIlkDirtNew
                                                              hilkDirtAssignOk
                                                          have _hprefixIlkDirtStoreTail :=
                                                            execBlock_append
                                                              _hprefixIlkDirtNewTail
                                                              hilkDirtAssignOk
                                                          let σIlkDirt :=
                                                            sstoreAccountMap I.codeOwner σDirt
                                                              (barkIlksDirtSlotFor I)
                                                              ilkDirtNew
                                                          let evmIlkDirtEvm :=
                                                            { evmDirtEvm with
                                                              accountMap := σIlkDirt }
                                                          let evmIlkDirtStele :=
                                                            Stele.EVM.storageStore evmDirtStele
                                                              evmDirtStele.executionEnv.codeOwner
                                                              (barkIlksDirtSlotFor I)
                                                              ilkDirtNew
                                                          have hDirtCodeOwner :
                                                              evmDirtStele.executionEnv.codeOwner =
                                                                I.codeOwner := by
                                                            simp [evmDirtStele, evmFessStele,
                                                              evmGrabStele, evmIlksPostStele,
                                                              evmPostStele, evmStele, initState,
                                                              storageStore_executionEnv]
                                                          have hAccountsIlkDirt :
                                                              Eq σIlkDirt
                                                                evmIlkDirtStele.accountMap := by
                                                            simpa [σIlkDirt, evmIlkDirtStele,
                                                              storageStore_accountMap,
                                                              hDirtCodeOwner] using
                                                              congrArg
                                                                (fun m => sstoreAccountMap
                                                                  I.codeOwner m
                                                                  (barkIlksDirtSlotFor I)
                                                                  ilkDirtNew)
                                                                hAccountsDirt
                                                          let memFess :=
                                                            barkVowFessPostCallMem
                                                              (barkVatGrabPostCallMem σ'' σ' I
                                                                mem0 outGrab dink dart)
                                                              outFess due
                                                          let memKickPre :=
                                                            twoWordHashMem (barkIlkWord I) ⟨1⟩
                                                              memFess
                                                          have hmemFessSize :
                                                              memFess.size = 580 := by
                                                            simpa [memFess] using
                                                              barkVowFessPostCallMem_size
                                                                hmemGrabSize
                                                          have hmemFessRead64 :
                                                              memFess.readWithPadding 64 32 =
                                                                UInt256.toByteArray ⟨384⟩ := by
                                                            simpa [memFess] using
                                                              barkVowFessPostCallMem_read64
                                                                hmemGrabSize hmemGrabRead64
                                                          have hread256Mem0 :
                                                              mem0.readWithPadding 256 32 =
                                                                UInt256.toByteArray
                                                                  (barkIlksClipWord σ' I) := by
                                                            simpa [mem0] using
                                                              barkVatIlksPostCallMem_read256_long
                                                                (σ := σ') (I := I)
                                                                solcFreePtrMem_size hretLong
                                                                hosz hretIlksLong hoszIlks
                                                          have hread256Grab :
                                                              (barkVatGrabPostCallMem σ'' σ' I
                                                                  mem0 outGrab dink dart).readWithPadding
                                                                  256 32 =
                                                                UInt256.toByteArray
                                                                  (barkIlksClipWord σ' I) :=
                                                            barkVatGrabPostCallMem_read256
                                                              (σ := σ'') (σMem := σ') (I := I)
                                                              (mem := mem0) (out := outGrab)
                                                              (dink := dink) (dart := dart)
                                                              (by simpa [mem0] using
                                                                hpostMemSize)
                                                              hread256Mem0
                                                          have hread256Fess :
                                                              memFess.readWithPadding 256 32 =
                                                                UInt256.toByteArray
                                                                  (barkIlksClipWord σ' I) := by
                                                            simpa [memFess] using
                                                              barkVowFessPostCallMem_read256
                                                                hmemGrabSize hread256Grab
                                                          have hmemKickPreSize :
                                                              memKickPre.size = 580 := by
                                                            simpa [memKickPre] using
                                                              twoWordHashMem_size_580
                                                                (barkIlkWord I) ⟨1⟩
                                                                hmemFessSize
                                                          have hmemKickPreRead64 :
                                                              memKickPre.readWithPadding 64 32 =
                                                                UInt256.toByteArray ⟨384⟩ := by
                                                            simpa [memKickPre] using
                                                              twoWordHashMem_read64_580
                                                                (barkIlkWord I) ⟨1⟩
                                                                hmemFessSize hmemFessRead64
                                                          have hmload256KickPre :
                                                              (if (⟨256⟩ : UInt256).toNat ≥
                                                                    memKickPre.size

                                                               then ⟨0⟩
                                                               else UInt256.ofNat
                                                                (fromByteArrayBigEndian
                                                                  (memKickPre.readWithPadding
                                                                    (⟨256⟩ : UInt256).toNat 32))) =
                                                                barkIlksClipWord σ' I := by
                                                            simpa [memKickPre] using
                                                              twoWordHashMem_mload256_580
                                                                (barkIlkWord I) ⟨1⟩
                                                                (barkIlksClipWord σ' I)
                                                                hmemFessSize hread256Fess
                                                          have hread256KickPre :
                                                              memKickPre.readWithPadding
                                                                  256 32 =
                                                                UInt256.toByteArray
                                                                  (barkIlksClipWord σ' I) := by
                                                            simpa [memKickPre] using
                                                              twoWordHashMem_read256_580
                                                                (barkIlkWord I) ⟨1⟩
                                                                (barkIlksClipWord σ' I)
                                                                hmemFessSize hread256Fess
                                                          let afterKick : List Stmt :=
                                                            [ .return [.var "id"] ]
                                                          let afterIlkDirtAssign : List Stmt :=
                                                            checkedExternalCallStmts
                                                              (.var "milkClip") "kick"
                                                              (.intLit 0)
                                                              [.var "tab", .var "dink",
                                                                .var "urn", .var "kpr"]
                                                              "id" ++
                                                            afterKick
                                                          have hmilkClipFess :
                                                              localsFess.get? "milkClip" =
                                                                some (.address
                                                                  (AccountAddress.ofNat
                                                                    (barkIlksClipWord σ' I).toNat)) :=
                                                            hpresFess (by decide) hmilkClipDue
                                                          have hdinkFess :
                                                              localsFess.get? "dink" =
                                                                some (.int
                                                                  (Int.ofNat dink.toNat)) :=
                                                            hpresFess (by decide) hdinkDue
                                                          have hurnFess :
                                                              localsFess.get? "urn" =
                                                                some (.address (barkUrn I)) :=
                                                            hpresFess (by decide) hurnDue
                                                          have hkprFess :
                                                              localsFess.get? "kpr" =
                                                                some (.address (barkKpr I)) :=
                                                            hpresFess (by decide) hkprDue
                                                          have hmilkClipTab :
                                                              localsTab.get? "milkClip" =
                                                                some (.address
                                                                  (AccountAddress.ofNat
                                                                    (barkIlksClipWord σ' I).toNat)) :=
                                                            hpresTab (by decide)
                                                              (hpresTabBase (by decide)
                                                                hmilkClipFess)
                                                          have hdinkTab :
                                                              localsTab.get? "dink" =
                                                                some (.int
                                                                  (Int.ofNat dink.toNat)) :=
                                                            hpresTab (by decide)
                                                              (hpresTabBase (by decide)
                                                                hdinkFess)
                                                          have hurnTab :
                                                              localsTab.get? "urn" =
                                                                some (.address (barkUrn I)) :=
                                                            hpresTab (by decide)
                                                              (hpresTabBase (by decide)
                                                                hurnFess)
                                                          have hkprTab :
                                                              localsTab.get? "kpr" =
                                                                some (.address (barkKpr I)) :=
                                                            hpresTab (by decide)
                                                              (hpresTabBase (by decide)
                                                                hkprFess)
                                                          have hmilkClipIlkDirtNew :
                                                              localsIlkDirtNew.get? "milkClip" =
                                                                some (.address
                                                                  (AccountAddress.ofNat
                                                                    (barkIlksClipWord σ' I).toNat)) :=
                                                            hpresIlkDirtNew (by decide)
                                                              (hpresDirtNew (by decide)
                                                                hmilkClipTab)
                                                          have htabIlkDirtNew :
                                                              localsIlkDirtNew.get? "tab" =
                                                                some (.int
                                                                  (Int.ofNat tab.toNat)) :=
                                                            hpresIlkDirtNew (by decide)
                                                              (hpresDirtNew (by decide)
                                                                htabGet)
                                                          have hdinkIlkDirtNew :
                                                              localsIlkDirtNew.get? "dink" =
                                                                some (.int
                                                                  (Int.ofNat dink.toNat)) :=
                                                            hpresIlkDirtNew (by decide)
                                                              (hpresDirtNew (by decide)
                                                                hdinkTab)
                                                          have hurnIlkDirtNew :
                                                              localsIlkDirtNew.get? "urn" =
                                                                some (.address (barkUrn I)) :=
                                                            hpresIlkDirtNew (by decide)
                                                              (hpresDirtNew (by decide)
                                                                hurnTab)
                                                          have hkprIlkDirtNew :
                                                              localsIlkDirtNew.get? "kpr" =
                                                                some (.address (barkKpr I)) :=
                                                            hpresIlkDirtNew (by decide)
                                                              (hpresDirtNew (by decide)
                                                                hkprTab)
                                                          have hclipReceiver :
                                                              evalExpr? config
                                                                { contract := contract,
                                                                  locals := localsIlkDirtNew, immutables := immStore v }
                                                                evmIlkDirtStele (.var "milkClip") =
                                                                .ok (.address
                                                                  (AccountAddress.ofNat
                                                                    (barkIlksClipWord σ' I).toNat)) := by
                                                            rw [evalExpr?]
                                                            change EvalResult.ofOption
                                                                EvalError.unboundVariable
                                                                (localsIlkDirtNew.get?
                                                                  "milkClip") =
                                                              .ok (.address
                                                                (AccountAddress.ofNat
                                                                  (barkIlksClipWord σ' I).toNat))
                                                            rw [hmilkClipIlkDirtNew]
                                                            rfl
                                                          by_cases hclipCodeZero :
                                                              Reasoning.Theory.extCodeSizeWord
                                                                σIlkDirt
                                                                (barkIlksClipWord σ' I) = ⟨0⟩
                                                          · obtain ⟨_, _, rd4370⟩ :=
                                                              RD.dogBarkKickExtcodesizeGuard
                                                                (v := v) (code := code)
                                                                (g := Sat256.ofUInt256 g)
                                                                (s0 := evmEvm) (I := I)
                                                                (ret := ⟨448⟩)
                                                                (sel := solcSelectorWord I)
                                                                (R := []) (σ := σIlkDirt) (σMem := σ')
                                                                hpatch hmemKickPreSize
                                                                hmemKickPreRead64
                                                                hmload256KickPre rd4267
                                                                (by simp)
                                                            have hclipZeroStele :
                                                                Reasoning.Theory.extCodeSizeWord
                                                                  evmIlkDirtStele.accountMap
                                                                  (barkIlksClipWord σ' I) = ⟨0⟩ :=
                                                              hAccountsIlkDirt ▸ hclipCodeZero
                                                            have hclipNoCode :
                                                                (UInt256.ofNat
                                                                  ((evmIlkDirtStele.lookupAccount
                                                                    (AccountAddress.ofNat
                                                                      (barkIlksClipWord σ' I).toNat)).option
                                                                      0 (fun acc => acc.code.size))).toNat =
                                                                  0 :=
                                                              code_zero_of_state_codeSize_zero
                                                                hclipZeroStele
                                                            have hkickGuardFalse :
                                                                evalExpr? config
                                                                  { contract := contract,
                                                                    locals := localsIlkDirtNew, immutables := immStore v }
                                                                  evmIlkDirtStele
                                                                  (.binary .gt
                                                                    (.extCodeSize
                                                                      (.var "milkClip"))
                                                                    (.intLit 0)) =
                                                                  .ok (.bool false) :=
                                                              evalExpr_barkAddressCodeGuard_false
                                                                hclipReceiver hclipNoCode
                                                            have hkickRev :=
                                                              dogBarkKickNoCodeBlock (v := v)
                                                                (evm := evmIlkDirtStele)
                                                                (locals := localsIlkDirtNew)
                                                                hkickGuardFalse
                                                            have htailPrefix :=
                                                              execBlock_append
                                                                _hprefixIlkDirtStoreTail hkickRev
                                                            have htailBody :
                                                                ExecTransitionBody config
                                                                  contract evmStele
                                                                  (barkLocals I)
                                                                  barkTransition.body
                                                                  .reverted (immStore v) := by
                                                              apply hbodyRevertOfTail
                                                              refine dogBarkDartTailFromLeftoverBlock
                                                                hleftover ?_
                                                              simpa only [afterIntGuard, afterGrab,
                                                                afterFess, afterTabBase,
                                                                afterTab, afterDirtAssign,
                                                                afterIlkDirtAssign, afterKick,
                                                                localsDink, localsGrab,
                                                                localsDue, localsFess,
                                                                localsTabBase, localsTab,
                                                                localsDirtNew,
                                                                localsIlkDirtNew, due, dink,
                                                                tabBase, tab, dirtNew,
                                                                ilkDirtNew, List.append_assoc] using
                                                                execBlock_append_term
                                                                  (s2 := afterKick)
                                                                  htailPrefix
                                                                  (by intro f e h; cases h)
                                                            have hrev :=
                                                              RD.dogBarkKickNoCodeRevert
                                                                hpatch rd4370 hclipCodeZero
                                                                (by simp)
                                                            exact hrev.reEquivExecutionRevert
                                                              hcode hdispatch hdecode htailBody
                                                          · have hclipNonzeroStele :
                                                                Reasoning.Theory.extCodeSizeWord
                                                                  evmIlkDirtStele.accountMap
                                                                  (barkIlksClipWord σ' I) ≠ ⟨0⟩ :=
                                                              hAccountsIlkDirt ▸ hclipCodeZero
                                                            have hclipCodePosStele :
                                                                0 < (UInt256.ofNat
                                                                  ((evmIlkDirtStele.lookupAccount
                                                                    (AccountAddress.ofNat
                                                                      (barkIlksClipWord σ' I).toNat)).option
                                                                      0 (fun acc => acc.code.size))).toNat :=
                                                              code_pos_of_state_codeSize_ne
                                                                hclipNonzeroStele
                                                            have hkickGuardTrue :
                                                                evalExpr? config
                                                                  { contract := contract,
                                                                    locals := localsIlkDirtNew, immutables := immStore v }
                                                                  evmIlkDirtStele
                                                                  (.binary .gt
                                                                    (.extCodeSize
                                                                      (.var "milkClip"))
                                                                    (.intLit 0)) =
                                                                  .ok (.bool true) :=
                                                              evalExpr_barkAddressCodeGuard_true
                                                                hclipReceiver hclipCodePosStele
                                                            have hIlkDirtEvmEnv :
                                                                evmIlkDirtEvm.executionEnv = I := by
                                                              simp [evmIlkDirtEvm, evmDirtEvm,
                                                                evmFessEvm, evmGrabEvm,
                                                                evmIlksPostEvm, evmPostEvm,
                                                                evmEvm, initState]
                                                            have hIlkDirtEvmMap :
                                                                evmIlkDirtEvm.accountMap = σIlkDirt := by
                                                              simp [evmIlkDirtEvm]
                                                            have hIlkDirtAccounts :
                                                                evmIlkDirtEvm.accountMap =
                                                                  evmIlkDirtStele.accountMap := by
                                                              exact hIlkDirtEvmMap.trans
                                                                hAccountsIlkDirt
                                                            have hIlkDirtEvmOrig :
                                                                evmIlkDirtEvm.σ₀ = evmEvm.σ₀ := by
                                                              simp [evmIlkDirtEvm, evmDirtEvm,
                                                                evmFessEvm, evmGrabEvm,
                                                                evmIlksPostEvm, evmPostEvm,
                                                                evmEvm, initState]
                                                            have hIlkDirtSteleEnv :
                                                                evmIlkDirtStele.executionEnv = I := by
                                                              simp [evmIlkDirtStele, evmDirtStele,
                                                                evmFessStele, evmGrabStele,
                                                                evmIlksPostStele, evmPostStele,
                                                                evmStele, initState,
                                                                storageStore_executionEnv]
                                                            have hIlkDirtSteleOrig :
                                                                evmIlkDirtStele.σ₀ = evmEvm.σ₀ := by
                                                              calc
                                                                evmIlkDirtStele.σ₀ = evmDirtStele.σ₀ := by
                                                                  simpa [evmIlkDirtStele] using
                                                                    storageStore_σ₀ evmDirtStele
                                                                      evmDirtStele.executionEnv.codeOwner
                                                                      (barkIlksDirtSlotFor I)
                                                                      ilkDirtNew
                                                                _ = evmFessStele.σ₀ := by
                                                                  simpa [evmDirtStele] using
                                                                    storageStore_σ₀ evmFessStele
                                                                      evmFessStele.executionEnv.codeOwner
                                                                      ⟨5⟩ dirtNew
                                                                _ = evmEvm.σ₀ := by
                                                                  simp [evmFessStele, evmGrabStele,
                                                                    evmIlksPostStele, evmPostStele,
                                                                    evmStele, evmEvm, initState]
                                                            have hIlkDirtOriginalAccounts :
                                                                evmIlkDirtEvm.σ₀ = evmIlkDirtStele.σ₀ := by
                                                              rw [hIlkDirtEvmOrig, hIlkDirtSteleOrig]
                                                            have hIlkDirtEnvEq :
                                                                evmIlkDirtStele.executionEnv =
                                                                  evmIlkDirtEvm.executionEnv := by
                                                              rw [hIlkDirtSteleEnv, hIlkDirtEvmEnv]
                                                            obtain ⟨σKick, zKick, outKick, AKick,
                                                                _, _, rd4386, hcallKickEvmRaw,
                                                                houtKickSize⟩ :=
                                                              RD.dogBarkKickPostCall
                                                                (v := v) (code := code)
                                                                (s0 := evmEvm)
                                                                (evm := evmIlkDirtEvm)
                                                                (ret := ⟨448⟩)
                                                                (sel := solcSelectorWord I)
                                                                (R := []) (σ := σIlkDirt)
                                                                (σMem := σ') hpatch rd4267
                                                                hmemKickPreSize hmemKickPreRead64
                                                                hmload256KickPre
                                                                hclipCodeZero
                                                                hIlkDirtEvmEnv hIlkDirtEvmMap
                                                                hIlkDirtEvmOrig hdepthLt
                                                                (by simp)
                                                            let evmKickEvm :=
                                                              { evmIlkDirtEvm with
                                                                accountMap := σKick,
                                                                substate := AKick }
                                                            have hcallKickEvm :
                                                                typedCallViaEVM config
                                                                  evmIlkDirtEvm
                                                                  (EVM.address
                                                                    (AccountAddress.ofNat
                                                                      (barkIlksClipWord σ' I).toNat))
                                                                  "kick" 0
                                                                  [.int (Int.ofNat tab.toNat),
                                                                    .int (Int.ofNat dink.toNat),
                                                                    .address (barkUrn I),
                                                                    .address (barkKpr I)]
                                                                  (zKick, evmKickEvm, outKick)
                                                                  true := by
                                                              simpa [evmKickEvm] using hcallKickEvmRaw
                                                            obtain ⟨σKickStele, AKickStele,
                                                                hcallKickSteleRaw,
                                                                hAccountsKickRaw⟩ :=
                                                              Reasoning.Theory.typedCallViaEVM_sameInputs
                                                                (evm_stele := evmIlkDirtStele)
                                                                hcallKickEvm
                                                                hIlkDirtAccounts
                                                                hIlkDirtOriginalAccounts
                                                                hIlkDirtEnvEq.symm
                                                            let evmKickStele :=
                                                              { evmIlkDirtStele with
                                                                accountMap := σKickStele,
                                                                substate := AKickStele }
                                                            have hcallKickStele :
                                                                typedCallViaEVM config
                                                                  evmIlkDirtStele
                                                                  (EVM.address
                                                                    (AccountAddress.ofNat
                                                                      (barkIlksClipWord σ' I).toNat))
                                                                  "kick" 0
                                                                  [.int (Int.ofNat tab.toNat),
                                                                    .int (Int.ofNat dink.toNat),
                                                                    .address (barkUrn I),
                                                                    .address (barkKpr I)]
                                                                  (zKick, evmKickStele, outKick)
                                                                  true := by
                                                              simpa [evmKickEvm, evmKickStele]
                                                                using hcallKickSteleRaw
                                                            have hAccountsKick :
                                                                Eq σKick
                                                                  evmKickStele.accountMap := by
                                                              simpa [evmKickEvm, evmKickStele]
                                                                using hAccountsKickRaw
                                                            cases zKick
                                                            · simp only [Bool.false_eq_true, if_false] at rd4386 hcallKickEvm hcallKickStele
                                                              have hkickRev :=
                                                                dogBarkKickCallFailureBlock
                                                                  (v := v)
                                                                  (evm := evmIlkDirtStele)
                                                                  (evm' := evmKickStele)
                                                                  (locals := localsIlkDirtNew)
                                                                  (outKick := outKick)
                                                                  (milkClip :=
                                                                    barkIlksClipWord σ' I)
                                                                  (tab := tab) (dink := dink)
                                                                  (urn := barkUrn I)
                                                                  (kpr := barkKpr I)
                                                                  hkickGuardTrue
                                                                  hmilkClipIlkDirtNew
                                                                  htabIlkDirtNew
                                                                  hdinkIlkDirtNew
                                                                  hurnIlkDirtNew
                                                                  hkprIlkDirtNew
                                                                  hcallKickStele
                                                              have htailPrefix :=
                                                                execBlock_append
                                                                  _hprefixIlkDirtStoreTail
                                                                  hkickRev
                                                              have htailBody :
                                                                  ExecTransitionBody config
                                                                    contract evmStele
                                                                    (barkLocals I)
                                                                    barkTransition.body
                                                                    .reverted (immStore v) := by
                                                                apply hbodyRevertOfTail
                                                                refine dogBarkDartTailFromLeftoverBlock
                                                                  hleftover ?_
                                                                simpa only [afterIntGuard, afterGrab,
                                                                  afterFess, afterTabBase,
                                                                  afterTab, afterDirtAssign,
                                                                  afterIlkDirtAssign, afterKick,
                                                                  localsDink, localsGrab,
                                                                  localsDue, localsFess,
                                                                  localsTabBase, localsTab,
                                                                  localsDirtNew,
                                                                  localsIlkDirtNew, due, dink,
                                                                  tabBase, tab, dirtNew,
                                                                  ilkDirtNew,
                                                                  List.append_assoc] using
                                                                  execBlock_append_term
                                                                    (s2 := afterKick)
                                                                    htailPrefix
                                                                    (by intro f e h; cases h)
                                                              have hrev :=
                                                                RD.dogBarkKickCallFailure
                                                                  hpatch rd4386 houtKickSize
                                                                  (by simp)
                                                              exact hrev.reEquivExecutionRevert
                                                                hcode hdispatch hdecode htailBody
                                                            · simp only [Bool.true_eq_false, if_true] at rd4386 hcallKickEvm hcallKickStele
                                                              obtain ⟨_, _, rd4404⟩ :=
                                                                RD.dogBarkKickCallSuccessToDecode
                                                                  hpatch rd4386 (by simp)
                                                              let memKickPost :=
                                                                barkKickPostCallMem I memKickPre
                                                                  outKick tab dink
                                                              have hminShort
                                                                  (hshort : outKick.size < 32) :
                                                                  (min barkKickOutSize
                                                                    (UInt256.ofNat
                                                                      outKick.size)).toNat =
                                                                    outKick.size := by
                                                                exact umin_ofNat_right_toNat_of_lt
                                                                  (c := 32) (n := outKick.size)
                                                                  (by decide) hshort
                                                                  houtKickSize
                                                              by_cases hkickRetLong :
                                                                  32 ≤ outKick.size
                                                              · let id :=
                                                                  UInt256.ofNat
                                                                    (fromByteArrayBigEndian
                                                                      (outKick.extract 0 32))
                                                                have hdecKick :
                                                                    config.externalABI.decode?
                                                                        "kick" outKick =
                                                                      some [.int
                                                                        (Int.ofNat id.toNat)] := by
                                                                  simpa [id] using
                                                                    barkKickDecode_ok (v := v)
                                                                      hkickRetLong
                                                                have hkickOk :=
                                                                  dogBarkKickCallSuccessBlock
                                                                    (v := v)
                                                                    (evm := evmIlkDirtStele)
                                                                    (evm' := evmKickStele)
                                                                    (locals := localsIlkDirtNew)
                                                                    (outKick := outKick)
                                                                    (milkClip :=
                                                                      barkIlksClipWord σ' I)
                                                                    (tab := tab) (dink := dink)
                                                                    (id := id)
                                                                    (urn := barkUrn I)
                                                                    (kpr := barkKpr I)
                                                                    hkickGuardTrue
                                                                    hmilkClipIlkDirtNew
                                                                    htabIlkDirtNew
                                                                    hdinkIlkDirtNew
                                                                    hurnIlkDirtNew
                                                                    hkprIlkDirtNew
                                                                    hcallKickStele hdecKick
                                                                have _hprefixKick :=
                                                                  execBlock_append
                                                                    _hprefixIlkDirtStore
                                                                    hkickOk
                                                                have _hprefixKickTail :=
                                                                  execBlock_append
                                                                    _hprefixIlkDirtStoreTail
                                                                    hkickOk
                                                                have hmemKickPostSize :
                                                                    memKickPost.size = 580 := by
                                                                  simpa [memKickPost] using
                                                                    barkKickPostCallMem_size_long
                                                                      hmemKickPreSize
                                                                      hkickRetLong
                                                                      houtKickSize
                                                                have hmemKickPostRead64 :
                                                                    memKickPost.readWithPadding
                                                                        64 32 =
                                                                      UInt256.toByteArray
                                                                        ⟨384⟩ := by
                                                                  simpa [memKickPost] using
                                                                    barkKickPostCallMem_read64_long
                                                                      hmemKickPreSize
                                                                      hmemKickPreRead64
                                                                      hkickRetLong
                                                                      houtKickSize
                                                                have hmload64KickPost :
                                                                    (if (⟨64⟩ : UInt256).toNat ≥
                                                                          memKickPost.size
 then ⟨0⟩
                                                                     else UInt256.ofNat
                                                                      (fromByteArrayBigEndian
                                                                        (memKickPost.readWithPadding
                                                                          (⟨64⟩ : UInt256).toNat
                                                                          32))) = ⟨384⟩ := by
                                                                  simpa [memKickPost] using
                                                                    barkKickPostCallMem_mload64_long
                                                                      hmemKickPreSize
                                                                      hmemKickPreRead64
                                                                      hkickRetLong
                                                                      houtKickSize
                                                                have hmload256KickPost :
                                                                    (if (⟨256⟩ : UInt256).toNat ≥
                                                                          memKickPost.size
 then ⟨0⟩
                                                                     else UInt256.ofNat
                                                                      (fromByteArrayBigEndian
                                                                        (memKickPost.readWithPadding
                                                                          (⟨256⟩ : UInt256).toNat
                                                                          32))) =
                                                                      barkIlksClipWord σ' I := by
                                                                  simpa [memKickPost] using
                                                                    barkKickPostCallMem_mload256_long
                                                                      hmemKickPreSize
                                                                      hread256KickPre
                                                                      hkickRetLong houtKickSize
                                                                have hmload384KickPost :
                                                                    (if (⟨384⟩ : UInt256).toNat ≥
                                                                          memKickPost.size
 then ⟨0⟩
                                                                     else UInt256.ofNat
                                                                      (fromByteArrayBigEndian
                                                                        (memKickPost.readWithPadding
                                                                          (⟨384⟩ : UInt256).toNat
                                                                          32))) = id := by
                                                                  simpa [memKickPost, id] using
                                                                    barkKickPostCallMem_mload384_long
                                                                      hmemKickPreSize
                                                                      hkickRetLong houtKickSize
                                                                obtain ⟨_, _, rd4427⟩ :=
                                                                  RD.dogBarkKickReturnDecodeOk
                                                                    hpatch rd4404 hkickRetLong
                                                                    houtKickSize
                                                                    hmload64KickPost
                                                                    hmload384KickPost (by simp)
                                                                obtain ⟨_, _, rd448⟩ :=
                                                                  RD.dogBarkKickDecodedToPublicReturn
                                                                    (v := v) (code := code)
                                                                    (σMem := σ') hpatch rd4427
                                                                    (dogPatchedJumpDest hpatch
                                                                      (by native_decide))
                                                                    _hperm hmemKickPostSize
                                                                    hmemKickPostRead64
                                                                    hmload256KickPost
                                                                let memLog :=
                                                                  barkBarkLogMem memKickPost
                                                                    dink dart due
                                                                    (barkIlksClipWord σ' I)
                                                                have hmemLogSize :
                                                                    memLog.size = 580 := by
                                                                  simpa [memLog] using
                                                                    barkBarkLogMem_size
                                                                      hmemKickPostSize
                                                                have hmemLogRead64 :
                                                                    memLog.readWithPadding 64 32 =
                                                                      UInt256.toByteArray
                                                                        ⟨384⟩ := by
                                                                  simpa [memLog] using
                                                                    barkBarkLogMem_read64
                                                                      hmemKickPostSize
                                                                      hmemKickPostRead64
                                                                have hmload64Log :
                                                                    (if (⟨64⟩ : UInt256).toNat ≥
                                                                          memLog.size
 then ⟨0⟩
                                                                     else UInt256.ofNat
                                                                      (fromByteArrayBigEndian
                                                                        (memLog.readWithPadding
                                                                          (⟨64⟩ : UInt256).toNat
                                                                          32))) = ⟨384⟩ := by
                                                                  simpa [memLog] using
                                                                    barkBarkLogMem_mload64
                                                                      hmemKickPostSize
                                                                      hmemKickPostRead64
                                                                let memReturn := barkReturnIdMem memLog id
                                                                have hmload64Return :
                                                                    (if (⟨64⟩ : UInt256).toNat ≥
                                                                          memReturn.size
 then ⟨0⟩
                                                                     else UInt256.ofNat
                                                                      (fromByteArrayBigEndian
                                                                        (memReturn.readWithPadding
                                                                          (⟨64⟩ : UInt256).toNat
                                                                          32))) = ⟨384⟩ := by
                                                                  simpa [memReturn] using
                                                                    barkReturnIdMem_mload64
                                                                      hmemLogSize hmemLogRead64
                                                                have hread384Return :
                                                                    memReturn.readWithPadding
                                                                        384 32 =
                                                                      UInt256.toByteArray id := by
                                                                  simpa [memReturn] using
                                                                    barkReturnIdMem_read384
                                                                      hmemLogSize
                                                                have hret :=
                                                                  RD.dogBarkPublicReturnId
                                                                    hpatch rd448 hmload64Log
                                                                    (by
                                                                      simp [memReturn, memLog,
                                                                        memKickPost, memKickPre,
                                                                        memFess, dink,
                                                                        barkReturnIdMem])
                                                                    hmload64Return
                                                                    hread384Return
                                                                let localsId :=
                                                                  barkLocalsId
                                                                    localsIlkDirtNew id
                                                                have hidGet :
                                                                    localsId.get? "id" =
                                                                      some (.int
                                                                        (Int.ofNat id.toNat)) := by
                                                                  simpa [localsId] using
                                                                    barkLocalsId_get_id
                                                                      localsIlkDirtNew id
                                                                have hreturn :=
                                                                  dogBarkReturnIdBlock (v := v)
                                                                    (evm := evmKickStele)
                                                                    (locals := localsId) hidGet
                                                                have htailReturn :=
                                                                  execBlock_append _hprefixKickTail
                                                                    hreturn
                                                                have htailBody :
                                                                    ExecTransitionBody config
                                                                      contract evmStele
                                                                      (barkLocals I)
                                                                      barkTransition.body
                                                                      (.returned
                                                                        { contract := contract,
                                                                          locals := localsId, immutables := immStore v }
                                                                        evmKickStele
                                                                        (some [.int
                                                                  (Int.ofNat
                                                                            id.toNat)])) (immStore v) := by
                                                                  apply hbodyReturnOfTail
                                                                  refine
                                                                    dogBarkDartTailFromLeftoverBlock
                                                                      hleftover ?_
                                                                  simpa only [afterIntGuard,
                                                                    afterGrab, afterFess,
                                                                    afterTabBase, afterTab,
                                                                    afterDirtAssign,
                                                                    afterIlkDirtAssign,
                                                                    afterKick, localsDink,
                                                                    localsGrab, localsDue,
                                                                    localsFess,
                                                                    localsTabBase, localsTab,
                                                                    localsDirtNew,
                                                                    localsIlkDirtNew, localsId,
                                                                    due, dink, tabBase, tab,
                                                                    dirtNew, ilkDirtNew,
                                                                    List.append_assoc] using
                                                                    htailReturn
                                                                have haccounts :
                                                                    Eq
                                                                      σKick
                                                                      evmKickStele.accountMap := by
                                                                  simpa [evmKickEvm,
                                                                    evmKickStele] using
                                                                    hAccountsKick
                                                                have henc :
                                                                    returnEquiv
                                                                      (UInt256.toByteArray id)
                                                                      (some [.int
                                                                        (Int.ofNat id.toNat)])
                                                                      barkTransition.returnType := by
                                                                  exact returnEquiv_of_encode
                                                                    (by
                                                                      simpa [uint256] using
                                                                        uint256ReturnEncoding id)
                                                                exact
                                                                  hret.reEquivExecutionGen
                                                                    hcode hdispatch hdecode
                                                                    htailBody haccounts henc
                                                              · have hshort :
                                                                    outKick.size < 32 := by
                                                                  omega
                                                                have hdecKick :
                                                                    config.externalABI.decode?
                                                                        "kick" outKick = none :=
                                                                  barkKickDecode_none_short
                                                                    (v := v) hshort
                                                                have hkickRev :=
                                                                  dogBarkKickDecodeRevertBlock
                                                                    (v := v)
                                                                    (evm := evmIlkDirtStele)
                                                                    (evm' := evmKickStele)
                                                                    (locals := localsIlkDirtNew)
                                                                    (outKick := outKick)
                                                                    (milkClip :=
                                                                      barkIlksClipWord σ' I)
                                                                    (tab := tab) (dink := dink)
                                                                    (urn := barkUrn I)
                                                                    (kpr := barkKpr I)
                                                                    hkickGuardTrue
                                                                    hmilkClipIlkDirtNew
                                                                    htabIlkDirtNew
                                                                    hdinkIlkDirtNew
                                                                    hurnIlkDirtNew
                                                                    hkprIlkDirtNew
                                                                    hcallKickStele hdecKick
                                                                have htailPrefix :=
                                                                  execBlock_append
                                                                    _hprefixIlkDirtStoreTail
                                                                    hkickRev
                                                                have htailBody :
                                                                    ExecTransitionBody config
                                                                      contract evmStele
                                                                      (barkLocals I)
                                                                      barkTransition.body
                                                                      .reverted (immStore v) := by
                                                                  apply hbodyRevertOfTail
                                                                  refine dogBarkDartTailFromLeftoverBlock
                                                                    hleftover ?_
                                                                  simpa only [afterIntGuard,
                                                                    afterGrab, afterFess,
                                                                    afterTabBase, afterTab,
                                                                    afterDirtAssign,
                                                                    afterIlkDirtAssign,
                                                                    afterKick, localsDink,
                                                                    localsGrab, localsDue,
                                                                    localsFess,
                                                                    localsTabBase, localsTab,
                                                                    localsDirtNew,
                                                                    localsIlkDirtNew, due, dink,
                                                                    tabBase, tab, dirtNew,
                                                                    ilkDirtNew,
                                                                    List.append_assoc] using
                                                                    execBlock_append_term
                                                                      (s2 := afterKick)
                                                                      htailPrefix
                                                                      (by intro f e h; cases h)
                                                                have hmin :
                                                                    (min barkKickOutSize
                                                                      (UInt256.ofNat
                                                                        outKick.size)).toNat =
                                                                      outKick.size :=
                                                                  hminShort hshort
                                                                have hmload64KickPost :
                                                                    (if (⟨64⟩ : UInt256).toNat ≥
                                                                          memKickPost.size
 then ⟨0⟩
                                                                     else UInt256.ofNat
                                                                      (fromByteArrayBigEndian
                                                                        (memKickPost.readWithPadding
                                                                          (⟨64⟩ : UInt256).toNat
                                                                          32))) = ⟨384⟩ := by
                                                                  simpa [memKickPost,
                                                                    barkKickPostCallMem, hmin] using
                                                                    barkKickPostCallWrite_mload64
                                                                      (I := I) (tab := tab)
                                                                      (dink := dink)
                                                                      (mem := memKickPre)
                                                                      (out := outKick)
                                                                      (L := outKick.size)
                                                                      hmemKickPreSize
                                                                      hmemKickPreRead64
                                                                      (by omega)
                                                                      (le_rfl)
                                                                have hrev :=
                                                                  RD.dogBarkKickReturnDecodeShortReverts
                                                                    hpatch rd4404 hshort
                                                                    houtKickSize
                                                                    hmload64KickPost
                                                                    (by simp)
                                                                exact hrev.reEquivExecutionRevert
                                                                  hcode hdispatch hdecode
                                                                  htailBody
                                                        · have hoverIlkDirt :
                                                              UInt256.size ≤
                                                                (barkIlksDirtWord σ' I).toNat +
                                                                  tab.toNat :=
                                                            Nat.le_of_not_gt hfitIlkDirt
                                                          have hilkDirtRev :=
                                                            dogBarkIlkDirtAddOverflowSource
                                                              (v := v) evmDirtStele
                                                              hmilkDirtDirtNew htabDirtNew
                                                              hoverIlkDirt
                                                          have htailPrefix :=
                                                            execBlock_append
                                                              _hprefixDirtStoreTail hilkDirtRev
                                                          have htailBody :
                                                              ExecTransitionBody config
                                                                contract evmStele
                                                                (barkLocals I)
                                                                barkTransition.body
                                                                .reverted (immStore v) := by
                                                            apply hbodyRevertOfTail
                                                            refine dogBarkDartTailFromLeftoverBlock
                                                              hleftover ?_
                                                            simpa only [afterIntGuard, afterGrab,
                                                              afterFess, afterTabBase,
                                                              afterTab, afterDirtAssign,
                                                              afterIlkDirtNew,
                                                              localsDink, localsGrab,
                                                              localsDue, localsFess,
                                                              localsTabBase, localsTab,
                                                              localsDirtNew, due, dink,
                                                              tabBase, tab, dirtNew,
                                                              List.append_assoc] using
                                                              execBlock_append_term
                                                                (s2 := afterIlkDirtNew)
                                                                htailPrefix
                                                                (by intro f e h; cases h)
                                                          have hrev :=
                                                            RD.dogBarkIlkDirtAddOverflowReverts
                                                              hpatch hmload352Fess
                                                              hoverIlkDirt rd4226 (by simp)
                                                          exact hrev.reEquivExecutionRevert
                                                            hcode hdispatch hdecode htailBody
                                                      · have hoverDirt :
                                                            UInt256.size ≤
                                                              (solcSlotWordAt ⟨5⟩ σFess I).toNat +
                                                                tab.toNat :=
                                                          Nat.le_of_not_gt hfitDirt
                                                        have hoverDirtStele :
                                                            UInt256.size ≤
                                                              (solcSlotWordAt ⟨5⟩
                                                                    evmFessStele.accountMap
                                                                    evmFessStele.executionEnv).toNat +
                                                                  tab.toNat := by
                                                          simpa [hDirtSlotFess] using hoverDirt
                                                        have hdirtRev :=
                                                          dogBarkDirtAddOverflowSource
                                                            (v := v) evmFessStele hDirtTab
                                                            htabGet hoverDirtStele
                                                        have htailPrefix :=
                                                          execBlock_append _hprefixTabTail
                                                            hdirtRev
                                                        have htailBody :
                                                            ExecTransitionBody config
                                                              contract evmStele
                                                              (barkLocals I)
                                                              barkTransition.body
                                                              .reverted (immStore v) := by
                                                          apply hbodyRevertOfTail
                                                          refine dogBarkDartTailFromLeftoverBlock
                                                            hleftover ?_
                                                          simpa only [afterIntGuard, afterGrab,
                                                            afterFess, afterTabBase, afterTab,
                                                            afterDirtNew,
                                                            localsDink, localsGrab, localsDue,
                                                            localsFess, localsTabBase, localsTab,
                                                            due, dink, tabBase, tab,
                                                            List.append_assoc] using
                                                            execBlock_append_term
                                                              (s2 := afterDirtNew) htailPrefix
                                                              (by intro f e h; cases h)
                                                        have hrev :=
                                                          RD.dogBarkDirtAddOverflowReverts
                                                            hpatch hoverDirt rd4211 (by simp)
                                                        exact hrev.reEquivExecutionRevert hcode
                                                          hdispatch hdecode htailBody
                                                    · have hoverTabBase :
                                                          UInt256.size ≤
                                                            due.toNat * milkChop.toNat :=
                                                        Nat.le_of_not_gt hfitTabBase
                                                      have htabRev :=
                                                        dogBarkTabBaseCheckedMulOverflowSource
                                                          (v := v) evmFessStele hdueFess
                                                          hmilkChopFess hoverTabBase
                                                      have htailPrefix :=
                                                        execBlock_append _hprefixFessTail htabRev
                                                      have htailBody :
                                                          ExecTransitionBody config
                                                            contract evmStele (barkLocals I)
                                                            barkTransition.body
                                                            .reverted (immStore v) := by
                                                        apply hbodyRevertOfTail
                                                        refine dogBarkDartTailFromLeftoverBlock
                                                          hleftover ?_
                                                        simpa only [afterIntGuard, afterGrab,
                                                          afterFess, afterTabBase,
                                                          localsDink, localsGrab, localsDue,
                                                          localsFess, due, dink,
                                                          List.append_assoc] using
                                                          execBlock_append_term
                                                            (s2 := afterTabBase)
                                                            htailPrefix
                                                            (by intro f e h; cases h)
                                                      have hrev :=
                                                        RD.dogBarkTabBaseCheckedMulOverflowReverts
                                                          hpatch hoverTabBase hmload288Fess
                                                          rd4176 (by simp)
                                                      exact hrev.reEquivExecutionRevert hcode
                                                        hdispatch hdecode htailBody
                                          · have hdinkOverflow :
                                                dogInt256LimitWord.toNat < dink.toNat :=
                                              Nat.lt_of_not_ge hdinkBound
                                            have hprefixGuard :=
                                              dogBarkPostLeftoverDinkGuardOkSource (v := v)
                                                evmIlksPostStele hink hdart hart hfitInkDart
                                                hartNe (by simpa [dink] using hdinkPos)
                                            have hintRev :=
                                              dogBarkInt256GuardDinkOverflowSource (v := v)
                                                evmIlksPostStele hdartDinkGet hdinkGet hdartBound
                                                (by simpa [dink] using hdinkOverflow)
                                            have htailPrefix :
                                                ExecBlock config
                                                  { contract := contract, locals := localsAfter, immutables := immStore v }
                                                  evmIlksPostStele
                                                  (checkedMulUintInto "inkDart" (.var "ink")
                                                      (.var "dart") ++
                                                    [ .letDecl "dink" (some uint256)
                                                        (.binary .div (.var "inkDart")
                                                          (.var "art")),
                                                      .require
                                                        (.binary .gt (.var "dink")
                                                          (.intLit 0)),
                                                      .require
                                                        (.binary .and
                                                          (.binary .le (.var "dart")
                                                            (.intLit int256Limit))
                                                          (.binary .le (.var "dink")
                                                            (.intLit int256Limit))) ])
                                                  .reverted := by
                                              simpa [List.append_assoc, localsDink, dink] using
                                                execBlock_append hprefixGuard hintRev
                                            have htailBody :
                                                ExecTransitionBody config contract
                                                  evmStele (barkLocals I)
                                                  barkTransition.body .reverted (immStore v) := by
                                              apply hbodyRevertOfTail
                                              refine dogBarkDartTailFromLeftoverBlock hleftover ?_
                                              simpa only [afterIntGuard, List.append_assoc] using
                                                execBlock_append_term (s2 := afterIntGuard)
                                                  htailPrefix
                                                  (by intro f e h; cases h)
                                            have hrev :=
                                              RD.dogBarkInt256GuardDinkOverflowReverts
                                                (v := v) (code := code) (ret := ⟨448⟩)
                                                (sel := solcSelectorWord I) (R := [])
                                                hpatch hdartBound
                                                (by simpa [dink] using hdinkOverflow)
                                                (by simpa [mem0] using hpostMemSize)
                                                (by simpa [mem0] using hpostMemRead64)
                                                rd3797 (by simp)
                                            exact hrev.reEquivExecutionRevert hcode hdispatch
                                              hdecode htailBody
                                        · have hdartOverflow :
                                              dogInt256LimitWord.toNat < dart.toNat :=
                                            Nat.lt_of_not_ge hdartBound
                                          have hprefixGuard :=
                                            dogBarkPostLeftoverDinkGuardOkSource (v := v)
                                              evmIlksPostStele hink hdart hart hfitInkDart
                                              hartNe (by simpa [dink] using hdinkPos)
                                          have hintRev :=
                                            dogBarkInt256GuardDartOverflowSource (v := v)
                                              evmIlksPostStele hdartDinkGet hdinkGet
                                              hdartOverflow
                                          have htailPrefix :
                                              ExecBlock config
                                                { contract := contract, locals := localsAfter, immutables := immStore v }
                                                evmIlksPostStele
                                                (checkedMulUintInto "inkDart" (.var "ink")
                                                    (.var "dart") ++
                                                  [ .letDecl "dink" (some uint256)
                                                      (.binary .div (.var "inkDart")
                                                        (.var "art")),
                                                    .require
                                                      (.binary .gt (.var "dink") (.intLit 0)),
                                                    .require
                                                      (.binary .and
                                                        (.binary .le (.var "dart")
                                                          (.intLit int256Limit))
                                                        (.binary .le (.var "dink")
                                                          (.intLit int256Limit))) ])
                                                .reverted := by
                                            simpa [List.append_assoc, localsDink, dink] using
                                              execBlock_append hprefixGuard hintRev
                                          have htailBody :
                                              ExecTransitionBody config contract
                                                evmStele (barkLocals I)
                                                barkTransition.body .reverted (immStore v) := by
                                            apply hbodyRevertOfTail
                                            refine dogBarkDartTailFromLeftoverBlock hleftover ?_
                                            simpa only [afterIntGuard, List.append_assoc] using
                                              execBlock_append_term (s2 := afterIntGuard)
                                                htailPrefix
                                                (by intro f e h; cases h)
                                          have hrev :=
                                            RD.dogBarkInt256GuardDartOverflowReverts
                                              (v := v) (code := code) (ret := ⟨448⟩)
                                              (sel := solcSelectorWord I) (R := [])
                                              hpatch hdartOverflow
                                              (by simpa [mem0] using hpostMemSize)
                                              (by simpa [mem0] using hpostMemRead64) rd3797
                                              (by simp)
                                          exact hrev.reEquivExecutionRevert hcode hdispatch
                                            hdecode htailBody
                                      · have hprefixDink :=
                                          dogBarkPostLeftoverDinkLetOkSource (v := v)
                                            evmIlksPostStele hink hdart hart hfitInkDart hartNe
                                        have hguardRev :=
                                          dogBarkDinkGuardRevertSource (v := v)
                                            evmIlksPostStele hdinkGet
                                            (by simpa [dink] using hdinkPos)
                                        have htailPrefix :
                                            ExecBlock config
                                              { contract := contract, locals := localsAfter, immutables := immStore v }
                                              evmIlksPostStele
                                              (checkedMulUintInto "inkDart" (.var "ink")
                                                  (.var "dart") ++
                                                [ .letDecl "dink" (some uint256)
                                                    (.binary .div (.var "inkDart")
                                                      (.var "art")),
                                                  .require
                                                    (.binary .gt (.var "dink") (.intLit 0)) ])
                                              .reverted := by
                                          simpa [List.append_assoc, localsDink, dink] using
                                            execBlock_append hprefixDink hguardRev
                                        have htailBody :
                                            ExecTransitionBody config contract
                                              evmStele (barkLocals I) barkTransition.body
                                              .reverted (immStore v) := by
                                          apply hbodyRevertOfTail
                                          refine dogBarkDartTailFromLeftoverBlock hleftover ?_
                                          simpa only [afterDinkGuard, afterIntGuard,
                                            List.append_assoc] using
                                            execBlock_append_term (s2 := afterDinkGuard)
                                              htailPrefix
                                              (by intro f e h; cases h)
                                        have hrev :=
                                          RD.dogBarkDinkGuardReverts
                                            (v := v) (code := code) (ret := ⟨448⟩)
                                            (sel := solcSelectorWord I) (R := []) hpatch
                                            (by simpa [dink] using hdinkPos)
                                            (by simpa [mem0] using hpostMemSize)
                                            (by simpa [mem0] using hpostMemRead64) rd3726
                                            (by simp)
                                        exact hrev.reEquivExecutionRevert hcode hdispatch
                                          hdecode htailBody
                                    · have hoverInkDart : UInt256.size ≤ ink.toNat * dart.toNat :=
                                        not_lt.mp hfitInkDart
                                      have htailPrefix :=
                                        dogBarkInkDartCheckedMulOverflow (v := v)
                                          evmIlksPostStele hink hdart hoverInkDart
                                      have htailBody :
                                          ExecTransitionBody config contract
                                            evmStele (barkLocals I) barkTransition.body
                                            .reverted (immStore v) := by
                                        apply hbodyRevertOfTail
                                        refine dogBarkDartTailFromLeftoverBlock hleftover ?_
                                        simpa only [afterInkDart, afterIntGuard,
                                          List.append_assoc] using
                                          execBlock_append_term (s2 := afterInkDart)
                                            htailPrefix
                                            (by intro f e h; cases h)
                                      have hrev :=
                                        RD.dogBarkInkDartOverflowReverts
                                          (v := v) (code := code) (ret := ⟨448⟩)
                                          (sel := solcSelectorWord I) (R := []) hpatch
                                          hoverInkDart rd3700 (by simp)
                                      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode
                                        htailBody
                                  have hrateDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "rate" =
                                        some (.int (Int.ofNat rate.toNat)) := by
                                    simpa [rate] using
                                      barkLocalsDart_get_rate evmPostStele evmIlksPostStele I
                                        out outIlks
                                  have hmilkClipDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "milkClip" =
                                        some (.address (AccountAddress.ofNat
                                          (barkIlksClipWord σ' I).toNat)) := by
                                    simpa [hmilkClip] using
                                      barkLocalsDart_get_milkClip evmPostStele evmIlksPostStele I
                                        out outIlks
                                  have hmilkChopDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "milkChop" =
                                        some (.int (Int.ofNat milkChop.toNat)) := by
                                    simpa [milkChop, hmilkChop] using
                                      barkLocalsDart_get_milkChop evmPostStele evmIlksPostStele I
                                        out outIlks
                                  have hmilkDirtDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "milkDirt" =
                                        some (.int (Int.ofNat
                                          (barkIlksDirtWord σ' I).toNat)) := by
                                    simpa [hmilkDirt] using
                                      barkLocalsDart_get_milkDirt evmPostStele evmIlksPostStele I
                                        out outIlks
                                  have hilkDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "ilk" =
                                        some (.fixedBytes bytes32Width (barkIlkBytes I)) :=
                                    barkLocalsDart_get_ilk evmPostStele evmIlksPostStele I out
                                      outIlks
                                  have hurnDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "urn" =
                                        some (.address (barkUrn I)) :=
                                    barkLocalsDart_get_urn evmPostStele evmIlksPostStele I out
                                      outIlks
                                  have hkprDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "kpr" =
                                        some (.address (barkKpr I)) :=
                                    barkLocalsDart_get_kpr evmPostStele evmIlksPostStele I out
                                      outIlks
                                  have hvowDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "vow" = none :=
                                    barkLocalsDart_get_vow evmPostStele evmIlksPostStele I out
                                      outIlks
                                  have hDirtDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "Dirt" = none :=
                                    barkLocalsDart_get_Dirt evmPostStele evmIlksPostStele I out
                                      outIlks
                                  have hilksDartBase :
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? "ilks" = none :=
                                    barkLocalsDart_get_ilks evmPostStele evmIlksPostStele I out
                                      outIlks
                                  have hpresDusty {name : Ident} {value : Value}
                                      (hname : ("dart" == name) = false)
                                      (hleftoverDueName : ("leftoverDue" == name) = false)
                                      (hleftoverArtName : ("leftoverArt" == name) = false)
                                      (hget :
                                        (barkLocalsDart evmPostStele evmIlksPostStele I out
                                            outIlks).get? name = some value) :
                                      (barkLocalsDustyDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? name = some value := by
                                    exact
                                      barkLocalsDustyDart_get_preserved
                                        (evmUrns := evmPostStele)
                                        (evmIlks := evmIlksPostStele) (I := I)
                                        (out := out) (outIlks := outIlks)
                                        (name := name) (value := value) hname
                                        (barkLocalsLeftoverDue_get_preserved
                                          hleftoverDueName
                                          (barkLocalsLeftoverArt_get_preserved
                                            hleftoverArtName hget))
                                  have hpresDustyNone {name : Ident}
                                      (hname : ("dart" == name) = false)
                                      (hleftoverDueName : ("leftoverDue" == name) = false)
                                      (hleftoverArtName : ("leftoverArt" == name) = false)
                                      (hget :
                                        (barkLocalsDart evmPostStele evmIlksPostStele I out
                                            outIlks).get? name = none) :
                                      (barkLocalsDustyDart evmPostStele evmIlksPostStele I out
                                          outIlks).get? name = none := by
                                    rw [barkLocalsDustyDart, store_get_ne _ _ hname,
                                      barkLocalsLeftoverDue, store_get_ne _ _ hleftoverDueName,
                                      barkLocalsLeftoverArt, store_get_ne _ _ hleftoverArtName]
                                    exact hget
                                  have hpresPartial {name : Ident} {value : Value}
                                      (hname : ("partialDue" == name) = false)
                                      (hleftoverDueName : ("leftoverDue" == name) = false)
                                      (hleftoverArtName : ("leftoverArt" == name) = false)
                                      (hget :
                                        (barkLocalsDart evmPostStele evmIlksPostStele I out
                                            outIlks).get? name = some value) :
                                      (barkLocalsPartialDue evmPostStele evmIlksPostStele I out
                                          outIlks).get? name = some value := by
                                    exact
                                      barkLocalsPartialDue_get_preserved
                                        (evmUrns := evmPostStele)
                                        (evmIlks := evmIlksPostStele) (I := I)
                                        (out := out) (outIlks := outIlks)
                                        (name := name) (value := value) hname
                                        (barkLocalsLeftoverDue_get_preserved
                                          hleftoverDueName
                                          (barkLocalsLeftoverArt_get_preserved
                                            hleftoverArtName hget))
                                  have hpresPartialNone {name : Ident}
                                      (hname : ("partialDue" == name) = false)
                                      (hleftoverDueName : ("leftoverDue" == name) = false)
                                      (hleftoverArtName : ("leftoverArt" == name) = false)
                                      (hget :
                                        (barkLocalsDart evmPostStele evmIlksPostStele I out
                                            outIlks).get? name = none) :
                                      (barkLocalsPartialDue evmPostStele evmIlksPostStele I out
                                          outIlks).get? name = none := by
                                    rw [barkLocalsPartialDue, store_get_ne _ _ hname,
                                      barkLocalsLeftoverDue, store_get_ne _ _ hleftoverDueName,
                                      barkLocalsLeftoverArt, store_get_ne _ _ hleftoverArtName]
                                    exact hget
                                  by_cases hnoLeftover : art.toNat ≤ dart0.toNat
                                  · obtain ⟨_, _, rd3700⟩ :=
                                      RD.dogBarkNoLeftoverToDinkEntry
                                        (v := v) (code := code) (ret := ⟨448⟩)
                                        (sel := solcSelectorWord I) (R := [])
                                        (room := room) (spot := spot) (dust := dust)
                                        (rate := rate) (dart := dart0) (art := art)
                                        (ink := ink) hpatch hnoLeftover rd3594Local
                                        (by simp)
                                    have hleftoverBlock :=
                                      dogBarkNoLeftoverIteOk (v := v) evmPostStele
                                        evmIlksPostStele I out outIlks
                                        (by simpa [art, dart0, hdartSourceLocal] using
                                          hnoLeftover)
                                    have hinkAfter :
                                        (barkLocalsDart evmPostStele evmIlksPostStele I out
                                            outIlks).get? "ink" =
                                          some (.int (Int.ofNat ink.toNat)) := by
                                      simpa [ink] using
                                        barkLocalsDart_get_ink evmPostStele evmIlksPostStele I
                                          out outIlks
                                    have hdartAfter :
                                        (barkLocalsDart evmPostStele evmIlksPostStele I out
                                            outIlks).get? "dart" =
                                          some (.int (Int.ofNat dart0.toNat)) := by
                                      simpa [dart0, hdartSourceLocal] using
                                        barkLocalsDart_get_dart evmPostStele evmIlksPostStele I
                                          out outIlks
                                    have hartAfter :
                                        (barkLocalsDart evmPostStele evmIlksPostStele I out
                                            outIlks).get? "art" =
                                          some (.int (Int.ofNat art.toNat)) := by
                                      simpa [art] using
                                        barkLocalsDart_get_art evmPostStele evmIlksPostStele I
                                          out outIlks
                                    have hdartLeArt :
                                        dart0.toNat ≤ art.toNat := by
                                      simpa [dart0, art, rate, milkChop] using
                                        barkDartWord_toNat_le_art σ'' σ' I art rate milkChop
                                    exact finishFromDartEntry dart0
                                      (barkLocalsDart evmPostStele evmIlksPostStele I out outIlks)
                                      hleftoverBlock hinkAfter hdartAfter hartAfter
                                      hrateDartBase hmilkClipDartBase hmilkChopDartBase
                                      hmilkDirtDartBase hilkDartBase hurnDartBase
                                      hkprDartBase hvowDartBase hDirtDartBase hilksDartBase
                                      hdartLeArt rd3700
                                  · have hleftover : dart0.toNat < art.toNat := by
                                      omega
                                    have hfitLeftoverDue :
                                        (barkLeftoverArtWord art dart0).toNat * rate.toNat <
                                          UInt256.size :=
                                      barkLeftoverDue_fit_of_art_fit
                                        (by simpa using le_of_lt hleftover)
                                        (by simpa [art, rate] using hfitArt)
                                    by_cases hdusty :
                                        (barkLeftoverDueWord art dart0 rate).toNat <
                                          dust.toNat
                                    · obtain ⟨_, _, rd3700⟩ :=
                                        RD.dogBarkDustyLeftoverToDinkEntry
                                          (v := v) (code := code) (ret := ⟨448⟩)
                                          (sel := solcSelectorWord I) (R := [])
                                          (room := room) (spot := spot) (dust := dust)
                                          (rate := rate) (dart := dart0) (art := art)
                                          (ink := ink) hpatch hleftover hfitLeftoverDue
                                          hdusty rd3594Local (by simp)
                                      have hleftoverBlock :=
                                        dogBarkDustyLeftoverIteOk (v := v) evmPostStele
                                          evmIlksPostStele I out outIlks
                                          (by simpa [art, dart0, hdartSourceLocal] using
                                            hleftover)
                                          (by simpa [art, dart0, rate, hdartSourceLocal] using
                                            hfitLeftoverDue)
                                          (by simpa [art, dart0, rate, dust,
                                            hdartSourceLocal] using hdusty)
                                      have hinkAfter :
                                          (barkLocalsDustyDart evmPostStele evmIlksPostStele I
                                              out outIlks).get? "ink" =
                                            some (.int (Int.ofNat ink.toNat)) := by
                                        simpa [ink] using
                                          barkLocalsDustyDart_get_preserved
                                            (evmUrns := evmPostStele)
                                            (evmIlks := evmIlksPostStele) (I := I)
                                            (out := out) (outIlks := outIlks)
                                            (name := "ink")
                                            (value := .int (Int.ofNat ink.toNat))
                                            (by decide)
                                            (barkLocalsLeftoverDue_get_preserved
                                              (by decide)
                                              (barkLocalsLeftoverArt_get_preserved
                                                (by decide)
                                                (by
                                                  simpa [ink] using
                                                    (barkLocalsDart_get_ink evmPostStele
                                                      evmIlksPostStele I out outIlks))))
                                      have hdartAfter :
                                          (barkLocalsDustyDart evmPostStele evmIlksPostStele I
                                              out outIlks).get? "dart" =
                                            some (.int (Int.ofNat art.toNat)) := by
                                        simpa [art] using
                                          barkLocalsDustyDart_get_dart evmPostStele
                                            evmIlksPostStele I out outIlks
                                      have hartAfter :
                                          (barkLocalsDustyDart evmPostStele evmIlksPostStele I
                                              out outIlks).get? "art" =
                                            some (.int (Int.ofNat art.toNat)) := by
                                        simpa [art] using
                                          barkLocalsDustyDart_get_preserved
                                            (evmUrns := evmPostStele)
                                            (evmIlks := evmIlksPostStele) (I := I)
                                            (out := out) (outIlks := outIlks)
                                            (name := "art")
                                            (value := .int (Int.ofNat art.toNat))
                                            (by decide)
                                            (barkLocalsLeftoverDue_get_preserved
                                              (by decide)
                                              (barkLocalsLeftoverArt_get_preserved
                                                (by decide)
                                                (by
                                                  simpa [art] using
                                                    (barkLocalsDart_get_art evmPostStele
                                                      evmIlksPostStele I out outIlks))))
                                      exact finishFromDartEntry art
                                        (barkLocalsDustyDart evmPostStele evmIlksPostStele I
                                          out outIlks)
                                        hleftoverBlock hinkAfter hdartAfter hartAfter
                                        (hpresDusty (by decide) (by decide) (by decide)
                                          hrateDartBase)
                                        (hpresDusty (by decide) (by decide) (by decide)
                                          hmilkClipDartBase)
                                        (hpresDusty (by decide) (by decide) (by decide)
                                          hmilkChopDartBase)
                                        (hpresDusty (by decide) (by decide) (by decide)
                                          hmilkDirtDartBase)
                                        (hpresDusty (by decide) (by decide) (by decide)
                                          hilkDartBase)
                                        (hpresDusty (by decide) (by decide) (by decide)
                                          hurnDartBase)
                                        (hpresDusty (by decide) (by decide) (by decide)
                                          hkprDartBase)
                                        (hpresDustyNone (by decide) (by decide) (by decide)
                                          hvowDartBase)
                                        (hpresDustyNone (by decide) (by decide) (by decide)
                                          hDirtDartBase)
                                        (hpresDustyNone (by decide) (by decide) (by decide)
                                          hilksDartBase)
                                        (Nat.le_refl _) rd3700
                                    · have hnotDusty :
                                          dust.toNat ≤
                                            (barkLeftoverDueWord art dart0 rate).toNat :=
                                        Nat.le_of_not_gt hdusty
                                      have hfitPartialDue :
                                          dart0.toNat * rate.toNat < UInt256.size :=
                                        barkPartialDue_fit_of_dart_le_art
                                          (by simpa using le_of_lt hleftover)
                                          (by simpa [art, rate] using hfitArt)
                                      by_cases hpartialDueOk :
                                          dust.toNat ≤
                                            (barkPartialDueWord dart0 rate).toNat
                                      · obtain ⟨_, _, rd3700⟩ :=
                                          RD.dogBarkPartialLeftoverToDinkEntry
                                            (v := v) (code := code) (ret := ⟨448⟩)
                                            (sel := solcSelectorWord I) (R := [])
                                            (room := room) (spot := spot) (dust := dust)
                                            (rate := rate) (dart := dart0) (art := art)
                                            (ink := ink) hpatch hleftover hfitLeftoverDue
                                            hnotDusty hfitPartialDue hpartialDueOk
                                            rd3594Local (by simp)
                                        have hleftoverBlock :=
                                          dogBarkPartialLeftoverIteOk (v := v) evmPostStele
                                            evmIlksPostStele I out outIlks
                                            (by simpa [art, dart0, hdartSourceLocal] using
                                              hleftover)
                                            (by simpa [art, dart0, rate, hdartSourceLocal] using
                                              hfitLeftoverDue)
                                            (by simpa [art, dart0, rate, dust,
                                              hdartSourceLocal] using hnotDusty)
                                            (by simpa [dart0, rate, hdartSourceLocal] using
                                              hfitPartialDue)
                                            (by simpa [dart0, rate, dust, hdartSourceLocal] using
                                              hpartialDueOk)
                                        have hinkAfter :
                                            (barkLocalsPartialDue evmPostStele evmIlksPostStele I
                                                out outIlks).get? "ink" =
                                              some (.int (Int.ofNat ink.toNat)) := by
                                          simpa [ink] using
                                            barkLocalsPartialDue_get_preserved
                                              (evmUrns := evmPostStele)
                                              (evmIlks := evmIlksPostStele) (I := I)
                                              (out := out) (outIlks := outIlks)
                                              (name := "ink")
                                              (value := .int (Int.ofNat ink.toNat))
                                              (by decide)
                                              (barkLocalsLeftoverDue_get_preserved
                                                (by decide)
                                                (barkLocalsLeftoverArt_get_preserved
                                                  (by decide)
                                                  (by
                                                    simpa [ink] using
                                                      (barkLocalsDart_get_ink evmPostStele
                                                        evmIlksPostStele I out outIlks))))
                                        have hdartAfter :
                                            (barkLocalsPartialDue evmPostStele evmIlksPostStele I
                                                out outIlks).get? "dart" =
                                              some (.int (Int.ofNat dart0.toNat)) := by
                                          simpa [dart0, hdartSourceLocal] using
                                            barkLocalsPartialDue_get_preserved
                                              (evmUrns := evmPostStele)
                                              (evmIlks := evmIlksPostStele) (I := I)
                                              (out := out) (outIlks := outIlks)
                                              (name := "dart")
                                              (value := .int (Int.ofNat dart0.toNat))
                                              (by decide)
                                              (barkLocalsLeftoverDue_get_preserved
                                                (by decide)
                                                (barkLocalsLeftoverArt_get_preserved
                                                  (by decide)
                                                  (by
                                                    simpa [dart0, hdartSourceLocal] using
                                                      (barkLocalsDart_get_dart evmPostStele
                                                        evmIlksPostStele I out outIlks))))
                                        have hartAfter :
                                            (barkLocalsPartialDue evmPostStele evmIlksPostStele I
                                                out outIlks).get? "art" =
                                              some (.int (Int.ofNat art.toNat)) := by
                                          simpa [art] using
                                            barkLocalsPartialDue_get_preserved
                                              (evmUrns := evmPostStele)
                                              (evmIlks := evmIlksPostStele) (I := I)
                                              (out := out) (outIlks := outIlks)
                                              (name := "art")
                                              (value := .int (Int.ofNat art.toNat))
                                              (by decide)
                                              (barkLocalsLeftoverDue_get_preserved
                                                (by decide)
                                                (barkLocalsLeftoverArt_get_preserved
                                                  (by decide)
                                                  (by
                                                    simpa [art] using
                                                      (barkLocalsDart_get_art evmPostStele
                                                        evmIlksPostStele I out outIlks))))
                                        have hdartLeArt :
                                            dart0.toNat ≤ art.toNat := by
                                          simpa [dart0, art, rate, milkChop] using
                                            barkDartWord_toNat_le_art σ'' σ' I art rate
                                              milkChop
                                        exact finishFromDartEntry dart0
                                          (barkLocalsPartialDue evmPostStele evmIlksPostStele I
                                            out outIlks)
                                          hleftoverBlock hinkAfter hdartAfter hartAfter
                                          (hpresPartial (by decide) (by decide) (by decide)
                                            hrateDartBase)
                                          (hpresPartial (by decide) (by decide) (by decide)
                                            hmilkClipDartBase)
                                          (hpresPartial (by decide) (by decide) (by decide)
                                            hmilkChopDartBase)
                                          (hpresPartial (by decide) (by decide) (by decide)
                                            hmilkDirtDartBase)
                                          (hpresPartial (by decide) (by decide) (by decide)
                                            hilkDartBase)
                                          (hpresPartial (by decide) (by decide) (by decide)
                                            hurnDartBase)
                                          (hpresPartial (by decide) (by decide) (by decide)
                                            hkprDartBase)
                                          (hpresPartialNone (by decide) (by decide) (by decide)
                                            hvowDartBase)
                                          (hpresPartialNone (by decide) (by decide) (by decide)
                                            hDirtDartBase)
                                          (hpresPartialNone (by decide) (by decide) (by decide)
                                            hilksDartBase)
                                          hdartLeArt rd3700
                                      · have hpartialDueBad :
                                            (barkPartialDueWord dart0 rate).toNat < dust.toNat :=
                                          Nat.lt_of_not_ge hpartialDueOk
                                        have hleftoverBlock :=
                                          dogBarkPartialLeftoverIteRevert (v := v) evmPostStele
                                            evmIlksPostStele I out outIlks
                                            (by simpa [art, dart0, hdartSourceLocal] using
                                              hleftover)
                                            (by simpa [art, dart0, rate, hdartSourceLocal] using
                                              hfitLeftoverDue)
                                            (by simpa [art, dart0, rate, dust,
                                              hdartSourceLocal] using hnotDusty)
                                            (by simpa [dart0, rate, hdartSourceLocal] using
                                              hfitPartialDue)
                                            (by simpa [dart0, rate, dust, hdartSourceLocal] using
                                              hpartialDueBad)
                                        have htailBody :
                                            ExecTransitionBody config contract
                                              evmStele (barkLocals I)
                                              barkTransition.body .reverted (immStore v) := by
                                          let afterLeftover : List Stmt :=
                                            checkedMulUintInto "inkDart" (.var "ink")
                                              (.var "dart") ++
                                            [ .letDecl "dink" (some uint256)
                                                (.binary .div (.var "inkDart")
                                                  (.var "art")),
                                              .require (.binary .gt (.var "dink")
                                                (.intLit 0)),
                                              .require
                                                (.binary .and
                                                  (.binary .le (.var "dart")
                                                    (.intLit int256Limit))
                                                  (.binary .le (.var "dink")
                                                    (.intLit int256Limit))) ] ++
                                            checkedExternalCallStmts vatExpr "grab"
                                              (.intLit 0)
                                              [ .var "ilk", .var "urn", .var "milkClip",
                                                vowAddr,
                                                asInt256 (.unary .neg (asInt256 (.var "dink"))),
                                                asInt256 (.unary .neg (asInt256 (.var "dart"))) ]
                                              "_grabRet" ++
                                            checkedMulUintInto "due" (.var "dart")
                                              (.var "rate") ++
                                            checkedExternalCallStmts vowAddr "fess"
                                              (.intLit 0) [.var "due"] "_fessRet" ++
                                            checkedMulUintInto "tabBase" (.var "due")
                                              (.var "milkChop") ++
                                            [ .letDecl "tab" (some uint256)
                                                (.binary .div (.var "tabBase")
                                                  (.intLit WAD)) ] ++
                                            checkedAddUintInto "DirtNew" (.storage DirtRef)
                                              (.var "tab") ++
                                            [ .assign .storage DirtRef (.var "DirtNew") ] ++
                                            checkedAddUintInto "ilkDirtNew" (.var "milkDirt")
                                              (.var "tab") ++
                                            [ .assign .storage
                                                (ilksF (.var "ilk") "dirt")
                                                (.var "ilkDirtNew") ] ++
                                            checkedExternalCallStmts (.var "milkClip") "kick"
                                              (.intLit 0)
                                              [.var "tab", .var "dink", .var "urn", .var "kpr"]
                                              "id" ++
                                            [ .return [.var "id"] ]
                                          apply hbodyRevertOfTail
                                          simpa only [afterLeftover, List.append_assoc] using
                                            execBlock_append_term (s2 := afterLeftover)
                                              hleftoverBlock (by intro f e h; cases h)
                                        have hrev :=
                                          RD.dogBarkPartialLeftoverDustyReverts
                                            (v := v) (code := code) (ret := ⟨448⟩)
                                            (sel := solcSelectorWord I) (R := [])
                                            (room := room) (spot := spot) (dust := dust)
                                            (rate := rate) (dart := dart0) (art := art)
                                            (ink := ink) hpatch hleftover hfitLeftoverDue
                                            hnotDusty hfitPartialDue hpartialDueBad
                                            (by simpa [mem0] using hpostMemSize)
                                            (by simpa [mem0] using hpostMemRead64)
                                            rd3594Local (by simp)
                                        exact hrev.reEquivExecutionRevert hcode hdispatch
                                          hdecode htailBody
                                · have hslot5 :
                                      solcSlotWordAt ⟨5⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv =
                                        solcSlotWordAt ⟨5⟩ σ'' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt ⟨5⟩ m I) hAccountsIlks
                                    simpa [evmIlksPostStele, evmPostStele, evmStele, initState]
                                      using h.symm
                                  have hslot4 :
                                      solcSlotWordAt ⟨4⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv =
                                        solcSlotWordAt ⟨4⟩ σ'' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt ⟨4⟩ m I) hAccountsIlks
                                    simpa [evmIlksPostStele, evmPostStele, evmStele, initState]
                                      using h.symm
                                  have hAccountsUrns :
                                      Eq σ' evmPostStele.accountMap := by
                                    simpa [evmPostEvm] using hStateCall.accountMap
                                  have hmilkDirt :
                                      solcSlotWordAt (barkIlksDirtSlotFor I)
                                          evmPostStele.accountMap evmPostStele.executionEnv =
                                        barkIlksDirtWord σ' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt (barkIlksDirtSlotFor I) m I) hAccountsUrns
                                    rw [barkIlksDirtWord_eq_slotFor (σ := σ') (I := I)
                                      hsz100]
                                    simpa [evmPostStele, evmStele, initState] using h.symm
                                  have hmilkHole :
                                      solcSlotWordAt (barkIlksHoleSlotFor I)
                                          evmPostStele.accountMap evmPostStele.executionEnv =
                                        barkIlksHoleWord σ' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt (barkIlksHoleSlotFor I) m I) hAccountsUrns
                                    rw [barkIlksHoleWord_eq_slotFor (σ := σ') (I := I)
                                      hsz100]
                                    simpa [evmPostStele, evmStele, initState] using h.symm
                                  have hmilkChop :
                                      solcSlotWordAt (barkIlksChopSlotFor I)
                                          evmPostStele.accountMap evmPostStele.executionEnv =
                                        barkIlksChopWord σ' I := by
                                    have h :=
                                      congrArg (fun m => solcSlotWordAt (barkIlksChopSlotFor I) m I) hAccountsUrns
                                    rw [barkIlksChopWord_eq_slotFor (σ := σ') (I := I)
                                      hsz100]
                                    simpa [evmPostStele, evmStele, initState] using h.symm
                                  have hlimitSource :
                                      (solcSlotWordAt ⟨5⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv).toNat <
                                        (solcSlotWordAt ⟨4⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv).toNat ∧
                                      (solcSlotWordAt (barkIlksDirtSlotFor I)
                                          evmPostStele.accountMap
                                          evmPostStele.executionEnv).toNat <
                                        (solcSlotWordAt (barkIlksHoleSlotFor I)
                                          evmPostStele.accountMap
                                          evmPostStele.executionEnv).toNat := by
                                    exact
                                      ⟨by simpa [hslot5, hslot4] using hlimit.1,
                                        by simpa [hmilkDirt, hmilkHole] using hlimit.2⟩
                                  have hglobalRoom :
                                      barkSourceGlobalRoomWord evmIlksPostStele =
                                        barkGlobalRoomWord σ'' I := by
                                    simp [barkSourceGlobalRoomWord, barkGlobalRoomWord, hslot4,
                                      hslot5]
                                  have hilkRoom :
                                      barkSourceIlkRoomWord evmPostStele I =
                                        barkIlkRoomWord σ' I := by
                                    simp [barkSourceIlkRoomWord, barkIlkRoomWord, hmilkHole,
                                      hmilkDirt]
                                  have hroom :
                                      barkSourceRoomWord evmPostStele evmIlksPostStele I =
                                        barkRoomWord σ'' σ' I := by
                                    simp [barkSourceRoomWord, barkRoomWord, hglobalRoom, hilkRoom]
                                  have hfitRoomSource :
                                      (barkSourceRoomWord evmPostStele evmIlksPostStele I).toNat *
                                          dogWadWord.toNat <
                                        UInt256.size := by
                                    simpa [hroom] using hfitRoom
                                  have hchopZeroRuntime : barkIlksChopWord σ' I = ⟨0⟩ := by
                                    by_contra hne
                                    exact hchopNe hne
                                  have hchopZeroSource :
                                      solcSlotWordAt (barkIlksChopSlotFor I)
                                          evmPostStele.accountMap evmPostStele.executionEnv =
                                        ⟨0⟩ := by
                                    rw [hmilkChop, hchopZeroRuntime]
                                  have hbody :
                                      ExecTransitionBody config contract evmStele
                                        (barkLocals I) barkTransition.body .reverted (immStore v) := by
                                    simpa [evmStele] using
                                      (dogBarkVatIlksMilkChopZeroSourceBody (v := v)
                                        (σ := σ)
                                        (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                        (evmUrns := evmPostStele)
                                        (evmIlks := evmIlksPostStele) (out := out)
                                        (outIlks := outIlks) hwv hliveStele hvatCode
                                        hcallStele hdecUrns hvatIlksCode hcallIlksStele
                                        hdecIlks hfitInk hfitArt hspotPos hsafeLt
                                        hlimitSource hfitRoomSource hrateNe hchopZeroSource
                                        hsz100)
                                  have hinvalid :=
                                    RD.dogBarkDartCandidateDivZeroInvalid
                                      (v := v) (code := code) (ret := ⟨448⟩)
                                      (sel := solcSelectorWord I) (R := []) (σ := σ'')
                                      (σMem := σ') hpatch hfitRoom hrateNe
                                      hchopZeroRuntime hmload288 rd3543 (by simp)
                                  rcases hinvalid with hoog | hinvalid
                                  · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                                      rw [← hcode] at hoog
                                      simpa [initState, Sat256.ofUInt256] using hoog))
                                  · have hxi :
                                        Ξ σ σ₀ g A I =
                                          .error .InvalidInstruction :=
                                      Xi_error_of_X (g := g) (by
                                        rw [← hcode] at hinvalid
                                        simpa [initState, Sat256.ofUInt256] using hinvalid)
                                    exact reEquiv_execution hdispatch hdecode hbody
                                      (execResultsEquiv.invalidHalt hxi rfl)
                              · have hslot5 :
                                    solcSlotWordAt ⟨5⟩ evmIlksPostStele.accountMap
                                        evmIlksPostStele.executionEnv =
                                      solcSlotWordAt ⟨5⟩ σ'' I := by
                                  have h :=
                                    congrArg (fun m => solcSlotWordAt ⟨5⟩ m I) hAccountsIlks
                                  simpa [evmIlksPostStele, evmPostStele, evmStele, initState]
                                    using h.symm
                                have hslot4 :
                                    solcSlotWordAt ⟨4⟩ evmIlksPostStele.accountMap
                                        evmIlksPostStele.executionEnv =
                                      solcSlotWordAt ⟨4⟩ σ'' I := by
                                  have h :=
                                    congrArg (fun m => solcSlotWordAt ⟨4⟩ m I) hAccountsIlks
                                  simpa [evmIlksPostStele, evmPostStele, evmStele, initState]
                                    using h.symm
                                have hAccountsUrns :
                                    Eq σ' evmPostStele.accountMap := by
                                  simpa [evmPostEvm] using hStateCall.accountMap
                                have hmilkDirt :
                                    solcSlotWordAt (barkIlksDirtSlotFor I)
                                        evmPostStele.accountMap evmPostStele.executionEnv =
                                      barkIlksDirtWord σ' I := by
                                  have h :=
                                    congrArg (fun m => solcSlotWordAt (barkIlksDirtSlotFor I) m I) hAccountsUrns
                                  rw [barkIlksDirtWord_eq_slotFor (σ := σ') (I := I)
                                    hsz100]
                                  simpa [evmPostStele, evmStele, initState] using h.symm
                                have hmilkHole :
                                    solcSlotWordAt (barkIlksHoleSlotFor I)
                                        evmPostStele.accountMap evmPostStele.executionEnv =
                                      barkIlksHoleWord σ' I := by
                                  have h :=
                                    congrArg (fun m => solcSlotWordAt (barkIlksHoleSlotFor I) m I) hAccountsUrns
                                  rw [barkIlksHoleWord_eq_slotFor (σ := σ') (I := I)
                                    hsz100]
                                  simpa [evmPostStele, evmStele, initState] using h.symm
                                have hlimitSource :
                                    (solcSlotWordAt ⟨5⟩ evmIlksPostStele.accountMap
                                        evmIlksPostStele.executionEnv).toNat <
                                      (solcSlotWordAt ⟨4⟩ evmIlksPostStele.accountMap
                                        evmIlksPostStele.executionEnv).toNat ∧
                                    (solcSlotWordAt (barkIlksDirtSlotFor I)
                                        evmPostStele.accountMap
                                        evmPostStele.executionEnv).toNat <
                                      (solcSlotWordAt (barkIlksHoleSlotFor I)
                                        evmPostStele.accountMap
                                        evmPostStele.executionEnv).toNat := by
                                  exact
                                    ⟨by simpa [hslot5, hslot4] using hlimit.1,
                                      by simpa [hmilkDirt, hmilkHole] using hlimit.2⟩
                                have hglobalRoom :
                                    barkSourceGlobalRoomWord evmIlksPostStele =
                                      barkGlobalRoomWord σ'' I := by
                                  simp [barkSourceGlobalRoomWord, barkGlobalRoomWord, hslot4,
                                    hslot5]
                                have hilkRoom :
                                    barkSourceIlkRoomWord evmPostStele I =
                                      barkIlkRoomWord σ' I := by
                                  simp [barkSourceIlkRoomWord, barkIlkRoomWord, hmilkHole,
                                    hmilkDirt]
                                have hroom :
                                    barkSourceRoomWord evmPostStele evmIlksPostStele I =
                                      barkRoomWord σ'' σ' I := by
                                  simp [barkSourceRoomWord, barkRoomWord, hglobalRoom, hilkRoom]
                                have hoverRoomSource :
                                    UInt256.size ≤
                                      (barkSourceRoomWord evmPostStele evmIlksPostStele I).toNat *
                                        dogWadWord.toNat := by
                                  simpa [hroom] using (not_lt.mp hfitRoom)
                                have hbody :
                                    ExecTransitionBody config contract evmStele
                                      (barkLocals I) barkTransition.body .reverted (immStore v) := by
                                  simpa [evmStele] using
                                    (dogBarkVatIlksRoomWadOverflowSourceBody (v := v)
                                      (σ := σ)
                                      (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                      (evmUrns := evmPostStele) (evmIlks := evmIlksPostStele)
                                      (out := out) (outIlks := outIlks) hwv hliveStele
                                      hvatCode hcallStele hdecUrns hvatIlksCode hcallIlksStele
                                      hdecIlks hfitInk hfitArt hspotPos hsafeLt hlimitSource
                                      hoverRoomSource hsz100)
                                have hoverRoomEvm :
                                    UInt256.size ≤
                                      (barkRoomWord σ'' σ' I).toNat * dogWadWord.toNat :=
                                  not_lt.mp hfitRoom
                                have hrev := RD.dogBarkRoomWadOverflowReverts
                                  (v := v) (code := code) (ret := ⟨448⟩)
                                  (sel := solcSelectorWord I) (R := []) (σ := σ'')
                                  (σMem := σ') hpatch hoverRoomEvm hmload288 rd3543 (by simp)
                                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                            · have hspotPos :
                                  0 < (barkVatIlksSpotWord outIlks).toNat := by
                                have hnatNe :
                                    (barkVatIlksSpotWord outIlks).toNat ≠ 0 := by
                                  intro hnat
                                  exact hspotZero (uint256_toNat_eq_zero hnat)
                                exact Nat.pos_of_ne_zero hnatNe
                              have hslot5 :
                                  solcSlotWordAt ⟨5⟩ evmIlksPostStele.accountMap
                                      evmIlksPostStele.executionEnv =
                                    solcSlotWordAt ⟨5⟩ σ'' I := by
                                have h :=
                                  congrArg (fun m => solcSlotWordAt ⟨5⟩ m I) hAccountsIlks
                                simpa [evmIlksPostStele, evmPostStele, evmStele, initState]
                                  using h.symm
                              have hslot4 :
                                  solcSlotWordAt ⟨4⟩ evmIlksPostStele.accountMap
                                      evmIlksPostStele.executionEnv =
                                    solcSlotWordAt ⟨4⟩ σ'' I := by
                                have h :=
                                  congrArg (fun m => solcSlotWordAt ⟨4⟩ m I) hAccountsIlks
                                simpa [evmIlksPostStele, evmPostStele, evmStele, initState]
                                  using h.symm
                              have hAccountsUrns :
                                  Eq σ' evmPostStele.accountMap := by
                                simpa [evmPostEvm] using hStateCall.accountMap
                              have hmilkDirt :
                                  solcSlotWordAt (barkIlksDirtSlotFor I)
                                      evmPostStele.accountMap evmPostStele.executionEnv =
                                    barkIlksDirtWord σ' I := by
                                have h :=
                                  congrArg (fun m => solcSlotWordAt (barkIlksDirtSlotFor I) m I) hAccountsUrns
                                rw [barkIlksDirtWord_eq_slotFor (σ := σ') (I := I)
                                  hsz100]
                                simpa [evmPostStele, evmStele, initState] using h.symm
                              have hmilkHole :
                                  solcSlotWordAt (barkIlksHoleSlotFor I)
                                      evmPostStele.accountMap evmPostStele.executionEnv =
                                    barkIlksHoleWord σ' I := by
                                have h :=
                                  congrArg (fun m => solcSlotWordAt (barkIlksHoleSlotFor I) m I) hAccountsUrns
                                rw [barkIlksHoleWord_eq_slotFor (σ := σ') (I := I)
                                  hsz100]
                                simpa [evmPostStele, evmStele, initState] using h.symm
                              have hlimitSource :
                                  ¬ ((solcSlotWordAt ⟨5⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv).toNat <
                                        (solcSlotWordAt ⟨4⟩ evmIlksPostStele.accountMap
                                          evmIlksPostStele.executionEnv).toNat ∧
                                      (solcSlotWordAt (barkIlksDirtSlotFor I)
                                          evmPostStele.accountMap
                                          evmPostStele.executionEnv).toNat <
                                        (solcSlotWordAt (barkIlksHoleSlotFor I)
                                          evmPostStele.accountMap
                                          evmPostStele.executionEnv).toNat) := by
                                intro hsrc
                                exact hlimit
                                  ⟨by simpa [hslot5, hslot4] using hsrc.1,
                                    by simpa [hmilkDirt, hmilkHole] using hsrc.2⟩
                              have hbody :
                                  ExecTransitionBody config contract evmStele
                                    (barkLocals I) barkTransition.body .reverted (immStore v) := by
                                simpa [evmStele] using
                                  (dogBarkVatIlksLiquidationLimitHitSourceBody (v := v)
                                    (σ := σ)
                                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                    (evmUrns := evmPostStele) (evmIlks := evmIlksPostStele)
                                    (out := out) (outIlks := outIlks) hwv hliveStele
                                    hvatCode hcallStele hdecUrns hvatIlksCode hcallIlksStele
                                    hdecIlks hfitInk hfitArt hspotPos hsafeLt hlimitSource
                                    hsz100)
                              have hsafeEvm :
                                  ((barkVatUrnsInkWord out) *
                                      (barkVatIlksSpotWord outIlks)).toNat <
                                    ((barkVatUrnsArtWord out) *
                                      (barkVatIlksRateWord outIlks)).toNat := by
                                simpa [barkInkSpotWord, barkArtRateUnsafeWord] using
                                  hsafeLt
                              have hmload320 :=
                                barkVatIlksPostCallMem_mload320_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              have hmload352 :=
                                barkVatIlksPostCallMem_mload352_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              have hrev := RD.dogBarkLiquidationLimitHitReverts
                                (v := v) (code := code) (ret := ⟨448⟩)
                                (sel := solcSelectorWord I) (R := []) (σMem := σ')
                                hpatch hspotZero hfitArt hfitInk hsafeEvm hlimit
                                hmload320 hmload352 hpostMemSize hpostMemRead64 rd3308
                                (by simp)
                              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · have hnotSafe :
                                ¬ (0 < (barkVatIlksSpotWord outIlks).toNat ∧
                                  (barkInkSpotWord out outIlks).toNat <
                                    (barkArtRateUnsafeWord out outIlks).toNat) := by
                              intro hsafe
                              exact hsafeLt hsafe.2
                            have hbody :
                                ExecTransitionBody config contract evmStele
                                  (barkLocals I) barkTransition.body .reverted (immStore v) := by
                              simpa [evmStele] using
                                (dogBarkVatIlksNotUnsafeSourceBody (v := v)
                                  (σ := σ) (σ₀ := σ₀)
                                  (A := A) (I := I) (g := g) (evmUrns := evmPostStele)
                                  (evmIlks := evmIlksPostStele) (out := out)
                                  (outIlks := outIlks) hwv hliveStele hvatCode hcallStele
                                  hdecUrns hvatIlksCode hcallIlksStele hdecIlks hfitInk
                                  hfitArt hnotSafe hsz100)
                            have hnotLtEvm :
                                ((barkVatUrnsArtWord out) *
                                    (barkVatIlksRateWord outIlks)).toNat ≤
                                  ((barkVatUrnsInkWord out) *
                                    (barkVatIlksSpotWord outIlks)).toNat := by
                              change (barkArtRateUnsafeWord out outIlks).toNat ≤
                                (barkInkSpotWord out outIlks).toNat
                              omega
                            have hrev := RD.dogBarkNotUnsafeReverts
                              (v := v) (code := code) (ret := ⟨448⟩)
                              (sel := solcSelectorWord I) (R := []) hpatch hspotZero
                              hfitArt hfitInk hnotLtEvm hpostMemSize hpostMemRead64 rd3308
                              (by simp)
                            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hretIlksShort : outIlks.size < 160 :=
                      Nat.lt_of_not_ge hretIlksLong
                    have hrev := RD.dogBarkVatIlksReturnDecodeShortReverts hpatch rd3263
                      solcFreePtrMem_size hretLong hosz hretIlksShort hoszIlks
                      (by simp only [List.length_cons, List.length_nil]; omega)
                    have hdecIlks : config.externalABI.decode? "ilks" outIlks = none :=
                      barkVatIlksDecode_none_short hretIlksShort
                    have hbody :
                        ExecTransitionBody config contract evmStele (barkLocals I)
                          barkTransition.body .reverted (immStore v) := by
                      simpa [evmStele] using
                        (dogBarkVatIlksDecodeRevertSourceBody (v := v)
                          (σ := σ) (σ₀ := σ₀) (A := A)
                          (I := I) (g := g) (evmUrns := evmPostStele)
                          (evmIlks := evmIlksPostStele) (out := out)
                          (outIlks := outIlks) hwv hliveStele hvatCode hcallStele
                          hdecUrns hvatIlksCode hcallIlksStele hdecIlks hsz100)
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hretShort : out.size < 64 := Nat.lt_of_not_ge hretLong
              have hrev := RD.dogBarkVatUrnsReturnDecodeShortReverts hpatch rd3026
                solcFreePtrMem_size solcFreePtrMem_read64 hretShort hosz
                (by simp only [List.length_cons, List.length_nil]; omega)
              have hdec : config.externalABI.decode? "urns" out = none :=
                barkVatUrnsDecode_none_short hretShort
              have hbody :
                  ExecTransitionBody config contract evmStele (barkLocals I)
                    barkTransition.body .reverted (immStore v) := by
                simpa [evmStele] using
                  (dogBarkVatUrnsDecodeRevertSourceBody (v := v)
                    (σ := σ) (σ₀ := σ₀) (A := A)
                    (I := I) (g := g) (evmCall := evmPostStele) (out := out)
                    hwv hliveStele hvatCode hcallStele hdec)
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdepth1024 : I.depth = 1024 := by
            apply Fin.ext
            have hlt := I.depth.isLt
            rw [not_lt] at hdepthLt
            omega
          have hrev := RD.dogBarkVatUrnsStaticcallDepthLimitRevert
            (v := v) (code := code) (ret := ⟨448⟩) (sel := solcSelectorWord I)
            (R := []) hpatch h2885 solcFreePtrMem_size solcFreePtrMem_read64
            hvatCodeSizeNe hdepth1024 (by simp)
          let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let evmCall :=
            { evm0 with
              substate :=
                (evm0.addAccessedAccount
                  (EVM.address (AccountAddress.ofNat v.vat.toNat))).substate }
          have hcallDepth :
              typedCallViaEVM config evm0
                (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
                [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
                (false, evmCall, ByteArray.empty) false := by
            simpa [evm0, evmCall, initState] using
              (callNotMade_depthLimit (cfg := config) (evm := evm0)
                (tgt := EVM.address (AccountAddress.ofNat v.vat.toNat)) (name := "urns")
                (args := [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)])
                (callPerm := false)
                (barkVatUrnsEncode_eq (I := I) (mem := solcFreePtrMem)
                  hsz100 solcFreePtrMem_size)
                (by simpa [evm0, initState] using hdepth1024))
          have hbody :
              ExecTransitionBody config contract evm0 (barkLocals I)
                barkTransition.body .reverted (immStore v) := by
            simpa [evm0] using
              (dogBarkVatUrnsCallFailureSourceBody (v := v)
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) (evmCall := evmCall) (out := ByteArray.empty)
                hwv hliveStele hvatCode hcallDepth)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hslotWord :
          solcSlotWordAt ⟨3⟩ σ I = solcSlotWordAt ⟨3⟩ σ I :=
        rfl
      have hliveStele : solcSlotWordAt ⟨3⟩ σ I ≠ ⟨1⟩ := by
        intro hstele
        exact hliveEvm (by rw [hslotWord, hstele])
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody config contract evm0 (barkLocals I)
            barkTransition.body .reverted (immStore v) := by
        simpa [evm0, barkTransition, barkBodyRest] using
          dogNonpayableLivePrefixRevert (v := v)
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := barkLocals I)
            (rest := barkBodyRest.drop 1)
            (barkLocals_get_live I) hwv hliveStele
      have hrev := RD.dogBarkLiveRevert hpatch hbodyReach
        (by simpa [solcSlotWordAt] using hliveEvm)
        (by simp only [List.length_cons, List.length_nil]; omega)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact dogBarkBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach


end Benchmarks.Dss.Dog
