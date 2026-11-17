import Benchmarks.Dss.Dog.BarkChunk3

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogBarkDueCheckedMulOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {dink dust rate dart art ink kpr urn ilk ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hfitDue : dart.toNat * rate.toNat < UInt256.size)
    (rd4057 : RD code I g s0 ⟨4057⟩
      (barkVatGrabEndPtr :: barkVatGrabSelectorWord :: barkVatWord v ::
        dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem aw rdata acc k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4071⟩
      (barkPartialDueWord dart rate :: ⟨0⟩ :: dink :: dust :: rate :: dart ::
        ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd4069 := evm_run rd4057 with [
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
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4071⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd4069.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨k', C', rd4071⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := dart) (y := rate) (ret := ⟨4071⟩)
      (R := ⟨0⟩ :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitDue rd4564
  exact ⟨k', C', by simpa [barkPartialDueWord] using rd4071⟩

theorem RD.dogBarkDueCheckedMulOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {dink dust rate dart art ink kpr urn ilk ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hoverDue : UInt256.size ≤ dart.toNat * rate.toNat)
    (rd4057 : RD code I g s0 ⟨4057⟩
      (barkVatGrabEndPtr :: barkVatGrabSelectorWord :: barkVatWord v ::
        dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem aw rdata acc k C)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  have rd4069 := evm_run rd4057 with [
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
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4071⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd4069.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (x := dart) (y := rate) (ret := ⟨4071⟩)
    (R := ⟨0⟩ :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
      ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (by simp only [List.length_cons]; omega) hoverDue rd4564

theorem RD.dogBarkFessExtcodesizeGuard {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    {due dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd4071 : RD code I g s0 ⟨4071⟩
      (due :: ⟨0⟩ :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hov : R.length + 43 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4139⟩
      (barkVowWord σ I :: barkVowWord σ I :: ⟨0⟩ :: barkVowFessOutPtr ::
        barkVowFessInSize :: barkVowFessOutPtr :: barkVowFessOutSize ::
        barkVowFessEndPtr :: barkVowFessSelectorWord :: barkVowWord σ I ::
        due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      (barkVowFessDueMem mem due) (UInt256.ofNat 19) rdata σ k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
  have hmload64Call :=
    barkVowFessDueMem_mload64 (mem := mem) (due := due) hmem hread64
  have hvowCanon : (barkVowWord σ I).toNat < EVM.addressModulus := by
    simpa [barkVowWord, u256_land_comm] using
      solcAddrMask_result_canonical (solcSlotWordAt ⟨2⟩ σ I)
  have hvowMask :
      UInt256.land solcAddrMask (barkVowWord σ I) = barkVowWord σ I :=
    solcAddrMask_clean_left hvowCanon
  have haddrMaskWord :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hvowWordLit :
      UInt256.land ({ val := 1461501637330902918203684832716283019655932542975 } :
        UInt256) (solcSlotWordAt ⟨2⟩ σ I) = barkVowWord σ I := by
    simp [barkVowWord, solcAddrMask]
  have hvowWordRight :
      UInt256.land (solcSlotWordAt ⟨2⟩ σ I) solcAddrMask = barkVowWord σ I := by
    rw [u256_land_comm (solcSlotWordAt ⟨2⟩ σ I) solcAddrMask]
  have rd4074 := evm_run rd4071 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨2⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k4075, C4075, rd4075raw⟩ := rd4074.sload
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4075 : RD code I g s0 ⟨4075⟩
      (solcSlotWordAt ⟨2⟩ σ I :: due :: ⟨0⟩ :: dink :: dust :: rate ::
        dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k4075 C4075 := by
    simpa [solcSlotWordAt] using rd4075raw
  have rd4139 := evm_run rd4075 with [
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
      mem_cost hmload64 (by native_decide) (by simp only [List.length_cons]; omega),
    raw push4 ⟨0x0d2fdf6f⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨227⟩
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
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVowFessSelectorMem mem) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by rfl) (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨4⟩
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
    raw dup5
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
    raw mstore 0 (barkVowFessDueMem mem due) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 4 } : UInt256).toNat = 388
          from by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
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
      mem_cost hmload64Call (by native_decide) (by simp only [List.length_cons]; omega),
    raw swap3
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
    raw swap1
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
    raw push4 barkVowFessSelectorWord
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
    raw push1 barkVowFessInSize
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
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 barkVowFessOutSize
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
    raw swap1
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
    raw swap1
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
    raw add
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
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
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
      (by evm_ov)]
  exact ⟨_, _, by
    convert rd4139 using 1 <;>
      simp only [barkVowFessSelectorWord, barkVowFessInSize, barkVowFessOutPtr,
        barkVowFessOutSize, barkVowFessEndPtr, haddrMaskWord, hvowMask, hvowWordLit,
        hvowWordRight,
        show UInt256.sub (⟨384⟩ : UInt256) ⟨384⟩ + barkVowFessInSize =
          barkVowFessInSize from by native_decide,
        show (⟨384⟩ : UInt256) + barkVowFessInSize = barkVowFessEndPtr
          from by native_decide] <;>
      native_decide⟩

theorem RD.dogBarkFessNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4139 : RD code I g s0 ⟨4139⟩ (barkVowWord σ I :: barkVowWord σ I :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (barkVowWord σ I) = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4139⟩) (okPc := ⟨4151⟩)
    rd4139 hcodeSize
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
    hov

theorem RD.dogBarkFessToCall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4139 : RD code I g s0 ⟨4139⟩ (barkVowWord σ I :: barkVowWord σ I :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (barkVowWord σ I) ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ gasWord k' C', RD code I g s0 ⟨4154⟩ (gasWord :: barkVowWord σ I :: R)
      mem (UInt256.ofNat 19) rdata σ k' C' := by
  obtain ⟨gasWord, k', C', rd4154⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4139⟩) (okPc := ⟨4151⟩)
      rd4139 hcodeSize
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
      (dogPatchedJumpDest hpatch (by native_decide))
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
      hov
  exact ⟨gasWord, k', C', by simpa using rd4154⟩

theorem RD.dogBarkFessCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4155 : RD code I g s0 ⟨4155⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4155⟩) (okPc := ⟨4171⟩) rd4155
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
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
    hrdataSize hov

theorem RD.dogBarkFessCallSuccess {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {a b c : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4155 : RD code I g s0 ⟨4155⟩ (⟨1⟩ :: a :: b :: c :: R)
      mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4176⟩ R mem aw rdata acc k' C' := by
  obtain ⟨k4173, C4173, rd4173⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨4155⟩) (okPc := ⟨4171⟩) rd4155
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
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
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (dogPatchedJumpDest hpatch (by native_decide))
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega)
  have rd4176 := evm_run rd4173 with [
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
  exact ⟨_, _, rd4176⟩

theorem RD.dogBarkFessPostCall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 evm : EVM.State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {due dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4071 : RD code I g s0 ⟨4071⟩
      (due :: ⟨0⟩ :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (barkVowWord σ I) ≠ ⟨0⟩)
    (hevmEnv : evm.executionEnv = I)
    (hevmMap : evm.accountMap = σ)
    (hevmOrig : evm.σ₀ = s0.σ₀)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 43 ≤ 1024) :
    ∃ (σ' : AccountMap) (z : Bool)
      (outFess : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g s0 ⟨4155⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: barkVowFessEndPtr ::
          barkVowFessSelectorWord :: barkVowWord σ I :: due :: dink :: dust :: rate ::
          dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
        (barkVowFessPostCallMem mem outFess due)
        (UInt256.ofNat 19) outFess σ' k' C'
      ∧ typedCallViaEVM config evm
          (EVM.address (AccountAddress.ofNat (barkVowWord σ I).toNat)) "fess" 0
          [.int (Int.ofNat due.toNat)]
          (z, { evm with accountMap := σ', substate := A' },
            outFess) true
      ∧ outFess.size < UInt256.size := by
  obtain ⟨_, _, rd4139⟩ :=
    RD.dogBarkFessExtcodesizeGuard (v := v) (code := code) (g := g)
      (s0 := s0) (I := I) (ret := ret) (sel := sel) (R := R)
      (σ := σ) hpatch hmem hread64 rd4071 hov
  obtain ⟨_, _, _, rd4154⟩ :=
    RD.dogBarkFessToCall hpatch rd4139 hcodeSize
      (by simp only [List.length_cons]; omega)
  obtain ⟨σ', z, outFess, A_in, callGas, k', C', hΘpack, rd4155raw, houtsz⟩ :=
    RD.call rd4154
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨σ', z, outFess, A', k', C', ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 19).toNat
          barkVowFessOutPtr.toNat barkVowFessInSize.toNat)
          barkVowFessOutPtr.toNat barkVowFessOutSize.toNat) = UInt256.ofNat 19 := by
      unfold barkVowFessOutPtr barkVowFessInSize barkVowFessOutSize
      native_decide
    change RD code I g s0 ⟨4155⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: barkVowFessEndPtr ::
        barkVowFessSelectorWord :: barkVowWord σ I :: due :: dink :: dust :: rate ::
        dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (outFess.write 0 (barkVowFessDueMem mem due) barkVowFessOutPtr.toNat
        (min barkVowFessOutSize (UInt256.ofNat outFess.size)).toNat)
      (UInt256.ofNat 19) outFess σ' k' C'
    exact haw ▸ rd4155raw
  · have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
      intro hdepthEq
      exact absurd hdepth (by rw [← hevmEnv, hdepthEq]; decide)
    have htargetNorm :
        EVM.address ↑(AccountAddress.ofNat (barkVowWord σ I).toNat) =
          AccountAddress.ofUInt256 (barkVowWord σ I) := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN, AccountAddress.ofNat, AccountAddress.ofUInt256,
        UInt256.toNat]
      rw [show AccountAddress.size = EVM.twoPow 160 from by decide]
      rw [Nat.mod_mod]
    have hΘ' :
        (σ', g'', A', z, outFess) =
          Ethereum.EVM.Θ evm.executionEnv.fork evm.accountMap evm.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
            evm.executionEnv.sender (AccountAddress.ofUInt256 (barkVowWord σ I))
            (toExecute evm.executionEnv.fork evm.accountMap (AccountAddress.ofUInt256 (barkVowWord σ I)))
            callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkVowFessDueMem mem due).readWithPadding
              barkVowFessOutPtr.toNat barkVowFessInSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks
            evm.executionEnv.perm := by
      simpa [hevmEnv, hevmMap, hevmOrig] using hΘ
    exact Reasoning.Theory.callCoincides
      (cfg := config) (evm := evm) (name := "fess")
      (args := [.int (Int.ofNat due.toNat)])
      (tgt := EVM.address (AccountAddress.ofNat (barkVowWord σ I).toNat))
      (targetWord := barkVowWord σ I) (σ' := σ') (A' := A')
      (A_in := A_in) (z := z) (o := outFess) (g'' := g'') (callGas := callGas)
      (mem := barkVowFessDueMem mem due) (inOff := barkVowFessOutPtr)
      (inSize := barkVowFessInSize) (callPerm := true) hdepthNe htargetNorm
      (barkVowFessEncode_eq (mem := mem) (due := due) hmem)
      hΘ'

theorem RD.dogBarkTabBaseCheckedMulOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {due dink dust rate dart art ink kpr urn ilk ret sel milkChop : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hfit : due.toNat * milkChop.toNat < UInt256.size)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        milkChop)
    (rd4176 : RD code I g s0 ⟨4176⟩
      (due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata acc k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4200⟩
      (barkTabBaseWord due milkChop :: dogWadWord :: ⟨0⟩ :: due :: dink :: dust ::
        rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret ::
        sel :: R)
      mem (UInt256.ofNat 19) rdata acc k' C' := by
  have rd4178 := evm_run rd4176 with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4187 := rd4178.pushConst dogWadWord (width := 8) (op := .PUSH8)
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4199 := evm_run rd4187 with [
    raw push2 ⟨4200⟩
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
    raw dup10
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
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
    raw mload 0 milkChop (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        simpa [show ((⟨256⟩ : UInt256) + ⟨32⟩) = ⟨288⟩ from by native_decide]
          using hmload288)
      (by native_decide) (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd4199.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨k', C', rd4200⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := due) (y := milkChop) (ret := ⟨4200⟩)
      (R := dogWadWord :: ⟨0⟩ :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfit rd4564
  exact ⟨k', C', by simpa [barkTabBaseWord] using rd4200⟩

theorem RD.dogBarkTabBaseCheckedMulOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {due dink dust rate dart art ink kpr urn ilk ret sel milkChop : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hover : UInt256.size ≤ due.toNat * milkChop.toNat)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        milkChop)
    (rd4176 : RD code I g s0 ⟨4176⟩
      (due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata acc k C)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  have rd4178 := evm_run rd4176 with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4187 := rd4178.pushConst dogWadWord (width := 8) (op := .PUSH8)
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4199 := evm_run rd4187 with [
    raw push2 ⟨4200⟩
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
    raw dup10
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
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
    raw mload 0 milkChop (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        simpa [show ((⟨256⟩ : UInt256) + ⟨32⟩) = ⟨288⟩ from by native_decide]
          using hmload288)
      (by native_decide) (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd4199.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (x := due) (y := milkChop) (ret := ⟨4200⟩)
    (R := dogWadWord :: ⟨0⟩ :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ ::
      art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (by simp only [List.length_cons]; omega) hover rd4564

theorem RD.dogBarkTabDivOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {tabBase due dink dust rate dart art ink kpr urn ilk ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4200 : RD code I g s0 ⟨4200⟩
      (tabBase :: dogWadWord :: ⟨0⟩ :: due :: dink :: dust :: rate :: dart ::
        ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata acc k C)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4211⟩
      (barkTabWord tabBase :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata acc k' C' := by
  have rd4205 := evm_run rd4200 with [
    raw jumpdest
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
    raw push2 ⟨4207⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4207 := rd4205.jumpiT
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by native_decide : dogWadWord ≠ ⟨0⟩)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd4211 := evm_run rd4207 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
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
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [barkTabWord] using rd4211⟩

theorem RD.dogBarkDirtAddOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {tab due dink dust rate dart art ink kpr urn ilk ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hfit :
      (solcSlotWordAt ⟨5⟩ σ I).toNat + tab.toNat < UInt256.size)
    (rd4211 : RD code I g s0 ⟨4211⟩
      (tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hov : R.length + 31 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4222⟩
      (barkDirtNewWord (solcSlotWordAt ⟨5⟩ σ I) tab :: tab :: due :: dink ::
        dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn ::
        ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k' C' := by
  have rd4216pre := evm_run rd4211 with [
    raw push2 ⟨4222⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k4217, C4217, rd4217raw⟩ := rd4216pre.sload
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4217 : RD code I g s0 ⟨4217⟩
      (solcSlotWordAt ⟨5⟩ σ I :: ⟨4222⟩ :: tab :: due :: dink :: dust :: rate ::
        dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k4217 C4217 := by
    simpa [solcSlotWordAt, solcSlotWord] using rd4217raw
  have rd4221 := evm_run rd4217 with [
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4625⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4625 := rd4221.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨k', C', rd4222⟩ :=
    RD.dogCheckedAddReturns (v := v) hpatch
      (x := solcSlotWordAt ⟨5⟩ σ I) (y := tab) (ret := ⟨4222⟩)
      (R := tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega) hfit rd4625
      (dogPatchedJumpDest hpatch (by native_decide))
  exact ⟨k', C', by simpa [barkDirtNewWord] using rd4222⟩

theorem RD.dogBarkDirtAddOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {tab due dink dust rate dart art ink kpr urn ilk ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hover :
      UInt256.size ≤ (solcSlotWordAt ⟨5⟩ σ I).toNat + tab.toNat)
    (rd4211 : RD code I g s0 ⟨4211⟩
      (tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hov : R.length + 31 ≤ 1024) :
    RDrev code g s0 := by
  have rd4216pre := evm_run rd4211 with [
    raw push2 ⟨4222⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k4217, C4217, rd4217raw⟩ := rd4216pre.sload
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4217 : RD code I g s0 ⟨4217⟩
      (solcSlotWordAt ⟨5⟩ σ I :: ⟨4222⟩ :: tab :: due :: dink :: dust :: rate ::
        dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k4217 C4217 := by
    simpa [solcSlotWordAt, solcSlotWord] using rd4217raw
  have rd4221 := evm_run rd4217 with [
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4625⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4625 := rd4221.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedAddOverflowReverts (v := v) hpatch
    (x := solcSlotWordAt ⟨5⟩ σ I) (y := tab) (ret := ⟨4222⟩)
    (R := tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
      ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (by simp only [List.length_cons]; omega) hover rd4625

theorem RD.dogBarkStoreDirtSplit {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {tab due dink dust rate dart art ink kpr urn ilk ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4222 : RD code I g s0 ⟨4222⟩
      (barkDirtNewWord (solcSlotWordAt ⟨5⟩ σ I) tab :: tab :: due :: dink ::
        dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn ::
        ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hov : R.length + 17 ≤ 1024) :
    (I.perm = true ∧
      ∃ k' C', RD code I g s0 ⟨4226⟩
        (tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
          ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
        mem (UInt256.ofNat 19) rdata
        (sstoreAccountMap I.codeOwner σ ⟨5⟩
          (barkDirtNewWord (solcSlotWordAt ⟨5⟩ σ I) tab)) k' C') ∨
      (I.perm = false ∧ RDstatic code g s0) := by
  have rd4225 := evm_run rd4222 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hstoreDec : decode code ⟨4225⟩ = some (.SSTORE, none) := by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd4225.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨k', C', rd4226⟩ := rd4225.sstore hperm
    hstoreDec
    (by simp only [List.length_cons]; omega)
  exact ⟨k', C', rd4226⟩

theorem RD.dogBarkIlkDirtAddOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {σStore : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {tab due dink dust rate dart art ink kpr urn ilk ret sel milkDirt : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        milkDirt)
    (hfit : milkDirt.toNat + tab.toNat < UInt256.size)
    (rd4226 : RD code I g s0 ⟨4226⟩
      (tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σStore k C)
    (hov : R.length + 31 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4240⟩
      (barkIlkDirtNewWord milkDirt tab :: tab :: due :: dink :: dust :: rate ::
        dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret ::
        sel :: R)
      mem (UInt256.ofNat 19) rdata σStore k' C' := by
  have rd4229pre := evm_run rd4226 with [
    raw push1 ⟨96⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4230raw := RD.add rd4229pre
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd352 : (⟨256⟩ : UInt256) + ⟨96⟩ = ⟨352⟩ := by
    native_decide
  have rd4230 := by
    simpa [hadd352] using rd4230raw
  have rd4231 := evm_run rd4230 with [
    raw mload 0 milkDirt (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload352 (by decide) (by evm_ov)]
  have rd4239 := evm_run rd4231 with [
    raw push2 ⟨4240⟩
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
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4625⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4625 := rd4239.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨k', C', rd4240⟩ :=
    RD.dogCheckedAddReturns (v := v) hpatch
      (x := milkDirt) (y := tab) (ret := ⟨4240⟩)
      (R := tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega) hfit rd4625
      (dogPatchedJumpDest hpatch (by native_decide))
  exact ⟨k', C', by simpa [barkIlkDirtNewWord] using rd4240⟩

theorem RD.dogBarkIlkDirtAddOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {σStore : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {tab due dink dust rate dart art ink kpr urn ilk ret sel milkDirt : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        milkDirt)
    (hover : UInt256.size ≤ milkDirt.toNat + tab.toNat)
    (rd4226 : RD code I g s0 ⟨4226⟩
      (tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σStore k C)
    (hov : R.length + 31 ≤ 1024) :
    RDrev code g s0 := by
  have rd4229pre := evm_run rd4226 with [
    raw push1 ⟨96⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4230raw := RD.add rd4229pre
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd352 : (⟨256⟩ : UInt256) + ⟨96⟩ = ⟨352⟩ := by
    native_decide
  have rd4230 := by
    simpa [hadd352] using rd4230raw
  have rd4231 := evm_run rd4230 with [
    raw mload 0 milkDirt (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload352 (by decide) (by evm_ov)]
  have rd4239 := evm_run rd4231 with [
    raw push2 ⟨4240⟩
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
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4625⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4625 := rd4239.jump
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedAddOverflowReverts (v := v) hpatch
    (x := milkDirt) (y := tab) (ret := ⟨4240⟩)
    (R := tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
      ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (by simp only [List.length_cons]; omega) hover rd4625

theorem RD.dogBarkStoreIlkDirt {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {σStore : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {ilkDirtNew tab due dink dust rate dart art ink kpr urn ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hsz100 : 100 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hmem : mem.size = 580)
    (rd4240 : RD code I g s0 ⟨4240⟩
      (ilkDirtNew :: tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: barkIlkWord I :: ret ::
        sel :: R)
      mem (UInt256.ofNat 19) rdata σStore k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4267⟩
      (tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: barkIlkWord I :: ret :: sel :: R)
      (twoWordHashMem (barkIlkWord I) ⟨1⟩ mem) (UInt256.ofNat 19) rdata
      (sstoreAccountMap I.codeOwner σStore (barkIlksDirtSlotFor I)
        ilkDirtNew) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((twoWordHashMem (barkIlkWord I) ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (barkIlkWord I) :=
    twoWordHashMem_solcMappingSlot_580 ⟨1⟩ (barkIlkWord I) hmem
  have hslotDirt :
      solcMappingSlot ⟨1⟩ (barkIlkWord I) + ⟨3⟩ =
        barkIlksDirtSlotFor I := by
    rw [barkIlksDirtSlotFor_eq hsz100]
  have rd4247pre := evm_run rd4240 with [
    raw jumpdest
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
    raw push1 ⟨0⟩
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
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4248 := rd4247pre.mstore 0 (wordAt0Mem (barkIlkWord I) mem)
    (UInt256.ofNat 19)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd4253pre := evm_run rd4248 with [
    raw push1 ⟨32⟩
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
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4254 := rd4253pre.mstore 0 (twoWordHashMem (barkIlkWord I) ⟨1⟩ mem)
    (UInt256.ofNat 19)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd4259pre := evm_run rd4254 with [
    raw push1 ⟨32⟩
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
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4260 := rd4259pre.keccak256 0 (solcMappingSlot ⟨1⟩ (barkIlkWord I))
    (UInt256.ofNat 19)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost hslot (by native_decide) (by evm_ov)
  have rd4265preRaw := evm_run rd4260 with [
    raw push1 ⟨3⟩
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
      (by evm_ov)]
  have hpc4265 :
      ((⟨4240⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨4265⟩ : UInt256) := by
    native_decide
  rw [hpc4265] at rd4265preRaw
  have hslotDirtLeft :
      (⟨3⟩ : UInt256) + solcMappingSlot ⟨1⟩ (barkIlkWord I) =
        barkIlksDirtSlotFor I := by
    rw [u256_add_comm, hslotDirt]
  rw [hslotDirtLeft] at rd4265preRaw
  obtain ⟨k4266, C4266, rd4266⟩ := rd4265preRaw.sstore hperm
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4267raw := evm_run rd4266 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hpc4267 : (⟨4265⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = (⟨4267⟩ : UInt256) := by
    native_decide
  rw [hpc4267] at rd4267raw
  exact ⟨_, _, rd4267raw⟩

theorem RD.dogBarkKickExtcodesizeGuard {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {σ σMem : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {R : List UInt256}
    {tab due dink dust rate dart art ink ret sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hmload256 :
      (if (⟨256⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
        barkIlksClipWord σMem I)
    (rd4267 : RD code I g s0 ⟨4267⟩
      (tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hov : R.length + 49 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4370⟩
      (barkIlksClipWord σMem I :: barkIlksClipWord σMem I :: ⟨0⟩ ::
        barkKickOutPtr :: barkKickInSize :: barkKickOutPtr :: barkKickOutSize ::
        barkKickEndPtr :: barkKickSelectorWord :: barkIlksClipWord σMem I ::
        tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkKickCalldataMem I mem tab dink) (UInt256.ofNat 19) rdata σ k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
  have hmload64Call :=
    barkKickCalldataMem_mload64 (I := I) (mem := mem) (tab := tab) (dink := dink)
      hmem hread64
  have haddrMaskWord :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hclipCanon : (barkIlksClipWord σMem I).toNat < EVM.addressModulus := by
    simpa [barkIlksClipWord, u256_land_comm] using
      solcAddrMask_result_canonical (solcSlotWord σMem I (barkIlksSlot I))
  have hclipCleanL :
      UInt256.land solcAddrMask (barkIlksClipWord σMem I) = barkIlksClipWord σMem I :=
    solcAddrMask_clean_left hclipCanon
  have hurnCanon : (barkUrnKey I).toNat < EVM.addressModulus := by
    simpa [barkUrnKey, u256_land_comm] using
      solcAddrMask_result_canonical (barkUrnWord I)
  have hurnCleanL :
      UInt256.land solcAddrMask (barkUrnKey I) = barkUrnKey I :=
    solcAddrMask_clean_left hurnCanon
  have hkprCanon : (barkKprKey I).toNat < EVM.addressModulus := by
    simpa [barkKprKey, u256_land_comm] using
      solcAddrMask_result_canonical (barkKprWord I)
  have hkprCleanL :
      UInt256.land solcAddrMask (barkKprKey I) = barkKprKey I :=
    solcAddrMask_clean_left hkprCanon
  have rd4370 := evm_run rd4267 with [
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
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
    raw mload 0 (barkIlksClipWord σMem I) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by simpa using hmload256) (by native_decide)
      (by simp only [List.length_cons]; omega),
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
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push4 barkKickSelectorWord
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
    raw dup6
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
    raw dup16
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
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
      mem_cost hmload64 (by native_decide) (by simp only [List.length_cons]; omega),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push4 ⟨4294967295⟩
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
    raw push1 ⟨224⟩
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
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkKickSelectorMem mem) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by rfl) (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨4⟩
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
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
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
    raw mstore 0 (barkKickTabMem mem tab) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ((⟨4⟩ : UInt256) + ⟨384⟩).toNat = 388 by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨32⟩
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
    raw dup5
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
    raw mstore 0 (barkKickDinkMem mem tab dink) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + ⟨384⟩)).toNat = 420
          by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨32⟩
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
    raw dup4
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
    raw and
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
    raw mstore 0 (barkKickUrnMem I mem tab dink) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) +
          ((⟨4⟩ : UInt256) + ⟨384⟩))).toNat = 452 by native_decide]
        simp [barkKickUrnMem, Reasoning.Theory.writeWord, haddrMaskWord,
          hurnCleanL])
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨32⟩
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
    raw dup3
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
    raw and
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
    raw mstore 0 (barkKickCalldataMem I mem tab dink) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) +
          ((⟨4⟩ : UInt256) + ⟨384⟩)))).toNat = 484 by native_decide]
        simp [barkKickCalldataMem, barkKickUrnMem, Reasoning.Theory.writeWord,
          haddrMaskWord, hkprCleanL])
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨32⟩
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
    raw swap5
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
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
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
      mem_cost hmload64Call (by native_decide) (by simp only [List.length_cons]; omega),
    raw dup1
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
    raw sub
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
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
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
      (by evm_ov)]
  exact ⟨_, _, by
    convert rd4370 using 1 <;>
      simp only [barkKickSelectorWord, barkKickOutPtr, barkKickInSize,
        barkKickOutSize, barkKickEndPtr, haddrMaskWord, hclipCleanL,
        hurnCleanL, hkprCleanL,
        show UInt256.sub (⟨384⟩ : UInt256) ⟨384⟩ + barkKickInSize =
          barkKickInSize from by native_decide,
        show (⟨384⟩ : UInt256) + barkKickInSize = barkKickEndPtr
          from by native_decide,
        show UInt256.sub
            ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) +
              ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + ⟨384⟩)))))
            ⟨384⟩ = barkKickInSize from by native_decide,
        show UInt256.sub (⟨516⟩ : UInt256) ⟨384⟩ = barkKickInSize
          from by native_decide,
        show ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) +
              ((⟨32⟩ : UInt256) + ((⟨4⟩ : UInt256) + ⟨384⟩))))) =
            barkKickEndPtr
          from by native_decide] <;>
      native_decide⟩

theorem RD.dogBarkKickNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ σMem : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4370 : RD code I g s0 ⟨4370⟩
      (barkIlksClipWord σMem I :: barkIlksClipWord σMem I :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkIlksClipWord σMem I) = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4370⟩) (okPc := ⟨4382⟩)
    rd4370 hcodeSize
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
    hov

theorem RD.dogBarkKickToCall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ σMem : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4370 : RD code I g s0 ⟨4370⟩
      (barkIlksClipWord σMem I :: barkIlksClipWord σMem I :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkIlksClipWord σMem I) ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ gasWord k' C', RD code I g s0 ⟨4385⟩
      (gasWord :: barkIlksClipWord σMem I :: R)
      mem (UInt256.ofNat 19) rdata σ k' C' := by
  obtain ⟨gasWord, k', C', rd4385⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4370⟩) (okPc := ⟨4382⟩)
      rd4370 hcodeSize
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
      (dogPatchedJumpDest hpatch (by native_decide))
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
      hov
  exact ⟨gasWord, k', C', by simpa using rd4385⟩

theorem RD.dogBarkKickPostCall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 evm : EVM.State} {I : ExecutionEnv}
    {σ σMem : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {tab due dink dust rate dart art ink : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4267 : RD code I g s0 ⟨4267⟩
      (tab :: due :: dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 19) rdata σ k C)
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hmload256 :
      (if (⟨256⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
        barkIlksClipWord σMem I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkIlksClipWord σMem I) ≠ ⟨0⟩)
    (hevmEnv : evm.executionEnv = I)
    (hevmMap : evm.accountMap = σ)
    (hevmOrig : evm.σ₀ = s0.σ₀)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 49 ≤ 1024) :
    ∃ (σ' : AccountMap) (z : Bool)
      (outKick : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g s0 ⟨4386⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: barkKickEndPtr ::
          barkKickSelectorWord :: barkIlksClipWord σMem I :: tab :: due ::
          dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
          barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
        (barkKickPostCallMem I mem outKick tab dink)
        (UInt256.ofNat 19) outKick σ' k' C'
      ∧ typedCallViaEVM config evm
          (EVM.address (AccountAddress.ofNat (barkIlksClipWord σMem I).toNat))
          "kick" 0
          [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat),
            .address (barkUrn I), .address (barkKpr I)]
          (z, { evm with accountMap := σ', substate := A' },
            outKick) true
      ∧ outKick.size < UInt256.size := by
  obtain ⟨_, _, rd4370⟩ :=
    RD.dogBarkKickExtcodesizeGuard (v := v) (code := code) (g := g)
      (s0 := s0) (I := I) (ret := ret) (sel := sel) (R := R)
      (σ := σ) (σMem := σMem) hpatch hmem hread64 hmload256
      rd4267 hov
  obtain ⟨_, _, _, rd4385⟩ :=
    RD.dogBarkKickToCall hpatch rd4370 hcodeSize
      (by simp only [List.length_cons]; omega)
  obtain ⟨σ', z, outKick, A_in, callGas, k', C', hΘpack, rd4386raw,
    houtsz⟩ :=
    RD.call rd4385
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨σ', z, outKick, A', k', C', ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 19).toNat
          barkKickOutPtr.toNat barkKickInSize.toNat)
          barkKickOutPtr.toNat barkKickOutSize.toNat) = UInt256.ofNat 19 := by
      unfold barkKickOutPtr barkKickInSize barkKickOutSize
      native_decide
    change RD code I g s0 ⟨4386⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: barkKickEndPtr ::
        barkKickSelectorWord :: barkIlksClipWord σMem I :: tab :: due ::
        dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (outKick.write 0 (barkKickCalldataMem I mem tab dink) barkKickOutPtr.toNat
        (min barkKickOutSize (UInt256.ofNat outKick.size)).toNat)
      (UInt256.ofNat 19) outKick σ' k' C'
    exact haw ▸ rd4386raw
  · have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
      intro hdepthEq
      exact absurd hdepth (by rw [← hevmEnv, hdepthEq]; decide)
    have htargetNorm :
        EVM.address (AccountAddress.ofNat (barkIlksClipWord σMem I).toNat) =
          AccountAddress.ofUInt256 (barkIlksClipWord σMem I) := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN, AccountAddress.ofNat, AccountAddress.ofUInt256,
        UInt256.toNat]
      rw [show AccountAddress.size = EVM.twoPow 160 from by decide]
      rw [Nat.mod_mod]
    have hΘ' :
        (σ', g'', A', z, outKick) =
          Ethereum.EVM.Θ evm.executionEnv.fork evm.accountMap evm.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
            evm.executionEnv.sender (AccountAddress.ofUInt256 (barkIlksClipWord σMem I))
            (toExecute evm.executionEnv.fork evm.accountMap (AccountAddress.ofUInt256 (barkIlksClipWord σMem I)))
            callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkKickCalldataMem I mem tab dink).readWithPadding
              barkKickOutPtr.toNat barkKickInSize.toNat)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks
            evm.executionEnv.perm := by
      simpa [hevmEnv, hevmMap, hevmOrig] using hΘ
    exact Reasoning.Theory.callCoincides
      (cfg := config) (evm := evm) (name := "kick")
      (args := [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat),
        .address (barkUrn I), .address (barkKpr I)])
      (tgt := EVM.address (AccountAddress.ofNat (barkIlksClipWord σMem I).toNat))
      (targetWord := barkIlksClipWord σMem I) (σ' := σ') (A' := A')
      (A_in := A_in) (z := z) (o := outKick) (g'' := g'') (callGas := callGas)
      (mem := barkKickCalldataMem I mem tab dink) (inOff := barkKickOutPtr)
      (inSize := barkKickInSize) (callPerm := true) hdepthNe htargetNorm
      (barkKickEncode_eq (I := I) (mem := mem) (tab := tab)
        (dink := dink) hmem)
      hΘ'

theorem RD.dogBarkKickCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4386 : RD code I g s0 ⟨4386⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4386⟩) (okPc := ⟨4402⟩) rd4386
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
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
    hrdataSize hov

theorem RD.dogBarkKickCallSuccessToDecode {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4386 : RD code I g s0 ⟨4386⟩ (⟨1⟩ :: d0 :: d1 :: d2 :: R)
      mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4404⟩ (d0 :: d1 :: d2 :: R)
      mem aw rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨4386⟩) (okPc := ⟨4402⟩) rd4386
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
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
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simpa only [List.length_cons] using hov)


end Benchmarks.Dss.Dog
