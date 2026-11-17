import Benchmarks.Dss.Dog.BarkPatchTemplate

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem dogBarkVatPatchWord3965 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.extract 3965 3997 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
  let pre : List (Nat × ByteArray) := [(1405, value), (2890, value), (3170, value)]
  let post : List (Nat × ByteArray) := []
  have hpatch' : patchRuntime dogBytecode (pre ++ (3965, value) :: post) = some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, Reasoning.Theory.wordBytes?, valueToWord,
      List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 3965 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 3965 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch (template := dogBytecode) (out := code)
    (value := value) (pre := pre) (post := post) (offset := 3965) hsize hpost hpatch'

theorem dogBarkVatConstDecode3964 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨3964⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32)) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? ({ val := 3964 } : UInt256).toNat =
      dogBytecode.get? ({ val := 3964 } : UInt256).toNat := by
    change code.get? 3964 = dogBytecode.get? 3964
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 3964) (stop := 3965)
        (template := dogBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (by
          intro p hp
          have hm := dogPatchOffsetMem v p hp
          simp [dogPatchOffsets] at hm
          rcases hm with h | h | h | h
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega)
        hpatch
  have hgetSome : code.get? ({ val := 3964 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.readWithPadding 3965 32), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32))
  rw [Reasoning.Theory.readWithPadding_eq_extract code 3965 (by rw [hsize]; native_decide),
    dogBarkVatPatchWord3965 hpatch,
    uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem RD.dogBarkVatUrnsToCallMload {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨2941⟩
      (⟨128⟩ :: barkUrnKey I :: barkIlkWord I :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
  have hvatCleanR :
      UInt256.land (barkVatWord v) solcAddrMask = barkVatWord v :=
    solcAddrMask_clean (barkVatWord_canonical v)
  have hvatCleanL :
      UInt256.land solcAddrMask (barkVatWord v) = barkVatWord v :=
    solcAddrMask_clean_left (barkVatWord_canonical v)
  have rd2886 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2889 := evm_run rd2886 with [
    raw push1 ⟨0⟩
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
  have rd2922 := rd2889.pushConst (barkVatWord v) (width := 32) (op := .PUSH32)
    (hop := by decide)
    (by simpa [barkVatWord] using dogBarkVatConstDecode2889 hpatch)
    (by evm_ov)
  have rd2940raw := evm_run rd2922 with [
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push4 ⟨606387804⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd2941raw := rd2940raw.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (mloadFreePtrValue (by rw [hmem]; decide) hread64)
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hvatCleanR, hvatCleanL] using rd2941raw⟩

theorem RD.dogBarkVatUrnsToExtcodesize {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2941⟩
      (⟨128⟩ :: barkUrnKey I :: barkIlkWord I :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨2992⟩
      (barkVatWord v :: barkVatWord v :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ ::
        ⟨64⟩ :: ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
        ret :: sel :: R)
      (barkVatUrnsCallMem I mem) (UInt256.ofNat 7) rdata acc k' C' := by
  have hurnCanon : (barkUrnKey I).toNat < EVM.addressModulus := by
    rw [barkUrnKey, u256_land_comm]
    exact solcAddrMask_result_canonical (barkUrnWord I)
  have hurnCleanR :
      UInt256.land (barkUrnKey I) solcAddrMask = barkUrnKey I :=
    solcAddrMask_clean hurnCanon
  have hurnCleanL :
      UInt256.land solcAddrMask (barkUrnKey I) = barkUrnKey I :=
    solcAddrMask_clean_left hurnCanon
  have rd2951prefix := evm_run h with [
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push4 ⟨4294967295⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨224⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd2953 := rd2951prefix.mstore 6 (barkVatUrnsSelectorMem mem) (UInt256.ofNat 5)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      have hsel :
          UInt256.shiftLeft (UInt256.land (⟨4294967295⟩ : UInt256) ⟨606387804⟩) ⟨224⟩ =
            barkVatUrnsSelectorWord := by
        native_decide
      dsimp [barkVatUrnsSelectorMem, Reasoning.Theory.writeWord]
      rw [hsel]
      rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide])
    (by native_decide) (by evm_ov)
  have rd2958prefix := evm_run rd2953 with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd2960 := rd2958prefix.mstore 3 (barkVatUrnsIlkMem I mem) (UInt256.ofNat 6)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      have h132 : UInt256.add (⟨4⟩ : UInt256) ⟨128⟩ = ⟨132⟩ := by
        native_decide
      dsimp [barkVatUrnsIlkMem, Reasoning.Theory.writeWord]
      rw [show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 by native_decide])
    (by native_decide) (by evm_ov)
  have rd2973raw := evm_run rd2960 with [
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
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd2974⟩ : ∃ k' C', RD code I g s0 ⟨2974⟩
      (⟨164⟩ :: barkUrnKey I :: ⟨164⟩ :: ⟨132⟩ :: barkUrnKey I ::
        barkIlkWord I :: ⟨606387804⟩ :: barkVatWord v :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsIlkMem I mem) (UInt256.ofNat 6) rdata acc k' C' := by
    exact ⟨_, _, by
      simpa [show UInt256.add (⟨32⟩ : UInt256) ⟨132⟩ = ⟨164⟩ by native_decide,
        show UInt256.add (⟨4⟩ : UInt256) ⟨128⟩ = ⟨132⟩ by native_decide,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, hurnCleanR, hurnCleanL] using rd2973raw⟩
  have rd2975 := rd2974.mstore 3 (barkVatUrnsCallMem I mem) (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsCallMem, Reasoning.Theory.writeWord]
      rw [show (⟨164⟩ : UInt256).toNat = 164 by native_decide])
    (by native_decide) (by evm_ov)
  have rd2985prefix := evm_run rd2975 with [
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
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
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
      (by evm_ov)]
  have rd2986 := rd2985prefix.mload 0 ⟨128⟩ (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (mloadFreePtrValue
      (by rw [barkVatUrnsCallMem_size hmem]; decide)
      (barkVatUrnsCallMem_read64 hmem hread64))
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [
      show UInt256.add (⟨32⟩ : UInt256) ⟨164⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨196⟩ : UInt256) ⟨128⟩ = ⟨68⟩ from by native_decide] using
      evm_run rd2986 with [
        raw dup1
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw dup4
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw sub
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw dup2
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw dup7
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw dup1
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov)]⟩

theorem RD.dogBarkVatUrnsNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata σ k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) = ⟨0⟩)
    (hov : R.length + 24 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd2941⟩ :=
    RD.dogBarkVatUrnsToCallMload hpatch h hmem hread64 (by omega)
  obtain ⟨_, _, rd2992⟩ :=
    RD.dogBarkVatUrnsToExtcodesize hpatch rd2941 hmem hread64 hov
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2992⟩) (okPc := ⟨3004⟩)
    rd2992 hcodeSize
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatUrnsToStaticcall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata σ k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hov : R.length + 24 ≤ 1024) :
    ∃ gasWord k' C', RD code I g s0 ⟨3007⟩
      (gasWord :: barkVatWord v :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨64⟩ ::
        ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsCallMem I mem) (UInt256.ofNat 7) rdata σ k' C' := by
  obtain ⟨_, _, rd2941⟩ :=
    RD.dogBarkVatUrnsToCallMload hpatch h hmem hread64 (by omega)
  obtain ⟨_, _, rd2992⟩ :=
    RD.dogBarkVatUrnsToExtcodesize hpatch rd2941 hmem hread64 hov
  obtain ⟨gasWord, k', C', rd3007⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2992⟩) (okPc := ⟨3004⟩)
      rd2992 hcodeSize
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (dogPatchedJumpDest hpatch (by native_decide))
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega)
  exact ⟨gasWord, k', C', by simpa using rd3007⟩

theorem RD.dogBarkVatUrnsPostStaticcall {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : Sat256} {ret sel : UInt256} {R : List UInt256}
    {k C : ℕ} {mem rdata : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g (initState σ σ₀ g A I) ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata σ k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 24 ≤ 1024) :
    ∃ (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g (initState σ σ₀ g A I) ⟨3008⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
          ret :: sel :: R)
        (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out σ' k' C'
      ∧ typedCallViaEVM config (initState σ σ₀ g A I)
          (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
          [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
          (z,
            { initState σ σ₀ g A I with
                accountMap := σ', substate := A' },
            out) false
      ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd3007⟩ :=
    RD.dogBarkVatUrnsToStaticcall hpatch h hmem hread64 hcodeSize hov
  obtain ⟨σ', z, out, A_in, callGas, k', C', hΘpack, rd3008raw, hosz⟩ :=
    RD.solcStaticcall rd3007
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨σ', z, out, A', k', C', ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat) = UInt256.ofNat 7 := by
      native_decide
    change RD code I g (initState σ σ₀ g A I) ⟨3008⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
        ret :: sel :: R)
      (out.write 0 (barkVatUrnsCallMem I mem) 128
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
      (UInt256.ofNat 7) out σ' k' C'
    exact haw ▸ rd3008raw
  · have hdepthNe : (initState σ σ₀ g A I).executionEnv.depth ≠ 1024 := by
      intro hdepthEq
      exact absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from hdepthEq]; decide)
    have hΘ' :
        (σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.fork  σ σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (barkVatWord v))
            (toExecute I.fork σ (AccountAddress.ofUInt256 (barkVatWord v)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkVatUrnsCallMem I mem).readWithPadding 128 68)
            (I.depth + 1) I.header I.blobVersionedHashes I.blocks false := by
      simpa [initState] using hΘ
    have htargetNorm :
        AccountAddress.ofUInt256 (barkVatWord v) =
          EVM.address ↑(AccountAddress.ofNat v.vat.toNat) := by
      rw [← barkVat_eq_vatKey v]
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact (Nat.mod_eq_of_lt (AccountAddress.ofNat v.vat.toNat).isLt).symm
    have hΘcall :
        (σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.fork  σ σ₀ A_in
            I.codeOwner I.sender (EVM.address (AccountAddress.ofNat v.vat.toNat))
            (toExecute I.fork σ (EVM.address (AccountAddress.ofNat v.vat.toNat)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkVatUrnsCallMem I mem).readWithPadding 128 68)
            (I.depth + 1) I.header I.blobVersionedHashes I.blocks false := by
      simpa [accountAddress_roundtrip I.codeOwner, htargetNorm] using hΘ'
    refine ⟨(barkVatUrnsCallMem I mem).readWithPadding 128 68,
      barkVatUrnsEncode_eq (I := I) (mem := mem) hsz100 hmem, ?_⟩
    exact callViaEVM.callMade (perm := false) wordOfInt_zero.symm
      ⟨callGas, A_in, by simpa [initState] using hΘcall⟩ rfl
      (by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _)
      hdepthNe

theorem RD.dogBarkVatUrnsCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3008⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3008⟩) (okPc := ⟨3024⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hrdataSize hov

theorem RD.dogBarkVatUrnsCallSuccessToDecode {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3008⟩ (⟨1⟩ :: d0 :: d1 :: d2 :: R)
      mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3026⟩ (d0 :: d1 :: d2 :: R)
      mem aw rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨3008⟩) (okPc := ⟨3024⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.dogBarkVatUrnsReturnDecodeShortReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem out : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3026⟩ (d0 :: d1 :: d2 :: R)
      (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 64) (hout : out.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop rd
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 7) rdPush64
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (barkVatUrnsPostCallMem_mload64 hmem hread64 hshort hout)
    (by decide)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush64' := RD.push1 rdReturndatasize ⟨64⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush64'
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rdIszero := RD.iszero rdLt
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨3046⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatUrnsReturnDecodeOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem out : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3026⟩
      (⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I ::
        barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3061⟩
      (barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k' C' := by
  have hmload64 := barkVatUrnsPostCallMem_mload64_long (I := I) hmem hread64 hlong hout
  have hmload128 := barkVatUrnsPostCallMem_mload128_long (I := I) hmem hlong hout
  have hmload160 := barkVatUrnsPostCallMem_mload160_long (I := I) hmem hlong hout
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hlong
  have rd3036 := evm_run rd with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3037raw := RD.lt rd3036
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3037 := by
    simpa [hlt] using rd3037raw
  have rd3043 := evm_run rd3037 with [
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3046⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3046 := rd3043.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd3054 := evm_run rd3046 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 (barkVatUrnsInkWord out) (UInt256.ofNat 7)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3055raw := RD.add rd3054
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨k3055, C3055, rd3055⟩ :
      ∃ k3055 C3055, RD code I g s0 ⟨3055⟩
        (⟨160⟩ :: barkVatUrnsInkWord out :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
          barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
        (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k3055 C3055 := by
    exact ⟨_, _, by simpa using rd3055raw⟩
  have rd3061 := evm_run rd3055 with [
    raw mload 0 (barkVatUrnsArtWord out) (UInt256.ofNat 7)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa using rd3061⟩

theorem RD.dogBarkVatUrnsMaterializeTuple {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem out : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3061⟩
      (barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3070⟩
      (barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsTupleMem I mem out) (UInt256.ofNat 8) out acc k' C' := by
  have hmload64 := barkVatUrnsPostCallMem_mload64_long (I := I) hmem hread64 hlong hout
  have hmask0 :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) ⟨0⟩ =
        ⟨0⟩ := by
    native_decide
  have rd3067 := evm_run rd with [
    raw push2 ⟨3068⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4641⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4641 := rd3067.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd4651prefix := evm_run rd4641 with [
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨128⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4652 := rd4651prefix.mstore 0 (barkVatUrnsTupleFreeMem I mem out)
    (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨128⟩) = ⟨256⟩ by native_decide]
      dsimp [barkVatUrnsTupleFreeMem, Reasoning.Theory.writeWord]
      rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4665prefix := evm_run rd4652 with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4666 := rd4665prefix.mstore 0 (barkVatUrnsTupleWord0Mem I mem out)
    (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsTupleWord0Mem, barkVatUrnsTupleFreeMem,
        Reasoning.Theory.writeWord]
      rw [hmask0, show (⟨128⟩ : UInt256).toNat = 128 by native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4672prefix := evm_run rd4666 with [
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
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4673 := rd4672prefix.mstore 0 (barkVatUrnsTupleWord1Mem I mem out)
    (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsTupleWord1Mem, barkVatUrnsTupleWord0Mem,
        barkVatUrnsTupleFreeMem, Reasoning.Theory.writeWord]
      rw [show ((⟨32⟩ : UInt256) + ⟨128⟩).toNat = 160 by native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4679prefix := evm_run rd4673 with [
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
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4680 := rd4679prefix.mstore 0 (barkVatUrnsTupleWord2Mem I mem out)
    (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsTupleWord2Mem, barkVatUrnsTupleWord1Mem,
        barkVatUrnsTupleWord0Mem, barkVatUrnsTupleFreeMem, Reasoning.Theory.writeWord]
      rw [show ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ⟨128⟩)).toNat = 192 by
        native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4686prefix := evm_run rd4680 with [
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
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4687 := rd4686prefix.mstore 3 (barkVatUrnsTupleMem I mem out)
    (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsTupleMem, barkVatUrnsTupleWord2Mem, barkVatUrnsTupleWord1Mem,
        barkVatUrnsTupleWord0Mem, barkVatUrnsTupleFreeMem, Reasoning.Theory.writeWord]
      rw [show
        ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ⟨128⟩))).toNat =
          224 by native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4689 := evm_run rd4687 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3068 := rd4689.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd3070 := evm_run rd3068 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa using rd3070⟩

theorem RD.dogBarkLoadIlkFields {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem out : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3070⟩
      (barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsTupleMem I mem out) (UInt256.ofNat 8) out σ k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) out σ k' C' := by
  have hslot := barkIlksHashMem_slot (I := I) (mem := mem) (out := out) hmem hlong hout
  have hmload64 := barkIlksHashMem_mload64 (I := I) (mem := mem) (out := out)
    hmem hlong hout
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rdMstore0Prefix := evm_run rd with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0
    (wordAt0Mem (barkIlkWord I) (barkVatUrnsTupleMem I mem out))
    (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (barkIlksHashMem I mem out)
    (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
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
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (barkIlksSlot I) (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost hslot (by native_decide) (by evm_ov)
  have rdAllocPrefix := evm_run rdSlot with [
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨256⟩ (UInt256.ofNat 8)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨128⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterAlloc := rdAllocPrefix.mstore 0 (barkIlksAllocMem I mem out)
    (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkIlksAllocMem, Reasoning.Theory.writeWord]
      rw [show ((⟨256⟩ : UInt256) + ⟨128⟩) = ⟨384⟩ by native_decide,
        show (⟨64⟩ : UInt256).toNat = 64 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rdBeforeClipLoad := rdAfterAlloc.dup2
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  obtain ⟨_, _, rdAfterClipLoad⟩ := rdBeforeClipLoad.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdClipStorePrefix := evm_run rdAfterClipLoad with [
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
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
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  rw [hmask] at rdClipStorePrefix
  have rdAfterClipStore := rdClipStorePrefix.mstore 3 (barkIlksClipMem σ I mem out)
    (UInt256.ofNat 9)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkIlksClipMem, barkIlksClipWord, solcSlotWord, Reasoning.Theory.writeWord]
      rw [show (⟨256⟩ : UInt256).toNat = 256 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rdChopLoadPrefix := evm_run rdAfterClipStore with [
    raw swap5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdAfterChopLoad⟩ := rdChopLoadPrefix.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdChopStorePrefix := evm_run rdAfterChopLoad with [
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterChopStore := rdChopStorePrefix.mstore 3 (barkIlksChopMem σ I mem out)
    (UInt256.ofNat 10)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkIlksChopMem, barkIlksChopWord, solcSlotWord, Reasoning.Theory.writeWord]
      rw [show ((⟨256⟩ : UInt256) + ⟨32⟩).toNat = 288 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rdHoleLoadPrefix := evm_run rdAfterChopStore with [
    raw push1 ⟨2⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdAfterHoleLoad⟩ := rdHoleLoadPrefix.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdHoleStorePrefix := evm_run rdAfterHoleLoad with [
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterHoleStore := rdHoleStorePrefix.mstore 3 (barkIlksHoleMem σ I mem out)
    (UInt256.ofNat 11)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkIlksHoleMem, barkIlksHoleWord, solcSlotWord, Reasoning.Theory.writeWord]
      rw [show ((⟨64⟩ : UInt256) + ⟨256⟩).toNat = 320 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rdDirtLoadPrefix := evm_run rdAfterHoleStore with [
    raw push1 ⟨3⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdAfterDirtLoad⟩ := rdDirtLoadPrefix.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdDirtStorePrefix := evm_run rdAfterDirtLoad with [
    raw push1 ⟨96⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdDirtStorePrefix3138⟩ : ∃ kD C_D,
      RD code I g s0 ⟨3138⟩
        (((⟨256⟩ : UInt256) + ⟨96⟩) :: barkIlksDirtWord σ I ::
          ⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
          barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
          barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
        (barkIlksHoleMem σ I mem out) (UInt256.ofNat 11) out σ kD C_D := by
    exact ⟨_, _, by simpa [barkIlksDirtWord, solcSlotWord] using rdDirtStorePrefix⟩
  have rdAfterDirtStore := rdDirtStorePrefix3138.mstore 3 (barkIlksMem σ I mem out)
    (UInt256.ofNat 12)
    (by
      exact dogDecodePatchedNoArg (pc := ⟨3138⟩) (byte := 0x52) (op := .MSTORE)
        hpatch (by native_decide)
        (by native_decide)
        (by native_decide) (by native_decide) (by native_decide))
    mem_cost
    (by
      dsimp [barkIlksMem, barkIlksDirtWord, solcSlotWord, Reasoning.Theory.writeWord]
      rw [show ((⟨256⟩ : UInt256) + ⟨96⟩).toNat = 352 by native_decide])
    (by native_decide)
    (by evm_ov)
  exact ⟨_, _, by simpa using rdAfterDirtStore⟩


end Benchmarks.Dss.Dog
