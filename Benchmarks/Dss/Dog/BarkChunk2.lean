import Benchmarks.Dss.Dog.BarkChunk1

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogBarkVatIlksToCallMload {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata σ k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3160⟩
      (⟨384⟩ :: ⟨384⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata σ k' C' := by
  have hmload64 := barkIlksMem_mload64 (σ := σ) (I := I) (mem := mem) (out := out)
    hmem hlong hout
  have hmloadCall := barkVatIlksCallMem_mload64 (σ := σ) (I := I) (mem := mem)
    (out := out) hmem hlong hout
  have rd3150prefix := evm_run rd with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 12)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw push4 ⟨1823590043⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨225⟩
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
      (by evm_ov)]
  have rd3151 := rd3150prefix.mstore 3 (barkVatIlksSelectorMem σ I mem out)
    (UInt256.ofNat 13)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatIlksSelectorMem, barkVatIlksSelectorWord, Reasoning.Theory.writeWord]
      rw [show (⟨384⟩ : UInt256).toNat = 384 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rd3157prefix := evm_run rd3151 with [
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
    raw dup12
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
  have rd3158 := rd3157prefix.mstore 3 (barkVatIlksCallMem σ I mem out)
    (UInt256.ofNat 14)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatIlksCallMem, Reasoning.Theory.writeWord]
      rw [show ((⟨384⟩ : UInt256) + ⟨4⟩).toNat = 388 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rd3160 := evm_run rd3158 with [
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 14)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmloadCall (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3160⟩

theorem RD.dogBarkVatIlksToGasPrep {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3160⟩
      (⟨384⟩ :: ⟨384⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3204⟩
      (⟨384⟩ :: ⟨384⟩ :: barkVatWord v :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨256⟩ :: barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata σ k' C' := by
  have hvatCleanR :
      UInt256.land (barkVatWord v) solcAddrMask = barkVatWord v :=
    solcAddrMask_clean (barkVatWord_canonical v)
  have rd3169 := evm_run rd with [
    raw swap2
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
    raw dup4
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
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3202 := rd3169.pushConst (barkVatWord v) (width := 32) (op := .PUSH32)
    (hop := by decide)
    (by simpa [barkVatWord] using dogBarkVatConstDecode3169 hpatch)
    (by evm_ov)
  have rd3204 := evm_run rd3202 with [
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [hvatCleanR] using rd3204⟩

theorem RD.dogBarkVatIlksToExtcodesize {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata σ k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3229⟩
      (barkVatWord v :: barkVatWord v :: ⟨384⟩ :: ⟨36⟩ :: ⟨384⟩ :: ⟨160⟩ ::
        ⟨420⟩ :: ⟨3647180086⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨256⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata σ k' C' := by
  obtain ⟨_, _, rd3160⟩ :=
    RD.dogBarkVatIlksToCallMload hpatch rd hmem hlong hout hov
  obtain ⟨_, _, rd3204⟩ :=
    RD.dogBarkVatIlksToGasPrep hpatch rd3160 hov
  have rd3229 := evm_run rd3204 with [
    raw push4 ⟨3647180086⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨36⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
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
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
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
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
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
    raw add
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
      (by evm_ov)]
  exact ⟨_, _, by
    simpa [show UInt256.sub (⟨384⟩ : UInt256) ⟨384⟩ = ⟨0⟩ by native_decide,
      show ((⟨0⟩ : UInt256) + ⟨36⟩) = ⟨36⟩ by native_decide,
      show ((⟨384⟩ : UInt256) + ⟨36⟩) = ⟨420⟩ by native_decide]
      using rd3229⟩

theorem RD.dogBarkVatIlksToStaticcall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata σ k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    ∃ gasWord k' C', RD code I g s0 ⟨3244⟩
      (gasWord :: barkVatWord v :: ⟨384⟩ :: ⟨36⟩ :: ⟨384⟩ :: ⟨160⟩ ::
        ⟨420⟩ :: ⟨3647180086⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨256⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata σ k' C' := by
  obtain ⟨_, _, rd3229⟩ :=
    RD.dogBarkVatIlksToExtcodesize hpatch rd hmem hlong hout (by omega)
  obtain ⟨gasWord, k', C', rd3244⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3229⟩) (okPc := ⟨3241⟩)
      rd3229 hcodeSize
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
  exact ⟨gasWord, k', C', by simpa using rd3244⟩

theorem RD.dogBarkVatIlksPostStaticcall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 evm : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata σ k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hevmEnv : evm.executionEnv = I)
    (hevmMap : evm.accountMap = σ)
    (hevmOrig : evm.σ₀ = s0.σ₀)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 40 ≤ 1024) :
    ∃ (σ' : AccountMap) (z : Bool)
      (outIlks : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g s0 ⟨3245⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨420⟩ :: ⟨3647180086⟩ :: barkVatWord v ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨256⟩ ::
          barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
          barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
        (barkVatIlksPostCallMem σ I mem out outIlks) (UInt256.ofNat 17) outIlks
        σ' k' C'
      ∧ typedCallViaEVM config evm
          (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
          [.fixedBytes bytes32Width (barkIlkBytes I)]
          (z,
            { evm with accountMap := σ', substate := A' },
            outIlks) false
      ∧ outIlks.size < UInt256.size := by
  obtain ⟨_, _, _, rd3244⟩ :=
    RD.dogBarkVatIlksToStaticcall hpatch rd hmem hlong hout hcodeSize hov
  obtain ⟨σ', z, outIlks, A_in, callGas, k', C', hΘpack, rd3245raw, hosz⟩ :=
    RD.solcStaticcall rd3244
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨σ', z, outIlks, A', k', C', ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat
          (⟨384⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨384⟩ : UInt256).toNat (⟨160⟩ : UInt256).toNat) = UInt256.ofNat 17 := by
      native_decide
    change RD code I g s0 ⟨3245⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨420⟩ :: ⟨3647180086⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨256⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384
        (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat)
      (UInt256.ofNat 17) outIlks σ' k' C'
    exact haw ▸ rd3245raw
  · have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
      intro hdepthEq
      exact absurd hdepth (by rw [← hevmEnv, hdepthEq]; decide)
    have htargetNorm :
        EVM.address ↑(AccountAddress.ofNat v.vat.toNat) =
          AccountAddress.ofUInt256 (barkVatWord v) := by
      rw [← barkVat_eq_vatKey v]
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (AccountAddress.ofNat v.vat.toNat).isLt
    have hΘ' :
        (σ', g'', A', z, outIlks) =
          Ethereum.EVM.Θ evm.executionEnv.fork evm.accountMap evm.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
            evm.executionEnv.sender (AccountAddress.ofUInt256 (barkVatWord v))
            (toExecute evm.executionEnv.fork evm.accountMap (AccountAddress.ofUInt256 (barkVatWord v)))
            callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkVatIlksCallMem σ I mem out).readWithPadding 384 36)
            (evm.executionEnv.depth + 1) evm.executionEnv.header
            evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks false := by
      simpa [hevmEnv, hevmMap, hevmOrig] using hΘ
    exact Reasoning.Theory.callCoincides
      (cfg := config) (evm := evm) (name := "ilks")
      (args := [.fixedBytes bytes32Width (barkIlkBytes I)])
      (tgt := EVM.address (AccountAddress.ofNat v.vat.toNat))
      (targetWord := barkVatWord v) (σ' := σ') (A' := A')
      (A_in := A_in) (z := z) (o := outIlks) (g'' := g'') (callGas := callGas)
      (mem := barkVatIlksCallMem σ I mem out) (inOff := ⟨384⟩) (inSize := ⟨36⟩)
      (callPerm := false) hdepthNe htargetNorm
      (barkVatIlksEncode_eq (σ := σ) (I := I) (mem := mem) (out := out)
        hsz100 hmem hlong hout)
      hΘ'

theorem RD.dogBarkVatIlksNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata σ k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) = ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd3229⟩ :=
    RD.dogBarkVatIlksToExtcodesize hpatch rd hmem hlong hout (by omega)
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3229⟩) (okPc := ⟨3241⟩)
    rd3229 hcodeSize
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

theorem RD.dogBarkVatIlksCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3245⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3245⟩) (okPc := ⟨3261⟩) rd
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

theorem RD.dogBarkVatIlksCallSuccessToDecode {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 ret sel : UInt256}
    {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3245⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 ::
        d10 :: d11 :: d12 :: d13 :: ret :: sel :: R)
      mem aw out acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3263⟩
      (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 ::
        d10 :: d11 :: d12 :: d13 :: ret :: sel :: R)
      mem aw out acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨3245⟩) (okPc := ⟨3261⟩) rd
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
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatIlksReturnDecodeShortReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap} {σ : AccountMap}
    {mem out outIlks : ByteArray} {k C : ℕ}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 ret sel : UInt256}
    {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3263⟩
      (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 ::
        d10 :: d11 :: d12 :: d13 :: ret :: sel :: R)
      (barkVatIlksPostCallMem σ I mem out outIlks) (UInt256.ofNat 17) outIlks acc k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hshort : outIlks.size < 160) (houtIlks : outIlks.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
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
    (by simp only [List.length_cons]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdMload64 := RD.mload 0 ⟨384⟩ (UInt256.ofNat 17) rdPush64
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (barkVatIlksPostCallMem_mload64 hmem hlong hout hshort houtIlks)
    (by decide)
    (by simp only [List.length_cons]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush160 := RD.push1 rdReturndatasize ⟨160⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush160
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat outIlks.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' outIlks.size houtIlks]
    exact hshort
  have rdIszero := RD.iszero rdLt
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨3283⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat outIlks.size) (⟨160⟩ : UInt256)) =
        ⟨0⟩ := by
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

theorem RD.dogBarkVatIlksReturnDecodeOkToSpotGuard {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : AccountMap} {σ : AccountMap}
    {mem out outIlks : ByteArray} {k C : ℕ}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 ret sel : UInt256}
    {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3263⟩
      (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 ::
        d10 :: d11 :: d12 :: d13 :: ret :: sel :: R)
      (barkVatIlksPostCallMem σ I mem out outIlks) (UInt256.ofNat 17) outIlks acc k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3308⟩
      (barkVatIlksSpotWord outIlks :: barkVatIlksDustWord outIlks ::
        barkVatIlksRateWord outIlks :: d6 :: d7 :: d8 :: d9 :: d10 ::
        d11 :: d12 :: d13 :: ret :: sel :: R)
      (barkVatIlksPostCallMem σ I mem out outIlks) (UInt256.ofNat 17) outIlks acc k' C' := by
  have hmload64 := barkVatIlksPostCallMem_mload64_long (σ := σ) (I := I)
    hmem hlong hout hlongIlks houtIlks
  have hmload416 := barkVatIlksPostCallMem_mload416_long (σ := σ) (I := I)
    hmem hlong hout hlongIlks houtIlks
  have hmload448 := barkVatIlksPostCallMem_mload448_long (σ := σ) (I := I)
    hmem hlong hout hlongIlks houtIlks
  have hmload512 := barkVatIlksPostCallMem_mload512_long (σ := σ) (I := I)
    hmem hlong hout hlongIlks houtIlks
  have hlt : UInt256.lt (UInt256.ofNat outIlks.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' outIlks.size houtIlks]
    exact hlongIlks
  have rd3272 := evm_run rd with [
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
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3273raw := RD.lt rd3272
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3273 := by
    simpa [hlt] using rd3273raw
  have rd3275 := evm_run rd3273 with [
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3283⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hcond : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by
    decide
  have rd3283 := RD.jumpiT rd3275
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd3288pre := evm_run rd3283 with [
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
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3289addrRaw := RD.add rd3288pre
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hadd416 : (⟨384⟩ : UInt256) + ⟨32⟩ = ⟨416⟩ := by
    native_decide
  have rd3289addr := by
    simpa [hadd416] using rd3289addrRaw
  have rd3293pre := evm_run rd3289addr with [
    raw mload 0 (barkVatIlksRateWord outIlks) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload416 (by decide) (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3294addrRaw := RD.add rd3293pre
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hadd448 : (⟨384⟩ : UInt256) + ⟨64⟩ = ⟨448⟩ := by
    native_decide
  have rd3294addr := by
    simpa [hadd448] using rd3294addrRaw
  have rd3299pre := evm_run rd3294addr with [
    raw mload 0 (barkVatIlksSpotWord outIlks) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload448 (by decide) (by evm_ov),
    raw push1 ⟨128⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3300addrRaw := RD.add rd3299pre
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hadd512 : (⟨384⟩ : UInt256) + ⟨128⟩ = ⟨512⟩ := by
    native_decide
  have rd3300addr := by
    simpa [hadd512] using rd3300addrRaw
  have rd3308 := evm_run rd3300addr with [
    raw mload 0 (barkVatIlksDustWord outIlks) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload512 (by decide) (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
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
  exact ⟨_, _, by simpa using rd3308⟩


@[reducible] def dogPostIlksErrorStringFullWordTailWf
    (code : ByteArray) (pc len word : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p68 := p27 + UInt256.ofNat 33
  let pDup3 := p68 + UInt256.ofNat 2
  let pAdd := pDup3 + ⟨1⟩
  let pMstore3 := pAdd + ⟨1⟩
  let pSwap := pMstore3 + ⟨1⟩
  let pMload := pSwap + ⟨1⟩
  let pSwap2 := pMload + ⟨1⟩
  let pDup2 := pSwap2 + ⟨1⟩
  let pSwap3 := pDup2 + ⟨1⟩
  let pSub := pSwap3 + ⟨1⟩
  let p100 := pSub + ⟨1⟩
  let pAdd2 := p100 + UInt256.ofNat 2
  let pSwap4 := pAdd2 + ⟨1⟩
  let pRev := pSwap4 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push .PUSH32, some (word, 32))
  ∧ decode code p68 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code pDup3 = some (.DUP3, .none)
  ∧ decode code pAdd = some (.ADD, .none)
  ∧ decode code pMstore3 = some (.MSTORE, .none)
  ∧ decode code pSwap = some (.SWAP1, .none)
  ∧ decode code pMload = some (.MLOAD, .none)
  ∧ decode code pSwap2 = some (.SWAP1, .none)
  ∧ decode code pDup2 = some (.DUP2, .none)
  ∧ decode code pSwap3 = some (.SWAP1, .none)
  ∧ decode code pSub = some (.SUB, .none)
  ∧ decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code pAdd2 = some (.ADD, .none)
  ∧ decode code pSwap4 = some (.SWAP1, .none)
  ∧ decode code pRev = some (.REVERT, .none)

theorem RD.dogBarkPostIlksErrorStringRevertTailFullWord {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv} {k C : ℕ}
    {pc len word : UInt256} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code I g s0 pc stk mem (UInt256.ofNat 17) rdata acc k C)
    (hwf : dogPostIlksErrorStringFullWordTailWf code pc len word)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256))
      (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17) hd3 mem_cost hmload64
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem0 mem) (UInt256.ofNat 17)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem1 mem) (UInt256.ofNat 17)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem2 len mem)
      (UInt256.ofNat 17) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst word (width := 32) (op := .PUSH32)
    (by decide) hd27 (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem3 len word mem)
      (UInt256.ofNat 17) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17) hdMload
      mem_cost (barkPostIlksErrorStringMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem RD.dogBarkSpotZeroReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot = ⟨0⟩)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata acc k C)
    (hov : R.length + 24 ≤ 1024) :
    RDrev code g s0 := by
  have htail : solcErrorStringRevertTailWf code ⟨3344⟩ ⟨14⟩
      dogNotUnsafeRawWord ⟨144⟩ .PUSH14 14 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]; native_decide)
  have rd3316 := evm_run rd3308 with [
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
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hjump : UInt256.isZero spot ≠ ⟨0⟩ := by
    rw [hspot]
    decide
  have rd3339 := rd3316.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hjump (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3343 := evm_run rd3339 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3405⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hfall : UInt256.isZero (UInt256.isZero spot) = ⟨0⟩ := by
    rw [hspot]
    decide
  have rd3344 := rd3343.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hfall (by evm_ov)
  have hpc3344 : (⟨3339⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨3344⟩ := by
    native_decide
  have rd3344pc := rd3344
  rw [hpc3344] at rd3344pc
  exact Benchmarks.Dss.Dog.RD.dogBarkPostIlksErrorStringRevertTail
    (pc := ⟨3344⟩) (len := ⟨14⟩) (rawWord := dogNotUnsafeRawWord)
    (shift := ⟨144⟩) (word := UInt256.shiftLeft dogNotUnsafeRawWord ⟨144⟩)
    (op := .PUSH14) (width := 14) rd3344pc htail (by decide) (by rfl) hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkArtRateOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256} {aw : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hoverArt : UInt256.size ≤ art.toNat * rate.toNat)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem aw rdata acc k C)
    (hov : R.length + 27 ≤ 1024) :
    RDrev code g s0 := by
  have rd3316 := evm_run rd3308 with [
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
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hzero : UInt256.isZero spot = ⟨0⟩ := isZero_eq_zero_of_ne hspot
  have rd3317 := rd3316.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hzero (by evm_ov)
  have rd3326 := evm_run rd3317 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3327⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3326.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (R := spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
      kpr :: urn :: ilk :: ret :: sel :: R)
    (x := art) (y := rate) (ret := ⟨3327⟩)
    (by simp only [List.length_cons]; omega) hoverArt rd4564

theorem RD.dogBarkInkSpotOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256} {aw : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hoverInk : UInt256.size ≤ ink.toNat * spot.toNat)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem aw rdata acc k C)
    (hov : R.length + 28 ≤ 1024) :
    RDrev code g s0 := by
  have rd3316 := evm_run rd3308 with [
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
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hzero : UInt256.isZero spot = ⟨0⟩ := isZero_eq_zero_of_ne hspot
  have rd3317 := rd3316.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hzero (by evm_ov)
  have rd3326 := evm_run rd3317 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3327⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564art := rd3326.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3327⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      (x := art) (y := rate) (ret := ⟨3327⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitArt rd4564art
  have rd3336 := evm_run rd3327 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3337⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564ink := rd3336.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (R := art * rate :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink ::
      ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (x := ink) (y := spot) (ret := ⟨3337⟩)
    (by simp only [List.length_cons]; omega) hoverInk rd4564ink

theorem RD.dogBarkNotUnsafeReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hfitInk : ink.toNat * spot.toNat < UInt256.size)
    (hnotLt : (art * rate).toNat ≤ (ink * spot).toNat)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata acc k C)
    (hov : R.length + 28 ≤ 1024) :
    RDrev code g s0 := by
  have htail : solcErrorStringRevertTailWf code ⟨3344⟩ ⟨14⟩
      dogNotUnsafeRawWord ⟨144⟩ .PUSH14 14 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
  have rd3316 := evm_run rd3308 with [
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
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hzero : UInt256.isZero spot = ⟨0⟩ := isZero_eq_zero_of_ne hspot
  have rd3317 := rd3316.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hzero (by evm_ov)
  have rd3326 := evm_run rd3317 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3327⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564art := rd3326.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3327⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      (x := art) (y := rate) (ret := ⟨3327⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitArt rd4564art
  have rd3336 := evm_run rd3327 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3337⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564ink := rd3336.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3337⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := art * rate :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (x := ink) (y := spot) (ret := ⟨3337⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitInk rd4564ink
  have hlt : UInt256.lt (ink * spot) (art * rate) = ⟨0⟩ :=
    Reasoning.Theory.ult_zero hnotLt
  have rd3339raw := evm_run rd3337 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hpc3339 : (⟨3337⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨3339⟩ := by
    native_decide
  have rd3339 := rd3339raw
  rw [hlt, hpc3339] at rd3339
  have rd3343 := evm_run rd3339 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3405⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3344 := rd3343.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have hpc3344 : (⟨3339⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨3344⟩ := by
    native_decide
  have rd3344pc := rd3344
  rw [hpc3344] at rd3344pc
  exact Benchmarks.Dss.Dog.RD.dogBarkPostIlksErrorStringRevertTail
    (pc := ⟨3344⟩) (len := ⟨14⟩) (rawWord := dogNotUnsafeRawWord)
    (shift := ⟨144⟩) (word := UInt256.shiftLeft dogNotUnsafeRawWord ⟨144⟩)
    (op := .PUSH14) (width := 14) rd3344pc htail (by decide) (by rfl) hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkSafeToLimitGuard {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hfitInk : ink.toNat * spot.toNat < UInt256.size)
    (hsafe : (ink * spot).toNat < (art * rate).toNat)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata acc k C)
    (hov : R.length + 28 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3405⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata acc k' C' := by
  have rd3316 := evm_run rd3308 with [
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
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hzero : UInt256.isZero spot = ⟨0⟩ := isZero_eq_zero_of_ne hspot
  have rd3317 := rd3316.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hzero (by evm_ov)
  have rd3326 := evm_run rd3317 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3327⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564art := rd3326.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3327⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      (x := art) (y := rate) (ret := ⟨3327⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitArt rd4564art
  have rd3336 := evm_run rd3327 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3337⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564ink := rd3336.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3337⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := art * rate :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (x := ink) (y := spot) (ret := ⟨3337⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitInk rd4564ink
  have hlt : UInt256.lt (ink * spot) (art * rate) = ⟨1⟩ :=
    Reasoning.Theory.ult_one hsafe
  have rd3339raw := evm_run rd3337 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hpc3339 : (⟨3337⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨3339⟩ := by
    native_decide
  have rd3339 := rd3339raw
  rw [hlt, hpc3339] at rd3339
  have rd3343 := evm_run rd3339 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3405⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3405 := rd3343.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, by simpa using rd3405⟩

theorem RD.dogBarkLimitGuardOk {v : DogImmutables} {code : ByteArray}
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
    (hlimit :
      (solcSlotWordAt ⟨5⟩ σ I).toNat < (solcSlotWordAt ⟨4⟩ σ I).toNat ∧
        (barkIlksDirtWord σMem I).toNat < (barkIlksHoleWord σMem I).toNat)
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
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 28 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3512⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
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
  have hgtGlobal :
      UInt256.gt (solcSlotWordAt ⟨4⟩ σ I) (solcSlotWordAt ⟨5⟩ σ I) = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hlimit.1
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
  have hgtMilk : UInt256.gt (barkIlksHoleWord σMem I) (barkIlksDirtWord σMem I) = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hlimit.2
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
  have rd3512 := rd3435.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, by simpa using rd3512⟩

theorem RD.dogBarkComputeRoom {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
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
    (rd3512 : RD code I g s0 ⟨3512⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3543⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
  have rd3519 := evm_run rd3512 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3540⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3521, C3521, rd3521raw⟩ := rd3519.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3521 : RD code I g s0 ⟨3521⟩
      (solcSlotWordAt ⟨5⟩ σ I :: ⟨3540⟩ :: ⟨0⟩ :: spot :: dust :: rate ::
        ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k3521 C3521 := by
    simpa [solcSlotWordAt, solcSlotWord] using rd3521raw
  have rd3523prep := evm_run rd3521 with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3524, C3524, rd3524raw⟩ := rd3523prep.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3524 : RD code I g s0 ⟨3524⟩
      (solcSlotWordAt ⟨4⟩ σ I :: solcSlotWordAt ⟨5⟩ σ I :: ⟨3540⟩ :: ⟨0⟩ ::
        spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k3524 C3524 := by
    simpa [solcSlotWordAt, solcSlotWord] using rd3524raw
  have rd3525 := evm_run rd3524 with [
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨96⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3528raw := RD.add rd3525
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd352 : (⟨96⟩ : UInt256) + ⟨256⟩ = ⟨352⟩ := by
    native_decide
  have rd3528 := by
    simpa [hadd352, barkGlobalRoomWord] using rd3528raw
  have rd3529 := evm_run rd3528 with [
    raw mload 0 (barkIlksDirtWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload352 (by decide) (by evm_ov)]
  have rd3533 := evm_run rd3529 with [
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3533raw := RD.add rd3533
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd320 : (⟨64⟩ : UInt256) + ⟨256⟩ = ⟨320⟩ := by
    native_decide
  have rd3533add := by
    simpa [hadd320, barkGlobalRoomWord] using rd3533raw
  have rd3534 := evm_run rd3533add with [
    raw mload 0 (barkIlksHoleWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload320 (by decide) (by evm_ov)]
  have rd3536 := evm_run rd3534 with [
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4600⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4600 := rd3536.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3540⟩ :=
    RD.dogMinReturns (v := v) hpatch (dogPatchedJumpDest hpatch (by native_decide))
      (x := barkGlobalRoomWord σ I) (y := barkIlkRoomWord σMem I)
      (ret := ⟨3540⟩)
      (R := ⟨0⟩ :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      rd4600
      (by simp only [List.length_cons]; omega)
  have rd3543 := evm_run rd3540 with [
    raw jumpdest
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
  exact ⟨_, _, by simpa [barkRoomWord] using rd3543⟩

theorem RD.dogBarkComputeDart {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hfitRoom :
      (barkRoomWord σ σMem I).toNat * dogWadWord.toNat < UInt256.size)
    (hrateNe : rate ≠ ⟨0⟩)
    (hchopNe : barkIlksChopWord σMem I ≠ ⟨0⟩)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        barkIlksChopWord σMem I)
    (rd3543 : RD code I g s0 ⟨3543⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3594⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate ::
        barkDartWord σ σMem I art rate (barkIlksChopWord σMem I) :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k' C' := by
  have rd3548 := evm_run rd3543 with [
    raw push2 ⟨3591⟩
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
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3550raw := RD.add rd3548
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd288 : (⟨32⟩ : UInt256) + ⟨256⟩ = ⟨288⟩ := by
    native_decide
  have rd3551 := by
    simpa [hadd288] using rd3550raw
  have rd3552 := evm_run rd3551 with [
    raw mload 0 (barkIlksChopWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload288 (by decide) (by evm_ov)]
  have rd3557 := evm_run rd3552 with [
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3570⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3566 := rd3557.pushConst dogWadWord (width := 8) (op := .PUSH8)
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3569 := evm_run rd3566 with [
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3569.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3570raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := barkRoomWord σ σMem I) (y := dogWadWord) (ret := ⟨3570⟩)
      (R := rate :: barkIlksChopWord σMem I :: art :: ⟨3591⟩ ::
        barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitRoom rd4564
  have rd3575 := evm_run rd3570raw with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3577⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3577 := rd3575.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hrateNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3579raw := evm_run rd3577 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3579 := by
    simpa [barkDartByRateWord] using rd3579raw
  have rd3583 := evm_run rd3579 with [
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3585⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3585 := rd3583.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hchopNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3587raw := evm_run rd3585 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4600⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3587 := by
    simpa [barkDartCandidateWord] using rd3587raw
  have rd4600 := rd3587.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd4600' := by
    simpa [barkDartCandidateWord, barkDartByRateWord, barkRoomWadWord] using rd4600
  obtain ⟨_, _, rd3591⟩ :=
    RD.dogMinReturns (v := v) hpatch (dogPatchedJumpDest hpatch (by native_decide))
      (x := art) (y := barkDartCandidateWord σ σMem I rate (barkIlksChopWord σMem I))
      (ret := ⟨3591⟩)
      (R := barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      rd4600'
      (by simp only [List.length_cons]; omega)
  have rd3594 := evm_run rd3591 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [barkDartWord] using rd3594⟩

theorem RD.dogBarkDartCandidateDivZeroInvalid {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hfitRoom :
      (barkRoomWord σ σMem I).toNat * dogWadWord.toNat < UInt256.size)
    (hrateNe : rate ≠ ⟨0⟩)
    (hchopZero : barkIlksChopWord σMem I = ⟨0⟩)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        barkIlksChopWord σMem I)
    (rd3543 : RD code I g s0 ⟨3543⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction := by
  have rd3548 := evm_run rd3543 with [
    raw push2 ⟨3591⟩
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
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3550raw := RD.add rd3548
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd288 : (⟨32⟩ : UInt256) + ⟨256⟩ = ⟨288⟩ := by
    native_decide
  have rd3551 := by
    simpa [hadd288] using rd3550raw
  have rd3552 := evm_run rd3551 with [
    raw mload 0 (barkIlksChopWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload288 (by decide) (by evm_ov)]
  have rd3557 := evm_run rd3552 with [
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3570⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3566 := rd3557.pushConst dogWadWord (width := 8) (op := .PUSH8)
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3569 := evm_run rd3566 with [
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3569.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3570raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := barkRoomWord σ σMem I) (y := dogWadWord) (ret := ⟨3570⟩)
      (R := rate :: barkIlksChopWord σMem I :: art :: ⟨3591⟩ ::
        barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitRoom rd4564
  have rd3575 := evm_run rd3570raw with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3577⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3577 := rd3575.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hrateNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3579raw := evm_run rd3577 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3579 := by
    simpa [barkDartByRateWord] using rd3579raw
  have rd3583 := evm_run rd3579 with [
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3585⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  rw [hchopZero] at rd3583
  have rd3584 := rd3583.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  exact RD.invalidError rd3584
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)

theorem RD.dogBarkRoomWadOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hoverRoom :
      UInt256.size ≤ (barkRoomWord σ σMem I).toNat * dogWadWord.toNat)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        barkIlksChopWord σMem I)
    (rd3543 : RD code I g s0 ⟨3543⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  have rd3548 := evm_run rd3543 with [
    raw push2 ⟨3591⟩
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
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3550raw := RD.add rd3548
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd288 : (⟨32⟩ : UInt256) + ⟨256⟩ = ⟨288⟩ := by
    native_decide
  have rd3551 := by
    simpa [hadd288] using rd3550raw
  have rd3552 := evm_run rd3551 with [
    raw mload 0 (barkIlksChopWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload288 (by decide) (by evm_ov)]
  have rd3557 := evm_run rd3552 with [
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3570⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3566 := rd3557.pushConst dogWadWord (width := 8) (op := .PUSH8)
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3569 := evm_run rd3566 with [
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3569.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (x := barkRoomWord σ σMem I) (y := dogWadWord) (ret := ⟨3570⟩)
    (R := rate :: barkIlksChopWord σMem I :: art :: ⟨3591⟩ ::
      barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
      art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (by simp only [List.length_cons]; omega) hoverRoom rd4564


end Benchmarks.Dss.Dog
