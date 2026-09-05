import Benchmarks.Dss.Clipper.TakeDynamicDog

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 2000000 in
theorem RD.clipperTakePostDogFluxExtcodesizeGuardWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5025⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw rdata (cA, σ) k C)
    (htabNew : tabNew = ⟨0⟩) (hmem : clipperTakeMemoryWF mem aw) :
    ∃ k' C', RD code ee g s0 ⟨5177⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      (clipperTakeVatFluxCalldataMem v ee packed lotNew mem) aw rdata
      (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hbaseMload64 := clipperTakeMemoryWF_mload64 mem aw hmem
  have hcallWF := clipperTakeVatFluxMemoryWF v ee packed lotNew hmem
  have hcallMload64 := clipperTakeMemoryWF_mload64
    (clipperTakeVatFluxCalldataMem v ee packed lotNew mem) aw hcallWF
  have haw64 := clipperTakeMemoryWF_mstore_aw mem aw (⟨64⟩ : UInt256) hmem (by decide)
  have haw128 := clipperTakeMemoryWF_mstore_aw mem aw (⟨128⟩ : UInt256) hmem (by decide)
  have haw132 := clipperTakeMemoryWF_mstore_aw mem aw (⟨132⟩ : UInt256) hmem (by decide)
  have haw164 := clipperTakeMemoryWF_mstore_aw mem aw (⟨164⟩ : UInt256) hmem (by decide)
  have haw196 := clipperTakeMemoryWF_mstore_aw mem aw (⟨196⟩ : UInt256) hmem (by decide)
  have haw228 := clipperTakeMemoryWF_mstore_aw mem aw (⟨228⟩ : UInt256) hmem (by decide)
  have rd5030pre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5222⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd5031 := rd5030pre.jumpiNT (by clipper_runtime_decode) htabNew (by evm_ov)
  have rd5034pre := evm_run rd5031 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have rd5035 := rd5034pre.mload 0 ⟨128⟩ aw
    (by clipper_runtime_decode) (clipperTakeMloadCostZero haw64)
    hbaseMload64 haw64 (by evm_ov)
  have rd5044pre := evm_run rd5035 with [
    raw push4 clipperTakeVatFluxSelectorSeed (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨225⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft clipperTakeVatFluxSelectorSeed ⟨225⟩ =
    clipperTakeVatFluxSelectorShifted from by native_decide] at rd5044pre
  have rd5045 := rd5044pre.mstore 0 (clipperTakeVatFluxSelectorMem mem) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw128) (by rfl)
    haw128 (by evm_ov)
  have rd5078 := rd5045.pushConst ilkWord (width := 32) (op := .PUSH32) (by decide)
    (by simpa [ilkWord] using clipperTakeIlkPush32Decode5045 v hpatch hilk hlen)
    (by evm_ov)
  have rd5082pre := evm_run rd5078 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide] at rd5082pre
  have rd5083 := rd5082pre.mstore 0 (clipperTakeVatFluxIlkMem v mem) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw132)
    (by
      rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
      simp [clipperTakeVatFluxIlkMem, clipperTakeIlkWord, hilk, ilkWord])
    haw132 (by evm_ov)
  have rd5088pre := evm_run rd5083 with [
    raw address (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide] at rd5088pre
  have rd5089 := rd5088pre.mstore 0
    (clipperTakeVatFluxThisMem ee (clipperTakeVatFluxIlkMem v mem)) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw164) (by rfl)
    haw164 (by evm_ov)
  have rd5104pre := evm_run rd5089 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup9 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd5104pre
  rw [show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide] at rd5104pre
  have rd5105 := rd5104pre.mstore 0
    (clipperTakeVatFluxWhoMem packed
      (clipperTakeVatFluxThisMem ee (clipperTakeVatFluxIlkMem v mem))) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw196) (by rfl)
    haw196 (by evm_ov)
  have rd5111pre := evm_run rd5105 with [
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by native_decide] at rd5111pre
  have rd5112 := rd5111pre.mstore 0
    (clipperTakeVatFluxCalldataMem v ee packed lotNew mem) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw228) (by rfl)
    haw228 (by evm_ov)
  have rd5113pre := evm_run rd5112 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5114 := rd5113pre.mload 0 ⟨128⟩ aw
    (by clipper_runtime_decode) (clipperTakeMloadCostZero haw64)
    hcallMload64 haw64 (by evm_ov)
  have rd5147 := rd5114.pushConst vatWord (width := 32) (op := .PUSH32) (by decide)
    (by simpa [vatWord] using clipperTakeVatPush32Decode5114 v hpatch) (by evm_ov)
  have rd5177 := evm_run rd5147 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperTakeVatFluxSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨132⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨132⟩ = ⟨260⟩ from by native_decide] at rd5177
  rw [show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by native_decide]
    at rd5177
  rw [show (⟨0⟩ : UInt256) + ⟨132⟩ = ⟨132⟩ from by native_decide] at rd5177
  exact ⟨_, _, by simpa [clipperTakeVatTarget, vatWord, u256_land_comm] using rd5177⟩

theorem RD.clipperTakePostDogFluxNoCodeWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5177⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw rdata (cA, σ) k C)
    (hcodeSizeVat : extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5177⟩) (okPc := ⟨5189⟩)
    rd hcodeSizeVat
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakePostDogFluxPostCallWF {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {baseMem rdata : ByteArray} {aw : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨5177⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      (clipperTakeVatFluxCalldataMem v I packed lotNew baseMem) aw rdata
      (cA, σ) k C)
    (hbaseMem : clipperTakeMemoryWF baseMem aw)
    (hcodeSizeVat : extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zVat : Bool) (outVat : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨5193⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
            stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
        (clipperTakeVatFluxCalldataMem v I packed lotNew baseMem) aw outVat
        (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat packed.toNat),
          .int (Int.ofNat lotNew.toNat)]
        (zVat,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat, substate := A_vat, createdAccounts := cA_vat },
          outVat) true ∧
      outVat.size < UInt256.size ∧
      clipperTakeMemoryWF (clipperTakeVatFluxCalldataMem v I packed lotNew baseMem) aw := by
  obtain ⟨gasWord, _, _, rd5192⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5177⟩) (okPc := ⟨5189⟩)
      rd hcodeSizeVat
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperTakeJumpDest5189 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA_vat, σ_vat, zVat, outVat, A_in, callGas, k5193, C5193, hΘpack,
      rd5193raw, houtVatSize⟩ :=
    RD.call rd5192 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_vat, hΘ⟩ := hΘpack
  have hsize := hbaseMem.1
  have hMIn : UInt256.ofNat
      (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat) = aw := by
    apply clipperTakeM_same_of_cover
    rcases hbaseMem with ⟨_, _, hcover, _⟩
    change 260 ≤ aw.toNat * 32
    omega
  have hactive : UInt256.ofNat
      (MachineState.M
        (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = aw := by
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
    rw [show MachineState.M
      (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
      (⟨128⟩ : UInt256).toNat 0 =
      MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat by
        simp [MachineState.M]]
    exact hMIn
  refine ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k5193, C5193, ?_, ?_,
    houtVatSize, clipperTakeVatFluxMemoryWF v I packed lotNew hbaseMem⟩
  · have hwrite : outVat.write 0 (clipperTakeVatFluxCalldataMem v I packed lotNew baseMem)
        (⟨128⟩ : UInt256).toNat
        (min (⟨0⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat =
        clipperTakeVatFluxCalldataMem v I packed lotNew baseMem := by
      simpa using clipperTakeZeroReturndataWrite_eq outVat
        (clipperTakeVatFluxCalldataMem v I packed lotNew baseMem)
    rw [hwrite, hactive] at rd5193raw
    simpa using rd5193raw
  · let evmVat : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A I with
        accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v) (evm := evmVat) (name := "flux")
      (args := [v.ilk, .address I.codeOwner,
        .address (AccountAddress.ofNat packed.toNat), .int (Int.ofNat lotNew.toNat)])
      (tgt := EVM.address v.vat) (targetWord := clipperTakeVatTarget v)
      (cA' := cA_vat) (σ' := σ_vat) (A' := A_vat) (A_in := A_in)
      (z := zVat) (o := outVat) (g'' := g'') (callGas := callGas)
      (mem := clipperTakeVatFluxCalldataMem v I packed lotNew baseMem)
      (inOff := ⟨128⟩) (inSize := ⟨132⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmVat, initState] using h
        rw [hI]
        decide)) ?_ ?_ ?_
    · rw [clipperTakeVatTargetAddress v]
      exact clipperTakeEVMAddressAccountAddress v.vat
    · simpa using clipperTakeVatFluxEncode_eq_ge v I packed lotNew hsize
    · simpa [evmVat, initState, hperm] using hΘ

end Benchmarks.Dss.Clipper
