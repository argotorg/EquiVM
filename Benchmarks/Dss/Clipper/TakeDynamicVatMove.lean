import Benchmarks.Dss.Clipper.TakeDynamicMemory
import Benchmarks.Dss.Clipper.TakeDogDigs

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeVatMoveExtcodesizeGuardWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4701 : RD code ee g s0 ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4813⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
        clipperTakeVatTarget v :: dog :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperTakeVatMoveCalldataMem σ ee owe mem) aw rdata (cA, σ) k' C' := by
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hbaseMload64 := clipperTakeMemoryWF_mload64 mem aw hmem
  have hcallWF := clipperTakeVatMoveMemoryWF σ ee owe hmem
  have hcallMload64 := clipperTakeMemoryWF_mload64
    (clipperTakeVatMoveCalldataMem σ ee owe mem) aw hcallWF
  have haw128 := clipperTakeMemoryWF_mstore_aw mem aw (⟨128⟩ : UInt256) hmem (by decide)
  have haw132 := clipperTakeMemoryWF_mstore_aw mem aw (⟨132⟩ : UInt256) hmem (by decide)
  have haw164 := clipperTakeMemoryWF_mstore_aw mem aw (⟨164⟩ : UInt256) hmem (by decide)
  have haw196 := clipperTakeMemoryWF_mstore_aw mem aw (⟨196⟩ : UInt256) hmem (by decide)
  have hmcost (off val : UInt256) (t : List UInt256)
      (hawOff : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
      ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = off :: val :: t → memoryExpansionCost s .MSTORE = 0 := by
    intro s haws hstks
    exact mstoreCost_of_stack haws hstks (by rw [hawOff]; simp)
  have hloadCost (off : UInt256) (t : List UInt256)
      (hawOff : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
      ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = off :: t → memoryExpansionCost s .MLOAD = 0 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rw [hawOff]
    simp
  have rd4708pre := evm_run rd4701 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd4705raw⟩ := rd4708pre.sload
    (by clipper_runtime_decode) (by evm_ov)
  have rd4708pre := evm_run rd4705raw with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have haw64 := clipperTakeMemoryWF_mstore_aw mem aw (⟨64⟩ : UInt256) hmem (by decide)
  have rd4709 := rd4708pre.mload 0 ⟨128⟩ aw
    (by clipper_runtime_decode) (hloadCost ⟨64⟩ _ haw64) hbaseMload64 haw64 (by evm_ov)
  have rd4717pre := evm_run rd4709 with [
    raw push4 clipperTakeVatMoveSelectorSeed (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft clipperTakeVatMoveSelectorSeed ⟨224⟩ =
    clipperTakeVatMoveSelectorShifted from rfl] at rd4717pre
  have rd4719 := rd4717pre.mstore 0
    (clipperTakeVatMoveSelectorMem mem) aw (by clipper_runtime_decode)
    (hmcost ⟨128⟩ _ _ haw128) (by rfl) haw128 (by evm_ov)
  have rd4724pre := evm_run rd4719 with [
    raw caller (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide] at rd4724pre
  have rd4725 := rd4724pre.mstore 0
    (clipperTakeVatMoveSenderMem ee mem) aw (by clipper_runtime_decode)
    (hmcost ⟨132⟩ _ _ haw132) (by rfl) haw132 (by evm_ov)
  have rd4740pre := evm_run rd4725 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4740pre
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide] at rd4740pre
  have rd4741 := rd4740pre.mstore 0
    (clipperTakeVatMoveVowMem σ ee mem) aw (by clipper_runtime_decode)
    (hmcost ⟨164⟩ _ _ haw164)
    (by
      rw [show (⟨164⟩ : UInt256).toNat = 164 from by decide]
      simp [clipperTakeVatMoveVowMem, clipperTakeVowTarget, solcSlotWord,
        u256_land_comm]) haw164 (by evm_ov)
  have rd4747pre := evm_run rd4741 with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide] at rd4747pre
  have rd4748 := rd4747pre.mstore 0
    (clipperTakeVatMoveCalldataMem σ ee owe mem) aw (by clipper_runtime_decode)
    (hmcost ⟨196⟩ _ _ haw196) (by rfl) haw196 (by evm_ov)
  have rd4749pre := evm_run rd4748 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd4750 := rd4749pre.mload 0 ⟨128⟩ aw
    (by clipper_runtime_decode) (hloadCost ⟨64⟩ _ haw64) hcallMload64 haw64 (by evm_ov)
  have rd4783 := rd4750.pushConst vatWord (width := 32) (op := .PUSH32)
    (by decide) (by simpa [vatWord] using clipperTakeVatPush32Decode4750 v hpatch)
    (by evm_ov)
  have rd4813 := evm_run rd4783 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperTakeVatMoveSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
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
  rw [show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by native_decide] at rd4813
  rw [show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by native_decide]
    at rd4813
  rw [show (⟨0⟩ : UInt256) + ⟨100⟩ = ⟨100⟩ from by native_decide] at rd4813
  rw [show UInt256.land solcAddrMask vatWord = clipperTakeVatTarget v from by rfl] at rd4813
  exact ⟨_, _, by simpa [clipperTakeVatTarget, vatWord, u256_land_comm] using rd4813⟩

theorem RD.clipperTakeVatMoveNoCodeWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4701 : RD code ee g s0 ⟨4701⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hcodeSizeVat : extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) : RDrev code g s0 := by
  obtain ⟨_, _, rd4813⟩ := RD.clipperTakeVatMoveExtcodesizeGuardWF
    (v := v) (hpatch := hpatch) rd4701 hmem hov
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4813⟩) (okPc := ⟨4825⟩)
    rd4813 hcodeSizeVat
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by simp only [List.length_cons]; omega)

theorem RD.clipperTakeVatMovePostCallWF {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} {aw : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd4813 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4813⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
        clipperTakeVatTarget v :: dog :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperTakeVatMoveCalldataMem σ I owe baseMem) aw rdata (cA, σ) k C)
    (hbaseMem : clipperTakeMemoryWF baseMem aw)
    (hcodeSizeVat : extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zVat : Bool) (outVat : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4829⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperTakeVatMoveSelectorWord ::
          clipperTakeVatTarget v :: dog :: slice :: owe :: tabNew :: lotNew :: price ::
          tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        (clipperTakeVatMoveCalldataMem σ I owe baseMem) aw outVat
        (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "move" 0
        [.address I.source,
          .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
          .int (Int.ofNat owe.toNat)]
        (zVat,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat, substate := A_vat, createdAccounts := cA_vat },
          outVat) true ∧
      outVat.size < UInt256.size ∧
      clipperTakeMemoryWF (clipperTakeVatMoveCalldataMem σ I owe baseMem) aw := by
  obtain ⟨gasWord, _, _, rd4828⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4813⟩) (okPc := ⟨4825⟩)
      rd4813 hcodeSizeVat
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperTakeJumpDest4825 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by simp only [List.length_cons]; omega)
  obtain ⟨cA_vat, σ_vat, zVat, outVat, A_in, callGas, k4829, C4829, hΘpack,
      rd4829raw, houtVatSize⟩ :=
    RD.call rd4828 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_vat, hΘ⟩ := hΘpack
  have hsize := hbaseMem.1
  have hMIn : UInt256.ofNat
      (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat) = aw := by
    apply clipperTakeM_same_of_cover
    rcases hbaseMem with ⟨_, _, hcover, _⟩
    change 228 ≤ aw.toNat * 32
    omega
  have hMOut : UInt256.ofNat
      (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = aw := by
    apply clipperTakeM_same_of_cover
    rcases hbaseMem with ⟨_, _, hcover, _⟩
    change 128 ≤ aw.toNat * 32
    omega
  have hactive : UInt256.ofNat
      (MachineState.M
        (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = aw := by
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
    rw [show MachineState.M
      (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
      (⟨128⟩ : UInt256).toNat 0 =
      MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat by
        simp [MachineState.M]]
    exact hMIn
  refine ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k4829, C4829, ?_, ?_,
    houtVatSize, clipperTakeVatMoveMemoryWF σ I owe hbaseMem⟩
  · have hwrite : outVat.write 0 (clipperTakeVatMoveCalldataMem σ I owe baseMem)
        (⟨128⟩ : UInt256).toNat
        (min (⟨0⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat =
        clipperTakeVatMoveCalldataMem σ I owe baseMem := by
      simpa using clipperTakeZeroReturndataWrite_eq outVat
        (clipperTakeVatMoveCalldataMem σ I owe baseMem)
    rw [hwrite] at rd4829raw
    rw [hactive] at rd4829raw
    simpa using rd4829raw
  · let evmVat : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A I with
        accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v) (evm := evmVat) (name := "move")
      (args :=
        [.address I.source,
          .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
          .int (Int.ofNat owe.toNat)])
      (tgt := EVM.address v.vat) (targetWord := clipperTakeVatTarget v)
      (cA' := cA_vat) (σ' := σ_vat) (A' := A_vat) (A_in := A_in)
      (z := zVat) (o := outVat) (g'' := g'') (callGas := callGas)
      (mem := clipperTakeVatMoveCalldataMem σ I owe baseMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmVat, initState] using h
        rw [hI]
        decide)) ?_ ?_ ?_
    · rw [clipperTakeVatTargetAddress v]
      exact clipperTakeEVMAddressAccountAddress v.vat
    · simpa using clipperTakeVatMoveEncode_eq_ge v σ I owe hsize
    · simpa [evmVat, initState, hperm] using hΘ

end Benchmarks.Dss.Clipper
