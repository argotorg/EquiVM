import Benchmarks.Dss.Clipper.TakeDynamicVatMove

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeDogDigsPrefixWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4850 : RD code ee g s0 ⟨4850⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4898⟩
      (clipperYankIlkWord v :: clipperDogDigsSelectorWord ::
        UInt256.land solcAddrMask dog :: dog :: slice :: owe :: tabNew :: lotNew :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  have rd4860pre := evm_run rd4850 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd4860pre
  have rd4865 := evm_run rd4860pre with [
    raw push4 clipperDogDigsSelectorWord (by clipper_runtime_decode) (by evm_ov)]
  have rd4898 := rd4865.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperTakeIlkPush32Decode4865 v hpatch hilk hlen)
    (by evm_ov)
  exact ⟨_, _, by simpa [clipperYankIlkWord, hilk, ilkWord] using rd4898⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeDogDigsTailWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4915 : RD code ee g s0 ⟨4915⟩
      (owe :: clipperYankIlkWord v :: clipperDogDigsSelectorWord ::
        UInt256.land solcAddrMask dog :: dog :: slice :: owe :: tabNew :: lotNew :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4964⟩
      (UInt256.land solcAddrMask dog :: UInt256.land solcAddrMask dog :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog ::
        dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperDogDigsCalldataMem v owe mem) aw rdata (cA, σ) k' C' := by
  have hmload64 := clipperTakeMemoryWF_mload64 mem aw hmem
  have hcallWF := clipperTakeDogDigsMemoryWF v owe hmem
  have hcallMload64 := clipperTakeMemoryWF_mload64
    (clipperDogDigsCalldataMem v owe mem) aw hcallWF
  have haw64 := clipperTakeMemoryWF_mstore_aw mem aw (⟨64⟩ : UInt256) hmem (by decide)
  have haw128 := clipperTakeMemoryWF_mstore_aw mem aw (⟨128⟩ : UInt256) hmem (by decide)
  have haw132 := clipperTakeMemoryWF_mstore_aw mem aw (⟨132⟩ : UInt256) hmem (by decide)
  have haw164 := clipperTakeMemoryWF_mstore_aw mem aw (⟨164⟩ : UInt256) hmem (by decide)
  have rd4919pre := evm_run rd4915 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4919 := rd4919pre.mload 0 ⟨128⟩ aw
    (by clipper_runtime_decode) (clipperTakeMloadCostZero haw64)
    hmload64 haw64 (by evm_ov)
  have rd4930pre := evm_run rd4919 with [
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ clipperDogDigsSelectorWord)
      ⟨224⟩ = clipperDogDigsSelectorShifted from by native_decide] at rd4930pre
  have rd4930 := rd4930pre.mstore 0 (clipperDogDigsSelectorMem mem) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw128) (by rfl)
    haw128 (by evm_ov)
  have rd4937pre := evm_run rd4930 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by native_decide] at rd4937pre
  have rd4937 := rd4937pre.mstore 0 (clipperDogDigsIlkMem v mem) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw132) (by rfl)
    haw132 (by evm_ov)
  have rd4943pre := evm_run rd4937 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨132⟩ = ⟨164⟩ from by native_decide] at rd4943pre
  have rd4943 := rd4943pre.mstore 0 (clipperDogDigsCalldataMem v owe mem) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw164) (by rfl)
    haw164 (by evm_ov)
  have rd4955pre := evm_run rd4943 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨164⟩ = ⟨196⟩ from by native_decide] at rd4955pre
  have rd4955 := rd4955pre.mload 0 ⟨128⟩ aw
    (by clipper_runtime_decode) (clipperTakeMloadCostZero haw64)
    hcallMload64 haw64 (by evm_ov)
  have rd4964 := evm_run rd4955 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (⟨196⟩ : UInt256) ⟨128⟩ = ⟨68⟩ from by native_decide]
    at rd4964
  exact ⟨_, _, by simpa [u256_land_comm] using rd4964⟩

theorem RD.clipperTakeDogDigsOweCallSetupNonzeroWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4850 : RD code ee g s0 ⟨4850⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hmem : clipperTakeMemoryWF mem aw) (hlotNew : lotNew ≠ ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4964⟩
      (UInt256.land solcAddrMask dog :: UInt256.land solcAddrMask dog :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog ::
        dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperDogDigsCalldataMem v owe mem) aw rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4898⟩ := RD.clipperTakeDogDigsPrefixWF
    (v := v) (hpatch := hpatch) rd4850 hov
  have rd4905pre := evm_run rd4898 with [
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4911⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4906 := rd4905pre.jumpiNT (by clipper_runtime_decode)
    (u256_eq_of_ne (by intro h; exact hlotNew h.symm)) (by evm_ov)
  have rd4910pre := evm_run rd4906 with [
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4915⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4915 := rd4910pre.jump (by clipper_runtime_decode)
    (clipperTakeJumpDest4915 v hpatch) (by evm_ov)
  exact RD.clipperTakeDogDigsTailWF v hpatch rd4915 hmem hov

theorem RD.clipperTakeDogDigsOweCallSetupZeroWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id :
      UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4850 : RD code ee g s0 ⟨4850⟩
      (dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hmem : clipperTakeMemoryWF mem aw) (hlotNew : lotNew = ⟨0⟩)
    (htabNew : tabNew = ⟨0⟩) (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4964⟩
      (UInt256.land solcAddrMask dog :: UInt256.land solcAddrMask dog :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        clipperDogDigsSelectorWord :: UInt256.land solcAddrMask dog ::
        dog :: slice :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: R)
      (clipperDogDigsCalldataMem v owe mem) aw rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4898⟩ := RD.clipperTakeDogDigsPrefixWF
    (v := v) (hpatch := hpatch) rd4850 hov
  have rd4905pre := evm_run rd4898 with [
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw eq (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨4911⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd4911 := rd4905pre.jumpiT (by clipper_runtime_decode)
    (by rw [hlotNew, u256_eq_refl]; decide)
    (clipperTakeJumpDest4911 v hpatch) (by evm_ov)
  have rd4915pre := evm_run rd4911 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨4911⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
    (⟨4915⟩ : UInt256) from by native_decide] at rd4915pre
  rw [htabNew, u256_zero_add] at rd4915pre
  have htail := RD.clipperTakeDogDigsTailWF (tabNew := (⟨0⟩ : UInt256))
    v hpatch rd4915pre hmem hov
  simpa [htabNew] using htail

theorem RD.clipperTakeDogDigsNoCodeWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {target dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max
      amt id : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd4964 : RD code ee g s0 ⟨4964⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: dog :: slice :: owe ::
        tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      mem aw rdata (cA, σ) k C)
    (hcodeSizeDog : extCodeSizeWord σ target = ⟨0⟩)
    (hov : R.length + 32 ≤ 1024) : RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4964⟩) (okPc := ⟨4976⟩)
    rd4964 hcodeSizeDog
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeDogDigsPostCallWF {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {target dog slice owe tabNew lotNew price tic packed stopped dataLen dataStart who max
      amt id : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray} {aw : UInt256}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd4964 : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4964⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨196⟩ :: clipperDogDigsSelectorWord :: target :: dog :: slice :: owe ::
        tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen :: dataStart ::
        who :: max :: amt :: id :: R)
      (clipperDogDigsCalldataMem v owe baseMem) aw rdata (cA, σ) k C)
    (hbaseMem : clipperTakeMemoryWF baseMem aw)
    (hcodeSizeDog : extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hov : R.length + 32 ≤ 1024) :
    ∃ (cA_dog : Batteries.RBSet AccountAddress compare) (σ_dog : AccountMap)
      (zDog : Bool) (outDog : ByteArray) (A_dog : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨4980⟩
        ((if zDog then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: clipperDogDigsSelectorWord ::
          target :: dog :: slice :: owe :: tabNew :: lotNew :: price :: tic ::
          packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: R)
        (clipperDogDigsCalldataMem v owe baseMem) aw outDog (cA_dog, σ_dog) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address (AccountAddress.ofUInt256 target)) "digs" 0
        [v.ilk, .int (Int.ofNat owe.toNat)]
        (zDog,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_dog, substate := A_dog, createdAccounts := cA_dog },
          outDog) true ∧
      outDog.size < UInt256.size ∧
      clipperTakeMemoryWF (clipperDogDigsCalldataMem v owe baseMem) aw := by
  obtain ⟨_, _, _, rd4979⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4964⟩) (okPc := ⟨4976⟩)
      rd4964 hcodeSizeDog
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperTakeJumpDest4976 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by simp only [List.length_cons]; omega)
  obtain ⟨cA_dog, σ_dog, zDog, outDog, A_in, callGas, k4980, C4980, hΘpack,
      rd4980raw, houtDogSize⟩ :=
    RD.call rd4979 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_dog, hΘ⟩ := hΘpack
  have hsize := hbaseMem.1
  have hMIn : UInt256.ofNat
      (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat) = aw := by
    apply clipperTakeM_same_of_cover
    rcases hbaseMem with ⟨_, _, hcover, _⟩
    change 196 ≤ aw.toNat * 32
    omega
  have hactive : UInt256.ofNat
      (MachineState.M
        (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = aw := by
    rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
    rw [show MachineState.M
      (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
      (⟨128⟩ : UInt256).toNat 0 =
      MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat by
        simp [MachineState.M]]
    exact hMIn
  refine ⟨cA_dog, σ_dog, zDog, outDog, A_dog, k4980, C4980, ?_, ?_,
    houtDogSize, clipperTakeDogDigsMemoryWF v owe hbaseMem⟩
  · have hwrite : outDog.write 0 (clipperDogDigsCalldataMem v owe baseMem)
        (⟨128⟩ : UInt256).toNat
        (min (⟨0⟩ : UInt256) (UInt256.ofNat outDog.size)).toNat =
        clipperDogDigsCalldataMem v owe baseMem := by
      simpa using clipperTakeZeroReturndataWrite_eq outDog
        (clipperDogDigsCalldataMem v owe baseMem)
    rw [hwrite, hactive] at rd4980raw
    simpa using rd4980raw
  · let evmDog : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A I with accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v) (evm := evmDog) (name := "digs")
      (args := [v.ilk, .int (Int.ofNat owe.toNat)])
      (tgt := EVM.address (AccountAddress.ofUInt256 target)) (targetWord := target)
      (cA' := cA_dog) (σ' := σ_dog) (A' := A_dog) (A_in := A_in)
      (z := zDog) (o := outDog) (g'' := g'') (callGas := callGas)
      (mem := clipperDogDigsCalldataMem v owe baseMem)
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hI : I.depth = (1024 : Fin 1025) := by
          simpa [evmDog, initState] using h
        rw [hI]
        decide)) ?_ ?_ ?_
    · apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa using clipperTakeDogDigsEncode_eq_ge v owe hsize
    · simpa [evmDog, initState, hperm] using hΘ

end Benchmarks.Dss.Clipper
