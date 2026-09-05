import Benchmarks.Dss.Clipper.TakeDynamicEvent
import Benchmarks.Dss.Clipper.TakeOweVatFlux

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeRemoveJoinMemoryWF (id : UInt256)
    {mem : ByteArray} {aw : UInt256} (hmem : clipperTakeMemoryWF mem aw) :
    let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
    let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
    let saleHashMem := twoWordHashMem id ⟨12⟩ activeMem
    let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
    let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
    let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
    clipperTakeMemoryWF saleHashMem aw5 := by
  dsimp only
  have haw0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw :=
    clipperTakeMemoryWF_mstore_aw mem aw ⟨0⟩ hmem (by decide)
  have haw32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw :=
    clipperTakeMemoryWF_mstore_aw mem aw ⟨32⟩ hmem (by decide)
  have haw64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
    simpa using clipperTakeM_same_of_cover aw (⟨0⟩ : UInt256) 64 (by
      change 64 ≤ aw.toNat * 32
      have hawGe := clipperTakeMemoryWF_aw_ge mem aw hmem
      omega)
  rw [haw0, haw0, haw0, haw32, haw64]
  exact clipperTakeTwoWordHashMemoryWF id ⟨12⟩
    (clipperTakeWordAt0MemoryWF ⟨11⟩ hmem)

theorem clipperTakeRemoveIdNeMoveMemoryWF (id move : UInt256)
    {mem : ByteArray} {aw : UInt256} (hmem : clipperTakeMemoryWF mem aw) :
    let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
    let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
    let saleHashMem := twoWordHashMem id ⟨12⟩ activeMem
    let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
    let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
    let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
    let activeIndexMem := wordAt0Mem (⟨11⟩ : UInt256) saleHashMem
    let aw6 := UInt256.ofNat (MachineState.M aw5.toNat 0 32)
    let aw7 := UInt256.ofNat (MachineState.M aw6.toNat 0 32)
    let aw8 := UInt256.ofNat (MachineState.M aw7.toNat 0 32)
    let moveHashMem := twoWordHashMem move ⟨12⟩ activeIndexMem
    let aw9 := UInt256.ofNat (MachineState.M aw8.toNat 32 32)
    let aw10 := UInt256.ofNat (MachineState.M aw9.toNat 0 64)
    clipperTakeMemoryWF moveHashMem aw10 := by
  dsimp only
  have haw0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw :=
    clipperTakeMemoryWF_mstore_aw mem aw ⟨0⟩ hmem (by decide)
  have haw32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw :=
    clipperTakeMemoryWF_mstore_aw mem aw ⟨32⟩ hmem (by decide)
  have haw64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
    simpa using clipperTakeM_same_of_cover aw (⟨0⟩ : UInt256) 64 (by
      change 64 ≤ aw.toNat * 32
      have hawGe := clipperTakeMemoryWF_aw_ge mem aw hmem
      omega)
  simp only [haw0, haw32, haw64]
  exact clipperTakeTwoWordHashMemoryWF move ⟨12⟩
    (clipperTakeWordAt0MemoryWF ⟨11⟩
      (clipperTakeTwoWordHashMemoryWF id ⟨12⟩
        (clipperTakeWordAt0MemoryWF ⟨11⟩ hmem)))

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeRemoveJoinToReturnSuccessWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {move owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8379⟩
      (move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price ::
        tic :: packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hmem : clipperTakeMemoryWF mem aw)
    (hperm : ee.perm = true) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner (clipperYankRemoveAccountMap σ ee lastIndex)
        ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  intro lastIndex
  obtain ⟨k5250, C5250, rd5250⟩ :=
    RD.clipperTakeRemoveJoinToEventTail (v := v) (hpatch := hpatch) rd hlen
      (by
        have hactive := clipperTakeWordAt0MemoryWF (⟨11⟩ : UInt256) hmem
        exact le_trans (by decide : 64 ≤ 260) hactive.1)
      hperm
  have htailMem := clipperTakeRemoveJoinMemoryWF (clipperYankArgWord ee) hmem
  exact RD.clipperTakeEventTailSuccessWF (v := v) (hpatch := hpatch)
    (σ := clipperYankRemoveAccountMap σ ee lastIndex)
    (by simpa [lastIndex] using rd5250)
    (by simpa using htailMem) hperm

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakePostDogLotNonzeroTabNonzeroToEventTailWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5025⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw o (cA, σ) k C)
    (htabNew : tabNew ≠ ⟨0⟩)
    (hmem : clipperTakeMemoryWF mem aw)
    (hperm : ee.perm = true) :
    ∃ k' C', RD code ee g s0 ⟨5250⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      (twoWordHashMem id ⟨12⟩ mem) aw o
      (cA,
        sstoreAccountMap ee.codeOwner
          (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨12⟩ id + ⟨1⟩) tabNew)
          (solcMappingSlot ⟨12⟩ id + ⟨2⟩) lotNew)
      k' C' := by
  have h5222 : (D_J code 0).contains (⟨5222⟩ : UInt256) = true := by
    apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
    unfold patches patchesFrom offsets immValues
    simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
    cases hIlk : wordBytes? v.ilk with
    | none => simp [hIlk]; native_decide
    | some bs => simp [hIlk]; native_decide
  have haw0 := clipperTakeMemoryWF_mstore_aw mem aw (⟨0⟩ : UInt256) hmem (by decide)
  have haw32 := clipperTakeMemoryWF_mstore_aw mem aw (⟨32⟩ : UInt256) hmem (by decide)
  have haw64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
    simpa using clipperTakeM_same_of_cover aw (⟨0⟩ : UInt256) 64 (by
      change 64 ≤ aw.toNat * 32
      have hawGe := clipperTakeMemoryWF_aw_ge mem aw hmem
      omega)
  have rd5030pre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5222⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd5222 := rd5030pre.jumpiT (by clipper_runtime_decode) htabNew h5222 (by evm_ov)
  have rd5227pre := evm_run rd5222 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup14 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5227 := rd5227pre.mstore 0 (wordAt0Mem id mem) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw0) (by rfl) haw0 (by evm_ov)
  have rd5232pre := evm_run rd5227 with [
    raw push1 ⟨12⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd5232 := rd5232pre.mstore 0 (twoWordHashMem id ⟨12⟩ mem) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw32) (by rfl) haw32
    (by evm_ov)
  have hsalesBase :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((twoWordHashMem id ⟨12⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨12⟩ id := by
    rw [clipperYankTwoWordHashMem_read0_64_of_ge id ⟨12⟩
      (le_trans (by decide : 64 ≤ 260) hmem.1)]
    unfold solcMappingSlot
    exact mappingSlot_single id ⟨12⟩
  have rd5236pre := evm_run rd5232 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd5236 := rd5236pre.keccak256 0 (solcMappingSlot ⟨12⟩ id) aw
    (by clipper_runtime_decode)
    (by
      intro s hawEq hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
      change Cₘ (UInt256.ofNat (MachineState.M aw.toNat 0 64)) - Cₘ aw = 0
      rw [haw64]
      simp)
    hsalesBase haw64 (by evm_ov)
  have rd5243pre := evm_run rd5236 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k5244, C5244, rd5244raw⟩ :=
    rd5243pre.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  have rd5244 : RD code ee g s0 ⟨5244⟩
      (solcMappingSlot ⟨12⟩ id :: owe :: tabNew :: lotNew :: price :: tic ::
        packed :: stopped :: dataLen :: dataStart :: who :: max :: amt :: id ::
        [⟨502⟩, sel])
      (twoWordHashMem id ⟨12⟩ mem) aw o
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨12⟩ id + ⟨1⟩) tabNew)
      k5244 C5244 := by
    simpa using rd5244raw
  have rd5249pre := evm_run rd5244 with [
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨k5250, C5250, rd5250raw⟩ :=
    rd5249pre.sstore hperm (by clipper_runtime_decode) (by evm_ov)
  rw [u256_add_comm ⟨2⟩ (solcMappingSlot ⟨12⟩ id)] at rd5250raw
  exact ⟨k5250, C5250, by simpa using rd5250raw⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakePostDogLotNonzeroTabNonzeroToReturnSuccessWF {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5025⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw o (cA, σ) k C)
    (htabNew : tabNew ≠ ⟨0⟩)
    (hmem : clipperTakeMemoryWF mem aw)
    (hperm : ee.perm = true) :
    RDret code g s0
      (cA,
        sstoreAccountMap ee.codeOwner
          (sstoreAccountMap ee.codeOwner
            (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨12⟩ id + ⟨1⟩) tabNew)
            (solcMappingSlot ⟨12⟩ id + ⟨2⟩) lotNew)
          ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨k5250, C5250, rd5250⟩ :=
    RD.clipperTakePostDogLotNonzeroTabNonzeroToEventTailWF
      (v := v) (hpatch := hpatch) rd htabNew hmem hperm
  exact RD.clipperTakeEventTailSuccessWF (v := v) (hpatch := hpatch) rd5250
    (clipperTakeTwoWordHashMemoryWF id ⟨12⟩ hmem) hperm

end Benchmarks.Dss.Clipper
