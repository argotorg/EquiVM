import Benchmarks.Dss.Clipper.TakeDynamicMemory
import Benchmarks.Dss.Clipper.TakeEvent

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeMemoryWF_mstore_aw_event (mem : ByteArray) (aw off : UInt256)
    (hmem : clipperTakeMemoryWF mem aw) (hoff : off.toNat + 32 ≤ 288) :
    UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw := by
  apply clipperTakeM_same_of_cover
  have hawGe := clipperTakeMemoryWF_aw_ge mem aw hmem
  omega

theorem clipperTakeEventMemoryWF (mem : ByteArray) (aw : UInt256)
    (max price owe tabNew lotNew : UInt256) (hmem : clipperTakeMemoryWF mem aw) :
    clipperTakeMemoryWF (clipperTakeEventMem mem max price owe tabNew lotNew) aw := by
  rcases hmem with ⟨hsize, hread64, hcover, hawSmall⟩
  have h0size : (clipperTakeEventMem0 mem max).size = mem.size := by
    exact clipperTakeWrite32_size_of_end_le mem max 128 (by omega)
  have h1size : (clipperTakeEventMem1 mem max price).size = mem.size := by
    unfold clipperTakeEventMem1
    rw [clipperTakeWrite32_size_of_end_le]
    · exact h0size
    · rw [h0size]
      omega
  have h2size : (clipperTakeEventMem2 mem max price owe).size = mem.size := by
    unfold clipperTakeEventMem2
    rw [clipperTakeWrite32_size_of_end_le]
    · exact h1size
    · rw [h1size]
      omega
  have h3size : (clipperTakeEventMem3 mem max price owe tabNew).size = mem.size := by
    unfold clipperTakeEventMem3
    rw [clipperTakeWrite32_size_of_end_le]
    · exact h2size
    · rw [h2size]
      omega
  have hfinalSize :
      (clipperTakeEventMem mem max price owe tabNew lotNew).size =
        Nat.max mem.size 288 := by
    unfold clipperTakeEventMem
    exact toByteArray_write32_size_of_le
      (clipperTakeEventMem3 mem max price owe tabNew) lotNew 256 mem.size
      (Nat.max mem.size 288) h3size (by rw [h3size]; omega) rfl
  have hfinalRead :
      (clipperTakeEventMem mem max price owe tabNew lotNew).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    unfold clipperTakeEventMem clipperTakeEventMem3 clipperTakeEventMem2
      clipperTakeEventMem1 clipperTakeEventMem0
    rw [toByteArray_write_read_below_of_gap lotNew _ 256 64
      (by rw [h3size]; omega) (by omega) (by rw [h3size]; apply lt_usize; omega)]
    rw [toByteArray_write_read_below_of_gap tabNew _ 224 64
      (by rw [h2size]; omega) (by omega) (by rw [h2size]; apply lt_usize; omega)]
    rw [toByteArray_write_read_below_of_gap owe _ 192 64
      (by rw [h1size]; omega) (by omega) (by rw [h1size]; apply lt_usize; omega)]
    rw [toByteArray_write_read_below_of_gap price _ 160 64
      (by rw [h0size]; omega) (by omega) (by rw [h0size]; apply lt_usize; omega)]
    rw [toByteArray_write_read_below_of_gap max _ 128 64
      (by omega) (by omega) (by apply lt_usize; omega)]
    exact hread64
  refine ⟨?_, hfinalRead, ?_, hawSmall⟩
  · rw [hfinalSize]
    exact le_trans hsize (Nat.le_max_left _ _)
  · rw [hfinalSize]
    have hawGe : 9 ≤ aw.toNat := by
      exact clipperTakeMemoryWF_aw_ge mem aw ⟨hsize, hread64, hcover, hawSmall⟩
    exact (Nat.max_le).2 ⟨hcover, by omega⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeEventTailSuccessWF {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5250⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hmem : clipperTakeMemoryWF mem aw)
    (hperm : ee.perm = true) :
    RDret code g s0 (cA, sstoreAccountMap ee.codeOwner σ ⟨13⟩ ⟨0⟩) ByteArray.empty := by
  let eventTopic : UInt256 :=
    ⟨2662707474673484271508566864567884168301912169458095775925153504702713661105⟩
  have haw64 := clipperTakeMemoryWF_mstore_aw_event mem aw (⟨64⟩ : UInt256) hmem
    (by decide)
  have haw128 := clipperTakeMemoryWF_mstore_aw_event mem aw (⟨128⟩ : UInt256) hmem
    (by decide)
  have haw160 := clipperTakeMemoryWF_mstore_aw_event mem aw (⟨160⟩ : UInt256) hmem
    (by decide)
  have haw192 := clipperTakeMemoryWF_mstore_aw_event mem aw (⟨192⟩ : UInt256) hmem
    (by decide)
  have haw224 := clipperTakeMemoryWF_mstore_aw_event mem aw (⟨224⟩ : UInt256) hmem
    (by decide)
  have haw256 := clipperTakeMemoryWF_mstore_aw_event mem aw (⟨256⟩ : UInt256) hmem
    (by decide)
  have hmload64 := clipperTakeMemoryWF_mload64 mem aw hmem
  have rd5254pre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have rd5255 := rd5254pre.mload 0 ⟨128⟩ aw
    (by clipper_runtime_decode) (clipperTakeMloadCostZero haw64) hmload64 haw64 (by evm_ov)
  have rd5257pre := evm_run rd5255 with [
    raw dup13 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5258 := rd5257pre.mstore 0 (clipperTakeEventMem0 mem max) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw128) (by rfl) haw128
    (by evm_ov)
  have rd5264pre := evm_run rd5258 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ from by native_decide] at rd5264pre
  have rd5265 := rd5264pre.mstore 0 (clipperTakeEventMem1 mem max price) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw160) (by rfl) haw160
    (by evm_ov)
  have rd5270pre := evm_run rd5265 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨64⟩ : UInt256) + ⟨128⟩ = ⟨192⟩ from by native_decide] at rd5270pre
  have rd5271 := rd5270pre.mstore 0 (clipperTakeEventMem2 mem max price owe) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw192) (by rfl) haw192
    (by evm_ov)
  have rd5277pre := evm_run rd5271 with [
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ from by native_decide] at rd5277pre
  have rd5278 := rd5277pre.mstore 0 (clipperTakeEventMem3 mem max price owe tabNew) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw224) (by rfl) haw224
    (by evm_ov)
  have rd5284pre := evm_run rd5278 with [
    raw push1 ⟨128⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨128⟩ = ⟨256⟩ from by native_decide] at rd5284pre
  have rd5285 := rd5284pre.mstore 0
    (clipperTakeEventMem mem max price owe tabNew lotNew) aw
    (by clipper_runtime_decode) (clipperTakeMstoreCostZero haw256) (by rfl) haw256
    (by evm_ov)
  have hEventWF := clipperTakeEventMemoryWF mem aw max price owe tabNew lotNew hmem
  have hmloadEvent64 := clipperTakeMemoryWF_mload64
    (clipperTakeEventMem mem max price owe tabNew lotNew) aw hEventWF
  have rd5287pre := evm_run rd5285 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd5288 := rd5287pre.mload 0 ⟨128⟩ aw
    (by clipper_runtime_decode) (clipperTakeMloadCostZero haw64) hmloadEvent64 haw64
    (by evm_ov)
  have rd5298pre := evm_run rd5288 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup9 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5299pre0 := RD.clipperDup16 rd5298pre
    (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5299pre := evm_run rd5299pre0 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd5299pre
  have rd5333 := rd5299pre.pushConst eventTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by simpa [eventTopic] using
      (show decode code ⟨5300⟩ = some (.PUSH32, some (eventTopic, 32)) by
        clipper_runtime_decode))
    (by evm_ov)
  have rd5341pre := evm_run rd5333 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have hawLog : UInt256.ofNat (MachineState.M aw.toNat 128 160) = aw := by
    simpa using clipperTakeM_same_of_cover aw (⟨128⟩ : UInt256) 160 (by
      change 128 + 160 ≤ aw.toNat * 32
      have hawGe := clipperTakeMemoryWF_aw_ge mem aw hmem
      omega)
  have rd5342 := RD.log3 0 aw rd5341pre
    (by clipper_runtime_decode) hperm
    (by
      intro s hawEq hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      rw [show ((⟨160⟩ : UInt256) + UInt256.sub ⟨128⟩ ⟨128⟩).toNat = 160 by
        native_decide]
      change Cₘ (UInt256.ofNat (MachineState.M aw.toNat 128 160)) - Cₘ aw = 0
      rw [hawLog]
      simp)
    hawLog
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5348pre := evm_run rd5342 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5349⟩ := rd5348pre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5360 := evm_run rd5349 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd502 := rd5360.jump (by clipper_runtime_decode)
    (clipperRelyReturnJumpDest v hpatch) (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_decode) (by evm_ov)
  exact RD.stop rd503 (by clipper_decode) (by evm_ov)

end Benchmarks.Dss.Clipper
