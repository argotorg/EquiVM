import Benchmarks.Dss.Clipper.TakePostDogFlux

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem RD.clipperTakeRemoveEmptyInvalid
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who maxArg amt sel : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8274⟩
      (clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ = ⟨0⟩) :
    RDinvalid code g s0 := by
  have rd8277 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8279⟩ := rd8277.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8294 := evm_run rd8279 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw not (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8296⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hcond :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) = ⟨0⟩ := by
    rw [hlen]
    native_decide
  exact RD.invalidHalt
    (rd8294.jumpiNT (by clipper_yank_remove_decode)
      (by simpa [solcSlotWord] using hcond) (by evm_ov))
    (by clipper_yank_remove_decode)


set_option maxHeartbeats 4000000 in
theorem RD.clipperTakeRemoveIdNeMoveToJoin
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who maxArg amt sel : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8274⟩
      (clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hne :
      let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
      clipperYankArgWord ee ≠ solcSlotWord σ ee (clipperYankActiveSlot lastIndex))
    (hactiveMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem).size)
    (hidxBound :
      (solcSlotWord σ ee (clipperYankSalesPosSlot ee)).toNat <
        (solcSlotWord σ ee ⟨11⟩).toNat)
    (hperm : ee.perm = true) :
    let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
    let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
    let idx := solcSlotWord σ ee (clipperYankSalesPosSlot ee)
    ∃ mem' aw' k' C',
      RD code ee g s0 ⟨8379⟩
        (move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt :: clipperYankArgWord ee :: ⟨502⟩ ::
          [sel])
        mem' aw' o (cA, clipperYankMoveAccountMap σ ee idx move) k' C' ∧
      64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem').size := by
  intro lastIndex move idx
  let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
  let saleKeyMem := wordAt0Mem (clipperYankArgWord ee) activeMem
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
  let saleHashMem := twoWordHashMem (clipperYankArgWord ee) ⟨12⟩ activeMem
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
  let activeIndexMem := wordAt0Mem (⟨11⟩ : UInt256) saleHashMem
  let aw6 := UInt256.ofNat (MachineState.M aw5.toNat 0 32)
  let aw7 := UInt256.ofNat (MachineState.M aw6.toNat 0 32)
  let σIndex := sstoreAccountMap ee.codeOwner σ (clipperYankActiveSlot idx) move
  let moveKeyMem := wordAt0Mem move activeIndexMem
  let aw8 := UInt256.ofNat (MachineState.M aw7.toNat 0 32)
  let moveHashMem := twoWordHashMem move ⟨12⟩ activeIndexMem
  let aw9 := UInt256.ofNat (MachineState.M aw8.toNat 32 32)
  let aw10 := UInt256.ofNat (MachineState.M aw9.toNat 0 64)
  have rd8277 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8279⟩ := rd8277.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8294 := evm_run rd8279 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw not (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8296⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hcond :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) = ⟨1⟩ :=
    clipperYankNonzeroLenPredLt (solcSlotWord σ ee ⟨11⟩) hlen
  have hcondNe :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) ≠ ⟨0⟩ := by
    rw [hcond]
    native_decide
  have rd8296 := rd8294.jumpiT (by clipper_yank_remove_decode)
    (by simpa [solcSlotWord] using hcondNe)
    (clipperYankJumpDest8296 v hpatch) (by evm_ov)
  have rd8300 := evm_run rd8296 with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8301 := rd8300.mstore (Cₘ aw1 - Cₘ aw) activeMem aw1
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw1]))
    (by simpa [activeMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (activeMem.readWithPadding 0 32))) =
        activeDataSlot := by
    simpa [activeMem, activeDataSlot,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) mem).trans
        (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))
  have rd8305 := evm_run rd8301 with [
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8306 := rd8305.keccak256 (Cₘ aw2 - Cₘ aw1) activeDataSlot aw2
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw2,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide])
    hslot (by rfl) (by evm_ov)
  have rd8307pre := evm_run rd8306 with [
    raw add (by clipper_yank_remove_decode) (by evm_ov)]
  have hslotActive :
      activeDataSlot + (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩) =
        clipperYankActiveSlot lastIndex := by
    simpa [lastIndex, clipperYankActiveSlot_eq]
  have hslotActive' :
      UInt256.lnot ⟨0⟩ + (solcSlotWord σ ee ⟨11⟩ + activeDataSlot) =
        clipperYankActiveSlot lastIndex := by
    rw [← u256_add_assoc]
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) (solcSlotWord σ ee ⟨11⟩)]
    rw [u256_add_assoc]
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) activeDataSlot]
    rw [← u256_add_assoc]
    rw [u256_add_comm (solcSlotWord σ ee ⟨11⟩) activeDataSlot]
    rw [u256_add_assoc]
    exact hslotActive
  obtain ⟨k8307, C8307, rd8307slot⟩ :
      ∃ k C, RD code ee g s0 ⟨8307⟩
        (clipperYankActiveSlot lastIndex :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord, hslotActive] using rd8307pre⟩
  obtain ⟨_, _, rd8308raw⟩ := rd8307slot.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8308, C8308, rd8308⟩ :
      ∃ k C, RD code ee g s0 ⟨8308⟩
        (move :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [move, solcSlotWord] using rd8308raw⟩
  have rd8312 := evm_run rd8308 with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw pop (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw eq (by clipper_yank_remove_decode) (by evm_ov)]
  have hneMove : clipperYankArgWord ee ≠ move := by
    simpa [lastIndex, move] using hne
  have hneCond : UInt256.eq (clipperYankArgWord ee) move = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (by
      intro hEqOne
      exact hneMove (uInt256_eq_one_eq hEqOne))
  have rd8316 := evm_run rd8312 with [
    raw push2 ⟨8379⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8317 := rd8316.jumpiNT (by clipper_yank_remove_decode)
    (by simpa using hneCond) (by evm_ov)
  have rd8321pre := evm_run rd8317 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8322 := rd8321pre.mstore (Cₘ aw3 - Cₘ aw2) saleKeyMem aw3
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw3]))
    (by simpa [saleKeyMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have rd8326pre := evm_run rd8322 with [
    raw push1 ⟨12⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8327 := rd8326pre.mstore (Cₘ aw4 - Cₘ aw3) saleHashMem aw4
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by
        simp [aw4, show (⟨32⟩ : UInt256).toNat = 32 from by decide]))
    (by rfl) (by rfl) (by evm_ov)
  have hsalesBase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (saleHashMem.readWithPadding 0 64))) =
        clipperYankSalesBaseSlot ee := by
    change
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((twoWordHashMem (clipperYankArgWord ee) (⟨12⟩ : UInt256) activeMem).readWithPadding
                0 64))) =
        clipperYankSalesBaseSlot ee
    rw [clipperYankTwoWordHashMem_read0_64_of_ge
      (clipperYankArgWord ee) (⟨12⟩ : UInt256) (by
        simpa [activeMem] using hactiveMemSize)]
    rw [clipperYankSalesBaseSlot_eq ee]
    exact mappingSlot_single (clipperYankArgWord ee) ⟨12⟩
  have rd8330pre := evm_run rd8327 with [
    raw push1 ⟨64⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8331pre := rd8330pre.keccak256 (Cₘ aw5 - Cₘ aw4) (clipperYankSalesBaseSlot ee) aw5
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw5,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    hsalesBase (by rfl) (by evm_ov)
  obtain ⟨_, _, rd8332raw⟩ := rd8331pre.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8332, C8332, rd8332⟩ :
      ∃ k C, RD code ee g s0 ⟨8332⟩
        (idx :: move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt :: clipperYankArgWord ee :: ⟨502⟩ ::
          [sel])
        saleHashMem aw5 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [idx, clipperYankSalesPosSlot, solcSlotWord] using rd8332raw⟩
  have rd8346 := evm_run rd8332 with [
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8336raw⟩ := rd8346.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8347pre := evm_run rd8336raw with [
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8348⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hidxCond : UInt256.lt idx (solcSlotWord σ ee ⟨11⟩) ≠ ⟨0⟩ := by
    rw [ult_one hidxBound]
    native_decide
  have rd8348 := rd8347pre.jumpiT (by clipper_yank_remove_decode)
    (by simpa [idx, solcSlotWord] using hidxCond)
    (clipperYankJumpDest8348 v hpatch) (by evm_ov)
  have rd8352pre := evm_run rd8348 with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8353 := rd8352pre.mstore (Cₘ aw6 - Cₘ aw5) activeIndexMem aw6
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw6]))
    (by simpa [activeIndexMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have hactiveBase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (activeIndexMem.readWithPadding 0 32))) =
        activeDataSlot := by
    simpa [activeIndexMem, activeDataSlot,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) saleHashMem).trans
        (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))
  have rd8358pre := evm_run rd8353 with [
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8359pre := rd8358pre.keccak256 (Cₘ aw7 - Cₘ aw6) activeDataSlot aw7
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw7,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide])
    hactiveBase (by rfl) (by evm_ov)
  have rd8365pre := evm_run rd8359pre with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap3 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨k8366, C8366, rd8366⟩ :
      ∃ k C, RD code ee g s0 ⟨8366⟩
        (⟨0⟩ :: ⟨32⟩ :: idx :: move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeIndexMem aw7 o (cA, σIndex) k C := by
    obtain ⟨k', C', rd'⟩ := rd8365pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by
      simpa [σIndex, clipperYankActiveSlot_eq, u256_add_comm activeDataSlot idx] using rd'⟩
  have rd8368pre := evm_run rd8366 with [
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8369 := rd8368pre.mstore (Cₘ aw8 - Cₘ aw7) moveKeyMem aw8
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw8]))
    (by simpa [moveKeyMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have rd8373pre := evm_run rd8369 with [
    raw push1 ⟨12⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8374 := rd8373pre.mstore (Cₘ aw9 - Cₘ aw8) moveHashMem aw9
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by
        simp [aw9, show (⟨32⟩ : UInt256).toNat = 32 from by decide]))
    (by rfl) (by rfl) (by evm_ov)
  have hsaleHashMemSize : 64 ≤ saleHashMem.size := by
    unfold saleHashMem twoWordHashMem wordAt32Mem
    exact toByteArray_write_size_ge_off_add32 (⟨12⟩ : UInt256)
      (wordAt0Mem (clipperYankArgWord ee) activeMem) 32 (by
        have hkeySize : 64 ≤ (wordAt0Mem (clipperYankArgWord ee) activeMem).size := by
          have hactiveMemSize' : 64 ≤ activeMem.size := by
            simpa [activeMem] using hactiveMemSize
          have hsizeEq :
              (wordAt0Mem (clipperYankArgWord ee) activeMem).size =
                max activeMem.size (0 + 32) := by
            simpa [wordAt0Mem, Reasoning.Theory.writeWord] using
              (Reasoning.Theory.writeWord_size activeMem 0 (clipperYankArgWord ee) (by
                simpa using lt_usize 0 (by norm_num)))
          rw [hsizeEq]
          exact le_trans hactiveMemSize' (Nat.le_max_left _ _)
        have hzero :
            32 - (wordAt0Mem (clipperYankArgWord ee) activeMem).size = 0 := by
          omega
        rw [hzero]
        exact lt_usize 0 (by norm_num))
  have hactiveIndexMemSize : 64 ≤ activeIndexMem.size := by
    have hsizeEq : activeIndexMem.size = max saleHashMem.size (0 + 32) := by
      simpa [activeIndexMem, wordAt0Mem, Reasoning.Theory.writeWord] using
        (Reasoning.Theory.writeWord_size saleHashMem 0 (⟨11⟩ : UInt256) (by
          simpa using lt_usize 0 (by norm_num)))
    rw [hsizeEq]
    exact le_trans hsaleHashMemSize (Nat.le_max_left _ _)
  have hmoveKeyMemSize : 64 ≤ moveKeyMem.size := by
    have hsizeEq : moveKeyMem.size = max activeIndexMem.size (0 + 32) := by
      simpa [moveKeyMem, wordAt0Mem, Reasoning.Theory.writeWord] using
        (Reasoning.Theory.writeWord_size activeIndexMem 0 move (by
          simpa using lt_usize 0 (by norm_num)))
    rw [hsizeEq]
    exact le_trans hactiveIndexMemSize (Nat.le_max_left _ _)
  have hmoveBase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (moveHashMem.readWithPadding 0 64))) =
        clipperYankSalesMovePosSlot move := by
    change
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((twoWordHashMem move (⟨12⟩ : UInt256) activeIndexMem).readWithPadding 0 64))) =
        clipperYankSalesMovePosSlot move
    rw [clipperYankTwoWordHashMem_read0_64_of_ge move (⟨12⟩ : UInt256)
      hactiveIndexMemSize]
    rw [mappingSlot_single move ⟨12⟩]
    unfold clipperYankSalesMovePosSlot clipperYankSalesBaseSlotOfWord salesBase mapSlot
    rw [keyValueToWord_uint256]
  have rd8377pre := evm_run rd8374 with [
    raw push1 ⟨64⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8378pre := rd8377pre.keccak256 (Cₘ aw10 - Cₘ aw9)
    (clipperYankSalesMovePosSlot move) aw10
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw10,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    hmoveBase (by rfl) (by evm_ov)
  obtain ⟨k8379, C8379, rd8379raw⟩ :
      ∃ k C, RD code ee g s0 ⟨8379⟩
        (move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt :: clipperYankArgWord ee :: ⟨502⟩ ::
          [sel])
        moveHashMem aw10 o (cA, clipperYankMoveAccountMap σ ee idx move) k C := by
    obtain ⟨k', C', rd'⟩ := rd8378pre.sstore hperm (by clipper_yank_remove_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    exact ⟨k', C', by
      simpa [clipperYankMoveAccountMap, σIndex] using rd'⟩
  have hmoveHashSize : 64 ≤ moveHashMem.size := by
    unfold moveHashMem twoWordHashMem wordAt32Mem
    exact toByteArray_write_size_ge_off_add32 (⟨12⟩ : UInt256)
      (wordAt0Mem move activeIndexMem) 32 (by
        have hzero : 32 - (wordAt0Mem move activeIndexMem).size = 0 := by
          have hkeySize : 64 ≤ (wordAt0Mem move activeIndexMem).size := by
            simpa [moveKeyMem] using hmoveKeyMemSize
          omega
        rw [hzero]
        exact lt_usize 0 (by norm_num))
  have hjoinMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) moveHashMem).size := by
    have hsizeEq :
        (wordAt0Mem (⟨11⟩ : UInt256) moveHashMem).size =
          max moveHashMem.size (0 + 32) := by
      simpa [wordAt0Mem, Reasoning.Theory.writeWord] using
        (Reasoning.Theory.writeWord_size moveHashMem 0 (⟨11⟩ : UInt256) (by
          simpa using lt_usize 0 (by norm_num)))
    rw [hsizeEq]
    exact le_trans hmoveHashSize (Nat.le_max_left _ _)
  exact ⟨moveHashMem, aw10, k8379, C8379, rd8379raw, hjoinMemSize⟩

set_option maxHeartbeats 4000000 in

theorem RD.clipperTakeRemoveIdNeMoveIndexOobInvalid
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who maxArg amt sel : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8274⟩
      (clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ ≠ ⟨0⟩)
    (hne :
      let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
      clipperYankArgWord ee ≠ solcSlotWord σ ee (clipperYankActiveSlot lastIndex))
    (hactiveMemSize : 64 ≤ (wordAt0Mem (⟨11⟩ : UInt256) mem).size)
    (hidxBound :
      (solcSlotWord σ ee ⟨11⟩).toNat ≤
        (solcSlotWord σ ee (clipperYankSalesPosSlot ee)).toNat) :
    RDinvalid code g s0 := by
  let lastIndex := solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩
  let move := solcSlotWord σ ee (clipperYankActiveSlot lastIndex)
  let idx := solcSlotWord σ ee (clipperYankSalesPosSlot ee)
  let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
  let saleKeyMem := wordAt0Mem (clipperYankArgWord ee) activeMem
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
  let saleHashMem := twoWordHashMem (clipperYankArgWord ee) ⟨12⟩ activeMem
  let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
  let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
  have rd8277 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8279⟩ := rd8277.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8294 := evm_run rd8279 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw not (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw add (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8296⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hcond :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) = ⟨1⟩ :=
    clipperYankNonzeroLenPredLt (solcSlotWord σ ee ⟨11⟩) hlen
  have hcondNe :
      UInt256.lt (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩)
        (solcSlotWord σ ee ⟨11⟩) ≠ ⟨0⟩ := by
    rw [hcond]
    native_decide
  have rd8296 := rd8294.jumpiT (by clipper_yank_remove_decode)
    (by simpa [solcSlotWord] using hcondNe)
    (clipperYankJumpDest8296 v hpatch) (by evm_ov)
  have rd8300 := evm_run rd8296 with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8301 := rd8300.mstore (Cₘ aw1 - Cₘ aw) activeMem aw1
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw1]))
    (by simpa [activeMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (activeMem.readWithPadding 0 32))) =
        activeDataSlot := by
    simpa [activeMem, activeDataSlot,
      show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) mem).trans
        (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))
  have rd8305 := evm_run rd8301 with [
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8306 := rd8305.keccak256 (Cₘ aw2 - Cₘ aw1) activeDataSlot aw2
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw2,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by decide])
    hslot (by rfl) (by evm_ov)
  have rd8307pre := evm_run rd8306 with [
    raw add (by clipper_yank_remove_decode) (by evm_ov)]
  have hslotActive :
      activeDataSlot + (solcSlotWord σ ee ⟨11⟩ + UInt256.lnot ⟨0⟩) =
        clipperYankActiveSlot lastIndex := by
    simpa [lastIndex, clipperYankActiveSlot_eq]
  obtain ⟨k8307, C8307, rd8307slot⟩ :
      ∃ k C, RD code ee g s0 ⟨8307⟩
        (clipperYankActiveSlot lastIndex :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord, hslotActive] using rd8307pre⟩
  obtain ⟨_, _, rd8308raw⟩ := rd8307slot.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8308, C8308, rd8308⟩ :
      ∃ k C, RD code ee g s0 ⟨8308⟩
        (move :: ⟨0⟩ :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt ::
          clipperYankArgWord ee :: ⟨502⟩ :: [sel])
        activeMem aw2 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [move, solcSlotWord] using rd8308raw⟩
  have rd8312 := evm_run rd8308 with [
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw pop (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw eq (by clipper_yank_remove_decode) (by evm_ov)]
  have hneMove : clipperYankArgWord ee ≠ move := by
    simpa [lastIndex, move] using hne
  have hneCond : UInt256.eq (clipperYankArgWord ee) move = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (by
      intro hEqOne
      exact hneMove (uInt256_eq_one_eq hEqOne))
  have rd8316 := evm_run rd8312 with [
    raw push2 ⟨8379⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8317 := rd8316.jumpiNT (by clipper_yank_remove_decode)
    (by simpa using hneCond) (by evm_ov)
  have rd8321pre := evm_run rd8317 with [
    raw push1 ⟨0⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup3 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8322 := rd8321pre.mstore (Cₘ aw3 - Cₘ aw2) saleKeyMem aw3
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by simp [aw3]))
    (by simpa [saleKeyMem, wordAt0Mem]) (by rfl) (by evm_ov)
  have rd8326pre := evm_run rd8322 with [
    raw push1 ⟨12⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8327 := rd8326pre.mstore (Cₘ aw4 - Cₘ aw3) saleHashMem aw4
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      exact mstoreCost_of_stack hawEq hstk (by
        simp [aw4, show (⟨32⟩ : UInt256).toNat = 32 from by decide]))
    (by rfl) (by rfl) (by evm_ov)
  have hsalesBase :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (saleHashMem.readWithPadding 0 64))) =
        clipperYankSalesBaseSlot ee := by
    change
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC
              ((twoWordHashMem (clipperYankArgWord ee) (⟨12⟩ : UInt256) activeMem).readWithPadding
                0 64))) =
        clipperYankSalesBaseSlot ee
    rw [clipperYankTwoWordHashMem_read0_64_of_ge
      (clipperYankArgWord ee) (⟨12⟩ : UInt256) (by
        simpa [activeMem] using hactiveMemSize)]
    rw [clipperYankSalesBaseSlot_eq ee]
    exact mappingSlot_single (clipperYankArgWord ee) ⟨12⟩
  have rd8330pre := evm_run rd8327 with [
    raw push1 ⟨64⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov)]
  have rd8331pre := rd8330pre.keccak256 (Cₘ aw5 - Cₘ aw4) (clipperYankSalesBaseSlot ee) aw5
    (by clipper_yank_remove_decode)
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk, aw5,
        show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    hsalesBase (by rfl) (by evm_ov)
  obtain ⟨_, _, rd8332raw⟩ := rd8331pre.sload (by clipper_yank_remove_decode) (by evm_ov)
  obtain ⟨k8332, C8332, rd8332⟩ :
      ∃ k C, RD code ee g s0 ⟨8332⟩
        (idx :: move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt :: clipperYankArgWord ee :: ⟨502⟩ ::
          [sel])
        saleHashMem aw5 o (cA, σ) k C := by
    exact ⟨_, _, by simpa [idx, clipperYankSalesPosSlot, solcSlotWord] using rd8332raw⟩
  have rd8346 := evm_run rd8332 with [
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8336raw⟩ := rd8346.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8347pre := evm_run rd8336raw with [
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap2 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup4 (by clipper_yank_remove_decode) (by evm_ov),
    raw swap1 (by clipper_yank_remove_decode) (by evm_ov),
    raw dup2 (by clipper_yank_remove_decode) (by evm_ov),
    raw lt (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8348⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  have hidxCond : UInt256.lt idx (solcSlotWord σ ee ⟨11⟩) = ⟨0⟩ :=
    ult_zero hidxBound
  exact RD.invalidHalt
    (rd8347pre.jumpiNT (by clipper_yank_remove_decode)
      (by simpa [idx, solcSlotWord] using hidxCond) (by evm_ov))
    (by clipper_yank_remove_decode)

theorem RD.clipperTakeRemoveJoinEmptyInvalid
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {move : UInt256}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who maxArg amt sel : UInt256}
    {cA σ}
    (rd : RD code ee g s0 ⟨8379⟩
      (move :: clipperYankArgWord ee :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: maxArg :: amt :: clipperYankArgWord ee :: ⟨502⟩ :: [sel])
      mem aw o (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨11⟩ = ⟨0⟩) :
    RDinvalid code g s0 := by
  let len := solcSlotWord σ ee ⟨11⟩
  have rd8384 := evm_run rd with [
    raw jumpdest (by clipper_yank_remove_decode) (by evm_ov),
    raw push1 ⟨11⟩ (by clipper_yank_remove_decode) (by evm_ov),
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov)]
  obtain ⟨_, _, rd8384raw⟩ := rd8384.sload (by clipper_yank_remove_decode) (by evm_ov)
  have rd8388 := evm_run rd8384raw with [
    raw dup1 (by clipper_yank_remove_decode) (by evm_ov),
    raw push2 ⟨8390⟩ (by clipper_yank_remove_decode) (by evm_ov)]
  exact RD.invalidHalt
    (rd8388.jumpiNT (by clipper_yank_remove_decode)
      (by simpa [len, solcSlotWord] using hlen) (by evm_ov))
    (by clipper_yank_remove_decode)

theorem clipperTakePostDogFluxRetRemoveArgs (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    let fluxRetFrame : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_fluxUsrRet" .unit }
    evalExprs? (config v) fluxRetFrame evmFlux [.var "id"] =
      .ok [clipperYankArgValue I] := by
  intro fluxRetFrame
  have hid :=
    clipperEvalTakeVarIdAtDigsRet v evmLoc evmRead evmVat evmFlux I price slice
      owe0 owe slice' tabNew lotNew
  have hid' :
      evalExpr? (config v) fluxRetFrame evmFlux (.var "id") =
        .ok (clipperYankArgValue I) := by
    dsimp only [fluxRetFrame]
    simp only [evalExpr?]
    rw [store_get_ne
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
      (k := "_fluxUsrRet") (a := "id") .unit (by decide)]
    simpa only [evalExpr?, clipperTakeIdValue, clipperYankArgValue,
      clipperTakeIdWord, clipperYankArgWord] using hid
  exact evalExprs?_singleton hid'

set_option maxHeartbeats 1000000 in
theorem clipperTakePostDogTabZeroFluxRemoveSourceRevertsOfBody
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outFlux : ByteArray}
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
          .int (Int.ofNat lotNew.toNat)]
        (true, evmFlux, outFlux) true)
    (hremoveBody :
      ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evmFlux
        removeFunction.body .reverted) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
        .assign .storage lockedRef (.intLit 0) ]
      .reverted := by
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
  let fluxRetFrame : Frame :=
    { contract := contract v,
      locals := digsRetFrame.locals.insert "_fluxUsrRet" .unit }
  have hlotCond := clipperEvalTakeLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond := clipperEvalTakeTabEqZeroAtDigsRet_true v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew htabNew
  have hargs := clipperEvalTakeVatFluxUsrArgsAtDigsRet v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew
  have hguard := clipperEvalTakeVatCodeGuard_true v evmDog digsRetFrame.locals hvatCode
  have hflux :
      ExecBlock (config v) digsRetFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        (.ok fluxRetFrame evmFlux) := by
    simpa [checkedExternalCallStmts, digsRetFrame, fluxRetFrame, collapseReturns] using
      (checkedExternalCallSuccess hguard
        (clipperEvalVat v evmDog digsRetFrame.locals) hargs hcallFlux
        (clipperTakeDecodeFluxVoid v outFlux))
  have hremove :
      ExecStmt (config v) fluxRetFrame evmFlux
        (.internalCall "_remove" [.var "id"] "_removeRet2") .reverted := by
    exact internalCallFunctionRevert
      (cfg := config v) (caller := fluxRetFrame) (evm := evmFlux)
      (name := "_remove") (retVar := "_removeRet2") (args := [.var "id"])
      (argVals := [clipperYankArgValue I]) (callee := removeFunction)
      (locals := clipperYankRemoveStore I)
      (by simpa [fluxRetFrame, digsRetFrame] using
        clipperTakePostDogFluxRetRemoveArgs v evmLoc evmRead evmVat evmFlux I
          price slice owe0 owe slice' tabNew lotNew)
      (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremoveBody
  have htabIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        .reverted := by
    exact ExecStmt.iteTrue (by simpa [digsRetFrame] using htabCond)
      (execBlockAppendOk hflux (ExecBlock.consRevert hremove))
  have hlotIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        .reverted := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using hlotCond)
      (ExecBlock.consRevert htabIte)
  exact ExecBlock.consRevert hlotIte

set_option maxHeartbeats 1000000 in
theorem clipperTakePostDogTabZeroFluxRemoveSourceOkOfBody
    (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux evmRemove : EVM.State)
    (I : ExecutionEnv) (price slice owe0 owe slice' tabNew lotNew : UInt256)
    {outFlux : ByteArray} {calleeSolm : Frame}
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
          .int (Int.ofNat lotNew.toNat)]
        (true, evmFlux, outFlux) true)
    (hremoveBody :
      ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evmFlux
        removeFunction.body (.returned calleeSolm evmRemove none)) :
    let frameRemoveRet : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_fluxUsrRet" .unit |>.insert
              "_removeRet2" .unit }
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
        .assign .storage lockedRef (.intLit 0) ]
      (.ok frameRemoveRet
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro frameRemoveRet
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
  let fluxRetFrame : Frame :=
    { contract := contract v,
      locals := digsRetFrame.locals.insert "_fluxUsrRet" .unit }
  have hlotCond := clipperEvalTakeLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond := clipperEvalTakeTabEqZeroAtDigsRet_true v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew htabNew
  have hargs := clipperEvalTakeVatFluxUsrArgsAtDigsRet v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew
  have hguard := clipperEvalTakeVatCodeGuard_true v evmDog digsRetFrame.locals hvatCode
  have hflux :
      ExecBlock (config v) digsRetFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        (.ok fluxRetFrame evmFlux) := by
    simpa [checkedExternalCallStmts, digsRetFrame, fluxRetFrame, collapseReturns] using
      (checkedExternalCallSuccess hguard
        (clipperEvalVat v evmDog digsRetFrame.locals) hargs hcallFlux
        (clipperTakeDecodeFluxVoid v outFlux))
  have hremove :
      ExecStmt (config v) fluxRetFrame evmFlux
        (.internalCall "_remove" [.var "id"] "_removeRet2")
        (.ok frameRemoveRet evmRemove) := by
    simpa [resumeAfterInternalCall, fluxRetFrame, digsRetFrame, frameRemoveRet] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := fluxRetFrame) (evm := evmFlux)
        (name := "_remove") (retVar := "_removeRet2") (args := [.var "id"])
        (argVals := [clipperYankArgValue I]) (callee := removeFunction)
        (locals := clipperYankRemoveStore I) (calleeSolm := calleeSolm)
        (calleeEvm := evmRemove) (value := none)
        (by simpa [fluxRetFrame, digsRetFrame] using
          clipperTakePostDogFluxRetRemoveArgs v evmLoc evmRead evmVat evmFlux I
            price slice owe0 owe slice' tabNew lotNew)
        (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremoveBody)
  have htabIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        (.ok frameRemoveRet evmRemove) := by
    exact ExecStmt.iteTrue (by simpa [digsRetFrame] using htabCond)
      (execBlockAppendOk hflux (ExecBlock.consNormal hremove ExecBlock.nil))
  have hlotIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        (.ok frameRemoveRet evmRemove) := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using hlotCond)
      (ExecBlock.consNormal htabIte ExecBlock.nil)
  have hzero :
      evalExpr? (config v) frameRemoveRet evmRemove (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure, frameRemoveRet]
  have hlocked : frameRemoveRet.locals.get? "locked" = none := by
    simp [frameRemoveRet]
  have hassign :
      assignStorageRef? (config v) frameRemoveRet evmRemove .storage lockedRef (.int 0) =
        .ok (frameRemoveRet,
          Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa [frameRemoveRet] using
      assign_clipperLocked v evmRemove frameRemoveRet.locals hlocked ⟨0⟩
  have hunlock :
      ExecStmt (config v) frameRemoveRet evmRemove
        (.assign .storage lockedRef (.intLit 0))
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecStmt.assign hzero hassign
  exact ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil)

end Benchmarks.Dss.Clipper
