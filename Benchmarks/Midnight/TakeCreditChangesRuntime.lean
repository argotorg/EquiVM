import Benchmarks.Midnight.TakeCreditChangesSource
import Benchmarks.Midnight.CheckedSubGas

variable {fork : Ethereum.Fork}

/-! Runtime credit and debt deltas, retaining the cost of both storage reads. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeCreditChangesMemory (mem : ByteArray) (sellerWord : UInt256) : ByteArray :=
  writeWord mem 352 sellerWord

set_option maxHeartbeats 1000000 in
theorem midnightTakeCreditChangesRuntime {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray}
    {aw sellerSlot marketSlot buyerSlot ratifierPtr time units : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hu : calldataWord I.calldata 68 = units)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12026⟩
      (sellerSlot :: marketSlot :: buyerSlot :: ratifierPtr :: time :: R)
      mem aw rdata σ k C) :
    let sellerCredit := low128 (solcSlotWordAt sellerSlot σ I)
    let buyerDebt := low128 (solcSlotWordAt (buyerSlot + ⟨2⟩) σ I)
    let sellerDecrease := wordMin units sellerCredit
    let mem' := takeCreditChangesMemory mem (solcSlotWordAt sellerSlot σ I)
    ∃ aw' k' C', MemoryFunding credit mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12118⟩
        ([UInt256.sub units sellerDecrease, UInt256.ofNat 12138, UInt256.ofNat 12144,
          UInt256.ofNat 1000000000000000000, UInt256.ofNat 12150, sellerCredit, buyerSlot, time,
          buyerDebt, sellerSlot, marketSlot, sellerDecrease, ratifierPtr,
          zeroFloorSubWord units buyerDebt] ++ R) mem' aw' rdata σ k' C' := by
  have hsave : memLoad (UInt256.ofNat 352)
      ((solcSlotWordAt sellerSlot σ I).toByteArray.write 0 mem 352 32) =
      solcSlotWordAt sellerSlot σ I := memLoad_writeWord mem (UInt256.ofNat 352) _
  have hcalldata : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 68).toNat 32) =
      units := hu
  change memLoad (UInt256.ofNat 352)
    ((σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD sellerSlot ⟨0⟩)).toByteArray.write 0 mem 352 32) = _ at hsave
  -- The generated summary existentially hides the two SLOAD costs.
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r8 := r7.dup5 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have ha9 := memoryFundingAt (credit := credit) r9 (by memory_fund ha)
  obtain ⟨_, _, hC10, r10⟩ := RD.sloadMono r9 (by native_decide) (by evm_ov)
  have ha10 := ha9.mono hC10
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r14 := r13.calldataload (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r18 := r17.calldataload (by native_decide) (by evm_ov)
  have r19 := r18.gt (by native_decide) (by evm_ov)
  have r20 := r19.mul (by native_decide) (by evm_ov)
  have r21 := r20.swap6 (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  have ha22 := memoryFundingAt (credit := credit) r22 (by memory_fund ha10)
  obtain ⟨_, _, hC23, r23⟩ := RD.sloadMono r22 (by native_decide) (by evm_ov)
  have ha23 := ha22.mono hC23
  have r24 := r23.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r25 := RD.genMstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r32 := RD.genMload r31 (by native_decide) (by evm_ov)
  have r33 := r32.and (by native_decide) (by evm_ov)
  have r34 := r33.swap5 (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r36 := r35.calldataload (by native_decide) (by evm_ov)
  have r37 := r36.dup7 (by native_decide) (by evm_ov)
  have r38 := r37.lt (by native_decide) (by evm_ov)
  have r39 := r38.dup7 (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r41 := r40.calldataload (by native_decide) (by evm_ov)
  have r42 := r41.xor (by native_decide) (by evm_ov)
  have r43 := r42.mul (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r45 := r44.calldataload (by native_decide) (by evm_ov)
  have r46 := r45.xor (by native_decide) (by evm_ov)
  have r47 := r46.swap6 (by native_decide) (by evm_ov)
  have r48 := r47.push2 (UInt256.ofNat 12150) (by native_decide) (by evm_ov)
  have r49 := r48.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by evm_ov)
  have r50 := r49.push2 (UInt256.ofNat 12144) (by native_decide) (by evm_ov)
  have r51 := r50.push2 (UInt256.ofNat 12138) (by native_decide) (by evm_ov)
  have r52 := r51.push2 (UInt256.ofNat 12118) (by native_decide) (by evm_ov)
  have r53 := r52.dup12 (by native_decide) (by evm_ov)
  have r54 := r53.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r55 := r54.calldataload (by native_decide) (by evm_ov)
  have r56 := r55.push2 (UInt256.ofNat 19447) (by native_decide) (by evm_ov)
  have r57 := r56.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19447)) r57 (by native_decide)
  have haFinal := memoryFundingAt (credit := credit) rFinal (by memory_fund ha23)
  simp only [uint128Mask_computed, show (UInt256.ofNat 352).toNat = 352 from rfl,
    hsave, hcalldata, wordMin_branchless, zeroFloorSubWord_eq] at rFinal
  obtain ⟨k1, C1, hC1, rd1⟩ := midnightCheckedSub_mono
    (by simp only [List.length_cons]; omega) (wordMin_le_left _ _) (by jump_dest) rFinal
  exact ⟨_, k1, C1, haFinal.mono hC1, rd1⟩

end Benchmarks.Midnight
