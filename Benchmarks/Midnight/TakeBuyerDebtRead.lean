import Benchmarks.Midnight.TakePositionsMemory

variable {fork : Ethereum.Fork}

/-! The short-circuited buyer update condition reads debt only when credit is zero. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES the generated block 14521 summary by retaining cumulative gas.
theorem midnightTakeBuyerDebtRead_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw old sellerSlot saved buyerSlot : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨14521⟩ (old :: sellerSlot :: saved :: buyerSlot :: R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨11961⟩
        (UInt256.gt (calldataWord I.calldata 68)
          (low128 (solcSlotWordAt (buyerSlot + ⟨2⟩) σ I)) :: sellerSlot :: saved :: buyerSlot :: R)
        mem aw rdata σ k' C' := by
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r9 := r8.dup5 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hC11, r11⟩ := RD.sloadMono r10 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r14 := r13.calldataload (by native_decide) (by evm_ov)
  have r15 := r14.gt (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 11961) (by native_decide) (by evm_ov)
  have r17 := r16.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11961)) r17 (by native_decide)
  simp only [uint128Mask_computed] at rFinal
  exact ⟨_, _, by omega, rFinal⟩

end Benchmarks.Midnight
