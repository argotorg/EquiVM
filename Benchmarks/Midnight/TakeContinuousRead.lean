import Benchmarks.Midnight.TakeCreditChangesRuntime
import Benchmarks.Midnight.TakeBuyerPendingSource

/-! Read the continuous-fee rate without losing the storage-read cost. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeContinuousRead_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray}
    {aw debt credit buyerSlot time buyerDebt sellerSlot marketSlot decrease ratifierPtr
      increase : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨12118⟩
      ([debt, UInt256.ofNat 12138, UInt256.ofNat 12144, takePendingScale, UInt256.ofNat 12150,
        credit, buyerSlot, time, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr,
        increase] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨20413⟩
      ([marketContinuousFee (solcSlotWordAt (marketSlot + ⟨2⟩) σ I), time,
        UInt256.ofNat 12138, UInt256.ofNat 12144, takePendingScale, UInt256.ofNat 12150,
        credit, buyerSlot, debt, buyerDebt, sellerSlot, marketSlot, decrease, ratifierPtr,
        increase] ++ R) mem aw rdata σ k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap7 (by native_decide) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r5 := r4.dup13 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hC7, r7⟩ := RD.sloadMono r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r9 := r8.shr (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 20413) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := UInt256.ofNat 20413) r12 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩

end Benchmarks.Midnight
