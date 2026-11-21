import Benchmarks.Midnight.TakeBuyerDebtWrite

/-! The market total-units store and the following saved asset reads. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES block 12566 with normalized storage and memory funding.
set_option maxRecDepth 10000 in
theorem midnightTakeMarketStore {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value slot : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hperm : I.perm = true) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12566⟩
      (value :: uint128Mask :: slot :: R) mem aw rdata σ k C) :
    ∃ k' C', MemoryFunding credit mem
        (M (M aw (UInt256.ofNat 416) ⟨32⟩) (UInt256.ofNat 256) ⟨32⟩) C' ∧
      RD midnightBytecode I g s0 ⟨19447⟩
        (memLoad (UInt256.ofNat 256) mem :: memLoad (UInt256.ofNat 416) mem :: ⟨12598⟩ :: R)
        mem (M (M aw (UInt256.ofNat 416) ⟨32⟩) (UInt256.ofNat 256) ⟨32⟩) rdata
        (storeLow128Accounts σ I slot value) k' C' := by
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc10, r10⟩ := RD.sloadMono r9 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc14, r14⟩ := sstoreMono r13 hperm (by native_decide) (by evm_ov)
  have ha14 := memoryFundingAt (credit := credit) r14 (ha.mono (by omega))
  have r15 := r14.push2 (UInt256.ofNat 12598) (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r17 := RD.genMload r16 (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r19 := RD.genMload r18 (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 19447) (by native_decide) (by evm_ov)
  have r21 := r20.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 19447)) r21 (by native_decide)
  have haFinal := memoryFundingAt (credit := credit) rFinal (by memory_fund ha14)
  exact ⟨_, _, haFinal, rFinal⟩

end Benchmarks.Midnight
