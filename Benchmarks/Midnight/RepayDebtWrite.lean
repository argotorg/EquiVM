import Benchmarks.Midnight.RepayBalanceSource
import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.RuntimeBlocks_039

variable {fork : Ethereum.Fork}

/-! The debt write and its static-call halt preserve previously paid gas. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayWriteDebt {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value slot dp id dl user callback units : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD fork midnightBytecode ee g s0 ⟨9925⟩
      (value :: uint128Mask :: slot :: dp :: id :: dl :: user :: callback :: units :: R)
      mem aw rdata σ k C) :
    (ee.perm = false ∧ RDstatic fork midnightBytecode g s0) ∨
    (ee.perm = true ∧ ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode ee g s0 ⟨23403⟩
      (units :: UInt256.ofNat 9950 :: dp :: id :: dl :: user :: callback :: units :: R)
      mem aw rdata (storeLow128Accounts σ ee slot value) k' C') := by
  have hvalid : (D_J midnightBytecode 0).contains (UInt256.ofNat 23403) = true := by jump_dest
  let r0 := h
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
  by_cases hp : ee.perm = true
  · obtain ⟨_, _, hc14, r14⟩ := sstoreMono r13 hp (by native_decide) (by evm_ov)
    have r15 := r14.push2 (UInt256.ofNat 9950) (by native_decide) (by evm_ov)
    have r16 := r15.dup7 (by native_decide) (by evm_ov)
    have r17 := r16.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
    have r18 := r17.jump (by native_decide) hvalid (by evm_ov)
    have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r18 (by native_decide)
    refine Or.inr ⟨hp, _, _, ?_, by
      simpa only [uint128Mask_computed, storeLow128Accounts, setUint128LowWord] using rFinal⟩
    omega
  · exact Or.inl ⟨Bool.eq_false_of_not_eq_true hp,
      r13.sstoreStatic (Bool.eq_false_of_not_eq_true hp) (by native_decide) (by evm_ov)⟩

end Benchmarks.Midnight
