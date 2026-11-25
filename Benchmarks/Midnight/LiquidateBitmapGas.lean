import Benchmarks.Midnight.RuntimeBlocks_028
import Benchmarks.Midnight.StorageWriteGas

variable {fork : Ethereum.Fork}

/-! Gas monotonicity for the optional liquidation bitmap write. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES the generated block at 6952 with cost monotonicity.
theorem liquidate_block_6952_mono {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 6833) = true)
    (h : RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6952) (x0 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C ≤ C' ∧ RD fork Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6833) (x0 :: R) mem aw rdata (sstoreAccountMap ee.codeOwner σ (x0 + (UInt256.ofNat 2)) (UInt256.lor (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))) (UInt256.shiftLeft (UInt256.land (UInt256.shiftRight (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x0 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.ofNat 128)) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1) (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 36).toNat 32))))) (UInt256.ofNat 128))) (UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD (x0 + (UInt256.ofNat 2)) (⟨0⟩ : UInt256))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc6, r6⟩ := RD.sloadMono r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.calldataload (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.not (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r20 := r19.swap3 (by native_decide) (by evm_ov)
  have r21 := r20.dup4 (by native_decide) (by evm_ov)
  have r22 := r21.shr (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.swap2 (by native_decide) (by evm_ov)
  have r26 := r25.shl (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r30 := r29.shl (by native_decide) (by evm_ov)
  have r31 := r30.sub (by native_decide) (by evm_ov)
  have r32 := r31.not (by native_decide) (by evm_ov)
  have r33 := r32.and (by native_decide) (by evm_ov)
  have r34 := r33.or (by native_decide) (by evm_ov)
  have r35 := r34.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc36, r36⟩ := sstoreMono r35 hperm (by native_decide) (by evm_ov)
  have r37 := r36.push2 (UInt256.ofNat 6833) (by native_decide) (by evm_ov)
  have r38 := r37.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6833)) r38 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩

end Benchmarks.Midnight
