import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.AdminSource
import Benchmarks.Midnight.RuntimeBlocks_009
import Benchmarks.Midnight.RuntimeBlocks_014
import Benchmarks.Midnight.RuntimeBlocks_016

variable {fork : Ethereum.Fork}

/-! The three matching packed-address update blocks for administrative roles. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def adminSetterWritePC (i : Fin 3) : UInt256 := [⟨3467⟩, ⟨2848⟩, ⟨1340⟩][i.val]

def adminSetterSlot (i : Fin 3) : UInt256 := UInt256.ofNat (10 + i.val)

theorem adminSetterTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value : UInt256} {R : List UInt256} (i : Fin 3)
    (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = false)
    (rd : RD fork midnightBytecode I g s0 (adminSetterWritePC i) (value :: R) mem aw rdata σ k C) :
    RDstatic fork midnightBytecode g s0 := by
  -- These blocks share the same prefix, with only their PCs and storage slots varying.
  have r1 := rd.push1 (UInt256.ofNat 1) (by clear * - i; revert i; native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by clear * - i; revert i; native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by clear * - i; revert i; native_decide) (by evm_ov)
  have r4 := r3.shl (by clear * - i; revert i; native_decide) (by evm_ov)
  have r5 := r4.sub (by clear * - i; revert i; native_decide) (by evm_ov)
  have r6 := r5.and (by clear * - i; revert i; native_decide) (by evm_ov)
  have r7 := r6.dup1 (by clear * - i; revert i; native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by clear * - i; revert i; native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by clear * - i; revert i; native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by clear * - i; revert i; native_decide) (by evm_ov)
  have r11 := r10.shl (by clear * - i; revert i; native_decide) (by evm_ov)
  have r12 := r11.sub (by clear * - i; revert i; native_decide) (by evm_ov)
  have r13 := r12.not (by clear * - i; revert i; native_decide) (by evm_ov)
  have r14 := r13.push1 (adminSetterSlot i) (by clear * - i; revert i; native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by clear * - i; revert i; native_decide) (by evm_ov)
  have r16 := r15.and (by clear * - i; revert i; native_decide) (by evm_ov)
  have r17 := r16.or (by clear * - i; revert i; native_decide) (by evm_ov)
  have r18 := r17.push1 (adminSetterSlot i) (by clear * - i; revert i; native_decide) (by evm_ov)
  exact r18.sstoreStatic hperm (by clear * - i; revert i; native_decide) (by evm_ov)

theorem adminSetterTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {aw value : UInt256}
    (i : Fin 3) (hperm : I.perm = true)
    (rd : RD fork midnightBytecode I g (initState σ σ₀ g A I) (adminSetterWritePC i)
      [value, solcSelectorWord I] midnightEntryMemory aw ByteArray.empty σ k C) :
    RDret fork midnightBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ (adminSetterSlot i)
        (setAddressOffset0Word (solcSlotWordAt (adminSetterSlot i) σ I) value))
      ByteArray.empty := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  all_goals
    have hr := by first
      | exact midnightBlocks.midnight_block_3467 (by simp) hperm rd
      | exact midnightBlocks.midnight_block_2848 (by simp) hperm rd
      | exact midnightBlocks.midnight_block_1340 (by simp) hperm rd
    simp only [addressMask_computed, midnightEntryMemory_zero,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero] at hr
    simpa only [setAddressOffset0Word, u256_land_comm] using hr

end Benchmarks.Midnight
