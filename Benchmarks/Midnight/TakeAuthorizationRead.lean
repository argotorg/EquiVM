import Benchmarks.Midnight.SupplyAuthorizationTrace
import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.RuntimeBlocks_056

/-! The take authorization mapping read, retaining the cost of input byte copies. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeAuthorizationSecondHash_funded {credit : Nat} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw slot : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hmem : 64 ≤ mem.size)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode ee g s0 ⟨15059⟩ (slot :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (twoWordHashMem (solcSourceWord ee) slot mem) aw' C' ∧
      RD midnightBytecode ee g s0 ⟨10951⟩
        (UInt256.land (solcSlotWordAt (solcMappingSlot slot (solcSourceWord ee)) σ ee) ⟨255⟩ :: R)
        (twoWordHashMem (solcSourceWord ee) slot mem) aw' rdata σ k' C' := by
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.caller (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := RD.genMstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have ha16 := memoryFundingAt (credit := credit) r16 (by memory_fund ha)
  obtain ⟨_, _, hc17, r17⟩ := RD.sloadMono r16 (by native_decide) (by evm_ov)
  have ha17 := ha16.mono hc17
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 10951) (by native_decide) (by evm_ov)
  have r20 := r19.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10951)) r20 (by native_decide)
  have haFinal := memoryFundingAt (credit := credit) rFinal (by memory_fund ha17)
  simp only [addressMask_computed, solcAddrMask_clean (solcSourceWord_canonical ee),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold]
    at rFinal haFinal
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (solcSourceWord ee) slot mem) =
      solcMappingSlot slot (solcSourceWord ee) := twoWordHashMem_mapSlot_of_ge64 _ _ hmem
  rw [hh] at rFinal
  exact ⟨_, _, _, haFinal, rFinal⟩

theorem midnightTakeAuthorizationRead_funded {credit : Nat} {I : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw check user : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hmem : 64 ≤ mem.size)
    (huser : memLoad (UInt256.ofNat 544) mem = user)
    (hcanon : user.toNat < EVM.addressModulus) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨15028⟩ (check :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (supplyAuthorizationMemory mem I user) aw' C' ∧
      RD midnightBytecode I g s0 ⟨10951⟩
        (UInt256.land (solcSlotWordAt (authorizationSlot user (solcSourceWord I)) σ I) ⟨255⟩ :: R)
        (supplyAuthorizationMemory mem I user) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_15028 (by omega) (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_15028_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_15028_stack,
    midnightBlocks.midnight_block_15028_memory, huser, addressMask_computed,
    u256_land_comm solcAddrMask, solcAddrMask_clean hcanon,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at rd1 ha1
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem user (UInt256.ofNat 3) mem) =
      solcMappingSlot ⟨3⟩ user := twoWordHashMem_mapSlot_of_ge64 _ _ hmem
  rw [hh] at rd1
  exact midnightTakeAuthorizationSecondHash_funded (by omega)
    (by rw [twoWordHashMem_size_of_ge_64 _ _ hmem]; exact hmem) ha1 rd1

end Benchmarks.Midnight
