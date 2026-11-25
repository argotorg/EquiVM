import Benchmarks.Midnight.TouchMarketPrefix
import Benchmarks.Midnight.MemoryFunding

variable {fork : Ethereum.Fork}

/-! Retaining non-memory work through the market hash and initialization check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketHashCheck_funded {credit : Nat} {evm : EVM.State} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root ptr ret : UInt256}
    {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 8 ≤ 1024) (hlo : 96 ≤ root.toNat)
    (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit (marketIdWorkMemory mem root m) aw C)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨20728⟩
      (marketIdPreimagePtr root m :: (marketIdPreimagePtr root m + UInt256.ofNat 32) ::
        ptr :: (ptr + UInt256.ofNat 32) :: ret :: R)
      (marketIdWorkMemory mem root m) aw rdata evm.accountMap k C) :
    (marketTickSpacing (marketFeeWord evm m.id) ≠ ⟨0⟩ ∧
      ∃ aw' k' C', MemoryFunding credit (touchMarketHashMemory mem root m) aw' C' ∧
        RD fork midnightBytecode evm.executionEnv g s0 ret (m.id :: R)
          (touchMarketHashMemory mem root m) aw' rdata evm.accountMap k' C') ∨
    (marketTickSpacing (marketFeeWord evm m.id) = ⟨0⟩ ∧
      ∃ aw' k' C', MemoryFunding credit (touchMarketHashMemory mem root m) aw' C' ∧
        RD fork midnightBytecode evm.executionEnv g s0 ⟨20764⟩
          ((ptr + UInt256.ofNat 32) :: ptr :: m.id :: ret :: R)
          (touchMarketHashMemory mem root m) aw' rdata evm.accountMap k' C') := by
  have hlen := marketIdWorkMemory_length mem m hlo hb
  have hhash := marketIdWorkMemory_hash mem m hlo hb
  have hmem : 64 ≤ (marketIdWorkMemory mem root m).size := by
    dsimp only [marketIdWorkMemory, marketIdMemory]
    rw [writeWord_sparse_size]; omega
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem m.id (UInt256.ofNat 1) (marketIdWorkMemory mem root m)) =
      solcMappingSlot ⟨1⟩ m.id := twoWordHashMem_mapSlot_of_ge64 m.id (UInt256.ofNat 1) hmem

  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := RD.genKeccak256 r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have ha17 := memoryFundingAt (credit := credit) r17 (by memory_fund ha)
  obtain ⟨_, _, hC18, r18⟩ := RD.sloadMono r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r20 := r19.shr (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.iszero (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 20764) (by native_decide) (by evm_ov)
  have ha18 := memoryFundingAt (credit := credit) r18
    ⟨ha17.paid.trans (Nat.add_le_add_right hC18 79), ha17.covered⟩
  by_cases hinit : marketTickSpacing (marketFeeWord evm m.id) = ⟨0⟩
  · have r24 := r23.jumpiT (by native_decide) (by
      simp only [hlen, hhash, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh]
      change UInt256.isZero (marketTickSpacing (marketFeeWord evm m.id)) ≠ UInt256.ofNat 0
      rw [hinit]; decide) (by jump_dest) (by evm_ov)
    have rFinal := RD.normalizePC (pc' := UInt256.ofNat 20764) r24 (by native_decide)
    have haFinal := memoryFundingAt (credit := credit) rFinal (by memory_fund ha18)
    simp only [hlen, hhash] at rFinal haFinal
    exact Or.inr ⟨hinit, _, _, _, haFinal, rFinal⟩
  · have r24 := r23.jumpiNT (by native_decide) (by
      simp only [hlen, hhash, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh]
      exact isZero_eq_zero_of_ne hinit) (by evm_ov)
    have rNext := RD.normalizePC (pc' := UInt256.ofNat 20760) r24 (by native_decide)
    have haNext := memoryFundingAt (credit := credit) rNext (by memory_fund ha18)
    simp only [hlen, hhash] at rNext haNext
    have rFinal := midnightBlocks.midnight_block_20760 (by omega) hret rNext
    have haFinal := memoryFundingAt (credit := credit) rFinal (by memory_fund haNext)
    exact Or.inl ⟨hinit, _, _, _, haFinal, rFinal⟩

end Benchmarks.Midnight
