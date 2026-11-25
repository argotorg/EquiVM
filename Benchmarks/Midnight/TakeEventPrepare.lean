import Benchmarks.Midnight.TakeEventHead

variable {fork : Ethereum.Fork}

/-! The encoded-offer hash and signed check preceding the trade event encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES block 12838 with retained funding for its memory reads and hash.
theorem midnightTakeEventPrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw encodedPtr encodedDataPtr decrease increase ratifierPtr : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hi : increase.toNat < 2^255) (hd : decrease.toNat < 2^255)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12838⟩
      (encodedPtr :: encodedDataPtr :: decrease :: increase :: ratifierPtr :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨12921⟩
        (midnightBlocks.midnight_block_12838_fallthrough_stack (mem := mem)
          (x0 := encodedPtr) (x1 := encodedDataPtr) (x2 := decrease)
          (x3 := increase) (x4 := ratifierPtr) (R := R)) mem aw' rdata σ k' C' := by
  have hcond := signedSubNonnegativeGuard hi hd
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := RD.genKeccak256 r3 (by native_decide) (by evm_ov)
  have ha4 := memoryFundingAt (credit := credit) r4 (by memory_fund ha)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r8 := RD.genMload r7 (by native_decide) (by evm_ov)
  have r9 := r8.add (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have ha10 := memoryFundingAt (credit := credit) r10 (by memory_fund ha4)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.genMload r22 (by native_decide) (by evm_ov)
  have ha23 := memoryFundingAt (credit := credit) r23 (by memory_fund ha10)
  have r24 := r23.and (by native_decide) (by evm_ov)
  have r25 := r24.swap4 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r28 := RD.genMload r27 (by native_decide) (by evm_ov)
  have r29 := r28.add (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have ha30 := memoryFundingAt (credit := credit) r30 (by memory_fund ha23)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r37 := r36.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r38 := RD.genMload r37 (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := RD.genMload r39 (by native_decide) (by evm_ov)
  have ha40 := memoryFundingAt (credit := credit) r40 (by memory_fund ha30)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.swap2 (by native_decide) (by evm_ov)
  have r43 := r42.push0 (by native_decide) (by evm_ov)
  have r44 := r43.dup7 (by native_decide) (by evm_ov)
  have r45 := r44.dup3 (by native_decide) (by evm_ov)
  have r46 := r45.sub (by native_decide) (by evm_ov)
  have r47 := r46.swap7 (by native_decide) (by evm_ov)
  have r48 := r47.slt (by native_decide) (by evm_ov)
  have r49 := r48.dup2 (by native_decide) (by evm_ov)
  have r50 := r49.dup8 (by native_decide) (by evm_ov)
  have r51 := r50.slt (by native_decide) (by evm_ov)
  have r52 := r51.dup2 (by native_decide) (by evm_ov)
  have r53 := r52.and (by native_decide) (by evm_ov)
  have r54 := r53.swap2 (by native_decide) (by evm_ov)
  have r55 := r54.dup8 (by native_decide) (by evm_ov)
  have r56 := r55.sgt (by native_decide) (by evm_ov)
  have r57 := r56.swap1 (by native_decide) (by evm_ov)
  have r58 := r57.iszero (by native_decide) (by evm_ov)
  have r59 := r58.and (by native_decide) (by evm_ov)
  have r60 := r59.or (by native_decide) (by evm_ov)
  have r61 := r60.push2 (UInt256.ofNat 7302) (by native_decide) (by evm_ov)
  have r62 := r61.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12921)) r62 (by native_decide)
  have haFinal := memoryFundingAt (credit := credit) rFinal (ha40.mono (by omega))
  exact ⟨_, _, _, haFinal, rFinal⟩

end Benchmarks.Midnight
