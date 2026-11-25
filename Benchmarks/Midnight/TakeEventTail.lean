import Benchmarks.Midnight.TakeEventHead

variable {fork : Ethereum.Fork}

/-! The remaining fixed words of the trade event, preserving the allocated heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeEventTailMemory (mem : ByteArray) (I : ExecutionEnv) (root difference : UInt256) :
    ByteArray :=
  midnightBlocks.midnight_block_12970_memory (ee := I) (mem := mem)
    (x1 := difference) (x3 := root)

theorem takeEventTailMemory_size (mem : ByteArray) (I : ExecutionEnv)
    (root difference : UInt256) :
    mem.size ≤ (takeEventTailMemory mem I root difference).size := by
  unfold takeEventTailMemory midnightBlocks.midnight_block_12970_memory
  change mem.size ≤ (writeWord (writeWord (writeWord (writeWord (writeWord
    (writeWord (writeWord mem _ _) _ _) _ _) _ _) _ _) _ _) _ _).size
  simp only [writeWord_sparse_size]
  omega

theorem takeEventTailMemory_prefix (mem : ByteArray) (I : ExecutionEnv)
    (root difference : UInt256) (hb : root.toNat + 416 < UInt256.size) :
    MemoryPrefix mem (takeEventTailMemory mem I root difference) root.toNat := by
  unfold takeEventTailMemory midnightBlocks.midnight_block_12970_memory
  change MemoryPrefix mem (writeWord (writeWord (writeWord (writeWord (writeWord
    (writeWord (writeWord mem _ _) _ _) _ _) _ _) _ _) _ _) _ _) root.toNat
  have hoff (n : Nat) (hn : n ≤ 384) : root.toNat ≤ (root + UInt256.ofNat n).toNat := by
    rw [uadd_word_ofNat_toNat _ _ (by omega)]
    omega
  exact ((((((memoryPrefix_writeWord _ _ _ _ (Or.inl (hoff 192 (by decide)))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (hoff 224 (by decide))))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (hoff 256 (by decide))))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (hoff 288 (by decide))))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (hoff 320 (by decide))))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (hoff 352 (by decide))))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (hoff 384 (by decide))))

theorem takeEventTailMemory_load (mem : ByteArray) (I : ExecutionEnv)
    (root difference read : UInt256) (hb : root.toNat + 416 < UInt256.size)
    (hin : read.toNat + 32 ≤ mem.size) (hlo : read.toNat + 32 ≤ root.toNat) :
    memLoad read (takeEventTailMemory mem I root difference) = memLoad read mem := by
  unfold takeEventTailMemory midnightBlocks.midnight_block_12970_memory
  change memLoad read (writeWord (writeWord (writeWord (writeWord (writeWord
    (writeWord (writeWord mem _ _) _ _) _ _) _ _) _ _) _ _) _ _) = _
  have hoff (n : Nat) (hn : n ≤ 384) : read.toNat + 32 ≤ (root + UInt256.ofNat n).toNat := by
    rw [uadd_word_ofNat_toNat _ _ (by omega)]
    omega
  rw [memLoad_writeWord_preserved _ _ read _
    (by simp only [writeWord_sparse_size]; omega) (Or.inl (hoff 384 (by decide))),
    memLoad_writeWord_preserved _ _ read _
    (by simp only [writeWord_sparse_size]; omega) (Or.inl (hoff 352 (by decide))),
    memLoad_writeWord_preserved _ _ read _
    (by simp only [writeWord_sparse_size]; omega) (Or.inl (hoff 320 (by decide))),
    memLoad_writeWord_preserved _ _ read _
    (by simp only [writeWord_sparse_size]; omega) (Or.inl (hoff 288 (by decide))),
    memLoad_writeWord_preserved _ _ read _
    (by simp only [writeWord_sparse_size]; omega) (Or.inl (hoff 256 (by decide))),
    memLoad_writeWord_preserved _ _ read _
    (by simp only [writeWord_sparse_size]; omega) (Or.inl (hoff 224 (by decide))),
    memLoad_writeWord_preserved _ _ read _ hin (Or.inl (hoff 192 (by decide)))]

-- GENERALIZES block 12970 with retained funding and heap preservation.
theorem midnightTakeEventTail {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root finish difference maker : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hb : root.toNat + 416 < UInt256.size) (hlo : 160 ≤ root.toNat) (hm : 160 ≤ mem.size)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12970⟩
      ([finish, difference, maker, root] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (takeEventTailMemory mem I root difference) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨13067⟩
        ([root, ⟨416⟩, UInt256.land (memLoad (UInt256.ofNat 128) mem) solcAddrMask,
          finish, maker, root] ++ R)
        (takeEventTailMemory mem I root difference) aw' rdata σ k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 192) (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have ha8 := memoryFundingAt (credit := credit) r8 (by memory_fund ha)
  have r9 := r8.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r12 := r11.dup6 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have ha14 := memoryFundingAt (credit := credit) r14 (by memory_fund ha8)
  have r15 := r14.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r18 := r17.dup6 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have ha20 := memoryFundingAt (credit := credit) r20 (by memory_fund ha14)
  have r21 := r20.push2 (UInt256.ofNat 480) (by native_decide) (by evm_ov)
  have r22 := RD.genMload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 288) (by native_decide) (by evm_ov)
  have r24 := r23.dup6 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := RD.genMstore r25 (by native_decide) (by evm_ov)
  have ha26 := memoryFundingAt (credit := credit) r26 (by memory_fund ha20)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r30 := r29.shl (by native_decide) (by evm_ov)
  have r31 := r30.sub (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r33 := RD.genMload r32 (by native_decide) (by evm_ov)
  have r34 := r33.and (by native_decide) (by evm_ov)
  have r35 := r34.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r36 := r35.dup6 (by native_decide) (by evm_ov)
  have r37 := r36.add (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have ha38 := memoryFundingAt (credit := credit) r38 (by memory_fund ha26)
  have r39 := r38.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r42 := r41.shl (by native_decide) (by evm_ov)
  have r43 := r42.sub (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r45 := RD.genMload r44 (by native_decide) (by evm_ov)
  have r46 := r45.and (by native_decide) (by evm_ov)
  have r47 := r46.push2 (UInt256.ofNat 352) (by native_decide) (by evm_ov)
  have r48 := r47.dup6 (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := RD.genMstore r49 (by native_decide) (by evm_ov)
  have ha50 := memoryFundingAt (credit := credit) r50 (by memory_fund ha38)
  have r51 := r50.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r52 := r51.dup5 (by native_decide) (by evm_ov)
  have r53 := r52.add (by native_decide) (by evm_ov)
  have r54 := RD.genMstore r53 (by native_decide) (by evm_ov)
  have ha54 := memoryFundingAt (credit := credit) r54 (by memory_fund ha50)
  have r55 := r54.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r57 := r56.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r58 := r57.shl (by native_decide) (by evm_ov)
  have r59 := r58.sub (by native_decide) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r61 := RD.genMload r60 (by native_decide) (by evm_ov)
  have ha61 := memoryFundingAt (credit := credit) r61 (by memory_fund ha54)
  have r62 := r61.and (by native_decide) (by evm_ov)
  have r63 := r62.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r64 := r63.dup5 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 13067)) r64 (by native_decide)
  have ha1 := memoryFundingAt (credit := credit) rFinal (ha61.mono (by omega))
  have rd1 := rFinal
  change MemoryFunding credit (takeEventTailMemory mem I root difference) _ _ at ha1
  change RD fork _ _ _ _ ⟨13067⟩
    (root :: ⟨416⟩ :: UInt256.land
      (memLoad (UInt256.ofNat 128) (takeEventTailMemory mem I root difference)) solcAddrMask ::
      finish :: maker :: root :: R) (takeEventTailMemory mem I root difference) _ _ _ _ _ at rd1
  rw [takeEventTailMemory_load mem I root difference (UInt256.ofNat 128) hb hm hlo] at rd1
  exact ⟨_, _, _, ha1, rd1⟩

end Benchmarks.Midnight
