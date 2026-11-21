import Benchmarks.Midnight.TakeEventTail
import Benchmarks.Midnight.DynamicLockMemory

/-! Emitting the trade log and constructing the subsequent transient-lock key. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeEventLogMemory (mem : ByteArray) (root receiver payer : UInt256) : ByteArray :=
  writeWord (writeWord mem (root + UInt256.ofNat 416).toNat receiver)
    (root + UInt256.ofNat 448).toNat (UInt256.land payer solcAddrMask)

theorem takeEventLogMemory_prefix (mem : ByteArray) (root receiver payer : UInt256)
    (hb : root.toNat + 480 < UInt256.size) :
    MemoryPrefix mem (takeEventLogMemory mem root receiver payer) root.toNat := by
  unfold takeEventLogMemory
  rw [uadd_word_ofNat_toNat root 416 (by omega),
    uadd_word_ofNat_toNat root 448 (by omega)]
  exact (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))

theorem takeEventLogMemory_load (mem : ByteArray) (root receiver payer read : UInt256)
    (hb : root.toNat + 480 < UInt256.size)
    (hin : read.toNat + 32 ≤ mem.size) (hlo : read.toNat + 32 ≤ root.toNat) :
    memLoad read (takeEventLogMemory mem root receiver payer) = memLoad read mem := by
  unfold takeEventLogMemory
  rw [uadd_word_ofNat_toNat root 416 (by omega),
    uadd_word_ofNat_toNat root 448 (by omega)]
  rw [memLoad_writeWord_preserved _ _ read _ (by rw [writeWord_sparse_size]; omega)
    (Or.inl (by omega)), memLoad_writeWord_preserved _ _ read _ hin (Or.inl (by omega))]

-- GENERALIZES block 13067 with normalized lock bytes and retained memory funding.
theorem midnightTakeEventLog {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root receiver finish maker callback payer id seller : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 9 ≤ 1024)
    (hb : root.toNat + 480 < UInt256.size) (hlo : 576 ≤ root.toNat) (hm : 576 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hcanon : seller.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨13067⟩
      ([root, ⟨416⟩, receiver, finish, maker, root, callback, payer] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit
        (dynamicLockHashMemory (takeEventLogMemory mem root receiver payer) root id seller) aw' C' ∧
      RD midnightBytecode I g s0 ⟨18444⟩
        ([root, ⟨128⟩, ⟨13223⟩, root, callback, payer] ++ R)
        (dynamicLockHashMemory (takeEventLogMemory mem root receiver payer) root id seller)
        aw' rdata σ k' C' := by
  have h32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have h64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have h96 : (root + UInt256.ofNat 96).toNat = root.toNat + 96 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  let logMem := takeEventLogMemory mem root receiver payer
  have hp := takeEventLogMemory_prefix mem root receiver payer hb
  have hload (read : UInt256) (hr : read.toNat + 32 ≤ 576) :
      memLoad read logMem = memLoad read mem :=
    takeEventLogMemory_load mem root receiver payer read hb (by omega) (by omega)
  have hs1 : memLoad (UInt256.ofNat 448)
      (writeWord logMem (root.toNat + 32) id) = seller := by
    rw [memLoad_writeWord_preserved _ _ (UInt256.ofNat 448) _
      (by change 480 ≤ logMem.size; have hh := hp.size; dsimp [logMem]; omega)
      (Or.inl (by change 480 ≤ root.toNat + 32; omega)), hload _ (by decide), hseller]
  simp only [List.cons_append, List.nil_append] at rd
  let r0 := rd
  have r1 := r0.add (by native_decide) (by evm_ov)
  have r2 := RD.genMstore r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup6 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have ha13 := memoryFundingAt (credit := credit) r13 (by memory_fund ha)
  change MemoryFunding credit logMem _ _ at ha13
  change RD _ _ _ _ _ _ logMem _ _ _ _ _ at r13
  have r14 := r13.pushConst (UInt256.ofNat 85728119599629476005759388951245938408922412091434260513249924659539733299184) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 544) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.swap4 (by native_decide) (by evm_ov)
  have r24 := r23.dup1 (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r26 := RD.genMload r25 (by native_decide) (by evm_ov)
  have r27 := r26.swap4 (by native_decide) (by evm_ov)
  have r28 := r27.sub (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  have r30 := RD.genLog4 r29 (by native_decide) hperm (by evm_ov)
  have ha30 := memoryFundingAt (credit := credit) r30 (by memory_fund ha13)
  have r31 := r30.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r32 := RD.genMload r31 (by native_decide) (by evm_ov)
  have ha32 := memoryFundingAt (credit := credit) r32 (by memory_fund ha30)
  rw [hload (UInt256.ofNat 64) (by decide), hfree] at r32
  have r33 := r32.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r34 := RD.genMload r33 (by native_decide) (by evm_ov)
  have ha34 := memoryFundingAt (credit := credit) r34 (by memory_fund ha32)
  rw [hload (UInt256.ofNat 512) (by decide), hid] at r34
  have r35 := r34.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r36 := r35.dup3 (by native_decide) (by evm_ov)
  have r37 := r36.add (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have ha38 := memoryFundingAt (credit := credit) r38 (by memory_fund ha34)
  simp only [h32] at r38 ha38
  change RD _ _ _ _ _ _ (writeWord logMem (root.toNat + 32) id) _ _ _ _ _ at r38
  change MemoryFunding credit (writeWord logMem (root.toNat + 32) id) _ _ at ha38
  have r39 := r38.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r42 := r41.shl (by native_decide) (by evm_ov)
  have r43 := r42.sub (by native_decide) (by evm_ov)
  have r44 := r43.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r45 := RD.genMload r44 (by native_decide) (by evm_ov)
  have ha45 := memoryFundingAt (credit := credit) r45 (by memory_fund ha38)
  rw [hs1] at r45
  have r46 := r45.and (by native_decide) (by evm_ov)
  simp only [addressMask_computed, solcAddrMask_clean hcanon] at r46
  have r47 := r46.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r48 := r47.dup3 (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := RD.genMstore r49 (by native_decide) (by evm_ov)
  have ha50 := memoryFundingAt (credit := credit) r50 (by memory_fund ha45)
  simp only [h64] at r50 ha50
  have r51 := r50.pushConst (UInt256.ofNat 65530685186148139943160654700974242543032290443373287283358098694458470976932) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r53 := r52.dup3 (by native_decide) (by evm_ov)
  have r54 := r53.add (by native_decide) (by evm_ov)
  have r55 := RD.genMstore r54 (by native_decide) (by evm_ov)
  have ha55 := memoryFundingAt (credit := credit) r55 (by memory_fund ha50)
  simp only [h96] at r55 ha55
  have r56 := r55.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r57 := r56.dup2 (by native_decide) (by evm_ov)
  have r58 := RD.genMstore r57 (by native_decide) (by evm_ov)
  have ha58 := memoryFundingAt (credit := credit) r58 (by memory_fund ha55)
  have r59 := r58.push2 (UInt256.ofNat 13223) (by native_decide) (by evm_ov)
  have r60 := r59.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r61 := r60.dup3 (by native_decide) (by evm_ov)
  have r62 := r61.push2 (UInt256.ofNat 18444) (by native_decide) (by evm_ov)
  have r63 := r62.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 18444)) r63 (by native_decide)
  have haFinal := memoryFundingAt (credit := credit) rFinal (ha58.mono (by omega))
  change MemoryFunding credit (dynamicLockHashMemory logMem root id seller) _ _ at haFinal
  change RD _ _ _ _ ⟨18444⟩
    ([root, ⟨128⟩, ⟨13223⟩, root, callback, payer] ++ R)
    (dynamicLockHashMemory logMem root id seller) _ _ _ _ _ at rFinal
  exact ⟨_, _, _, haFinal, rFinal⟩

end Benchmarks.Midnight
