import Benchmarks.Midnight.SellCallbackHead
import Benchmarks.Midnight.Uint128Arithmetic

variable {fork : Ethereum.Fork}

/-! The fixed scalar arguments written after encoding the seller callback's market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES block 13539 with explicit scalar values and retained funding.
theorem midnightSellCallbackFields {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root ptr ret assets units fee user receiver : UInt256}
    {σ : AccountMap} {k C count : Nat} {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hb : root.toNat + 260 < UInt256.size) (hlo : 608 ≤ root.toNat) (hm : 608 ≤ mem.size)
    (haRead : memLoad (UInt256.ofNat 416) mem = assets)
    (huRead : calldataWord I.calldata 68 = units)
    (hfRead : memLoad (UInt256.ofNat 160) mem = fee)
    (hbRead : memLoad (UInt256.ofNat 448) mem = user)
    (hrRead : memLoad (UInt256.ofNat 128) mem = receiver)
    (hrcanon : receiver.toNat < EVM.addressModulus)
    (hf128 : fee.toNat < 2^128) (huser : user.toNat < EVM.addressModulus)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨13539⟩
      ((root + UInt256.ofNat (548 + 128 * count)) :: ptr :: ret :: root :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit
        (writeWordArray mem (root.toNat + 68)
          [assets, units, fee, user, receiver, UInt256.ofNat (544 + 128 * count)]) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨20095⟩
        (ptr :: (root + UInt256.ofNat (548 + 128 * count)) :: ret :: root :: R)
        (writeWordArray mem (root.toNat + 68)
          [assets, units, fee, user, receiver, UInt256.ofNat (544 + 128 * count)]) aw' rdata σ k' C' := by
  have hoff (n : Nat) (hn : n ≤ 228) :
      (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hload (words : List UInt256) (read : UInt256) (hr : read.toNat + 32 ≤ 608) :
      memLoad read (writeWordArray mem (root.toNat + 68) words) = memLoad read mem :=
    memLoad_writeWordArray_below _ _ _ _ (by omega) (by omega)
  have hfee : memLoad (UInt256.ofNat 160)
      (writeWord (writeWord mem (root.toNat + 68) assets) (root.toNat + 100) units) = fee := by
    simpa only [writeWordArray, Nat.add_assoc, Nat.reduceAdd, hfRead] using
      hload [assets, units] (UInt256.ofNat 160) (by decide)
  have hseller : memLoad (UInt256.ofNat 448)
      (writeWord (writeWord (writeWord mem (root.toNat + 68) assets)
        (root.toNat + 100) units) (root.toNat + 132) fee) = user := by
    simpa only [writeWordArray, Nat.add_assoc, Nat.reduceAdd, hbRead] using
      hload [assets, units, fee] (UInt256.ofNat 448) (by decide)
  have hreceiver : memLoad (UInt256.ofNat 128)
      (writeWord (writeWord (writeWord (writeWord mem (root.toNat + 68) assets)
        (root.toNat + 100) units) (root.toNat + 132) fee)
        (root.toNat + 164) user) = receiver := by
    simpa only [writeWordArray, Nat.add_assoc, Nat.reduceAdd, hrRead] using
      hload [assets, units, fee, user] (UInt256.ofNat 128) (by decide)
  have he : (UInt256.sub (root + UInt256.ofNat (548 + 128 * count)) root) +
      UInt256.lnot (UInt256.ofNat 3) = UInt256.ofNat (544 + 128 * count) := by
    rw [word_add_sub_left, u256_add_comm]
    have hbase : UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat 548 = UInt256.ofNat 544 :=
      by decide +kernel
    rw [← wordAddNat_add, hbase]
    apply u256_inj
    simp only [uadd_toNat, ofNat_toNat_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  simp only [Reasoning.Theory.writeWord] at hfee hseller hreceiver
  change uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 68).toNat 32) = units at huRead
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 416) (by native_decide) (by evm_ov)
  have r4 := RD.genMload r3 (by native_decide) (by evm_ov)
  rw [haRead] at r4
  have r5 := r4.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.genMstore r7 (by native_decide) (by evm_ov)
  have ha8 := memoryFundingAt (credit := credit) r8 (by memory_fund ha)
  simp only [hoff 68 (by decide)] at r8 ha8
  have r9 := r8.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r10 := r9.calldataload (by native_decide) (by evm_ov)
  rw [huRead] at r10
  have r11 := r10.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r12 := r11.dup6 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := RD.genMstore r13 (by native_decide) (by evm_ov)
  have ha14 := memoryFundingAt (credit := credit) r14 (by memory_fund ha8)
  simp only [hoff 100 (by decide)] at r14 ha14
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r21 := RD.genMload r20 (by native_decide) (by evm_ov)
  rw [hfee] at r21
  have r22 := r21.and (by native_decide) (by evm_ov)
  simp only [uint128Mask_computed, uint128Mask_clean hf128] at r22
  have r23 := r22.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r24 := r23.dup6 (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := RD.genMstore r25 (by native_decide) (by evm_ov)
  have ha26 := memoryFundingAt (credit := credit) r26 (by memory_fund ha14)
  simp only [hoff 132 (by decide)] at r26 ha26
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r30 := r29.shl (by native_decide) (by evm_ov)
  have r31 := r30.sub (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 448) (by native_decide) (by evm_ov)
  have r33 := RD.genMload r32 (by native_decide) (by evm_ov)
  rw [hseller] at r33
  have r34 := r33.and (by native_decide) (by evm_ov)
  simp only [addressMask_computed, solcAddrMask_clean huser] at r34
  have r35 := r34.push1 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r36 := r35.dup6 (by native_decide) (by evm_ov)
  have r37 := r36.add (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have ha38 := memoryFundingAt (credit := credit) r38 (by memory_fund ha26)
  simp only [hoff 164 (by decide)] at r38 ha38
  have r39 := r38.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r42 := r41.shl (by native_decide) (by evm_ov)
  have r43 := r42.sub (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r45 := RD.genMload r44 (by native_decide) (by evm_ov)
  rw [hreceiver] at r45
  have r46 := r45.and (by native_decide) (by evm_ov)
  simp only [addressMask_computed, solcAddrMask_clean hrcanon] at r46
  have r47 := r46.push1 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r48 := r47.dup6 (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := RD.genMstore r49 (by native_decide) (by evm_ov)
  have ha50 := memoryFundingAt (credit := credit) r50 (by memory_fund ha38)
  simp only [hoff 196 (by decide)] at r50 ha50
  have r51 := r50.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r52 := r51.not (by native_decide) (by evm_ov)
  have r53 := r52.dup5 (by native_decide) (by evm_ov)
  have r54 := r53.dup4 (by native_decide) (by evm_ov)
  have r55 := r54.sub (by native_decide) (by evm_ov)
  have r56 := r55.add (by native_decide) (by evm_ov)
  rw [he] at r56
  have r57 := r56.push1 (UInt256.ofNat 228) (by native_decide) (by evm_ov)
  have r58 := r57.dup6 (by native_decide) (by evm_ov)
  have r59 := r58.add (by native_decide) (by evm_ov)
  have r60 := RD.genMstore r59 (by native_decide) (by evm_ov)
  have ha60 := memoryFundingAt (credit := credit) r60 (by memory_fund ha50)
  simp only [hoff 228 (by decide)] at r60 ha60
  have r61 := r60.push2 (UInt256.ofNat 20095) (by native_decide) (by evm_ov)
  have r62 := r61.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 20095)) r62 (by native_decide)
  have haFinal := memoryFundingAt (credit := credit) rFinal (ha60.mono (by omega))
  change MemoryFunding credit (writeWordArray mem (root.toNat + 68)
    [assets, units, fee, user, receiver, UInt256.ofNat (544 + 128 * count)]) _ _ at haFinal
  change RD fork _ _ _ _ ⟨20095⟩ _ (writeWordArray mem (root.toNat + 68)
    [assets, units, fee, user, receiver, UInt256.ofNat (544 + 128 * count)]) _ _ _ _ _ at rFinal
  exact ⟨_, _, _, haFinal, rFinal⟩

end Benchmarks.Midnight
