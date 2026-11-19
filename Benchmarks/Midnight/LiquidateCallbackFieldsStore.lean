import Benchmarks.Midnight.LiquidateCallbackFieldsMemory
import Benchmarks.Midnight.CollateralLoopMemory
import Benchmarks.Midnight.RuntimeBlocks_025

/-! Memory normalization for the final scalar stores in the liquidation callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem liquidateCallbackDataOffset (n : Nat) :
    UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat (612 + 128 * n) =
      UInt256.ofNat (608 + 128 * n) := by
  have he : UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat 612 = UInt256.ofNat 608 :=
    by decide +kernel
  rw [← wordAddNat_add, he]
  apply u256_inj
  simp only [uadd_toNat, ofNat_toNat_mod, Nat.add_mod_mod, Nat.mod_add_mod]

theorem liquidateCallbackFieldsStore_eq {I : ExecutionEnv} {mem : ByteArray}
    {root index seized repaid borrower : UInt256} {receiver : AccountAddress} {m : MarketData}
    (hi : calldataWord I.calldata 36 = index) (hroot : root.toNat < 2^128)
    (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid) :
    midnightBlocks.midnight_block_6136_memory (ee := I)
      (mem := writeWordArray mem (root.toNat + 452)
        [m.maturity, m.rcfThreshold, UInt256.ofNat m.enterGate.val])
      (x0 := UInt256.ofNat m.liquidatorGate.val) (x1 := solcAddrMask) (x2 := borrower)
      (x3 := solcAddrMask) (x4 := UInt256.ofNat receiver.val) (x5 := solcAddrMask)
      (x8 := root + UInt256.ofNat (612 + 128 * m.collaterals.length)) (x11 := root) =
      liquidateCallbackFieldsMemory mem root.toNat m index seized repaid borrower
        (UInt256.ofNat receiver.val) := by
  let third := writeWordArray mem (root.toNat + 452)
    [m.maturity, m.rcfThreshold, UInt256.ofNat m.enterGate.val]
  have ho (n : Nat) (hn : n ≤ 548) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hrawIndex : uInt256OfByteArray (I.calldata.readBytes 36 32) = index := hi
  have hclean : UInt256.land (UInt256.ofNat m.liquidatorGate.val) solcAddrMask =
      UInt256.ofNat m.liquidatorGate.val := addressWord_val_clean m.liquidatorGate
  have hrecv : UInt256.land (UInt256.ofNat receiver.val) solcAddrMask =
      UInt256.ofNat receiver.val := addressWord_val_clean receiver
  let indexed := writeWord (writeWord third (root.toNat + 548)
    (UInt256.ofNat m.liquidatorGate.val)) (root.toNat + 100) index
  have hp : MemoryPrefix mem indexed root.toNat :=
    ((memoryPrefix_writeWordArray _ _ _ _ (by omega)).trans
      (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))).trans
      (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))
  have h640 : memLoad (UInt256.ofNat 640) indexed = seized :=
    (hp.load ⟨640⟩ (by decide) (by change 672 ≤ root.toNat; omega)
      (by change 672 ≤ mem.size; omega)).trans hseized
  have hp' : MemoryPrefix mem (writeWord indexed (root.toNat + 132) seized) root.toNat :=
    hp.trans (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))
  have h608 : memLoad (UInt256.ofNat 608) (writeWord indexed (root.toNat + 132) seized) = repaid :=
    (hp'.load ⟨608⟩ (by decide) (by change 640 ≤ root.toNat; omega)
      (by change 640 ≤ mem.size; omega)).trans hpaid
  simp only [indexed, Reasoning.Theory.writeWord] at h640 h608
  have hdelta := liquidateCallbackDataOffset m.collaterals.length
  have hm5 : midnightBlocks.midnight_block_6136_memory (ee := I) (mem := third)
      (x0 := UInt256.ofNat m.liquidatorGate.val) (x1 := solcAddrMask) (x2 := borrower)
      (x3 := solcAddrMask) (x4 := UInt256.ofNat receiver.val) (x5 := solcAddrMask)
      (x8 := root + UInt256.ofNat (612 + 128 * m.collaterals.length)) (x11 := root) =
      liquidateCallbackFieldsMemory mem root.toNat m index seized repaid borrower
        (UInt256.ofNat receiver.val) := by
    simp only [midnightBlocks.midnight_block_6136_memory, hclean, hrecv,
      solcAddrMask_clean hcanon, word_add_sub_left, hdelta,
      show (UInt256.ofNat 36).toNat = 36 from rfl, hrawIndex,
      ho 548 (by decide), ho 100 (by decide), ho 132 (by decide), ho 164 (by decide),
      ho 196 (by decide), ho 228 (by decide), ho 260 (by decide), h640, h608]
    simp only [liquidateCallbackFieldsMemory, third, writeWordArray, Reasoning.Theory.writeWord,
      Nat.add_assoc, Nat.reduceAdd]
  exact hm5

end Benchmarks.Midnight
