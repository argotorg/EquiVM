import Benchmarks.Midnight.LiquidateCallbackFieldsStore
import Benchmarks.Midnight.CalldataAddressFunding
import Benchmarks.Midnight.CollateralLoopMemory
import Benchmarks.Midnight.RuntimeBlocks_025

/-! The callback's final market fields and scalar argument stores. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCallbackFields {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root index seized repaid dp dl borrower badDebt
      x0 x1 x2 : UInt256} {receiver : AccountAddress} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 24 ≤ 1024)
    (hd : decodeCalldataMarket I.calldata 4 = some m) (hi : calldataWord I.calldata 36 = index)
    (hroot : root.toNat < 2^128) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨6050⟩
      ([x0, x1, x2, borrower, UInt256.ofNat receiver.val, dp, dl,
        root + UInt256.ofNat (612 + 128 * m.collaterals.length), root, badDebt, root] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding credit
        (liquidateCallbackFieldsMemory mem root.toNat m index seized repaid borrower
          (UInt256.ofNat receiver.val)) aw' C' ∧
      RD midnightBytecode I g s0 ⟨19711⟩
        ([dp, dl, root + UInt256.ofNat (612 + 128 * m.collaterals.length), ⟨6199⟩,
          badDebt, root, root, ⟨32⟩, root] ++ R)
        (liquidateCallbackFieldsMemory mem root.toNat m index seized repaid borrower
          (UInt256.ofNat receiver.val)) aw' rdata σ k' C' := by
  have ho (n : Nat) (hn : n ≤ 548) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hmat := decodeCalldataMarket_maturity hd
  have hrcf := decodeCalldataMarket_rcfThreshold hd
  simp only [calldataWord] at hmat hrcf
  let first := writeWordArray mem (root.toNat + 452) [m.maturity, m.rcfThreshold]
  let third := writeWordArray mem (root.toNat + 452)
    [m.maturity, m.rcfThreshold, UInt256.ofNat m.enterGate.val]
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_6050 (R := root :: R)
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_6050_memory
    memory_fund ha)
  have hm1 : midnightBlocks.midnight_block_6050_memory (ee := I) (mem := mem) (x8 := root) =
      first := by
    simp only [midnightBlocks.midnight_block_6050_memory,
      show (UInt256.ofNat 4).toNat = 4 from rfl, hmat, hrcf,
      ho 452 (by decide), ho 484 (by decide), first, writeWordArray,
      Reasoning.Theory.writeWord, Nat.add_assoc, Nat.reduceAdd]
  rw [hm1] at rd1 ha1
  simp only [midnightBlocks.midnight_block_6050_stack, addressMask_computed] at rd1
  have he := decodeCalldataMarket_enterGate hd
  obtain ⟨k2, C2, _, ha2, rd2⟩ := midnightCalldataAddress_funded
    (head := calldataWord I.calldata 4 + UInt256.ofNat 196) (ret := UInt256.ofNat 6114)
    (R := [solcAddrMask, borrower, solcAddrMask, UInt256.ofNat receiver.val, solcAddrMask, dp, dl,
      root + UInt256.ofNat (612 + 128 * m.collaterals.length), ⟨6199⟩, badDebt, root, root, ⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [he]; exact addressWord_val_canonical _) (by jump_dest) ha1 rd1
  rw [he] at rd2
  have rd3 := midnightBlocks.midnight_block_6114 (R := [root, ⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd2
  have ha3 := memoryFundingAt (credit := credit) rd3 (by
    unfold midnightBlocks.midnight_block_6114_memory
    memory_fund ha2)
  have heclean : UInt256.land (UInt256.ofNat m.enterGate.val) solcAddrMask =
      UInt256.ofNat m.enterGate.val := addressWord_val_clean m.enterGate
  have hm3 : midnightBlocks.midnight_block_6114_memory (mem := first)
      (x0 := UInt256.ofNat m.enterGate.val) (x1 := solcAddrMask) (x11 := root) = third := by
    simp only [midnightBlocks.midnight_block_6114_memory, heclean, ho 516 (by decide),
      first, third, writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc, Nat.reduceAdd]
  rw [hm3] at rd3 ha3
  simp only [midnightBlocks.midnight_block_6114_stack] at rd3
  have hl := decodeCalldataMarket_liquidatorGate hd
  obtain ⟨k4, C4, _, ha4, rd4⟩ := midnightCalldataAddress_funded
    (head := calldataWord I.calldata 4 + UInt256.ofNat 228) (ret := UInt256.ofNat 6136)
    (R := [solcAddrMask, borrower, solcAddrMask, UInt256.ofNat receiver.val, solcAddrMask, dp, dl,
      root + UInt256.ofNat (612 + 128 * m.collaterals.length), ⟨6199⟩, badDebt, root, root, ⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [hl]; exact addressWord_val_canonical _) (by jump_dest) ha3 rd3
  rw [hl] at rd4
  have rd5 := midnightBlocks.midnight_block_6136 (R := [root, ⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd4
  have ha5 := memoryFundingAt (credit := credit) rd5 (by
    unfold midnightBlocks.midnight_block_6136_memory
    memory_fund ha4)
  have hm5 := liquidateCallbackFieldsStore_eq (m := m) (receiver := receiver)
    hi hroot hlo hsize hcanon hseized hpaid
  rw [hm5] at rd5 ha5
  simp only [midnightBlocks.midnight_block_6136_stack] at rd5
  exact ⟨_, _, _, ha5, rd5⟩

end Benchmarks.Midnight
