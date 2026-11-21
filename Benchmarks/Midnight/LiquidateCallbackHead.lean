import Benchmarks.Midnight.LiquidateCallbackHeadMemory
import Benchmarks.Midnight.CalldataAddressFunding
import Benchmarks.Midnight.RuntimeBlocks_024

/-! Callback selector, caller, identifier, and the first market fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateCallbackHead {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root id dp dl borrower receiver badDebt : UInt256}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hroot : root.toNat < 2^128) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 768) mem = id) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5824⟩
      ([dp, dl, borrower, badDebt, receiver] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding (credit + 4) (liquidateCallbackHeadMemory mem root.toNat I.source id m) aw' C' ∧
      RD midnightBytecode I g s0 ⟨5931⟩
        ([UInt256.ofNat m.loanToken.val, solcAddrMask, borrower, receiver, dp, dl,
          root + UInt256.ofNat 580, badDebt, root] ++ R)
        (liquidateCallbackHeadMemory mem root.toNat I.source id m) aw' rdata σ k' C' := by
  have hoff (n : Nat) (hn : n ≤ 580) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hsel : UInt256.shiftLeft (UInt256.ofNat 1081233153) (UInt256.ofNat 225) =
      liquidateCallbackSelector := by decide +kernel
  have hchain : uInt256OfByteArray
      (I.calldata.readBytes (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat 32) = m.chainId :=
    decodeCalldataMarket_chainId hd
  simp only [calldataWord] at hchain
  let pre := writeWord (writeWord mem root.toNat liquidateCallbackSelector)
    (root.toNat + 4) (UInt256.ofNat I.source.val)
  have hid1 : memLoad (UInt256.ofNat 768) pre = id := by
    unfold pre
    rw [memLoad_writeWord_preserved _ _ _ _ (by rw [writeWord_sparse_size]; change 800 ≤ _; omega)
      (Or.inl (by change 800 ≤ root.toNat + 4; omega)),
      memLoad_writeWord_preserved _ _ _ _ (by change 800 ≤ mem.size; omega)
        (Or.inl (by change 800 ≤ root.toNat; omega)), hid]
  have hm1 : midnightBlocks.midnight_block_5824_memory (ee := I) (mem := mem) =
      writeWord (liquidateCallbackPrefixMemory mem root.toNat I.source id)
        (root.toNat + 324) m.chainId := by
    simp only [midnightBlocks.midnight_block_5824_memory, hfree, hsel,
      show (UInt256.ofNat 4).toNat = 4 from rfl, hchain,
      hoff 4 (by decide), hoff 36 (by decide), hoff 68 (by decide), hoff 324 (by decide)]
    change writeWord (writeWord (writeWord pre (root.toNat + 36)
      (memLoad (UInt256.ofNat 768) pre)) (root.toNat + 68) (UInt256.ofNat 320))
      (root.toNat + 324) m.chainId = _
    rw [hid1]
    simp only [liquidateCallbackPrefixMemory, writeWordArray, pre, Nat.add_assoc, Nat.reduceAdd]
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_5824 (by omega) (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit + 4) rd1 (by
    unfold midnightBlocks.midnight_block_5824_memory
    memory_fund ha)
  rw [hm1] at rd1 ha1
  simp only [midnightBlocks.midnight_block_5824_stack, hfree, addressMask_computed] at rd1 ha1
  have hm : calldataWord I.calldata (calldataWord I.calldata 4 + UInt256.ofNat 36).toNat =
      UInt256.ofNat m.midnight.val := decodeCalldataMarket_midnight hd
  obtain ⟨k2, C2, _, ha2, rd2⟩ := midnightCalldataAddress_funded
    (head := calldataWord I.calldata 4 + UInt256.ofNat 36) (ret := UInt256.ofNat 5902)
    (R := [solcAddrMask, borrower, receiver, dp, dl, root + UInt256.ofNat 580, badDebt, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [hm]; exact addressWord_val_canonical _) (by jump_dest) ha1 rd1
  rw [hm] at rd2
  have rd3 := midnightBlocks.midnight_block_5902 (R := R)
    (by omega) (by jump_dest) rd2
  have ha3 := memoryFundingAt (credit := credit + 4) rd3 (by
    unfold midnightBlocks.midnight_block_5902_memory
    memory_fund ha2)
  have hm3 : midnightBlocks.midnight_block_5902_memory
      (mem := writeWord (liquidateCallbackPrefixMemory mem root.toNat I.source id)
        (root.toNat + 324) m.chainId) (x0 := UInt256.ofNat m.midnight.val)
      (x1 := solcAddrMask) (x8 := root) =
      liquidateCallbackHeadMemory mem root.toNat I.source id m := by
    have hclean : UInt256.land (UInt256.ofNat m.midnight.val) solcAddrMask =
        UInt256.ofNat m.midnight.val := addressWord_val_clean m.midnight
    simp only [midnightBlocks.midnight_block_5902_memory, hclean,
      hoff 356 (by decide)]
    simp only [liquidateCallbackHeadMemory, writeWordArray, Reasoning.Theory.writeWord,
      Nat.add_assoc, Nat.reduceAdd]
  rw [hm3] at rd3 ha3
  simp only [midnightBlocks.midnight_block_5902_stack, addressMask_computed] at rd3
  have ht := decodeCalldataMarket_loanToken hd
  obtain ⟨k4, C4, _, ha4, rd4⟩ := midnightCalldataAddress_funded
    (head := calldataWord I.calldata 4 + UInt256.ofNat 68) (ret := UInt256.ofNat 5931)
    (R := [solcAddrMask, borrower, receiver, dp, dl, root + UInt256.ofNat 580, badDebt, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [ht]; exact addressWord_val_canonical _) (by jump_dest) ha3 rd3
  rw [ht] at rd4
  exact ⟨_, _, _, ha4, rd4⟩

end Benchmarks.Midnight
