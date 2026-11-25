import Benchmarks.Midnight.LiquidateCallbackArrayBounds
import Benchmarks.Midnight.LiquidateCallbackHeadMemory
import Benchmarks.Midnight.RuntimeBlocks_024
import Benchmarks.Midnight.RuntimeBlocks_025
import Benchmarks.Midnight.MemoryFunding

variable {fork : Ethereum.Fork}

/-! The collateral-array bounds checks, header, and initial callback-loop state. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateCallbackArraySetupMemory (mem : ByteArray) (root : Nat) (m : MarketData) : ByteArray :=
  writeWord (writeWord (writeWord mem (root + 388) (UInt256.ofNat m.loanToken.val))
    (root + 420) (UInt256.ofNat 256)) (root + 580) (UInt256.ofNat m.collaterals.length)

theorem midnightLiquidateCallbackArrayHead {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root dp dl borrower receiver badDebt : UInt256}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hroot : root.toNat < 2^128) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨5931⟩
      ([UInt256.ofNat m.loanToken.val, solcAddrMask, borrower, receiver, dp, dl,
        root + UInt256.ofNat 580, badDebt, root] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding credit (liquidateCallbackArraySetupMemory mem root.toNat m) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨6038⟩
        ([⟨0⟩, liquidateCallbackArrayBase I.calldata,
          UInt256.ofNat (marketCollateralDataStart I.calldata), borrower, receiver, dp, dl,
          root + UInt256.ofNat 612, root, badDebt, root] ++ R)
        (liquidateCallbackArraySetupMemory mem root.toNat m) aw' rdata σ k' C' := by
  obtain ⟨hcheck, hcountGuard, hend, hptr, hcount⟩ := liquidateCallbackArrayFacts hd
  have ho (n : Nat) (hn : n ≤ 612) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hclean : UInt256.land (UInt256.ofNat m.loanToken.val) solcAddrMask =
      UInt256.ofNat m.loanToken.val := addressWord_val_clean m.loanToken
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_5931_fallthrough (R := R) (by omega) hcheck rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_5931_fallthrough_memory
    memory_fund ha)
  simp only [midnightBlocks.midnight_block_5931_fallthrough_memory, hclean, ho 388 (by decide)]
    at rd1 ha1
  change RD fork midnightBytecode I g s0 ⟨5961⟩
    ([liquidateCallbackArrayOffset I.calldata, borrower, receiver, dp, dl,
      root + UInt256.ofNat 580, badDebt, root] ++ R) _ _ rdata σ _ _ at rd1
  have rd2 := midnightBlocks.midnight_block_5961_fallthrough
    (R := [badDebt, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hcountGuard rd1
  change RD fork midnightBytecode I g s0 ⟨5988⟩
    ([root + UInt256.ofNat 580, liquidateCallbackArrayBase I.calldata,
      borrower, receiver, dp, dl, liquidateCallbackArrayBase I.calldata + UInt256.ofNat 36,
      badDebt, root] ++ R) _ _ rdata σ _ _ at rd2
  have rd3 := midnightBlocks.midnight_block_5988_fallthrough
    (R := [badDebt, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hend rd2
  have ha3 := memoryFundingAt (credit := credit) rd3 (ha1.mono (by omega))
  change RD fork _ _ _ _ _ _ (writeWord mem (root.toNat + 388) (UInt256.ofNat m.loanToken.val))
    _ _ _ _ _ at rd3
  change MemoryFunding credit (writeWord mem (root.toNat + 388) (UInt256.ofNat m.loanToken.val))
    _ _ at ha3
  have rd4 := midnightBlocks.midnight_block_6004 (R := R) (by omega) rd3
  have ha4 := memoryFundingAt (credit := credit) rd4 (by
    unfold midnightBlocks.midnight_block_6004_memory
    memory_fund ha3)
  have hn : uInt256OfByteArray
      (I.calldata.readBytes (liquidateCallbackArrayBase I.calldata + UInt256.ofNat 4).toNat 32) =
      UInt256.ofNat m.collaterals.length := hcount
  have hm : midnightBlocks.midnight_block_6004_memory (ee := I)
      (mem := writeWord mem (root.toNat + 388) (UInt256.ofNat m.loanToken.val))
      (x0 := root + UInt256.ofNat 580) (x1 := liquidateCallbackArrayBase I.calldata) (x8 := root) =
      liquidateCallbackArraySetupMemory mem root.toNat m := by
    simp only [midnightBlocks.midnight_block_6004_memory, hn, ho 420 (by decide), ho 580 (by decide)]
    rfl
  rw [hm] at rd4 ha4
  have hz' : memLoad (UInt256.ofNat 800) (liquidateCallbackArraySetupMemory mem root.toNat m) =
      ⟨0⟩ := by
    unfold liquidateCallbackArraySetupMemory
    rw [memLoad_writeWord_preserved _ _ _ _ (by
        simp only [writeWord_sparse_size]; change 832 ≤ _; omega)
      (Or.inl (by change 832 ≤ root.toNat + 580; omega)),
      memLoad_writeWord_preserved _ _ _ _ (by
        rw [writeWord_sparse_size]; change 832 ≤ _; omega)
      (Or.inl (by change 832 ≤ root.toNat + 420; omega)),
      memLoad_writeWord_preserved _ _ _ _ (by exact hsize)
      (Or.inl (by change 832 ≤ root.toNat + 388; omega)), hz]
  have hstack4 : midnightBlocks.midnight_block_6004_stack (ee := I)
      (mem := writeWord mem (root.toNat + 388) (UInt256.ofNat m.loanToken.val))
      (x0 := root + UInt256.ofNat 580) (x1 := liquidateCallbackArrayBase I.calldata)
      (x2 := borrower) (x3 := receiver) (x4 := dp) (x5 := dl)
      (x6 := liquidateCallbackArrayBase I.calldata + UInt256.ofNat 36)
      (x7 := badDebt) (x8 := root) (R := R) =
      [⟨0⟩, liquidateCallbackArrayBase I.calldata,
        UInt256.ofNat (marketCollateralDataStart I.calldata), borrower, receiver, dp, dl,
        root + UInt256.ofNat 612, root, badDebt, root] ++ R := by
    simp only [midnightBlocks.midnight_block_6004_stack, hn, ho 420 (by decide),
      ho 580 (by decide), hptr]
    change memLoad (UInt256.ofNat 800) (liquidateCallbackArraySetupMemory mem root.toNat m) :: _ = _
    rw [hz']
    rfl
  rw [hstack4] at rd4
  exact ⟨_, _, _, ha4, rd4⟩

end Benchmarks.Midnight
