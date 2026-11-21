import Benchmarks.Midnight.WithdrawCollateralSource
import Benchmarks.Midnight.SafeTransferBudget
import Benchmarks.Midnight.RuntimeBlocks_021
import Benchmarks.Midnight.RuntimeBlocks_017
import Benchmarks.Midnight.AddressDecode

/-! The withdrawal event and token transfer, including the empty return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem withdrawCollateralTransfer {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw root index id user assets : UInt256} {token receiver : AccountAddress}
    {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : WithdrawSourceFrame frame m id user index assets token receiver)
    (hperm : I.perm = true) (hstack : R.length + 16 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hroot : root.toNat < 2^64) (hlower : 832 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget root credit mem aw C)
    (hcredit : 4 * ((root.toNat + safeTransferCallAllocation false + 31) / 32) ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨4649⟩
      ([user, UInt256.ofNat token.val, UInt256.ofNat receiver.val, assets, id] ++ R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (withdrawCollateralTransition.body.drop 13) .reverted) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (withdrawCollateralTransition.body.drop 13) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_4649 (by omega) hperm (by jump_dest) rd
  have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by
    simp only [midnightBlocks.midnight_block_4649_memory]
    transfer_budget hb)
  let mm := writeWord (writeWord (writeWord mem root.toNat (UInt256.ofNat I.source.val))
    (root + UInt256.ofNat 32).toNat assets) (root + UInt256.ofNat 64).toNat
      (UInt256.ofNat receiver.val)
  have hclean : UInt256.land (UInt256.ofNat receiver.val) solcAddrMask =
      UInt256.ofNat receiver.val := addressWord_val_clean receiver
  have hm : midnightBlocks.midnight_block_4649_memory (ee := I) (mem := mem)
      (x2 := UInt256.ofNat receiver.val) (x3 := assets) = mm := by
    simp only [midnightBlocks.midnight_block_4649_memory, hfree, addressMask_computed, hclean]
    rfl
  rw [hm] at rd1 hb1
  simp only [midnightBlocks.midnight_block_4649_stack, hfree] at rd1 hb1
  have hr32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat root 32 (by change _ < 2^256; omega)
  have hr64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat root 64 (by change _ < 2^256; omega)
  have hp : MemoryPrefix mem mm root.toNat :=
    (memoryPrefix_writeWord mem _ _ _ (Or.inl le_rfl)).trans
      ((memoryPrefix_writeWord _ _ _ _ (Or.inl (by rw [hr32]; omega))).trans
        (memoryPrefix_writeWord _ _ _ _ (Or.inl (by rw [hr64]; omega))))
  have hsz : 832 ≤ mm.size := hmem.trans hp.size
  have hused : root.toNat ≤ mm.size := by
    dsimp only [mm]; rw [writeWord_sparse_size, hr64]; omega
  have hfree1 : memLoad (UInt256.ofNat 64) mm = root := by
    dsimp only [mm]
    rw [memLoad_writeWord_preserved _ _ _ _ (by
          change 96 ≤ _; simp only [writeWord_sparse_size]; omega)
        (Or.inl (by change 96 ≤ _; rw [hr64]; omega)),
      memLoad_writeWord_preserved _ _ _ _ (by
          change 96 ≤ _; rw [writeWord_sparse_size]; omega)
        (Or.inl (by change 96 ≤ _; rw [hr32]; omega)),
      memLoad_writeWord_preserved _ _ _ _ (by change 96 ≤ _; omega)
        (Or.inl (by change 96 ≤ root.toNat; omega)), hfree]
  have hz1 : memLoad (UInt256.ofNat 96) mm = ⟨0⟩ := by
    rw [hp.load (UInt256.ofNat 96) (by decide)
      (by change 128 ≤ root.toNat; omega) (by change 128 ≤ mem.size; omega), hzero]
  have hz800 : memLoad (UInt256.ofNat 800) mm = ⟨0⟩ := by
    rw [hp.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
  have hl : lookupCallable? frame.contract "SafeTransferLib_safeTransfer" =
      some (safeTransferFunctionFor false).toCallable := by
    rw [hf.contract]; exact safeTransferLookup false
  have sourcePrefix {result : ExecResult}
      (ht : ExecBlock config frame evm (withdrawCollateralTransition.body.drop 14) result) :
      ExecBlock config frame evm (withdrawCollateralTransition.body.drop 13) result :=
    (withdrawCollateralEmit hf (by rw [hs.env]; exact hperm)).run ht
  rcases safeTransferBudgeted false frame.immutables (token := token) (sender := I.source)
      (recipient := receiver) (value := assets) (by omega) (by omega) (by omega)
      hfree1 hz1 hb1 hused hcredit hgas hfork hs (by jump_dest) rd1 with
    hoog | ⟨hbody, hr⟩ |
      ⟨evm', σ', out, mem', ptr', aw2, k2, C2, hbody, hs', hp2, _, _, _, _, rd2⟩
  · exact Or.inl hoog
  · exact Or.inr (Or.inl ⟨hr, sourcePrefix (ExecBlock.consRevert
      (internalCallFunctionRevert (withdrawCollateralTransferArgs hf) hl
        (safeTransferBind false token I.source receiver assets)
        (by simpa only [safeTransferFrame, hf.contract] using hbody)))⟩)
  · refine Or.inr (Or.inr ⟨_, evm', sourcePrefix (ExecBlock.consNormal
      (internalCallFunctionReturn (withdrawCollateralTransferArgs hf) hl
        (safeTransferBind false token I.source receiver assets)
        (by simpa only [safeTransferFrame, hf.contract] using hbody)) ExecBlock.nil), ?_⟩)
    rw [hs'.accounts] at rd2
    have hzret : memLoad (UInt256.ofNat 800) mem' = ⟨0⟩ := by
      rw [hp2.load (UInt256.ofNat 800) (by decide) hlower hsz, hz800]
    have hr := midnightBlocks.midnight_block_3723 (by omega) rd2
    simpa only [hzret, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      byteArray_readWithPadding_zero] using hr

end Benchmarks.Midnight
