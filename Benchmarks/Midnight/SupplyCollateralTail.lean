import Benchmarks.Midnight.SupplyCollateralArithmetic
import Benchmarks.Midnight.SupplyCollateralSource
import Benchmarks.Midnight.SafeTransferBudget

/-! Collateral supply from the final balance addition through the token transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyCollateralTail {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw root unused0 unused1 old index id user assets : UInt256} {token : AccountAddress}
    {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hstack : R.length + 24 ≤ 1024) (hmem : 128 ≤ mem.size)
    (hroot : root.toNat < 2^64) (hlower : 128 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : TransferBudget root credit mem aw C)
    (hcredit : 4 * ((root.toNat + safeTransferCallAllocation true + 31) / 32) ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨17124⟩
      ([unused0, unused1, old, index, id, user, UInt256.ofNat token.val, assets,
        positionSlot id user + UInt256.ofNat 3] ++ R) mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (supplyCollateralTransition.body.drop 9) .reverted) ∨
    (RDstatic midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (supplyCollateralTransition.body.drop 9) .staticViolation) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (supplyCollateralTransition.body.drop 9) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  rcases supplyCollateralArithmetic hs.env (by omega) hi rd with ⟨hbad, hr⟩ |
    ⟨hfit, hperm, hr⟩ | ⟨hfit, hperm, k1, C1, hc1, rd1⟩
  · exact Or.inr (Or.inl ⟨hr, supplyAddRevert hf hbad⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, supplyAddStatic hf hcanon hi hfit
      (by rw [hs.env]; exact hperm)⟩))
  · let evm1 := collateralWriteState evm id user index (old + assets)
    let frame1 := wordLocal frame "__c4" (old + assets)
    have henv1 : evm1.executionEnv = I := (collateralWriteState_env ..).trans hs.env
    have hf1 : SupplySourceFrame frame1 m id user index assets old token :=
      hf.insert "__c4" (.int (old + assets).toNat) (by decide)
    have hs1 : SourceState s0 I evm1.accountMap evm1 := by
      refine ⟨?_, henv1, rfl⟩
      simpa only [evm1, collateralWriteState, storageStore_σ₀] using hs.world
    have sourcePrefix {result : ExecResult}
        (ht : ExecBlock config frame1 evm1 (supplyCollateralTransition.body.drop 12) result) :
        ExecBlock config frame evm (supplyCollateralTransition.body.drop 9) result := by
      apply supplyAddSource hf hcanon hi hfit (by rw [hs.env]; exact hperm)
      exact (supplyCollateralEmit hf1 (by rw [henv1]; exact hperm)).run ht
    simp only [List.cons_append, List.nil_append] at rd1
    have rd2 := midnightBlocks.midnight_block_17152
      (by simp only [List.length_cons]; omega) hperm (by jump_dest) rd1
    have hb2 := transferBudgetAt (root := root) (credit := credit) rd2 (by
      simp only [midnightBlocks.midnight_block_17152_memory]
      have hb1 := hb.mono hc1
      transfer_budget hb1)
    let mm := writeWord (writeWord mem root.toNat (UInt256.ofNat I.source.val))
      (root + UInt256.ofNat 32).toNat assets
    have hm : midnightBlocks.midnight_block_17152_memory
        (ee := I) (mem := mem) (x4 := assets) = mm := by
      simp only [midnightBlocks.midnight_block_17152_memory, hfree]
      rfl
    rw [hm] at rd2 hb2
    simp only [midnightBlocks.midnight_block_17152_stack, hfree] at rd2 hb2
    have hr32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
      addWord_toNat root (UInt256.ofNat 32) (by change root.toNat + 32 < 2^256; omega)
    have hm1 : 128 ≤ (writeWord mem root.toNat (UInt256.ofNat I.source.val)).size := by
      rw [writeWord_sparse_size]; omega
    have hsz : 128 ≤ mm.size := by
      dsimp only [mm]; rw [writeWord_sparse_size]; omega
    have hused : root.toNat ≤ mm.size := by
      dsimp only [mm]; rw [writeWord_sparse_size, hr32]; omega
    have hfree2 : memLoad (UInt256.ofNat 64) mm = root := by
      dsimp only [mm]
      rw [memLoad_writeWord_preserved _ _ _ _ (by change 96 ≤ _; omega)
          (Or.inl (by change 96 ≤ _; rw [hr32]; omega)),
        memLoad_writeWord_preserved _ _ _ _ (by change 96 ≤ _; omega)
          (Or.inl (by change 96 ≤ root.toNat; omega)), hfree]
    have hzero2 : memLoad (UInt256.ofNat 96) mm = ⟨0⟩ := by
      dsimp only [mm]
      rw [memLoad_writeWord_preserved _ _ (UInt256.ofNat 96) _ hm1
          (Or.inl (by change 128 ≤ _; rw [hr32]; omega)),
        memLoad_writeWord_preserved _ _ (UInt256.ofNat 96) _ hmem (Or.inl hlower), hzero]
    have he := supplyCollateralTransferArgs (evm := evm1) hf1
    rw [henv1] at he
    have hl : lookupCallable? frame1.contract "SafeTransferLib_safeTransferFrom" =
        some (safeTransferFunctionFor true).toCallable := by
      rw [hf1.contract]; exact safeTransferLookup true
    rcases safeTransferBudgeted true frame1.immutables (token := token)
        (sender := I.source) (recipient := I.codeOwner) (value := assets)
        (by omega) hsz hlower hfree2 hzero2 hb2 hused hcredit hgas hfork hs1
        (by jump_dest) rd2 with hoog | ⟨hbody, hr⟩ |
          ⟨evm', σ', out, mem', ptr', aw3, k3, C3, hbody, hs', _, _, _, _, _, rd3⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hr, sourcePrefix (ExecBlock.consRevert
        (internalCallFunctionRevert he hl (safeTransferBind true token I.source I.codeOwner assets)
          (by simpa only [safeTransferFrame, hf1.contract] using hbody)))⟩)
    · refine Or.inr (Or.inr (Or.inr ⟨_, evm', sourcePrefix (ExecBlock.consNormal
        (internalCallFunctionReturn he hl (safeTransferBind true token I.source I.codeOwner assets)
          (by simpa only [safeTransferFrame, hf1.contract] using hbody)) ExecBlock.nil), ?_⟩))
      rw [hs'.accounts] at rd3
      exact midnightBlocks.midnight_block_15786 (by omega) rd3

end Benchmarks.Midnight
