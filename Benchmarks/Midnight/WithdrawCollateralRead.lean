import Benchmarks.Midnight.WithdrawCollateralBlocksGas
import Benchmarks.Midnight.ArrayIndexGas
import Benchmarks.Midnight.PositionUpdateMemory
import Benchmarks.Midnight.CollateralStorage
import Benchmarks.Midnight.AddressDecode

/-! Bounds checks, token lookup, and the initial packed collateral read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

private theorem withdrawLookupPayment
    {n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 credit spent : Nat}
    (h : n0 + credit ≤ spent + 79) :
    n11 + credit ≤ spent + (121 + (n1 - n0) + (n2 - n1) + (n3 - n2) +
      (n4 - n3) + (n5 - n4) + (n6 - n5) + (n7 - n6) + (n8 - n7) + 42 +
      (n9 - n8) + (n10 - n9) + (n11 - n10) + 42) + 79 := by
  have step (a b : Nat) : b ≤ a + (b - a) := by omega
  have h1 := step n0 n1
  have h2 := step n1 n2
  have h3 := step n2 n3
  have h4 := step n3 n4
  have h5 := step n4 n5
  have h6 := step n5 n6
  have h7 := step n6 n7
  have h8 := step n7 n8
  have h9 := step n8 n9
  have h10 := step n9 n10
  have h11 := step n10 n11
  omega -splitNatSub

set_option maxRecDepth 2000000 in
theorem midnightWithdrawCollateralRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw market array limit root id user index assets receiver : UInt256}
    {m : MarketData} {σ : AccountMap} {k C credit : Nat} {R : List UInt256}
    (hstack : R.length + 26 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hz800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hm : MarketStored mem market array limit m)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨4472⟩
      ([id, user, UInt256.ofNat 4643, user, index, receiver, assets, market] ++ R) mem aw rdata σ k C) :
    ((¬ index.toNat < m.collaterals.length ∨ ¬ index.toNat < 128) ∧
      RDrev midnightBytecode g s0) ∨
    (∃ hi : index.toNat < m.collaterals.length, index.toNat < 128 ∧
      ∃ aw' k' C',
        TransferBudget root credit (positionReadMemory mem id user) aw' C' ∧
        RD midnightBytecode I g s0 ⟨19447⟩
          ([collateralWord (fun slot ↦ solcSlotWordAt slot σ I) id user index,
            assets, UInt256.ofNat 4573, UInt256.ofNat 4624,
            positionSlot id user + UInt256.ofNat 3, index, positionSlot id user,
            market, id, user, UInt256.ofNat 4643, user,
            UInt256.ofNat m.collaterals[index.toNat].token.val, receiver, assets, id] ++ R)
          (positionReadMemory mem id user) aw' rdata σ k' C') := by
  change RD midnightBytecode I g s0 ⟨4472⟩
    (id :: user :: UInt256.ofNat 4643 :: user :: index :: receiver :: assets :: market :: R) mem aw rdata σ k C at rd
  have rd1 := midnightBlocks.midnight_block_4472 (R := R)
    (by omega) (by jump_dest) rd
  have hb1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget hb)
  simp only [midnightBlocks.midnight_block_4472_stack, hm.arrayPtr, addressMask_computed] at rd1
  have hlen : (memLoad array mem).toNat = m.collaterals.length := by
    rw [hm.length, UInt256.toNat_ofNat_of_lt (by
      have := hm.collateralCount; change _ < 2^256; omega)]
  by_cases hi : index.toNat < m.collaterals.length
  · have hi64 : index.toNat < 2^64 := hi.trans hm.collateralCount
    obtain ⟨aw2, k2, C2, hb2, rd2⟩ := midnightMemoryArrayIndex_funded
      (by simp only [List.length_cons]; omega) hi64 (by rw [hlen]; exact hi)
      (by jump_dest) hb1 rd1
    obtain ⟨cp, hcp, hcplo, hcphi, hcw⟩ := hm.collaterals.get index.toNat hi
    have htoken : memLoad cp mem = UInt256.ofNat m.collaterals[index.toNat].token.val :=
      hcw.load_word ⟨0, by simp [CollateralData.words]⟩ (by simp)
    have rd3 := midnightBlocks.midnight_block_4496 (R := id :: R)
      (by simp only [List.length_cons]; omega) (by jump_dest) rd2
    have hz1 : memLoad (UInt256.ofNat 800) (writeWord mem 0 id) = ⟨0⟩ := by
      rw [memLoad_writeWord_preserved mem 0 (UInt256.ofNat 800) id hmem (Or.inr (by decide)), hz800]
    have hz2 : memLoad (UInt256.ofNat 800) (twoWordHashMem id ⟨0⟩ mem) = ⟨0⟩ := by
      rw [memLoad_twoWordHashMem id ⟨0⟩ (UInt256.ofNat 800) (by decide) hmem, hz800]
    have hh0 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id ⟨0⟩ mem) =
        solcMappingSlot ⟨0⟩ id := twoWordHashMem_mapSlot_of_ge64 id ⟨0⟩ (by omega)
    have hs0 : 64 ≤ (twoWordHashMem id ⟨0⟩ mem).size := by
      rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega
    have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (twoWordHashMem user (solcMappingSlot ⟨0⟩ id) (twoWordHashMem id ⟨0⟩ mem)) =
        positionSlot id user := twoWordHashMem_mapSlot_of_ge64 _ _ hs0
    simp only [midnightBlocks.midnight_block_4496_stack, midnightBlocks.midnight_block_4496_memory,
      hcp, htoken, hz800, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold] at rd3
    have hz1' : memLoad (UInt256.ofNat 800) (wordAt0Mem id mem) = ⟨0⟩ := hz1
    rw [hz1'] at rd3
    simp only [twoWordHash_fold, hz2, hh0, hh1, uint128Mask_computed] at rd3
    have hb3 := transferBudgetAt (root := root) (credit := credit) rd3 (by
      rcases hb2 with hsmall | ⟨halign, hfund⟩
      · exact Or.inl hsmall
      · refine Or.inr ⟨halign, ?_, ?_⟩
        · have hp := hfund.paid
          simp only [memExpansionCost] at hp ⊢
          exact withdrawLookupPayment hp
        · change MemoryCovered (positionReadMemory mem id user) _
          unfold MemoryCovered
          rw [positionReadMemory_size _ _ _ (by omega)]
          change MemoryCovered mem _
          repeat apply MemoryCovered.expand
          exact hfund.covered)
    have hclean : UInt256.land (UInt256.ofNat m.collaterals[index.toNat].token.val) solcAddrMask =
        UInt256.ofNat m.collaterals[index.toNat].token.val := addressWord_val_clean _
    rw [hclean] at rd3
    by_cases hi128 : index.toNat < 128
    · obtain ⟨k4, C4, hc4, rd4⟩ := midnightUint128ArrayLocation_mono
        (by simp only [List.length_cons]; omega) hi128 (by jump_dest) rd3
      have hb4 := transferBudgetAt (root := root) (credit := credit) rd4 (hb3.mono hc4)
      let old := collateralWord (fun slot ↦ solcSlotWordAt slot σ I) id user index
      have ho : UInt256.land
          (UInt256.shiftRight (solcSlotWordAt (positionSlot id user + UInt256.ofNat 3 +
            UInt256.ofNat (index.toNat / 2)) σ I)
              (UInt256.shiftLeft (UInt256.ofNat (16 * (index.toNat % 2))) (UInt256.ofNat 3)))
          uint128Mask = old := by
        rw [(uint128ArrayIndexFacts index hi128).2.2]
        rfl
      dsimp only [solcSlotWordAt] at ho
      obtain ⟨k5, C5, hc5, rd5⟩ := withdrawal_block_4560_mono
        (by simp only [List.length_cons]; omega) (by jump_dest) rd4
      have hb5 := transferBudgetAt (root := root) (credit := credit) rd5 (hb4.mono hc5)
      simp only [midnightBlocks.midnight_block_4560_stack, ho] at rd5
      exact Or.inr ⟨hi, hi128, _, _, _, hb5, rd5⟩
    · exact Or.inl ⟨Or.inr hi128, midnightUint128ArrayLocationRevert
        (by simp only [List.length_cons]; omega) (by omega) rd3⟩
  · exact Or.inl ⟨Or.inl hi, midnightMemoryArrayIndexRevert
      (by simp only [List.length_cons]; omega) (by rw [hlen]; omega) rd1⟩

end Benchmarks.Midnight
