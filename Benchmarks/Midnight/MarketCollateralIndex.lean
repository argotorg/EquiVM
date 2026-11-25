import Benchmarks.Midnight.MarketCollateralReference

variable {fork : Ethereum.Fork}

/-! A checked calldata record pointer at the liquidation's requested collateral index. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketCollateralPointer (bytes : ByteArray) (index : UInt256) : UInt256 :=
  UInt256.shiftLeft index ⟨7⟩ + UInt256.ofNat (marketCollateralDataStart bytes)

theorem marketCollateralPointer_bound {bytes : ByteArray} {m : MarketData} {index : UInt256}
    (hd : decodeCalldataMarket bytes 4 = some m) (hi : index.toNat < m.collaterals.length) :
    (marketCollateralPointer bytes index).toNat = marketCollateralDataStart bytes + 128 * index.toNat ∧
      (marketCollateralPointer bytes index).toNat + 128 ≤ bytes.size := by
  obtain ⟨hstart, hc⟩ := decodeCalldataMarket_collateralsAt hd
  obtain ⟨hbound, _, _⟩ := decodeCollateralElements_get hc index.toNat hi
  obtain ⟨_, hn, _, hl, _⟩ := decodeCalldataMarket_collateralArray hd
  have hs := (decodeCalldataMarket_data hd).2.1
  have hp : (UInt256.ofNat (marketCollateralDataStart bytes)).toNat = marketCollateralDataStart bytes :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)
  have he : (marketCollateralPointer bytes index).toNat =
      marketCollateralDataStart bytes + 128 * index.toNat := by
    rw [marketCollateralPointer, calldataCollateralIndex_toNat (by omega)
      (by rw [hp]; change _ < 2 ^ 256; omega), hp]
  exact ⟨he, by rw [he]; exact hbound⟩

theorem marketCollateralPointer_fields {bytes : ByteArray} {m : MarketData} {index : UInt256}
    (hd : decodeCalldataMarket bytes 4 = some m) (hi : index.toNat < m.collaterals.length) :
    calldataWord bytes (marketCollateralPointer bytes index + UInt256.ofNat 32).toNat =
      m.collaterals[index.toNat].lltv ∧
    calldataWord bytes (marketCollateralPointer bytes index + UInt256.ofNat 64).toNat =
      m.collaterals[index.toNat].liquidationCursor := by
  obtain ⟨he, hb⟩ := marketCollateralPointer_bound hd hi
  obtain ⟨_, hc⟩ := decodeCalldataMarket_collateralsAt hd
  obtain ⟨_, _, hat⟩ := decodeCollateralElements_get hc index.toNat hi
  have hs := (decodeCalldataMarket_data hd).2.1
  rw [hat]
  constructor
  · change calldataWord bytes _ = calldataWord bytes _
    apply congrArg (calldataWord bytes)
    rw [uadd_word_ofNat_toNat _ 32 (by change _ < 2 ^ 256; omega), he]
  · change calldataWord bytes _ = calldataWord bytes _
    apply congrArg (calldataWord bytes)
    rw [uadd_word_ofNat_toNat _ 64 (by change _ < 2 ^ 256; omega), he]

-- GENERALIZES the shared array-reference and index-check routines to any return continuation.
theorem midnightMarketCollateralIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {m : MarketData} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 7 ≤ 1024)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨20488⟩
      ((⟨4⟩ + calldataWord I.calldata 4) :: (calldataWord I.calldata 4 + ⟨100⟩) ::
        ⟨5534⟩ :: ret :: R) mem aw rdata σ k C) :
    (¬ (calldataWord I.calldata 36).toNat < m.collaterals.length ∧ RDrev fork midnightBytecode g s0) ∨
    ((calldataWord I.calldata 36).toNat < m.collaterals.length ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ret
        (marketCollateralPointer I.calldata (calldataWord I.calldata 36) :: R)
        mem aw rdata σ k' C') := by
  have hn : m.collaterals.length < 2 ^ 64 := by
    obtain ⟨_, hn, _, hl, _⟩ := decodeCalldataMarket_collateralArray hd
    rw [hl]
    exact hn
  have hcount : (UInt256.ofNat m.collaterals.length).toNat = m.collaterals.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)
  obtain ⟨k1, C1, hc1, rd1⟩ := midnightMarketCollateralReference
    (by simp only [List.length_cons]; omega) hd (by jump_dest) rd
  have rd2 := midnightBlocks.midnight_block_5534 (R := ret :: R)
    (by simp only [List.length_cons]; omega) (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_5534_stack] at rd2
  by_cases hi : (calldataWord I.calldata 36).toNat < m.collaterals.length
  · obtain ⟨k3, C3, hc3, rd3⟩ := midnightCalldataCollateralIndex (R := R) (by omega)
      (by rw [hcount]; exact hi) hret rd2
    exact Or.inr ⟨hi, k3, C3, by omega, rd3⟩
  · have rd3 := midnightBlocks.midnight_block_20541_taken (R := ret :: R)
      (by simp only [List.length_cons]; omega)
      (by rw [ult_zero (by rw [hcount]; exact Nat.le_of_not_gt hi)]; decide) (by jump_dest) rd2
    exact Or.inl ⟨hi, midnightBlocks.midnight_block_19161 (by
      simp only [midnightBlocks.midnight_block_20541_taken_stack, List.length_cons]; omega) rd3⟩

end Benchmarks.Midnight
