import Benchmarks.Midnight.MarketCollateralToken
import Benchmarks.Midnight.TransferHeap

/-! The collateral-token lookup and amount load before the outgoing liquidation transfer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateTransferPrepare {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root index seized : UInt256} {receiver : AccountAddress}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index) (hidx : index.toNat < m.collaterals.length)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized) (hh : TransferHeap mem aw root C)
    (rd : RD midnightBytecode I g s0 ⟨20488⟩
      ([⟨4⟩ + calldataWord I.calldata 4, calldataWord I.calldata 4 + ⟨100⟩,
        ⟨5734⟩, ⟨5750⟩, UInt256.ofNat receiver.val, ⟨5543⟩, ⟨5755⟩] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', TransferHeap mem aw' root C' ∧
      RD midnightBytecode I g s0 (safeTransferEntryPC false)
        (safeTransferEntryStack false m.collaterals[index.toNat].token I.source receiver
          seized (⟨5755⟩ :: R)) mem aw' rdata σ k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  obtain ⟨k1, C1, hc1, rd1⟩ := midnightMarketCollateralReference
    (R := [⟨5750⟩, UInt256.ofNat receiver.val, ⟨5543⟩, ⟨5755⟩] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hd (by jump_dest) rd
  have hf1 := hh.funding.mono hc1
  have rd2 := midnightBlocks.midnight_block_5734 (R := ⟨5755⟩ :: R)
    (by simp only [List.length_cons]; omega)
    (by jump_dest) rd1
  have hf2 := memoryFundingAt (credit := transferHeapCredit root) rd2 (by memory_fund hf1)
  simp only [midnightBlocks.midnight_block_5734_stack, hseized] at rd2
  have hn : m.collaterals.length < 2^64 := by
    obtain ⟨_, hn, _, hl, _⟩ := decodeCalldataMarket_collateralArray hd
    rw [hl]
    exact hn
  have hcount : (UInt256.ofNat m.collaterals.length).toNat = m.collaterals.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  obtain ⟨k3, C3, hc3, rd3⟩ := midnightCalldataCollateralIndex
    (R := [⟨5750⟩, UInt256.ofNat receiver.val, seized, ⟨5755⟩] ++ R)
    (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)
    (by change (calldataWord I.calldata 36).toNat < _; rw [hi, hcount]; exact hidx)
    (by jump_dest) rd2
  have rd4 := midnightBlocks.midnight_block_5543
    (R := marketCollateralPointer I.calldata (calldataWord I.calldata 36) ::
      [⟨5750⟩, UInt256.ofNat receiver.val, seized, ⟨5755⟩] ++ R)
    (by simp only [List.length_cons, List.length_append, List.length_nil]; omega) (by jump_dest) rd3
  obtain ⟨k5, C5, hc5, rd5⟩ := midnightCalldataAddressDirectRead
    (R := [UInt256.ofNat receiver.val, seized, ⟨5755⟩] ++ R)
    (by simp only [List.length_cons, List.length_append, List.length_nil]; omega)
    (by change calldataWord I.calldata (marketCollateralPointer I.calldata
          (calldataWord I.calldata 36)).toNat = _
        rw [hi]; exact marketCollateralPointer_token hd hidx)
    (by jump_dest) rd4
  have rd6 := midnightBlocks.midnight_block_5750
    (R := [UInt256.ofNat m.collaterals[index.toNat].token.val,
      UInt256.ofNat receiver.val, seized, ⟨5755⟩] ++ R)
    (by simp only [List.length_cons, List.length_append, List.length_nil]; omega) (by jump_dest) rd5
  have hf6 := memoryFundingAt (credit := transferHeapCredit root) rd6
    (hf2.mono (by omega))
  refine ⟨_, _, _, ?_, rd6⟩
  exact { hh with
    covered := hh.covered.trans (Nat.mul_le_mul_left 32 (memoryWords_ge aw _ _))
    funding := hf6 }

end Benchmarks.Midnight
