import Benchmarks.Midnight.MarketCalldataHead
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.RuntimeBlocks_023
import Benchmarks.Midnight.RuntimeBlocks_032

/-! The liquidator gate address is read from the already validated calldata market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 2000000

theorem decodeCalldataMarket_liquidatorGate {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    calldataWord bytes (calldataWord bytes 4 + UInt256.ofNat 228).toNat =
      UInt256.ofNat m.liquidatorGate.val := by
  dsimp only [decodeCalldataMarket] at hd
  split at hd
  · cases hd
  · rename_i hbound
    have hr : (calldataWord bytes 4).toNat < 2^64 := by
      change ¬ (2^64 - 1 < _ ∨ _) at hbound
      omega
    obtain ⟨_, hcanon, _, _, _, cs, _, he⟩ := decodeMarketData_success hd
    rw [he, uadd_word_ofNat_toNat _ 228 (by change _ < 2^256; omega)]
    have ho : (calldataWord bytes 4).toNat + 228 = 4 + (calldataWord bytes 4).toNat + 224 := by
      omega
    rw [ho]
    exact (addressWord_eq_ofNat_address hcanon.2.2.2).symm

theorem midnightLiquidatorGateHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {m : MarketData}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hd : decodeCalldataMarket ee.calldata 4 = some m)
    (rd : RD midnightBytecode ee g s0 ⟨5275⟩ R mem aw rdata σ k C) :
    (m.liquidatorGate = 0 ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode ee g s0 ⟨5311⟩ R mem aw rdata σ k' C') ∨
    (m.liquidatorGate ≠ 0 ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode ee g s0 ⟨8315⟩
        (UInt256.ofNat m.liquidatorGate.val :: solcAddrMask :: UInt256.ofNat 32 ::
          UInt256.ofNat 36 :: R) mem aw rdata σ k' C') := by
  have hw := decodeCalldataMarket_liquidatorGate hd
  have hc : (calldataWord ee.calldata
      (calldataWord ee.calldata 4 + UInt256.ofNat 228).toNat).toNat < EVM.addressModulus := by
    rw [hw]
    exact addressWord_val_canonical _
  have rd1 := midnight_block_5275 (by omega) (by jump_dest) rd
  have rd2 := midnight_block_19691_fallthrough
    (by simp only [List.length_cons]; omega) (addressCheck_zero hc) rd1
  have rd3 := midnight_block_19709 (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  change RD midnightBytecode ee g s0 ⟨5296⟩
    (calldataWord ee.calldata (calldataWord ee.calldata 4 + UInt256.ofNat 228).toNat ::
      solcAddrMask :: R) mem aw rdata σ _ _ at rd3
  rw [hw] at rd3
  have hclean : UInt256.land (UInt256.ofNat m.liquidatorGate.val) solcAddrMask =
      UInt256.ofNat m.liquidatorGate.val := addressWord_val_clean m.liquidatorGate
  by_cases hz : m.liquidatorGate = 0
  · have hw0 : UInt256.ofNat m.liquidatorGate.val = (⟨0⟩ : UInt256) := by rw [hz]; rfl
    have rd4 := midnight_block_5296_fallthrough (by omega)
      (by rw [hclean, hw0]; decide) rd3
    have rd5 := midnight_block_5305_fallthrough (by omega)
      (by simp only [midnight_block_5296_fallthrough_stack, hclean, hw0]; decide) rd4
    exact Or.inl ⟨hz, _, _, by omega, rd5⟩
  · have hw0 : UInt256.ofNat m.liquidatorGate.val ≠ (⟨0⟩ : UInt256) := by
      intro h
      apply hz
      apply Fin.ext
      have ha : m.liquidatorGate.val < 2^160 := m.liquidatorGate.isLt
      have he := congrArg UInt256.toNat h
      rw [UInt256.toNat_ofNat_of_lt (by change m.liquidatorGate.val < 2^256; omega)] at he
      exact he
    have rd4 := midnight_block_5296_taken (by omega)
      (by rw [hclean, isZero_eq_zero_of_ne hw0]; decide) (by jump_dest) rd3
    have rd5 := midnight_block_8288 (by omega) (by jump_dest) rd4
    have rd6 := midnight_block_19691_fallthrough
      (by simp only [List.length_cons]; omega) (addressCheck_zero hc) rd5
    have rd7 := midnight_block_19709 (by simp only [List.length_cons]; omega)
      (by jump_dest) rd6
    change RD midnightBytecode ee g s0 ⟨8315⟩
      (calldataWord ee.calldata (calldataWord ee.calldata 4 + UInt256.ofNat 228).toNat ::
        solcAddrMask :: UInt256.ofNat 32 :: UInt256.ofNat 36 :: R)
      mem aw rdata σ _ _ at rd7
    rw [hw] at rd7
    exact Or.inr ⟨hz, _, _, by omega, rd7⟩

end Benchmarks.Midnight
