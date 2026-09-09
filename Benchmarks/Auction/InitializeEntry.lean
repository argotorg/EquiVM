import Benchmarks.Auction.InitializeMaps

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000

namespace Auction

def auctionInitializableAlreadyStringWord1 : UInt256 :=
  ⟨0x496e697469616c697a61626c653a20636f6e747261637420697320616c726561⟩

def auctionInitializableAlreadyRawStringWord2 : UInt256 :=
  ⟨0x191e481a5b9a5d1a585b1a5e9959⟩

def auctionInitializableAlreadyStringWord2 : UInt256 :=
  UInt256.shiftLeft auctionInitializableAlreadyRawStringWord2 ⟨146⟩

noncomputable def auctionInitializableAlreadyStringMem4 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray auctionInitializableAlreadyStringWord2).write 0
    (solcErrorStringMem3 ⟨46⟩ auctionInitializableAlreadyStringWord1 mem) 228 32

theorem auctionInitializableAlreadyStringMem4_read64 :
    (auctionInitializableAlreadyStringMem4 solcFreePtrMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold auctionInitializableAlreadyStringMem4
  rw [toByteArray_write_read_below_of_gap auctionInitializableAlreadyStringWord2
    (solcErrorStringMem3 ⟨46⟩ auctionInitializableAlreadyStringWord1 solcFreePtrMem) 228 64]
  · exact solcErrorStringMem3_read64 ⟨46⟩ auctionInitializableAlreadyStringWord1
      solcFreePtrMem_size solcFreePtrMem_read64
  · rw [solcErrorStringMem3_size ⟨46⟩ auctionInitializableAlreadyStringWord1
      solcFreePtrMem_size]
    omega
  · omega
  · rw [solcErrorStringMem3_size ⟨46⟩ auctionInitializableAlreadyStringWord1
      solcFreePtrMem_size]
    native_decide

theorem auctionInitializableAlreadyStringMem4_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionInitializableAlreadyStringMem4 solcFreePtrMem).size
        ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 9) * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((auctionInitializableAlreadyStringMem4 solcFreePtrMem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = (⟨128⟩ : UInt256) := by
  apply mloadFreePtrValue
  · unfold auctionInitializableAlreadyStringMem4
    have hge := toByteArray_write_size_ge_off_add32 auctionInitializableAlreadyStringWord2
      (solcErrorStringMem3 ⟨46⟩ auctionInitializableAlreadyStringWord1 solcFreePtrMem) 228 (by
        rw [solcErrorStringMem3_size ⟨46⟩ auctionInitializableAlreadyStringWord1
          solcFreePtrMem_size]
        native_decide)
    omega
  · decide
  · exact auctionInitializableAlreadyStringMem4_read64

set_option maxHeartbeats 1000000 in
theorem auctionInitializeX_toCore_nested {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hnz : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ ≠ ⟨0⟩)
    (hdecoded : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2130⟩
      [auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2213⟩
      [⟨0⟩, auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2130⟩ := hdecoded
  have rd2132₀ := evm_run rd2130 with [jumpdest, push0]
  obtain ⟨_, _, rd2133₀⟩ := rd2132₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2133⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2133⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2133₀⟩
  have rd2142₀ := evm_run rd2133 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hinitComm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hnz' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ≠ ⟨0⟩ := by
    simpa [hinitComm] using hnz
  have rd2153 := evm_run rd2142₀ with [
    push2 ⟨2153⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd2181 := evm_run rd2153 with [
    push2 ⟨2181⟩, jumpiT hnz' (by jump_dest), jumpdest]
  have rd2183₀ := evm_run rd2181 with [push0]
  obtain ⟨_, _, rd2184₀⟩ := rd2183₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2184⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2184⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2184₀⟩
  have rd2195₀ := evm_run rd2184 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hiz : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨0⟩ :=
    isZero_eq_zero_of_ne hnz'
  have rd2195 := rd2195₀
  rw [hiz] at rd2195
  exact ⟨_, _, evm_run rd2195 with [
    push2 ⟨2213⟩, jumpiT (by native_decide) (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeX_toCore_top {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true)
    (hinitZero : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ =
      ⟨0⟩)
    (hinitializedZero : UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ = ⟨0⟩)
    (hdecoded : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2130⟩
      [auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2213⟩
      [⟨1⟩, auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (setBoolOffset0Word (auctionSetBoolOffset1TrueWord (auctionSlotWord ⟨0⟩ σ I)) ⟨1⟩))
      k C := by
  obtain ⟨_, _, rd2130⟩ := hdecoded
  have rd2132₀ := evm_run rd2130 with [jumpdest, push0]
  obtain ⟨_, _, rd2133₀⟩ := rd2132₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2133⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2133⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2133₀⟩
  have rd2142₀ := evm_run rd2133 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hinitComm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hinitZero' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) = ⟨0⟩ := by
    simpa [hinitComm] using hinitZero
  have rd2142 := rd2142₀
  rw [hinitZero'] at rd2142
  have rd2147 := evm_run rd2142 with [
    push2 ⟨2153⟩, jumpiNT (by native_decide), pop, push0]
  obtain ⟨_, _, rd2149₀⟩ := rd2147.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2149⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2149⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2149₀⟩
  have rd2153₀ := evm_run rd2149 with [push1 ⟨255⟩, and, iszero]
  have hinitdComm : UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I)
  have hinitializedZero' : UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I) = ⟨0⟩ := by
    simpa [hinitdComm] using hinitializedZero
  have hiszeroInitd :
      UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I)) = ⟨1⟩ := by
    rw [hinitializedZero']
    decide
  have rd2153 := rd2153₀
  rw [hiszeroInitd] at rd2153
  have rd2181 := evm_run rd2153 with [
    jumpdest, push2 ⟨2181⟩, jumpiT (by native_decide) (by jump_dest), jumpdest]
  have rd2183₀ := evm_run rd2181 with [push0]
  obtain ⟨_, _, rd2184₀⟩ := rd2183₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2184⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2184⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2184₀⟩
  have rd2195₀ := evm_run rd2184 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, iszero, dup1, iszero]
  have hisTop : UInt256.isZero
      (UInt256.land ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)) =
        ⟨1⟩ := by
    rw [hinitZero']
    decide
  have rd2195 := rd2195₀
  rw [hisTop] at rd2195
  have rd2200 := evm_run rd2195 with [
    push2 ⟨2213⟩, jumpiNT (by native_decide), push0, dup1]
  obtain ⟨_, _, rd2202₀⟩ := rd2200.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2202⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2202⟩
      [auctionSlotWord ⟨0⟩ σ I, ⟨0⟩, ⟨1⟩, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I,
        auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2202₀⟩
  have rd2212₀ := evm_run rd2202 with [
    push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have rd2212₁ := RD.lor rd2212₀ (by native_decide) (by evm_ov)
  have hlor : UInt256.lor ⟨257⟩
      (UInt256.land (UInt256.lnot ⟨65535⟩) (auctionSlotWord ⟨0⟩ σ I)) =
        setBoolOffset0Word (auctionSetBoolOffset1TrueWord (auctionSlotWord ⟨0⟩ σ I)) ⟨1⟩ := by
    rw [u256_land_comm]
    rw [u256_lor_comm]
    exact (auctionSetBoolOffset1TrueThenOffset0True_eq_mask
      (auctionSlotWord ⟨0⟩ σ I)).symm
  have rd2212 := rd2212₁
  rw [hlor] at rd2212
  have rd2213₀ := evm_run rd2212 with [swap1]
  obtain ⟨_, _, rd2213₁⟩ := rd2213₀.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [sstoreAccountMap] using rd2213₁⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializeX_revert_initialized {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hinitZero : UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ =
      ⟨0⟩)
    (hinitializedNz : UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ ≠ ⟨0⟩)
    (hdecoded : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2130⟩
      [auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2130⟩ := hdecoded
  have rd2132₀ := evm_run rd2130 with [jumpdest, push0]
  obtain ⟨_, _, rd2133₀⟩ := rd2132₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2133⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2133⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2133₀⟩
  have rd2142₀ := evm_run rd2133 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1]
  have hinitComm : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) =
        UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩)
  have hinitZero' : UInt256.land ⟨255⟩
      (UInt256.div (auctionSlotWord ⟨0⟩ σ I) ⟨256⟩) = ⟨0⟩ := by
    simpa [hinitComm] using hinitZero
  have rd2142 := rd2142₀
  rw [hinitZero'] at rd2142
  have rd2147 := evm_run rd2142 with [
    push2 ⟨2153⟩, jumpiNT (by native_decide), pop, push0]
  obtain ⟨_, _, rd2149₀⟩ := rd2147.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2149⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2149⟩
      [auctionSlotWord ⟨0⟩ σ I, auctionInitializeDurationWord I,
        auctionInitializeMinBidIncrementPercentageWord I, auctionInitializeReservePriceWord I,
        auctionInitializeTimeBufferWord I, auctionInitializeWethWord I, auctionInitializeNounsWord I,
        ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd2149₀⟩
  have rd2153₀ := evm_run rd2149 with [push1 ⟨255⟩, and, iszero]
  have hinitdComm : UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨0⟩ σ I) ⟨255⟩ :=
    u256_land_comm ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I)
  have hinitializedNz' : UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I) ≠ ⟨0⟩ := by
    simpa [hinitdComm] using hinitializedNz
  have hiszeroInitd :
      UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨0⟩ σ I)) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hinitializedNz'
  have rd2153 := rd2153₀
  rw [hiszeroInitd] at rd2153
  have rd2158 := evm_run rd2153 with [jumpdest, push2 ⟨2181⟩, jumpiNT (by native_decide)]
  have rd2161 := evm_run rd2158 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by native_decide) (by evm_ov)]
  have rd2165 := rd2161.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd2173₀ := evm_run rd2165 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 6 (solcErrorStringMem0 solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, add]
  have rd2173 := rd2173₀
  rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ by decide] at rd2173
  have rd5742 := evm_run rd2173 with [
    push2 ⟨994⟩, swap1, push2 ⟨5742⟩, jump (by jump_dest)]
  have rd5754 := evm_run rd5742 with [
    jumpdest, push1 ⟨32⟩, dup1, dup3,
    raw mstore 3 (solcErrorStringMem1 solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨46⟩, swap1, dup3, add,
    raw mstore 3 (solcErrorStringMem2 ⟨46⟩ solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd5787 := rd5754.pushConst auctionInitializableAlreadyStringWord1
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd5792 := evm_run rd5787 with [
    push1 ⟨64⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 ⟨46⟩ auctionInitializableAlreadyStringWord1 solcFreePtrMem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd5807 := rd5792.pushConst auctionInitializableAlreadyRawStringWord2
    (width := 14) (op := .PUSH14) (by native_decide) (by native_decide) (by evm_ov)
  have rd5809₀ := evm_run rd5807 with [push1 ⟨146⟩, shl]
  have rd5809 := rd5809₀
  rw [show UInt256.shiftLeft auctionInitializableAlreadyRawStringWord2 ⟨146⟩ =
      auctionInitializableAlreadyStringWord2 by rfl] at rd5809
  have rd5819₀ := evm_run rd5809 with [
    push1 ⟨96⟩, dup3, add,
    raw mstore 3 (auctionInitializableAlreadyStringMem4 solcFreePtrMem)
      (UInt256.ofNat 9) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨128⟩, add, swap1]
  have rd5819 := rd5819₀
  rw [show (⟨128⟩ : UInt256) + ⟨132⟩ = ⟨260⟩ by decide] at rd5819
  have rd994 := evm_run rd5819 with [jump (by jump_dest)]
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost auctionInitializableAlreadyStringMem4_mload64 (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [show UInt256.sub (⟨260⟩ : UInt256) ⟨128⟩ = ⟨132⟩ by decide] at rd1001
  exact evm_run rd1001 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]



end Auction
