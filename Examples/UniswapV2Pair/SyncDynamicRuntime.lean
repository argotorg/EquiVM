import Examples.UniswapV2Pair.SyncDynamicCore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem RD.uniswapUpdateEmitSyncAndJump_dynamic {g : Sat256} {s0 : State}
    {I : ExecutionEnv} {k C : Nat}
    {packed elapsed timestamp reserve1 reserve0 balance1 balance0 ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw ptr : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨7339⟩
      (reserve112Shift :: reserve112Mask :: packed :: elapsed :: timestamp :: reserve1 ::
        reserve0 :: balance1 :: balance0 :: ret :: R) mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 95 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hperm : I.perm = true) (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ret R
      (pairDynamicMem mem ptr (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed))
      (pairDynamicWords aw ptr) rdata acc k' C' := by
  have h64 : (⟨64⟩ : UInt256).toNat + 32 ≤ aw.toNat * 32 := hawLo
  have hw64 := UInt256_M_same_of_cover aw ⟨64⟩ haw h64
  have hm64 : memoryWordLoad mem aw ⟨64⟩ = ptr := mloadWordValue_of_readWithPadding
    (by change 64 < _; omega) (UInt256_mload_haw_of_cover aw ⟨64⟩ haw h64) hread
  obtain ⟨hmLog, hwLog⟩ := pairDynamicMem_mload64 aw ptr
    (uniswapSyncReserve0Word packed) (uniswapSyncReserve1Word packed) hin hlo hgap hfit haw hread
  have hcLog := (pairDynamicWords_bounds aw ptr haw hfit).2
  have hwLog64 := UInt256_M_same_of_cover_len (pairDynamicWords aw ptr) ptr 64 hcLog
  have hlen : (⟨64⟩ : UInt256) + UInt256.sub ptr ptr = ⟨64⟩ := by
    rw [u256_sub_self]
    rfl
  refine RD.uniswapUpdateEmitSyncAndJumpCore (awLoad := aw)
    (awStore0 := pairDynamicWords0 aw ptr)
    (mcostLoad := 0) (mcostStore0 := Cₘ (pairDynamicWords0 aw ptr) - Cₘ aw)
    (mcostStore1 := Cₘ (pairDynamicWords aw ptr) - Cₘ (pairDynamicWords0 aw ptr))
    (mcostLoadLog := 0) (mcostLog := 0) rd ?_ hm64 hw64 ?_ rfl ?_ rfl ?_ hmLog hwLog ?_ ?_
    hperm hret hov
  · intro s haws hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk,
      List.getElem!_cons_zero, hw64, Nat.sub_self]
  · intro s haws hstk
    exact mstoreCost_of_stack haws hstk rfl
  · intro s haws hstk
    exact mstoreCost_of_stack haws hstk rfl
  · intro s haws hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk,
      List.getElem!_cons_zero, hwLog, Nat.sub_self]
  · intro s haws hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk,
      List.getElem!_cons_zero, List.getElem!_cons_succ, hlen]
    change Cₘ (UInt256.ofNat (MachineState.M (pairDynamicWords aw ptr).toNat ptr.toNat 64)) - Cₘ (pairDynamicWords aw ptr) = 0
    rw [hwLog64, Nat.sub_self]
  · simpa only [hlen] using hwLog64

end UniswapV2Pair
