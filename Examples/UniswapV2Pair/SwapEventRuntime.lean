import Examples.UniswapV2Pair.QuadDynamicMemory
import Examples.UniswapV2Pair.SwapUpdateRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000

abbrev uniswapSwapTopic : UInt256 :=
  ⟨97492587597809768260878645486617631645481691101407825574583615073533464008738⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapEmitEvent {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {amount1In amount0In balance1 balance0 reserve1 reserve0 dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {aw ptr : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd2712 : RD uniswapV2PairBytecode I g s0 ⟨2712⟩
      (amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 159 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hperm : I.perm = true) (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2797⟩
      (amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R)
      (quadDynamicMem mem ptr amount0In amount1In amount0Out amount1Out)
      (quadDynamicWords aw ptr) rdata acc k' C' := by
  have h64 : (⟨64⟩ : UInt256).toNat + 32 ≤ aw.toNat * 32 := by change 64 + 32 ≤ _; omega
  have hw64 := UInt256_M_same_of_cover aw ⟨64⟩ haw h64
  change memoryWordActiveWords aw ⟨64⟩ = aw at hw64
  have hm64 : memoryWordLoad mem aw ⟨64⟩ = ptr := mloadWordValue_of_readWithPadding
    (by change 64 < _; omega) (UInt256_mload_haw_of_cover aw ⟨64⟩ haw h64) hread
  have hw0 := UInt256_M_same_of_cover aw ptr haw (by omega)
  change memoryWordActiveWords aw ptr = aw at hw0
  have h32 : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hw1 := UInt256_M_same_of_cover aw (ptr + ⟨32⟩) haw (by rw [h32]; omega)
  change memoryWordActiveWords aw (ptr + ⟨32⟩) = aw at hw1
  have hwPair : pairDynamicWords aw ptr = aw := by
    unfold pairDynamicWords pairDynamicWords0
    rw [hw0, hw1]
  have hsum : (ptr + ⟨64⟩) + ⟨32⟩ = ptr + ⟨96⟩ := by
    rw [u256_add_assoc, show (⟨64⟩ : UInt256) + ⟨32⟩ = ⟨96⟩ by native_decide]
  have rd2716 := evm_run rd2712 with [jumpdest, push1 ⟨64⟩, dup1]
  have rd2717 := RD.mloadWord rd2716 (by native_decide) hm64 (by evm_ov)
  rw [hw64] at rd2717
  have rd2719 := evm_run rd2717 with [dup4, dup2]
  have rd2720 := RD.mstoreWord rd2719 (by native_decide) (by evm_ov)
  rw [hw0] at rd2720
  have rd2726 := evm_run rd2720 with [push1 ⟨32⟩, dup2, add, dup4, swap1]
  have rd2727 := RD.mstoreWord rd2726 (by native_decide) (by evm_ov)
  rw [hw1] at rd2727
  have rd2732 := evm_run rd2727 with [dup1, dup3, add, dup14, swap1]
  rw [u256_add_comm (⟨64⟩ : UInt256) ptr] at rd2732
  have rd2733 := RD.mstoreWord rd2732 (by native_decide) (by evm_ov)
  have rd2739 := evm_run rd2733 with [push1 ⟨96⟩, dup2, add, dup13, swap1]
  have rd2740 := RD.mstoreWord rd2739 (by native_decide) (by evm_ov)
  have rd2741 := evm_run rd2740 with [swap1]
  have hmLog := (quadDynamicMem_mload64 aw ptr amount0In amount1In amount0Out amount1Out hin hlo hgap hfit haw hread).1
  have hwLog64 := (quadDynamicMem_mload64 aw ptr amount0In amount1In amount0Out amount1Out hin hlo hgap hfit haw hread).2
  have hwQuad : quadDynamicWords aw ptr = pairDynamicWords aw (ptr + ⟨64⟩) := by
    unfold quadDynamicWords
    rw [hwPair]
  simp only [quadDynamicMem, pairDynamicMem, pairDynamicMem0, hwQuad, pairDynamicWords, pairDynamicWords0, hsum] at hmLog hwLog64
  have rd2742 := RD.mloadWord rd2741 (by native_decide) hmLog (by evm_ov)
  rw [hwLog64] at rd2742
  have rd2755 := evm_run rd2742 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup12, and, swap2, caller, swap2]
  have rd2788 := RD.pushConst rd2755 uniswapSwapTopic (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd2796 := evm_run rd2788 with [swap2, dup2, swap1, sub, push1 ⟨128⟩, add, swap1]
  rw [u256_sub_self, show (⟨128⟩ : UInt256) + ⟨0⟩ = ⟨128⟩ by native_decide] at rd2796
  have hcoverQ := (quadDynamicWords_bounds aw ptr haw hfit).2
  have hwLog := UInt256_M_same_of_cover_len (quadDynamicWords aw ptr) ptr 128 hcoverQ
  simp only [hwQuad, pairDynamicWords, pairDynamicWords0, hsum] at hwLog
  simpa only [quadDynamicMem, pairDynamicMem, pairDynamicMem0, hwQuad,
    pairDynamicWords, pairDynamicWords0, hsum] using
    (show ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2797⟩ _ _ _ rdata acc k' C' from
      ⟨_, _, RD.log3 0 _ rd2796 (by native_decide) hperm (by
        intro s haws hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        change Cₘ (UInt256.ofNat (MachineState.M _ ptr.toNat 128)) - Cₘ _ = 0
        rw [hwLog, Nat.sub_self]) hwLog (by evm_ov)⟩)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapUnlockAndStop {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {amount1In amount0In balance1 balance0 reserve1 reserve0 dataLen dataPtr toWord amount1Out amount0Out : UInt256}
    {aw : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : Nat}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd2797 : RD uniswapV2PairBytecode I g s0 ⟨2797⟩
      (amount1In :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: ⟨570⟩ :: R) mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hov : R.length + 14 ≤ 1024) :
    RDret uniswapV2PairBytecode g s0 (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨1⟩) ByteArray.empty := by
  have rd2803 := evm_run rd2797 with [pop, pop, push1 ⟨1⟩, push1 ⟨12⟩]
  obtain ⟨_, _, rd2804⟩ := rd2803.sstore hperm (by native_decide) (by evm_ov)
  have rd571 := evm_run rd2804 with [pop, pop, pop, pop, pop, pop, pop, pop, pop,
    jump (by jump_dest), jumpdest]
  exact rd571.stop (by native_decide) (by evm_ov)

end UniswapV2Pair
