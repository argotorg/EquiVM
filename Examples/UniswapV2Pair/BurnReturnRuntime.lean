import Examples.UniswapV2Pair.PairDynamicReturnMemory
import Examples.UniswapV2Pair.Routines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnReturnPair {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {amount1 amount0 aw ptr : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨1201⟩ (amount1 :: amount0 :: R) mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 95 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 5 ≤ 1024) :
    RDret uniswapV2PairBytecode g s0 acc (amount0.toByteArray ++ amount1.toByteArray) := by
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
  have hmLog := (pairDynamicMem_mload64 aw ptr amount0 amount1 hin hlo hgap hfit haw hread).1
  rw [hwPair] at hmLog
  have rd1205 := evm_run rd with [jumpdest, push1 ⟨64⟩, dup1]
  have rd1206 := RD.mloadWord rd1205 (by native_decide) hm64 (by evm_ov)
  rw [hw64] at rd1206
  have rd1208 := evm_run rd1206 with [swap3, dup4]
  have rd1209 := RD.mstoreWord rd1208 (by native_decide) (by evm_ov)
  rw [hw0] at rd1209
  have rd1216 := evm_run rd1209 with [push1 ⟨32⟩, dup4, add, swap2, swap1, swap2]
  have rd1217 := RD.mstoreWord rd1216 (by native_decide) (by evm_ov)
  rw [hw1] at rd1217
  have rd1218 := evm_run rd1217 with [dup1]
  have rd1219 := RD.mloadWord rd1218 (by native_decide) hmLog (by evm_ov)
  rw [hw64] at rd1219
  have rd1225 := evm_run rd1219 with [swap2, dup3, swap1, sub, add, swap1]
  rw [u256_sub_self, show (⟨0⟩ : UInt256) + ⟨64⟩ = ⟨64⟩ by rfl] at rd1225
  have hwRet := UInt256_M_same_of_cover_len aw ptr 64 hcover
  exact rd1225.ret 0 _ (by native_decide) (by
    intro s haws hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    change Cₘ (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 64)) - Cₘ aw = 0
    rw [hwRet, Nat.sub_self])
    (pairDynamicMem_read_ptr ptr amount0 amount1 hgap (by omega)) (by evm_ov)

end UniswapV2Pair
