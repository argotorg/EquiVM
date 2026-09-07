import Examples.UniswapV2Pair.SyncDynamicCore
import Examples.UniswapV2Pair.Dup16Routines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach


namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev uniswapBurnTopic : UInt256 :=
  ⟨99871480218394181533792129255988232578950765970976763863841734512143989171350⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnEmitEvent {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {supply fee liquidity balance1 balance0 token1 token0 reserve1 reserve0 amount1 amount0 toWord ret : UInt256}
    {aw ptr : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4933⟩
      (supply :: fee :: liquidity :: balance1 :: balance0 :: token1 :: token0 :: reserve1 :: reserve0 ::
        amount1 :: amount0 :: toWord :: ret :: R) mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 95 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hcover : ptr.toNat + 64 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hperm : I.perm = true) (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨5006⟩
      (supply :: fee :: liquidity :: balance1 :: balance0 :: token1 :: token0 :: reserve1 :: reserve0 ::
        amount1 :: amount0 :: toWord :: ret :: R)
      (pairDynamicMem mem ptr amount0 amount1) aw rdata acc k' C' := by
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
  have rd4937 := evm_run rd with [jumpdest, push1 ⟨64⟩, dup1]
  have rd4938 := RD.mloadWord rd4937 (by native_decide) hm64 (by evm_ov)
  rw [hw64] at rd4938
  have rd4940 := evm_run rd4938 with [dup13, dup2]
  have rd4941 := RD.mstoreWord rd4940 (by native_decide) (by evm_ov)
  rw [hw0] at rd4941
  have rd4947 := evm_run rd4941 with [push1 ⟨32⟩, dup2, add, dup13, swap1]
  have rd4948 := RD.mstoreWord rd4947 (by native_decide) (by evm_ov)
  rw [hw1] at rd4948
  have rd4949 := evm_run rd4948 with [dup2]
  have rd4950 := RD.mloadWord rd4949 (by native_decide) hmLog (by evm_ov)
  rw [hw64] at rd4950
  have rd4963 := evm_run rd4950 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup16, and, swap3, caller, swap3]
  have rd4996 := rd4963.pushConst uniswapBurnTopic (width := 32) (op := .PUSH32)
    (by native_decide) (by decide) (by evm_ov)
  have rd5005 := evm_run rd4996 with [swap3, swap1, dup2, swap1, sub, swap1, swap2, add, swap1]
  rw [u256_sub_self, show (⟨64⟩ : UInt256) + ⟨0⟩ = ⟨64⟩ by rfl] at rd5005
  have hwLog := UInt256_M_same_of_cover_len aw ptr 64 hcover
  exact ⟨_, _, rd5005.log3 0 aw (by native_decide) hperm (by
    intro s haws hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    change Cₘ (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 64)) - Cₘ aw = 0
    rw [hwLog, Nat.sub_self]) hwLog (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnUnlockAndJump {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {supply fee liquidity balance1 balance0 token1 token0 reserve1 reserve0 amount1 amount0 toWord ret : UInt256}
    {aw : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : Nat}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨5006⟩
      (supply :: fee :: liquidity :: balance1 :: balance0 :: token1 :: token0 :: reserve1 :: reserve0 ::
        amount1 :: amount0 :: toWord :: ret :: R) mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hret : (D_J uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ret (amount1 :: amount0 :: R) mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨1⟩) k' C' := by
  have rd5021 := evm_run rd with [pop, pop, pop, pop, pop, pop, pop, pop, pop,
    push1 ⟨1⟩, push1 ⟨12⟩, dup2, swap1]
  obtain ⟨_, _, rd5022⟩ := rd5021.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd5022 with [pop, swap2, pop, swap2, jump hret]⟩

end UniswapV2Pair
