import Benchmarks.UniswapV4PoolManager.PoolSwapSlot0Packing
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_062

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapSlot0AW (aw state : UInt256) : UInt256 :=
  M (M (M aw (state+UInt256.ofNat 32) ⟨32⟩) state ⟨32⟩) (state+UInt256.ofNat 64) ⟨32⟩

theorem poolSwapLiquidityStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id liquidity step : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024)
    (hI : evm.executionEnv = I) (hperm : I.perm = true) (hl : liquidity.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨21813⟩ (liquidity :: step :: poolSlot id :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨21698⟩ (⟨0⟩ :: step :: poolSlot id :: R)
      mem aw rdata (poolLiquidityStore evm id liquidity).accountMap k' C' := by
  obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_21813 hstack hperm
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  have hread : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac => ac.storage.getD (poolSlot id+UInt256.ofNat 3) ⟨0⟩)) = poolLiquidityPacked evm id :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  have hclean : UInt256.land (UInt256.ofNat 340282366920938463463374607431768211455) liquidity = liquidity := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat liquidity _ rfl hl
  simp only [poolManagerBlocks.poolManager_block_21813_stack, hread, hclean] at rd1
  rw [u256_land_comm (poolLiquidityPacked evm id)
    (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480)] at rd1
  refine ⟨k1, C1, ?_⟩
  rw [poolLiquidityStore, storageStore_accountMap, hI]
  exact rd1

theorem poolSwapSlot0StoreTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id packed remaining ret params calculated fee protocol amount inv step state : UInt256}
    {r : PoolSwapResultWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (hI : evm.executionEnv = I) (hperm : I.perm = true)
    (hp : r.price.toNat < 2^160) (hl : r.liquidity.toNat < 2^128)
    (hmprice : memLoad state mem = r.price)
    (hmtick : memLoad (state+UInt256.ofNat 32) mem = r.tick)
    (hmliq : memLoad (state+UInt256.ofNat 64) mem = r.liquidity)
    (h : RD (deployedRuntime v) I g s0 ⟨21536⟩
      ([remaining, ret, params, calculated, packed, fee, protocol, amount, inv, step, poolSlot id, state]++R)
      mem aw rdata evm.accountMap k C) :
    ∃ dummy k' C', RD (deployedRuntime v) I g s0 ⟨21698⟩
      ([dummy, step, poolSlot id, inv, remaining, params, calculated, state, fee, amount, ret]++R)
      mem (poolSwapSlot0AW aw state) rdata
      (poolSwapLiquidityPost (poolSwapSlot0Post evm id packed r) id r.liquidity).accountMap k' C' := by
  let post := poolSwapSlot0Post evm id packed r
  have hIp : post.executionEnv = I := (poolSwapSlot0Post_executionEnv ..).trans hI
  have hword : UInt256.lor (UInt256.lor
      (UInt256.land packed (UInt256.ofNat 115792089237316195423546465080034053631536251113206159092519684181958192005120))
      (UInt256.land (UInt256.ofNat 24519927192352584402830634230720114221616806299005091840)
        (UInt256.shiftLeft (memLoad (state+UInt256.ofNat 32) mem) (UInt256.ofNat 160))))
      (UInt256.land (memLoad state mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) =
      poolSwapSlot0Word packed r := by
    rw [hmtick, hmprice]
    exact poolSwapSlot0Word_compiled packed r hp
  have hacct : post.accountMap = sstoreAccountMap I.codeOwner evm.accountMap (poolSlot id) (poolSwapSlot0Word packed r) := by
    dsimp only [post, poolSwapSlot0Post]
    rw [storageStore_accountMap, hI]
  have hread : UInt256.land (post.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac => ac.storage.getD (poolSlot id+UInt256.ofNat 3) ⟨0⟩))
      (UInt256.ofNat 340282366920938463463374607431768211455) = poolLiquidityWord post id :=
    congrArg (fun w => UInt256.land w (UInt256.ofNat 340282366920938463463374607431768211455))
      (storageLoad_codeOwner_eq_solcSlotWordAt post I (poolSlot id+UInt256.ofNat 3) (by rw [hIp])).symm
  have hclean : UInt256.land r.liquidity (UInt256.ofNat 340282366920938463463374607431768211455) = r.liquidity :=
    u256LandMaskCleanOfToNat r.liquidity _ rfl hl
  by_cases he : poolLiquidityWord post id = r.liquidity
  · obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_21536_fallthrough hstack hperm
      (by rw [hword, ← hacct, hread, hmliq, hclean]; exact u256_sub_eq_zero_iff_eq.mpr he) h
    simp only [poolManagerBlocks.poolManager_block_21536_fallthrough_stack, hmliq, hclean, hword, ← hacct] at rd1
    rw [poolSwapLiquidityPost, if_pos he]
    exact ⟨r.liquidity, k1, C1, rd1⟩
  · obtain ⟨k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_21536_taken hstack hperm
      (by rw [hword, ← hacct, hread, hmliq, hclean]; exact fun hh => he (u256_sub_eq_zero_iff_eq.mp hh))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_21536_taken_stack, hmliq, hclean, hword, ← hacct] at rd1
    obtain ⟨k2, C2, rd2⟩ := poolSwapLiquidityStoreTrace v
      (by change R.length+8+6 ≤ 1024; omega) hIp hperm hl rd1
    rw [poolSwapLiquidityPost, if_neg he]
    exact ⟨⟨0⟩, k2, C2, rd2⟩

end Benchmarks.UniswapV4PoolManager
