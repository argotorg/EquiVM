import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeMemory
import Benchmarks.UniswapV4PoolManager.PoolSwapProtocolInitSource
import Benchmarks.UniswapV4PoolManager.ProtocolSwapFeeTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapProtocolCostBlock

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapProtocolLoadTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id state params ret amount : UInt256} {zeroForOne : Bool}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+13 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (params+UInt256.ofNat 64) (poolSwapResultZeroMem mem state) = UInt256.fromBool zeroForOne)
    (h : RD (deployedRuntime v) I g s0 ⟨18793⟩
      ([amount, params, ret, poolSlot id, state]++R) mem aw rdata evm.accountMap k C) :
    ∃ k' C', C ≤ C' ∧ C+Cₘ (poolSwapResultZeroAW aw state params) ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ⟨18842⟩
      ([ret, params, state+UInt256.ofNat 32, state+UInt256.ofNat 64, state,
        poolSwapProtocolWord (poolSlot0Word evm id) zeroForOne, amount, UInt256.fromBool (!zeroForOne),
        poolSlot0Word evm id, poolSlot id, state]++R)
      (poolSwapResultZeroMem mem state) (poolSwapResultZeroAW aw state params) rdata evm.accountMap k' C' := by
  have hmRaw := hm
  dsimp only [poolSwapResultZeroMem, Reasoning.Theory.writeWord] at hmRaw
  have hslot : (evm.accountMap.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac => ac.storage.getD (poolSlot id) ⟨0⟩)) = poolSlot0Word evm id :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I (poolSlot id) (by rw [hI])).symm
  obtain ⟨k1, C1, hc1, hp1, rd1⟩ := poolSwapProtocolCostBlock (R := R) (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_18793_taken_stack, hmRaw, hslot] at rd1
  have hfirst : RD (deployedRuntime v) I g s0
      (if zeroForOne then ⟨18833⟩ else ⟨22261⟩)
      ([params, state+UInt256.ofNat 32, state+UInt256.ofNat 64, state, ret, amount,
        UInt256.fromBool (!zeroForOne), poolSlot0Word evm id, poolSlot id, state]++R)
      (poolSwapResultZeroMem mem state) (poolSwapResultZeroAW aw state params) rdata evm.accountMap k1 C1 := by
    cases zeroForOne <;> exact rd1
  have rd2 := protocolFeeDirectionTrace v zeroForOne (by change R.length+2+11 ≤ 1024; omega) hfirst
  exact ⟨_, _, by omega, by omega, rd2⟩

end Benchmarks.UniswapV4PoolManager
