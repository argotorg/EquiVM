import Benchmarks.UniswapV4PoolManager.PoolInitializeTrace
import Benchmarks.UniswapV4PoolManager.TransientTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolInitializeGuardTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw x0 x1 price id currency1Ptr feePtr hooksPtr keyPtr spacingPtr fee : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 12 ≤ 1024) (hI : evm.executionEnv = I)
    (hid : keccakWord keyPtr (UInt256.ofNat 160) mem = id)
    (h : RD (deployedRuntime v) I g s0 ⟨4292⟩
      (x0 :: x1 :: price :: currency1Ptr :: feePtr :: hooksPtr :: keyPtr :: price :: spacingPtr :: fee :: R)
      mem aw rdata evm.accountMap k C) :
    (poolSqrtPriceWord evm id ≠ ⟨0⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
    (poolSqrtPriceWord evm id = ⟨0⟩ ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨4341⟩
      (price :: poolSlot id :: id :: currency1Ptr :: feePtr :: hooksPtr :: keyPtr :: price :: spacingPtr :: fee :: R)
      (twoWordHashMem id ⟨6⟩ mem) aw' rdata evm.accountMap k' C') := by
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (keccakWord keyPtr (UInt256.ofNat 160) mem) ⟨6⟩ mem) = poolSlot id := by
    rw [hid]
    exact mappingMemory_slot_any id ⟨6⟩ mem
  have hword : solcSlotWordAt (poolSlot id) evm.accountMap I = poolSlot0Word evm id :=
    (storageLoad_codeOwner_eq_solcSlotWordAt evm I _ (by rw [hI])).symm
  have hcond : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975)
      (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (twoWordHashMem (keccakWord keyPtr (UInt256.ofNat 160) mem) ⟨6⟩ mem)) evm.accountMap I) =
      poolSqrtPriceWord evm id := by
    rw [hslot, hword]
    exact u256_land_comm _ _
  by_cases hz : poolSqrtPriceWord evm id = ⟨0⟩
  · obtain ⟨aw1, k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_4292_fallthrough_packed
      (by simp only [List.length_cons]; omega) (hcond.trans hz) h
    simp only [poolManagerBlocks.poolManager_block_4292_fallthrough_stack,
      poolManagerBlocks.poolManager_block_4292_fallthrough_memory] at rd1
    change RD _ _ _ _ ⟨4341⟩
      (price :: keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (twoWordHashMem (keccakWord keyPtr (UInt256.ofNat 160) mem) ⟨6⟩ mem) ::
        keccakWord keyPtr (UInt256.ofNat 160) mem :: currency1Ptr :: feePtr :: hooksPtr :: keyPtr ::
        price :: spacingPtr :: fee :: R)
      (twoWordHashMem (keccakWord keyPtr (UInt256.ofNat 160) mem) ⟨6⟩ mem) _ _ _ _ _ at rd1
    rw [hslot, hid] at rd1
    exact .inr ⟨hz, aw1, k1, C1, rd1⟩
  · obtain ⟨aw1, k1, C1, rd1⟩ := poolManagerBlocks.poolManager_block_4292_taken_packed
      (by simp only [List.length_cons]; omega) (fun he => hz (hcond.symm.trans he))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact .inl ⟨hz, poolManagerBlocks.poolManager_block_4792
      (by change R.length + 12 ≤ 1024; exact hstack) rd1⟩

@[irreducible] def poolInitializeTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm : State) (mem rdata : ByteArray) (id price fee currency1Ptr feePtr hooksPtr keyPtr spacingPtr : UInt256)
    (R : List UInt256) : Prop :=
  if poolSqrtPriceWord evm id ≠ ⟨0⟩ then RDrev (deployedRuntime v) g s0 else
    match tickPriceResult price with
    | none => RDrev (deployedRuntime v) g s0
    | some tick =>
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨4555⟩
        (memLoad hooksPtr (initializeEventMemory (twoWordHashMem id ⟨6⟩ mem) feePtr hooksPtr spacingPtr price tick) ::
          keyPtr :: price :: tick :: UInt256.ofNat 32 :: R)
        (initializeEventMemory (twoWordHashMem id ⟨6⟩ mem) feePtr hooksPtr spacingPtr price tick) aw' rdata
        (poolInitializePost evm id price tick fee).accountMap k' C'

theorem poolInitializeTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw x0 x1 price id currency1Ptr feePtr hooksPtr keyPtr spacingPtr fee : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 35 ≤ 1024) (hI : evm.executionEnv = I)
    (hid : keccakWord keyPtr (UInt256.ofNat 160) mem = id)
    (hp : price.toNat < 2^160) (hf : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨4292⟩
      (x0 :: x1 :: price :: currency1Ptr :: feePtr :: hooksPtr :: keyPtr :: price :: spacingPtr :: fee :: R)
      mem aw rdata evm.accountMap k C) :
    poolInitializeTraceResult v I g s0 evm mem rdata id price fee currency1Ptr feePtr hooksPtr keyPtr spacingPtr R := by
  unfold poolInitializeTraceResult
  rcases poolInitializeGuardTrace v (by omega) hI hid h with ⟨hn, hr⟩ | ⟨hz, aw1, k1, C1, rd1⟩
  · simp only [if_pos hn]
    exact hr
  · simp only [hz, ne_eq, not_true_eq_false, if_false]
    rcases poolInitializeTickTrace v hstack hp rd1 with ⟨hn, hr⟩ | ⟨tick, k2, C2, ht, hc, rd2⟩
    · simp only [hn]
      exact hr
    · simp only [ht]
      exact poolInitializeStoreTrace v (by omega) hI hp hf hc rd2

end Benchmarks.UniswapV4PoolManager
