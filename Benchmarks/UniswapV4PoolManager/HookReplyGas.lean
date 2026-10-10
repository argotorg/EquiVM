import Benchmarks.UniswapV4PoolManager.HookReplyTrace
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- Copying a reply near the allocator's 64-bit capacity exceeds the permitted gas. -/
theorem hookLargeReply_outOfGas {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw ptr hook ret free : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length+7 ≤ 1024) (hgas : g.toNat < 324518553658429321982441292826060)
    (haw : aw.toNat ≤ 2048) (hf : free.toNat ≤ 2048)
    (ho : out.size < UInt256.size) (hlarge : solcMaxU64 < out.size+4096)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨16189⟩
      (ptr :: hook :: ret :: (ptr+⟨32⟩) :: R) mem aw out σ k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass := by
  have hfit : free.toNat+32 < UInt256.size := by change _ < 2^256; omega
  have hout : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt ho
  have hm : poolManagerBlocks.poolManager_block_16189_taken_memory (mem := mem) (rdata := out) =
      solcReturnDataMem mem free out := by
    simp only [poolManagerBlocks.poolManager_block_16189_taken_memory, hfree, hout]
    rfl
  have hlength := returnDataMemory_length mem free out hfit
  have hlong : 32 ≤ out.size := by change 2^64-1 < out.size+4096 at hlarge; omega
  have hlt : UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨0⟩ :=
    ult_zero (by rw [hout]; exact hlong)
  have rd := poolManagerBlocks.poolManager_block_16189_taken hstack
    (by rw [hout]; change 0+out.size ≤ out.size; omega)
    (by change UInt256.isZero (UInt256.lt (memLoad (memLoad (UInt256.ofNat 64) mem)
          (poolManagerBlocks.poolManager_block_16189_taken_memory (mem := mem) (rdata := out))) _) ≠ _
        rw [hfree, hm, hlength, hlt]; decide)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [hfree] at rd
  let a1 := M aw (UInt256.ofNat 64) ⟨32⟩
  let a2 := M a1 (UInt256.ofNat 64) ⟨32⟩
  let a3 := M a2 free ⟨32⟩
  let a4 := M a3 (free+UInt256.ofNat 32) (UInt256.ofNat out.size)
  have h1 : a1.toNat ≤ 2048 := memoryWords_le haw (by decide)
  have h2 : a2.toNat ≤ 2048 := memoryWords_le h1 (by decide)
  have h3 : a3.toNat ≤ 2048 := memoryWords_le h2 (by change free.toNat+32 ≤ 32*2048; omega)
  have hsmall : Cₘ a3 ≤ Cₘ (UInt256.ofNat 2048) := memoryCost_mono h3
  have hw := memoryWords_ge_span a3 (free+UInt256.ofNat 32) (UInt256.ofNat out.size)
    (by rw [hout]; omega)
  rw [hout, uadd_word_ofNat_toNat free 32 hfit] at hw
  change (free.toNat+32+out.size+31)/32 ≤ a4.toNat at hw
  have hbig : (UInt256.ofNat (2^59-128)).toNat ≤ a4.toNat := by
    change 2^59-128 ≤ a4.toNat
    change 2^64-1 < out.size+4096 at hlarge
    omega
  have hcost := memoryCost_mono hbig
  have hbound : 324518553658429321982441292826060+Cₘ (UInt256.ofNat 2048) <
      Cₘ (UInt256.ofNat (2^59-128)) := by decide +kernel
  have hcopy : 324518553658429321982441292826060 <
      memExpansionCost a3 (free+UInt256.ofNat 32) (UInt256.ofNat out.size) := by
    change _ < Cₘ a4-Cₘ a3
    omega
  apply RD.oog_of_cost_gt rd
  change g.toNat < C+(103+memExpansionCost aw (UInt256.ofNat 64) ⟨32⟩+
    memExpansionCost a1 (UInt256.ofNat 64) ⟨32⟩+memExpansionCost a2 free ⟨32⟩+
    memExpansionCost a3 (free+UInt256.ofNat 32) (UInt256.ofNat out.size)+
    (3+3*(((UInt256.ofNat out.size).toNat+31)/32))+memExpansionCost a4 free ⟨32⟩)
  omega

end Benchmarks.UniswapV4PoolManager
