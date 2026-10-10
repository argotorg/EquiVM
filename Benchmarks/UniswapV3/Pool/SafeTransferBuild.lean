import Benchmarks.UniswapV3.Pool.SafeTransferBuildMemory
import Benchmarks.UniswapV3.Pool.SafeTransferCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem safeTransferBuildX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p value : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15238⟩ (value :: EVM.word recipient.val :: R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 100 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15319⟩
      (p :: (p + ⟨32⟩) :: ⟨68⟩ :: (p + ⟨100⟩) :: solcAddrMask :: ⟨0⟩ :: ⟨0⟩ ::
        value :: EVM.word recipient.val :: R)
      (safeTransferBuildMem mem p (EVM.word recipient.val) value) aw' rdata σ k' C' ∧
      HeapMemory (safeTransferBuildMem mem p (EVM.word recipient.val) value) aw' (p + ⟨100⟩) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have haddr : UInt256.land (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (EVM.word recipient.val) = EVM.word recipient.val := by
    change UInt256.land solcAddrMask _ = _
    rw [u256_land_comm]
    exact addressWord_val_clean _
  have hoff (n : Nat) (hn : n ≤ 100) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hargs : memLoad (UInt256.ofNat 64)
      (value.toByteArray.write 0 ((EVM.word recipient.val).toByteArray.write 0 mem
        (p + UInt256.ofNat 36).toNat 32) (p + UInt256.ofNat 68).toNat 32) = p := by
    rw [hoff 36 (by decide), hoff 68 (by decide)]
    exact safeTransferArgsMem_load64 hm _ _
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 224 - 1) := by decide +kernel
  have rdNext := uniswapV3Pool_block_15238 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_15238_stack, uniswapV3Pool_block_15238_memory,
    hload, haddr, hargs, u256_sub_self, u256_add_zero, hmask] at rdNext
  simp only [hoff 36 (by decide), hoff 68 (by decide), hoff 32 (by decide)] at rdNext
  have hmask160 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide +kernel
  simp only [show (UInt256.ofNat 64).toNat = 64 from rfl, hmask160] at rdNext
  have hargsEq : value.toByteArray.write 0
      ((EVM.word recipient.val).toByteArray.write 0 mem (p.toNat + 36) 32) (p.toNat + 68) 32 =
      safeTransferArgsMem mem p (EVM.word recipient.val) value := rfl
  have hheadEq : (p + UInt256.ofNat 100).toByteArray.write 0
      ((UInt256.ofNat 68).toByteArray.write 0
        (safeTransferArgsMem mem p (EVM.word recipient.val) value) p.toNat 32) 64 32 =
      safeTransferHeadMem mem p (EVM.word recipient.val) value := rfl
  have hpatchEq (old : UInt256) : UInt256.lor
      (UInt256.shiftLeft (UInt256.ofNat 2835717307) (UInt256.ofNat 224))
      (UInt256.land (UInt256.ofNat (2 ^ 224 - 1)) old) = transferSelectorPatchedWord old := rfl
  have hbuildEq : (transferSelectorPatchedWord (memLoad (p + UInt256.ofNat 32)
      (safeTransferHeadMem mem p (EVM.word recipient.val) value))).toByteArray.write 0
      (safeTransferHeadMem mem p (EVM.word recipient.val) value) (p.toNat + 32) 32 =
      safeTransferBuildMem mem p (EVM.word recipient.val) value := rfl
  simp only [hargsEq, hheadEq, hpatchEq, hbuildEq] at rdNext
  simp only [safeTransferBuildMem_load_length _ _ _ _ hm.lower,
    safeTransferBuildMem_load64 _ _ _ _ hm.lower] at rdNext
  refine ⟨_, _, _, rdNext, ?_⟩
  refine ⟨?_, safeTransferBuildMem_read64 _ _ _ _ hm.lower, ?_, ?_, ?_⟩
  · rw [safeTransferBuildMem_size _ _ _ _ hm.lower]; have hp := hm.lower; omega
  · rw [show (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 from hoff 100 (by decide)]
    have hp := hm.lower
    omega
  · rw [show (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 from hoff 100 (by decide),
      safeTransferBuildMem_size _ _ _ _ hm.lower]
    omega
  · repeat' apply activeWords_expand32
    all_goals first | exact hm.active | (change 64 + 32 ≤ _; omega) |
      (change (p + UInt256.ofNat _).toNat + 32 ≤ _; rw [hoff _ (by omega)]; omega) | omega

end Benchmarks.UniswapV3.Pool
