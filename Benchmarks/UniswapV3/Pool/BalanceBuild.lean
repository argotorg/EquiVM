import Benchmarks.UniswapV3.Pool.BalanceMemory
import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_050
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def balanceEntry (second : Bool) : UInt256 := if second then ⟨15901⟩ else ⟨15572⟩
def balanceBuildExit (second : Bool) : UInt256 := if second then ⟨16013⟩ else ⟨15684⟩

set_option maxHeartbeats 1000000 in
theorem balanceBuildX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (balanceEntry second) R mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 68 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (balanceBuildExit second)
      (⟨36⟩ :: (p + ⟨68⟩) :: p :: (p + ⟨32⟩) :: EVM.word (balanceToken v second).val ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: R)
      (balanceBuildMem mem p (EVM.word ee.codeOwner.val)) aw' rdata σ k' C' ∧
      HeapMemory (balanceBuildMem mem p (EVM.word ee.codeOwner.val)) aw' (p + ⟨68⟩) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hoff (n : Nat) (hn : n ≤ 68) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hargs : memLoad (UInt256.ofNat 64)
      ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 mem
        (p + UInt256.ofNat 36).toNat 32) = p := by
    rw [hoff 36 (by decide)]
    exact balanceArgsMem_load64 hm _
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 224))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 224 - 1) := by decide +kernel
  have hmask160 : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide +kernel
  have haddr (a : AccountAddress) :
      UInt256.land (EVM.Word.ofNat a.val) solcAddrMask = EVM.word a.val :=
    addressWord_val_clean a
  have hargsEq : (UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 mem (p.toNat + 36) 32 =
      balanceArgsMem mem p (EVM.word ee.codeOwner.val) := rfl
  have hheadEq : (p + UInt256.ofNat 68).toByteArray.write 0
      ((UInt256.ofNat 36).toByteArray.write 0 (balanceArgsMem mem p (EVM.word ee.codeOwner.val))
        p.toNat 32) 64 32 = balanceHeadMem mem p (EVM.word ee.codeOwner.val) := rfl
  have hpatchEq (old : UInt256) : UInt256.lor
      (UInt256.shiftLeft (UInt256.ofNat 1889567281) (UInt256.ofNat 224))
      (UInt256.land (UInt256.ofNat (2 ^ 224 - 1)) old) = balanceSelectorPatchedWord old := rfl
  have hbuildEq : (balanceSelectorPatchedWord (memLoad (p + UInt256.ofNat 32)
      (balanceHeadMem mem p (EVM.word ee.codeOwner.val)))).toByteArray.write 0
      (balanceHeadMem mem p (EVM.word ee.codeOwner.val)) (p.toNat + 32) 32 =
      balanceBuildMem mem p (EVM.word ee.codeOwner.val) := rfl
  cases second
  all_goals first
    | have rdNext := uniswapV3Pool_block_15572 (immWords := wordsOf (immStore v)) hov rd
    | have rdNext := uniswapV3Pool_block_15901 (immWords := wordsOf (immStore v)) hov rd
  all_goals
    simp only [uniswapV3Pool_block_15572_stack, uniswapV3Pool_block_15572_memory,
      uniswapV3Pool_block_15901_stack, uniswapV3Pool_block_15901_memory,
      hload, hargs, u256_sub_self, u256_add_zero, hmask, hmask160,
      wordsOf_immStore_token0, wordsOf_immStore_token1, haddr] at rdNext
    simp only [hoff 36 (by decide), hoff 32 (by decide),
      show (UInt256.ofNat 64).toNat = 64 from rfl, hargsEq, hheadEq, hpatchEq, hbuildEq,
      balanceBuildMem_load_length _ _ _ hm.lower, balanceBuildMem_load64 _ _ _ hm.lower] at rdNext
    refine ⟨_, _, _, rdNext, ?_⟩
    refine ⟨?_, balanceBuildMem_read64 _ _ _ hm.lower, ?_, ?_, ?_⟩
    · rw [balanceBuildMem_size _ _ _ hm.lower]; have hp := hm.lower; omega
    · rw [show (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 from hoff 68 (by decide)]
      have hp := hm.lower
      omega
    · rw [show (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 from hoff 68 (by decide),
        balanceBuildMem_size _ _ _ hm.lower]
      omega
    · repeat' apply activeWords_expand32
      all_goals first | exact hm.active | (change 64 + 32 ≤ _; omega) |
        (change (p + UInt256.ofNat _).toNat + 32 ≤ _; rw [hoff _ (by omega)]; omega) | omega

end Benchmarks.UniswapV3.Pool
