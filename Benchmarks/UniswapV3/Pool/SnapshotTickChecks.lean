import Benchmarks.UniswapV3.Pool.SnapshotMapping
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_032

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def snapshotTickStack (lower upper : Int) (σ : AccountMap) (I : ExecutionEnv)
    (R : List UInt256) : List UInt256 :=
  [tickFieldWord upper 3 31 1 σ I, tickFieldWord lower 3 31 1 σ I,
   solcMappingSlot ⟨5⟩ (EVM.wordOfInt upper), solcMappingSlot ⟨5⟩ (EVM.wordOfInt lower),
   (tickOutside upper σ I).seconds, (tickOutside lower σ I).seconds,
   (tickOutside upper σ I).secondsPerLiquidity, (tickOutside lower σ I).secondsPerLiquidity,
   EVM.wordOfInt (tickOutside upper σ I).cumulative, EVM.wordOfInt (tickOutside lower σ I).cumulative] ++ R

theorem snapshotTickChecksX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw a b c lowerRaw upperRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (lower upper : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨10065⟩
      (snapshotLowerStack lower upper σ ee a b c lowerRaw upperRaw R) mem aw rdata σ k C)
    (hov : R.length + 20 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ (tickOutside lower σ ee).initialized = false) ∨
    (RDrev (deployedRuntime v) g s0 ∧ (tickOutside lower σ ee).initialized = true ∧
      (tickOutside upper σ ee).initialized = false) ∨
    ((tickOutside lower σ ee).initialized = true ∧ (tickOutside upper σ ee).initialized = true ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨10148⟩
        (snapshotTickStack lower upper σ ee (a :: b :: c :: upperRaw :: lowerRaw :: R))
        mem aw rdata σ k' C') := by
  simp only [snapshotLowerStack, List.cons_append, List.nil_append] at rd
  have hli := tickOutsideInitializedWord lower σ ee
  have hui := tickOutsideInitializedWord upper σ ee
  by_cases hl : tickFieldWord lower 3 31 1 σ ee = ⟨0⟩
  · have rdFail := uniswapV3Pool_block_10065_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [← hli]; exact hl) rd
    simp only [uniswapV3Pool_block_10065_fallthrough_stack] at rdFail
    exact Or.inl ⟨uniswapV3Pool_block_10075 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail,
      (tickOutsideInitialized_false lower σ ee).mpr hl⟩
  · have hlt := (tickOutsideInitialized_true lower σ ee).mpr hl
    have rdLower := uniswapV3Pool_block_10065_taken (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [← hli]; exact hl)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_10065_taken_stack, ← hli] at rdLower
    have hui' : tickFieldWord upper 3 31 1 σ ee =
        UInt256.land (UInt256.ofNat 255)
          (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac => ac.storage.getD (solcMappingSlot ⟨5⟩ (EVM.wordOfInt upper) + UInt256.ofNat 3) ⟨0⟩))
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248))) := hui
    by_cases hu : tickFieldWord upper 3 31 1 σ ee = ⟨0⟩
    · obtain ⟨kr, Cr, rdFail⟩ := uniswapV3Pool_block_10079_fallthrough
        (immWords := wordsOf (immStore v)) (by evm_ov) (by rw [← hui']; exact hu) rdLower
      simp only [uniswapV3Pool_block_10079_fallthrough_stack] at rdFail
      exact Or.inr (Or.inl ⟨uniswapV3Pool_block_10144 (immWords := wordsOf (immStore v))
        (by evm_ov) rdFail, hlt, (tickOutsideInitialized_false upper σ ee).mpr hu⟩)
    · obtain ⟨kr, Cr, rdUpper⟩ := uniswapV3Pool_block_10079_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [← hui']; exact hu)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdLower
      simp only [uniswapV3Pool_block_10079_taken_stack, ← hui'] at rdUpper
      change RD (deployedRuntime v) ee g s0 ⟨10148⟩
        (tickFieldWord upper 3 31 1 σ ee :: tickFieldWord lower 3 31 1 σ ee ::
         solcMappingSlot ⟨5⟩ (EVM.wordOfInt upper) :: solcMappingSlot ⟨5⟩ (EVM.wordOfInt lower) ::
         UInt256.land (UInt256.ofNat 4294967295) (UInt256.div (solcSlotWordAt (tickFieldSlot upper 3) σ ee)
           (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216))) :: (tickOutside lower σ ee).seconds ::
         UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
           (UInt256.ofNat 1)) (UInt256.div (solcSlotWordAt (tickFieldSlot upper 3) σ ee)
             (UInt256.ofNat 72057594037927936)) :: (tickOutside lower σ ee).secondsPerLiquidity ::
         UInt256.signextend (UInt256.ofNat 6) (solcSlotWordAt (tickFieldSlot upper 3) σ ee) ::
         EVM.wordOfInt (tickOutside lower σ ee).cumulative :: a :: b :: c :: upperRaw :: lowerRaw :: R)
        mem aw rdata σ kr Cr at rdUpper
      rw [← tickOutsideSecondsWord, ← tickOutsideLiquidityWord, ← tickOutsideTickWord] at rdUpper
      exact Or.inr (Or.inr ⟨hlt, (tickOutsideInitialized_true upper σ ee).mpr hu, kr, Cr, rdUpper⟩)

end Benchmarks.UniswapV3.Pool
