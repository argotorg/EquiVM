import Benchmarks.UniswapV3.Pool.FlashGrowthTrace
import Benchmarks.UniswapV3.Pool.FlashPrefix
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashFinishSource (locals imms : Store) (evm : EVM.State)
    (recipient : AccountAddress) (amount0 amount1 paid0 paid1 : UInt256)
    (hr : locals.get? "recipient" = some (.address recipient))
    (ha0 : locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (ha1 : locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hp0 : locals.get? "paid0" = some (.int (Int.ofNat paid0.toNat)))
    (hp1 : locals.get? "paid1" = some (.int (Int.ofNat paid1.toNat)))
    (hslot : locals.get? "slot0" = none) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (flashTransition.body.drop 25)
      (.ok {contract := contract, locals := locals, immutables := imms} (storeSlot0Unlocked evm true)) := by
  refine ExecBlock.consNormal (ExecStmt.emit (vals := [.address evm.executionEnv.source,
    .address recipient, .int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat),
    .int (Int.ofNat paid0.toNat), .int (Int.ofNat paid1.toNat)]) ?_) ?_
  · simp only [evalExprs?, evalExpr?, hr, ha0, ha1, hp0, hp1, EvalResult.ofOption,
      envValue, bind, EvalResult.bind, pure]
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp only [evalExpr?, pure]) (assignSlot0Unlocked evm locals imms true hslot))
    ExecBlock.nil

theorem flashFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity len start amount1 amount0 recipient : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7421⟩
      (flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity
        (len :: start :: amount1 :: amount0 :: recipient :: ⟨857⟩ :: R)) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (hov : R.length + 26 ≤ 1024) :
    RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm true).accountMap ByteArray.empty := by
  obtain ⟨_, _, rdEvent⟩ := uniswapV3Pool_block_7421 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm rd
  simp only [uniswapV3Pool_block_7421_stack] at rdEvent
  obtain ⟨_, _, rdDone⟩ := uniswapV3Pool_block_7532 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEvent
  have hmap := storeSlot0Unlocked_accountMap evm true
  rw [slot0UnlockedWord_true, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm true).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
          (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))))) at hmap
  simp only [uniswapV3Pool_block_7532_stack] at rdDone
  have hr := uniswapV3Pool_block_857 (immWords := wordsOf (immStore v)) (by evm_ov) rdDone
  simpa only [← hmap] using hr

end Benchmarks.UniswapV3.Pool
