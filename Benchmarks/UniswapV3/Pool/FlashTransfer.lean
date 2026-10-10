import Benchmarks.UniswapV3.Pool.FlashTransferBuild
import Benchmarks.UniswapV3.Pool.SafeTransfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashTransferX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw p junk bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (recipient : AccountAddress) (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 (flashTransferEntry second)
      (flashTransferInput second junk bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 recipient R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hr : locals.get? "recipient" = some (.address recipient))
    (ha : locals.get? (poolAmountName second) =
      some (.int (Int.ofNat (if second then amount1 else amount0).toNat)))
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) (hov : R.length + 30 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashTransferStmt second) .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashTransferStmt second)
        (.ok { contract := contract
               locals := flashTransferLocals locals second (if second then amount1 else amount0)
               immutables := immStore v } evm') ∧
      RD (deployedRuntime v) ee g s0 (flashTransferExit second)
        (flashTransferRest bal1 bal0 fee1 fee0 liquidity len start amount1 amount0 recipient R)
        mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ 128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      next.toNat ≤ p.toNat + 2 ^ 138 + 163 := by
  rcases flashTransferBuildX (v := v) second recipient rd (by omega) with
    ⟨hz, kSkip, CSkip, rdSkip⟩ | ⟨hz, kCall, CCall, rdCall⟩
  · refine Or.inr ⟨evm, σ, rdata, mem, aw, p, kSkip, CSkip, hs, ?_, rdSkip, hm, hmem, hzero, by omega⟩
    simp only [flashTransferLocals, hz, if_pos] at ⊢
    exact flashTransferSkip v locals evm second (by simpa only [hz] using ha)
  · have hret : (D_J (deployedRuntime v) 0).contains (flashTransferExit second) = true := by
      rw [uniswapV3PoolPatchedValidJumps v]; cases second <;> native_decide
    have hpos : 0 < (if second then amount1 else amount0).toNat :=
      Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    rcases safeTransferX (v := v) (immStore v) (poolToken v second) recipient rdCall
        hs hperm hm hmem hzero hb hret
        (by simpa only [flashTransferRest, List.length_cons] using hov) with
      ⟨rdBad, hbad⟩ | ⟨evm', σ', out, mem', aw', next, k', C', hs', hgood, rdGood, hm', hpref, hnext⟩
    · exact Or.inl ⟨rdBad, flashTransferReverts v locals evm second recipient _ hr ha hpos hbad⟩
    · refine Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', ?_, rdGood, hm',
        le_trans hmem hpref.size, ?_, hnext⟩
      · simpa only [flashTransferLocals, if_neg hz] using
          flashTransferReturns v locals evm evm' second recipient _ _ hr ha hpos hgood
      · rw [MemoryPrefix.memLoad hpref (UInt256.ofNat 96) (by decide) hm.lower hmem, hzero]

end Benchmarks.UniswapV3.Pool
