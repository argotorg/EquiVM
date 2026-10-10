import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleEntryTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionMiddlePrefix
import Benchmarks.UniswapV3.Pool.ModifyPositionMemory
import Benchmarks.UniswapV3.Pool.OracleWriteInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def modifyPositionMiddleMemory (mem : ByteArray) (free : UInt256) (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : ByteArray :=
  oracleWriteMemory mem free (modifyPositionMiddleOracleArgs v a evm) (modifyPositionUpdatedState v a evm)

def modifyPositionMiddleFree (free : UInt256) (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : UInt256 :=
  oracleWriteFree free (modifyPositionMiddleOracleArgs v a evm) (modifyPositionUpdatedState v a evm)

theorem modifyPositionMiddleOracleX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free key : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (modifyPositionUpdatedState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨16536⟩
      (p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hplo : 96 ≤ p.toNat) (hqlo : 96 ≤ q.toNat)
    (hphi : p.toNat + 224 ≤ free.toNat) (hqhi : q.toNat + 128 ≤ free.toNat)
    (hb : free.toNat + 384 ≤ 2 ^ 200) (hov : R.length + 33 ≤ 1024) :
    (ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) (modifyPositionMiddleBody.take 3) .reverted ∧
      RDinvalid (deployedRuntime v) g s0) ∨
    (ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) (modifyPositionMiddleBody.take 3) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) (modifyPositionMiddleBody.take 3)
      (.ok (modifyPositionMiddleOracleFrame v a evm) (modifyPositionMiddleOracleState v a evm)) ∧
      oracleWriteValid (modifyPositionMiddleOracleArgs v a evm) (modifyPositionUpdatedState v a evm) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (modifyPositionMiddleOracleState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨16595⟩
        (oracleWriteResultCardinality (modifyPositionMiddleOracleArgs v a evm)
            (modifyPositionUpdatedState v a evm) ::
          oracleWriteResultIndex (modifyPositionMiddleOracleArgs v a evm)
            (modifyPositionUpdatedState v a evm) ::
          modifyPositionMiddleLiquidity v a evm :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
        (modifyPositionMiddleMemory mem free v a evm) aw' rdata σ' k' C' ∧
      HeapMemory (modifyPositionMiddleMemory mem free v a evm) aw'
        (modifyPositionMiddleFree free v a evm) ∧
      ModifyPositionParamsMemory (modifyPositionMiddleMemory mem free v a evm) q a ∧
      Slot0Memory (modifyPositionMiddleMemory mem free v a evm) p evm.accountMap evm.executionEnv) := by
  obtain ⟨aw1, k1, C1, r1, hm1⟩ := modifyPositionMiddleEntryX (v := v) a evm hs rd hm hp
    (by omega) (by omega)
  have htime : UInt256.land (UInt256.ofNat ee.header.timestamp) (UInt256.ofNat (2 ^ 32 - 1)) =
      (modifyPositionMiddleOracleArgs v a evm).time := by
    dsimp only [modifyPositionMiddleOracleArgs, blockTimestampWord]
    rw [hs.env]
  have hprefix := modifyPositionMiddlePrefixSource v a evm
  have hbody : modifyPositionMiddleBody.take 3 = modifyPositionMiddleBody.take 2 ++
      [.internalCall "Oracle_write" modifyPositionMiddleOracleExprs "__c7"] := rfl
  rcases oracleWriteInternalRawX (v := v) (modifyPositionMiddleOracleArgs v a evm)
    (modifyPositionMiddleTimeFrame v a evm) (modifyPositionUpdatedState v a evm)
    modifyPositionMiddleOracleExprs "__c7" (modifyPositionMiddleTimeFrame_eq v a evm)
    (evalModifyPositionMiddleOracleExprs v a evm _) hs r1
    (modifyPositionMiddleOracleArgs_fits v a evm) htime hm1 hb
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
      ⟨hcall, rr⟩ | ⟨hcall, rr⟩ | ⟨hcall, hv, σ', aw', kr, Cr, hs', rr, hm'⟩
  · exact Or.inl ⟨hbody.symm ▸ execBlock_append_ok hprefix (execBlock_singleton hcall), rr⟩
  · exact Or.inr (Or.inl ⟨hbody.symm ▸ execBlock_append_ok hprefix (execBlock_singleton hcall), rr⟩)
  · have hmem := oracleWriteMemory_prefix mem free (modifyPositionMiddleOracleArgs v a evm)
      (modifyPositionUpdatedState v a evm) hb
    have hq' := MemoryPrefix.wordArray hmem hq hqlo (by exact hqhi)
    have hp' := MemoryPrefix.wordArray hmem hp hplo (by exact hphi)
    exact Or.inr (Or.inr ⟨hbody.symm ▸ execBlock_append_ok hprefix (execBlock_singleton hcall), hv,
      σ', aw', kr, Cr, hs', rr, hm', hq', hp'⟩)

end Benchmarks.UniswapV3.Pool
