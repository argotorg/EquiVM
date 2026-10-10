import Benchmarks.UniswapV3.Pool.UpdatePositionObserveEntryTrace
import Benchmarks.UniswapV3.Pool.UpdatePositionObserve
import Benchmarks.UniswapV3.Pool.OracleObserveZeroBoundedTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionOracleMemory (mem : ByteArray) (p : UInt256)
    (σ : AccountMap) (ee : ExecutionEnv) : ByteArray :=
  oracleObserveZeroMemory mem p (oracleStoredObservation (slot0FieldWord 23 2 σ ee) σ ee)
    (blockTimestampWord ee) (slot0TickValue σ ee) (poolLiquidityWord σ ee)

def updatePositionOracleFree (p : UInt256) (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  oracleObserveZeroFree p (oracleStoredObservation (slot0FieldWord 23 2 σ ee) σ ee)
    (blockTimestampWord ee)

theorem updatePositionOracleFree_bound (p : UInt256) (σ : AccountMap) (ee : ExecutionEnv)
    (hb : p.toNat + 384 ≤ 2 ^ 200) :
    (updatePositionOracleFree p σ ee).toNat ≤ p.toNat + 384 :=
  oracleObserveZeroFree_bound p _ _ hb

theorem updatePositionObserveX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨19190⟩ R mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (hov : R.length + 33 ≤ 1024) :
    (¬(slot0FieldWord 23 2 σ ee).toNat < 65535 ∧ RDinvalid (deployedRuntime v) g s0) ∨
    ((slot0FieldWord 23 2 σ ee).toNat < 65535 ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨19273⟩
        ((snapshotCurrent σ ee).secondsPerLiquidity ::
          EVM.wordOfInt (snapshotCurrent σ ee).tickCumulative ::
          ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ee.header.timestamp :: R)
        (updatePositionOracleMemory mem p σ ee) aw' rdata σ k' C' ∧
      HeapMemory (updatePositionOracleMemory mem p σ ee) aw'
        (updatePositionOracleFree p σ ee)) := by
  obtain ⟨_, _, r1⟩ := updatePositionObserveEntryX (v := v) rd (by omega)
  have hi : (slot0FieldWord 23 2 σ ee).toNat < 2 ^ 16 :=
    u256LandMaskToNatLtOfToNat _ _ (by decide)
  have ht : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt (slot0TickValue σ ee)) =
      EVM.wordOfInt (slot0TickValue σ ee) := by
    have ht := slot0TickValue_bounds σ ee
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ ht.1 ht.2]
  exact oracleObserveSingleZeroBoundedX (v := v) r1 hi rfl ht
    (poolLiquidityWord_lt σ ee) hm hb
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)

end Benchmarks.UniswapV3.Pool
