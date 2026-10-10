import Benchmarks.UniswapV3.Pool.OracleInitializeStorage
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_056
import Benchmarks.UniswapV3.Pool.Calls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleInitializeTime (word : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 4294967295) word

theorem oracleInitializeTime_lt (word : UInt256) : (oracleInitializeTime word).toNat < 2 ^ 32 := by
  unfold oracleInitializeTime
  rw [u256_land_comm]
  exact u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem oracleInitializePackedWord (time old : UInt256) :
    UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248))
      (UInt256.land (UInt256.ofNat 4294967295)
        (UInt256.lor (UInt256.land (UInt256.ofNat 4294967295) time)
          (UInt256.land (UInt256.lnot (UInt256.ofNat 4294967295)) old))) =
      oracleInitializeWord (oracleInitializeTime time) := by
  have hclean : UInt256.land (UInt256.ofNat 4294967295)
      (UInt256.lor (UInt256.land (UInt256.ofNat 4294967295) time)
        (UInt256.land (UInt256.lnot (UInt256.ofNat 4294967295)) old)) =
      oracleInitializeTime time := by
    apply u256_inj
    simp only [uland_toNat, u256_lor_toNat_exact, Nat.and_or_distrib_left,
      ← Nat.and_assoc, Nat.and_self, oracleInitializeTime]
    rw [show (UInt256.ofNat 4294967295).toNat &&&
      (UInt256.lnot (UInt256.ofNat 4294967295)).toNat = 0 by decide,
      Nat.zero_and, Nat.or_zero]
  rw [hclean]
  apply u256_inj
  rw [u256_lor_toNat_exact, oracleInitializeWord_toNat _ (oracleInitializeTime_lt time),
    show (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248)).toNat = 2 ^ 248 by decide,
    Nat.or_comm]
  simpa only [Nat.one_mul] using nat_lor_shift_add (oracleInitializeTime time).toNat 1 248
    (lt_of_lt_of_le (oracleInitializeTime_lt time) (by decide))

def oracleInitializeMemory (mem : ByteArray) (time : UInt256) : ByteArray :=
  uniswapV3Pool_block_17514_memory (mem := mem) (x0 := time)

theorem oracleInitializeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw time ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨17514⟩ (time :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C' aw', SourceState s0 ee (oracleInitializeState evm (oracleInitializeTime time)).accountMap
        (oracleInitializeState evm (oracleInitializeTime time)) ∧
      RD (deployedRuntime v) ee g s0 ret (⟨1⟩ :: ⟨1⟩ :: R) (oracleInitializeMemory mem time) aw' rdata
        (oracleInitializeState evm (oracleInitializeTime time)).accountMap k' C' := by
  obtain ⟨k', C', rout⟩ := uniswapV3Pool_block_17514 (immWords := wordsOf (immStore v))
    hov hperm hret rd
  rw [oracleInitializePackedWord] at rout
  have hs' : SourceState s0 ee
      (sstoreAccountMap ee.codeOwner σ ⟨8⟩ (oracleInitializeWord (oracleInitializeTime time)))
      (oracleInitializeState evm (oracleInitializeTime time)) := by
    simpa only [oracleInitializeState, hs.env] using
      hs.storageWrite ⟨8⟩ (oracleInitializeWord (oracleInitializeTime time))
  rw [hs'.accounts] at rout
  exact ⟨k', C', _, ⟨hs'.world, hs'.env, rfl⟩, rout⟩

end Benchmarks.UniswapV3.Pool
