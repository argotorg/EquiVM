import Benchmarks.UniswapV3.Pool.OracleObserveCompareTrace
import Benchmarks.UniswapV3.Pool.OracleObserveExactTrace
import Benchmarks.UniswapV3.Pool.OracleInterpolationTrace
import Benchmarks.UniswapV3.Pool.OracleObserveReturnTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObservePairX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free beforePtr afterPtr card liquidity index : UInt256}
    {tickArg secondsAgoRaw timeRaw ret time secondsAgo targetRaw : UInt256}
    {tick : Int} {before after : OracleObservation} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13381⟩
      (afterPtr :: beforePtr :: ⟨0⟩ :: ⟨0⟩ :: targetRaw :: ⟨0⟩ :: ⟨0⟩ :: card :: liquidity ::
        index :: tickArg :: secondsAgoRaw :: timeRaw :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hn : secondsAgo ≠ ⟨0⟩) (hin : index.toNat < 65535)
    (hrun : OracleSurroundingRun time (oracleDelta time secondsAgo) tick index liquidity card
      σ ee before after)
    (hm : HeapMemory mem aw free) (hb : free.toNat ≤ 2 ^ 200)
    (hbefore : ObservationMemory mem beforePtr before) (hafter : ObservationMemory mem afterPtr after)
    (hbe : beforePtr.toNat + 128 ≤ free.toNat) (hae : afterPtr.toNat + 128 ≤ free.toNat)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = oracleDelta time secondsAgo)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 26 ≤ 1024) :
    OracleObserveSingleOutcome v ee g s0 σ rdata ret R time secondsAgo tick index liquidity card
      mem aw free C := by
  obtain ⟨vb, va⟩ := hrun.valid (oracleDelta_lt _ _)
  have r1 := oracleObserveCompareBeforeX (v := v) rd hm hb hbefore hbe hcover
    vb.timestamp htarget (by evm_ov)
  by_cases htb : oracleDelta time secondsAgo = before.timestamp
  · rw [if_pos htb] at r1
    have r2 := oracleObserveExactX (v := v) false r1 hm hb hbefore hbe hcover (by evm_ov)
    have hs : OracleObserveSingleRun time secondsAgo tick index liquidity card σ ee
        before.cumulatives := by
      simpa only [if_pos htb] using OracleObserveSingleRun.observation hn hin hrun (Or.inl htb)
    obtain ⟨out⟩ := oracleObserveReturnX (v := v) r2 hm hcover hs vb.cleanTick
      (by rw [wordOfInt_ofNat_toNat]; exact vb.cleanSeconds) vb.tick
      ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr vb.seconds⟩ hret (by omega)
    exact Or.inr (Or.inr ⟨out.lift (by omega) (le_refl _) (MemoryPrefix.refl _ _)⟩)
  · rw [if_neg htb] at r1
    have r2 := oracleObserveCompareAfterX (v := v) r1 hm hb hafter hae hcover
      va.timestamp htarget (by evm_ov)
    by_cases hta : oracleDelta time secondsAgo = after.timestamp
    · rw [if_pos hta] at r2
      have r3 := oracleObserveExactX (v := v) true r2 hm hb hafter hae hcover (by evm_ov)
      have hs : OracleObserveSingleRun time secondsAgo tick index liquidity card σ ee
          after.cumulatives := by
        simpa only [if_neg htb] using OracleObserveSingleRun.observation hn hin hrun (Or.inr hta)
      obtain ⟨out⟩ := oracleObserveReturnX (v := v) r3 hm hcover hs va.cleanTick
        (by rw [wordOfInt_ofNat_toNat]; exact va.cleanSeconds) va.tick
        ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr va.seconds⟩ hret (by omega)
      exact Or.inr (Or.inr ⟨out.lift (by omega) (le_refl _) (MemoryPrefix.refl _ _)⟩)
    · rw [if_neg hta] at r2
      rcases oracleInterpolationX (v := v) (target := oracleDelta time secondsAgo)
        r2 hm hb hbefore hafter hbe hae hcover
        (by rw [u256_land_comm]; exact htarget) (by evm_ov) with ⟨hd, rbad⟩ | ⟨hd, k3, C3, hC3, r3⟩
      · exact Or.inr (Or.inl ⟨.interpolation hn hin hrun htb hta hd, Or.inr rbad⟩)
      · have hs := OracleObserveSingleRun.interpolated hn hin hrun htb hta hd
        obtain ⟨out⟩ := oracleObserveReturnX (v := v) r3 hm hcover hs
          (oracleInterpolatedTick_word _ _ _).symm (oracleInterpolatedSeconds_word _ _ _).symm
          (normalizeSint_bounds ⟨56, by decide⟩ _)
          ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩ hret (by omega)
        exact Or.inr (Or.inr ⟨out.lift (by omega) (le_refl _) (MemoryPrefix.refl _ _)⟩)

end Benchmarks.UniswapV3.Pool
