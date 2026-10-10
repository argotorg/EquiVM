import Benchmarks.UniswapV3.Pool.OracleSearchLoop
import Benchmarks.UniswapV3.Pool.OracleSearchInitialize

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSearchZeroX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p cardRaw index targetRaw timeRaw ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20379⟩
      (cardRaw :: index :: targetRaw :: timeRaw :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hcard : UInt256.land cardRaw (UInt256.ofNat 65535) = ⟨0⟩)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 256 ≤ 2 ^ 200) (hov : R.length + 26 ≤ 1024) :
    RDinvalid (deployedRuntime v) g s0 := by
  obtain ⟨_, _, _, _, r1, _, _, _⟩ := oracleSearchInitializeX (v := v) rd hm hb hov
  have r2 := uniswapV3Pool_block_20395_fallthrough (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [u256_land_comm]; exact hcard) r1
  exact uniswapV3Pool_block_20416 (immWords := wordsOf (immStore v)) r2

set_option maxHeartbeats 1000000 in
theorem oracleSearchNonzeroX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw p cardRaw index targetRaw timeRaw ret : UInt256}
    {card time target : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨20379⟩
      (cardRaw :: index :: targetRaw :: timeRaw :: ⟨8⟩ :: ret :: R) mem aw rdata σ k C)
    (hcard : UInt256.land cardRaw (UInt256.ofNat 65535) = card)
    (hn : card.toNat ≠ 0) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htarget : UInt256.land (UInt256.ofNat 4294967295) targetRaw = target)
    (hm : HeapMemory mem aw p) (hbudget : MemoryGasBound aw C allowance)
    (hallowance : allowance ≤ 2 ^ 200) (hcover : p.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 26 ≤ 1024) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      Nonempty (OracleSearchExit v ee g s0 σ rdata ret R time target card
        (oracleSearchLeft index card) (oracleSearchRight index card) mem aw p C) := by
  rcases memoryGasCapacityOrOOG rd hbudget hallowance hcover with hoog | hb
  · exact Or.inl hoog
  obtain ⟨aw1, k1, C1, hC1, r1, hm1, hpre1, hcover1⟩ :=
    oracleSearchInitializeX (v := v) rd hm (by omega) hov
  have hp1 : (p + (⟨128⟩ : UInt256)).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have hp2 : (p + (⟨128⟩ : UInt256) + ⟨128⟩).toNat = p.toNat + 256 := by
    have hadd : (p + (⟨128⟩ : UInt256) + ⟨128⟩).toNat =
        (p + (⟨128⟩ : UInt256)).toNat + 128 :=
      uadd_word_ofNat_toNat (p + ⟨128⟩) 128 (by rw [hp1]; change _ < 2 ^ 256; omega)
    rw [hp1] at hadd
    omega
  have hne : card ≠ UInt256.ofNat 0 := by intro hz; apply hn; rw [hz]; rfl
  have hcard' : UInt256.land (UInt256.ofNat 65535) cardRaw = card := by
    rw [u256_land_comm]; exact hcard
  have r2 := uniswapV3Pool_block_20395_taken (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [hcard']; exact hne)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := uniswapV3Pool_block_20417 (immWords := wordsOf (immStore v)) (by evm_ov) r2
  have hleft : UInt256.land (UInt256.ofNat 65535) (oracleSearchLeft index card) =
      oracleSearchLeft index card := by
    rw [u256_land_comm]
    apply u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide)
    have hl := oracleSearchRemainder_lt
      (UInt256.land (index + ⟨1⟩) (UInt256.ofNat 65535)) card hn hc
    change (oracleSearchLeft index card).toNat < 65535 at hl
    change (oracleSearchLeft index card).toNat < 65536
    omega
  simp only [uniswapV3Pool_block_20417_stack,
    hcard', u256_add_comm (UInt256.ofNat 1), u256_land_comm (UInt256.ofNat 65535)] at r3
  change RD _ _ _ _ ⟨20441⟩
    (⟨0⟩ :: UInt256.sub
      (UInt256.land (oracleSearchLeft index card) (UInt256.ofNat 65535) + card) ⟨1⟩ ::
      UInt256.land (oracleSearchLeft index card) (UInt256.ofNat 65535) ::
      (p + ⟨128⟩) :: p :: cardRaw :: index :: targetRaw :: timeRaw :: ⟨8⟩ :: ret :: R)
    _ _ _ _ _ _ at r3
  rw [u256_land_comm] at hleft
  rw [hleft] at r3
  have hb1 := hbudget.advance hC1
  obtain hoog | hout := oracleSearchLoopX (v := v) r3 hcard hn hc htime htarget hm1
    (hb1.mono_cost (by omega)) hallowance hcover1 hret hov
  · exact Or.inl hoog
  · obtain ⟨out⟩ := hout
    exact Or.inr ⟨out.lift (fun _ _ hr ↦ hr) (by omega) (by rw [hp2]; omega) hpre1⟩

end Benchmarks.UniswapV3.Pool
