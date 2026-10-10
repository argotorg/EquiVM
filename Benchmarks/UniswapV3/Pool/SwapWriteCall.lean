import Benchmarks.UniswapV3.Pool.SwapWriteLoad
import Benchmarks.UniswapV3.Pool.SourceCallFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapWriteCallFrame (frame : Frame) (a : OracleWriteArgs) (evm : EVM.State) : Frame :=
  resumeAfterInternalCall frame "__c16"
    (some [.int (Int.ofNat (oracleWriteResultIndex a evm).toNat),
      .int (Int.ofNat (oracleWriteResultCardinality a evm).toNat)])

theorem swapWriteCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p cache snap exactWord free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4021⟩
      ([p, exactWord, cache, snap] ++ R) mem aw rdata σ k C)
    (hf : frame = {contract := contract, locals := frame.locals, immutables := immStore v})
    (hcget : frame.locals.get? "cache" = some c.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv))
    (hsource : SourceState s0 ee σ evm)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv) (hcf : c.Fits)
    (hsl : 96 ≤ snap.toNat) (hcache : 96 ≤ cache.toNat)
    (hsnapc : snap.toNat + 224 ≤ cache.toNat) (hcp : cache.toNat + 192 ≤ p.toNat)
    (hpfree : p.toNat + 224 ≤ free.toNat) (hb : free.toNat + 384 ≤ 2 ^ 200)
    (hov : R.length + 33 ≤ 1024) :
    let a := swapWriteArgs c initial
    let m := oracleWriteMemory mem free a evm
    (ExecStmt config frame evm swapWriteBody[0]! .reverted ∧
      RDinvalid (deployedRuntime v) g s0) ∨
    (ExecStmt config frame evm swapWriteBody[0]! .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config frame evm swapWriteBody[0]!
        (.ok (swapWriteCallFrame frame a evm) (oracleWriteState a evm)) ∧
      oracleWriteValid a evm ∧ ∃ σ' aw' k' C',
        SourceState s0 ee σ' (oracleWriteState a evm) ∧
        RD (deployedRuntime v) ee g s0 ⟨4077⟩
          ([oracleWriteResultCardinality a evm, oracleWriteResultIndex a evm,
            ⟨0⟩, ⟨0⟩, p, exactWord, cache, snap] ++ R) m aw' rdata σ' k' C' ∧
        HeapMemory m aw' (oracleWriteFree free a evm) ∧
        SwapCacheMemory m cache c ∧ SwapStateMemory m p s ∧
        Slot0Memory m snap initial.accountMap initial.executionEnv ∧
        MemoryPrefix mem m free.toNat ∧
        free.toNat ≤ (oracleWriteFree free a evm).toNat ∧
        (oracleWriteFree free a evm).toNat ≤ free.toNat + 384) := by
  dsimp only
  obtain ⟨aw1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapWriteLoadX (v := v) c initial rd hm hc hsnap (by omega) (by omega) (by omega)
  rcases oracleWriteInternalX (v := v) (swapWriteArgs c initial) frame evm swapWriteCallArgs
      "__c16" hf (evalSwapWriteArgs c initial hcget hslot) hsource r1
      (swapWriteArgs_fits c initial hcf) hm1 hb
      (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
      (by change R.length + 6 + 27 ≤ 1024; omega) with
    ⟨hex, hr⟩ | (⟨hex, hr⟩ | ⟨hex, hv, σ2, aw2, k2, C2, hsrc, r2, hm2⟩)
  · exact Or.inl ⟨hex, hr⟩
  · exact Or.inr (Or.inl ⟨hex, hr⟩)
  · have hp := oracleWriteMemory_prefix mem free (swapWriteArgs c initial) evm hb
    have hbfree := oracleWriteFree_bounds free (swapWriteArgs c initial) evm hb
    exact Or.inr (Or.inr ⟨hex, hv, σ2, aw2, k2, C2, hsrc, r2, hm2,
      MemoryPrefix.wordArray hp hc hcache (by change cache.toNat + 192 ≤ free.toNat; omega),
      MemoryPrefix.wordArray hp hs (by omega) hpfree,
      MemoryPrefix.wordArray hp hsnap hsl (by change snap.toNat + 224 ≤ free.toNat; omega),
      hp, hbfree⟩)

end Benchmarks.UniswapV3.Pool
