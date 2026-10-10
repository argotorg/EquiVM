import Benchmarks.CompoundIII.Comet.AbsorbLoopTailModel
import Benchmarks.CompoundIII.Comet.AbsorbLoopEvm
import Benchmarks.CompoundIII.Comet.AbsorbAfterLoopEvm
import Benchmarks.CompoundIII.Comet.InternalBoundedOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbLoopTail {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free old price delta ptr absorber ret : UInt256} {σ : AccountMap} {k C i : Nat}
    {R : List UInt256} (account : AccountAddress) (basic : UserBasicData)
    (hstack : R.length + 34 ≤ 1024) (hi : i ≤ v.numAssets.toNat)
    (hbasic : UserBasicMemory mem ptr basic) (hptr : 96 ≤ ptr.toNat)
    (hsep : ptr.toNat + 160 ≤ free.toNat)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : free.toNat ≤ mem.size)
    (hbound : free.toNat + 928 * (v.numAssets.toNat - i) + 256 < 2^64)
    (hs : SourceState s0 ee σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17110⟩
      (absorbLoopStack i basic.assets basic.reserved old basic.principal price (EVM.word account.val)
        delta ptr absorber (ret :: R)) mem aw rdata σ k C) :
    ∃ result, AbsorbLoopTailTrace v account basic old price i delta evm result ∧
      internalBoundedRun (deployedRuntime v) ee g s0 free.toNat
        (free.toNat + 928 * (v.numAssets.toNat - i)) ret R result := by
  obtain ⟨result, ht, growth, hg, hr⟩ := cometAbsorbLoop (v := v) account
    (by change R.length + 1 + 27 ≤ 1024; omega) basic.assets_lt basic.reserved_lt hi
    hfree hlo hmem hbound hs h
  cases result with
  | reverted => exact ⟨.reverted, .loopReverted ht, hr⟩
  | staticViolation => exact ⟨.staticViolation, .loopStatic ht, hr⟩
  | ok evm' finalDelta =>
      obtain ⟨σ1, mem1, free1, aw1, data1, k1, C1, hs1, hfn, hf1, hsize, hp, r1⟩ := hr
      have hbasic1 := hbasic.preserve hptr (hp.mono hsep)
      obtain ⟨result, hfinish, hr⟩ := cometAbsorbAfterLoop account basic hstack hbasic1 hptr hf1
        (by omega) hsize (by change free1.toNat + 64 < 2^256; omega) hs1 hret r1
      exact ⟨result, .finished ht hfinish, hr.bounded (by omega) (by omega) hsize⟩

end Benchmarks.CompoundIII.Comet
