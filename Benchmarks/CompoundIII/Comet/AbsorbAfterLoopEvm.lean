import Benchmarks.CompoundIII.Comet.AbsorbAfterLoopModel
import Benchmarks.CompoundIII.Comet.AbsorbBalanceEvm
import Benchmarks.CompoundIII.Comet.AbsorbFinishEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbAfterLoop {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw i old delta price ptr absorber ret free : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (basic : UserBasicData) (hstack : R.length + 34 ≤ 1024)
    (hbasic : UserBasicMemory mem ptr basic) (hptr : 96 ≤ ptr.toNat)
    (hf : memLoad ⟨64⟩ mem = free) (hl : 96 ≤ free.toNat) (hm : free.toNat ≤ mem.size)
    (hb : free.toNat + 64 < UInt256.size) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17156⟩
      (i :: basic.reserved :: basic.assets :: old :: basic.principal :: price :: EVM.word account.val ::
        delta :: ptr :: absorber :: ret :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbAfterLoopTrace v account basic old delta price evm result ∧
      internalPreservingRun (deployedRuntime v) ee g s0 mem free rdata ret R result := by
  have hr := cometAbsorbBalance (v := v) (by change R.length + 3 + 18 ≤ 1024; omega) h
  by_cases hv : AbsorbBalanceValid v old delta price
  · rw [if_pos hv] at hr
    obtain ⟨k1, C1, r1⟩ := hr
    obtain ⟨result, ht, hr⟩ := cometAbsorbFinish account basic hstack
      (absorbBalanceWord_lt v old delta price) hbasic hptr hf hl hm hb hs hret r1
    exact ⟨result, .finished hv ht, hr⟩
  · rw [if_neg hv] at hr
    exact ⟨.reverted, .balanceReverted hv, hr⟩

end Benchmarks.CompoundIII.Comet
