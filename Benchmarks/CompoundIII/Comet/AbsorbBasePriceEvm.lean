import Benchmarks.CompoundIII.Comet.AbsorbBasePriceModel
import Benchmarks.CompoundIII.Comet.AbsorbLoopTailEvm
import Benchmarks.CompoundIII.Comet.PriceInternal
import Benchmarks.CompoundIII.Comet.PriceAssetMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbBasePrice {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free old ptr absorber ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (basic : UserBasicData) (hstack : R.length + 34 ≤ 1024)
    (hbasic : UserBasicMemory mem ptr basic) (hptr : 96 ≤ ptr.toNat)
    (hsep : ptr.toNat + 160 ≤ free.toNat)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : free.toNat ≤ mem.size)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hs : SourceState s0 ee σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17062⟩
      (basic.reserved :: basic.principal :: basic.assets :: EVM.word account.val :: old :: ptr ::
        absorber :: ret :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbBasePriceTrace v account basic old evm result ∧
      internalBoundedRun (deployedRuntime v) ee g s0 free.toNat
        (free.toNat + 160 + 928 * v.numAssets.toNat) ret R result := by
  have r1 := cometWithExtendedAssetList_block_17062 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_17062_stack, wordsOf_immStore_baseTokenPriceFeed] at r1
  obtain ⟨evm', σ', z, out, hcall, hs', hh, hr⟩ := cometPriceInternal (v := v) v.baseTokenPriceFeed
    (by change R.length + 8 + 12 ≤ 1024; omega) hfree hlo (by omega) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  have hh' : out.size < 2^255 := lt_trans hh (by decide)
  by_cases hv : z = true ∧ PriceValid out
  · rw [if_pos hv] at hr
    obtain ⟨rfl, hv⟩ := hv
    obtain ⟨aw2, k2, C2, r2⟩ := hr
    have hhi : out.size < UInt256.size := lt_trans hh (by change 2^138 < 2^256; decide)
    have hf : (free + (⟨160⟩ : UInt256)).toNat = free.toNat + 160 :=
      uadd_word_ofNat_toNat free 160 (by change free.toNat + 160 < 2^256; omega)
    have hgap : free.toNat ≤ mem.size + 32 := by omega
    have hm := hbasic.preserve hptr ((priceReturnMemory_prefix hv.1 hhi).mono hsep)
    have r3 := cometWithExtendedAssetList_block_17104 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 8 ≤ 1024; omega) r2
    obtain ⟨result, ht, hrun⟩ := cometAbsorbLoopTail account basic hstack (Nat.zero_le _)
      hm hptr (by rw [hf]; omega) (priceReturnMemory_free hlo hgap hv.1 hhi)
      (by rw [hf]; omega)
      (by rw [priceReturnMemory_size hlo hgap hv.1 hhi, hf]; omega)
      (by rw [hf, Nat.sub_zero]; exact hbound) hs' hret r3
    exact ⟨result, .finished hcall hh' hv ht, hrun.mono (by rw [hf]; omega)
      (by rw [hf, Nat.sub_zero])⟩
  · rw [if_neg hv] at hr
    exact ⟨.reverted, .priceFailed hcall hh' hv, hr⟩

end Benchmarks.CompoundIII.Comet
