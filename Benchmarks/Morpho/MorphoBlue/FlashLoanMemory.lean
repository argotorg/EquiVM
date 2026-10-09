import Benchmarks.Morpho.MorphoBlue.ZeroAssetsMessage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def flashLoanGuardMem : ByteArray := morphoZeroAssetsMem solcFreePtrMem

theorem flashLoanGuardMem_facts : flashLoanGuardMem.size = 192 ∧
    memLoad (UInt256.ofNat 64) flashLoanGuardMem = UInt256.ofNat 192 ∧
    memLoad (UInt256.ofNat 96) flashLoanGuardMem = UInt256.ofNat 0 ∧
    morphoErrorLength flashLoanGuardMem (UInt256.ofNat 128) = UInt256.ofNat 11 := by native_decide

def flashLoanEnterMem (assets : UInt256) : ByteArray := writeWord flashLoanGuardMem 192 assets

theorem flashLoanEnterMem_facts (assets : UInt256) :
    MorphoHeap (flashLoanEnterMem assets) (UInt256.ofNat 192) 0 ∧
    (flashLoanEnterMem assets).size = 224 ∧
    memLoad (UInt256.ofNat 96) (flashLoanEnterMem assets) = UInt256.ofNat 0 := by
  obtain ⟨hs, hf, hz, _⟩ := flashLoanGuardMem_facts
  have hg : 192 - flashLoanGuardMem.size < USize.size := by rw [hs]; exact USize.size_pos
  have hm : (flashLoanEnterMem assets).size = 224 := by
    rw [flashLoanEnterMem, writeWord_size _ _ _ hg, hs]; rfl
  have h64 : memLoad (UInt256.ofNat 64) (flashLoanEnterMem assets) = UInt256.ofNat 192 := by
    rw [flashLoanEnterMem, memLoad_writeWord_disjoint _ _ _ _ hg (by rw [hs]; decide) (Or.inl (by decide))]
    exact hf
  refine ⟨⟨by rw [hm]; decide, h64, by decide, by rw [hm]; exact USize.size_pos, by decide⟩, hm, ?_⟩
  rw [flashLoanEnterMem, memLoad_writeWord_disjoint _ _ _ _ hg (by rw [hs]; decide) (Or.inl (by decide))]
  exact hz

end Benchmarks.Morpho.MorphoBlue
