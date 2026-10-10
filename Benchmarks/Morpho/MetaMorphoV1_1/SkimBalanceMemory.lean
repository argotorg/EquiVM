import Benchmarks.Morpho.MetaMorphoV1_1.TokenBalanceMemory

/-! The initial balance request creates the zero slot needed by empty transfer return data. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem skimBalanceRequest_zero (owner : AccountAddress) :
    memLoad ⟨96⟩ (tokenBalanceCallMem solcFreePtrMem 128 owner) = ⟨0⟩ := by
  change memLoad ⟨96⟩ ((UInt256.ofNat owner.toNat).toByteArray.write 0
    (writeWord solcFreePtrMem 128 tokenBalanceSelectorWord) 132 32) = _
  rw [memLoad_write_disjoint _ _ _ _
    (by rw [writeWord_sparse_size]; change 128 ≤ _; omega) (.inl (by decide))]
  decide +kernel

theorem skimBalanceMemory_zero (owner : AccountAddress) (out : ByteArray)
    (hl : 32 ≤ out.size) (hh : out.size < UInt256.size) :
    memLoad ⟨96⟩ (tokenBalanceReadMemory solcFreePtrMem ⟨128⟩ owner out) = ⟨0⟩ := by
  have hp : MemoryPrefix (tokenBalanceCallMem solcFreePtrMem 128 owner)
      (fixedReturnBuffer (tokenBalanceCallMem solcFreePtrMem 128 owner) ⟨128⟩ out 32) 128 := by
    rw [fixedReturnBuffer_long _ _ _ hl hh]
    exact copyWindow_prefix _ _ _ _ _ _ (by decide) (by omega)
      (by rw [tokenBalanceCallMem_size]; change 128 ≤ max solcFreePtrMem.size 164; omega)
      (.inl (le_refl _))
  have hp' := hp.trans (memoryPrefix_sparse_writeWord _ 64 128
    (nextCursor ⟨128⟩ ⟨32⟩) (.inr (by decide)))
  have h := hp'.load_preserved (by decide : 96 ≤ 96) (by decide)
    (by rw [tokenBalanceCallMem_size]; omega) (by decide)
  exact h.trans (skimBalanceRequest_zero owner)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
