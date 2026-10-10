import Benchmarks.UniswapV3.Pool.BalanceCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem balanceArgsMem_fresh_read96 (who : UInt256) :
    (balanceArgsMem solcFreePtrMem ⟨128⟩ who).readWithPadding 96 32 =
      (⟨0⟩ : UInt256).toByteArray := by
  change (Reasoning.Theory.writeWord solcFreePtrMem 164 who).readWithPadding 96 32 = _
  rw [writeWord_sparse_eq _ _ _ (by rw [solcFreePtrMem_size]; decide), solcFreePtrMem_size]
  rw [readWithPadding_eq_extract _ 96 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, solcFreePtrMem_size,
      toByteArray_size]; decide)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray_zeroes_size, solcFreePtrMem_size]; decide)]
  decide +kernel

theorem balanceBuildMem_fresh_read96 (who : UInt256) :
    (balanceBuildMem solcFreePtrMem ⟨128⟩ who).readWithPadding 96 32 =
      (⟨0⟩ : UInt256).toByteArray := by
  unfold balanceBuildMem
  rw [writeWord_sparse_read_preserved _ _ 96 _ (Or.inl ⟨by decide, by
    rw [balanceHeadMem_size _ _ _ (by decide), solcFreePtrMem_size]; decide⟩)]
  unfold balanceHeadMem
  rw [writeWord_sparse_read_preserved _ _ 96 _ (Or.inr ⟨by decide, by
    rw [writeWord_sparse_size, balanceArgsMem_size, solcFreePtrMem_size]; decide⟩)]
  rw [writeWord_sparse_read_preserved _ _ 96 _ (Or.inl ⟨by decide, by
    rw [balanceArgsMem_size, solcFreePtrMem_size]; decide⟩)]
  exact balanceArgsMem_fresh_read96 who

theorem balanceCopyBuild_fresh_zero (who : AccountAddress) :
    memLoad (UInt256.ofNat 96)
      (balanceCopyMem2 (balanceBuildMem solcFreePtrMem ⟨128⟩ (EVM.word who.val)) ⟨128⟩) = ⟨0⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [balanceCopyMem2_size]; change 96 < max _ 260; omega
  · change (balanceCopyMem2 (balanceBuildMem solcFreePtrMem ⟨128⟩ (EVM.word who.val))
        ⟨128⟩).readWithPadding 96 32 = _
    have hpref := balanceCopyMem2_prefix (balanceBuildMem solcFreePtrMem ⟨128⟩ (EVM.word who.val))
      (⟨128⟩ : UInt256)
    rw [hpref.read 96 (by decide) (by decide)
      (by rw [balanceBuildMem_size _ _ _ (by decide), solcFreePtrMem_size]; decide)]
    exact balanceBuildMem_fresh_read96 _

end Benchmarks.UniswapV3.Pool
