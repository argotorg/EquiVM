import Benchmarks.CurveVault.TokenMemory
import Benchmarks.CurveVault.MutationSites
import Benchmarks.CurveVault.RuntimeBlocks_012
import Benchmarks.CurveVault.RuntimeBlocks_014
import Benchmarks.CurveVault.RuntimeBlocks_017
import Benchmarks.CurveVault.RuntimeBlocks_020

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultMutationReturn (flow : VaultFlow) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {target value : UInt256} {R : List UInt256}
    (hsize : 704 ≤ mem.size) (hload : memLoad (UInt256.ofNat 672) mem = value)
    (hperm : I.perm = true) (hstack : R.length + 6 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.saveNext) (target :: R) mem aw rdata σ k C) :
    RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩) value.toByteArray := by
  have hread (off : Nat) (hafter : 704 ≤ off) (hsmall : off + 32 < USize.size) (a b : UInt256) :
      (b.toByteArray.write 0 (a.toByteArray.write 0 mem off 32) (off + 32) 32).readWithPadding 672 32 =
        value.toByteArray := by
    have hframe := (wordMemoryRange_write mem a off 0 704
      (lt_of_le_of_lt (Nat.sub_le _ _) (by omega)) (Or.inl hafter)).trans
      (wordMemoryRange_write _ b (off + 32) 0 704
        (lt_of_le_of_lt (Nat.sub_le _ _) hsmall) (Or.inl (by omega)))
    exact readWithPadding_of_memLoad _ 672 value (le_trans hsize hframe.size) (by decide +kernel)
      ((hframe.load 672 (by omega) (by omega) hsize (by decide +kernel)).trans hload)
  cases flow with
  | deposit =>
    have hret := vaultBlocks.vault_block_2816 (by omega) hperm h
    change RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (((_ : UInt256).toByteArray.write 0 ((_ : UInt256).toByteArray.write 0 mem 704 32) (704 + 32) 32).readWithPadding 672 32) at hret
    rwa [hread 704 (by omega) (lt_usize _ (by omega))] at hret
  | mint =>
    have hret := vaultBlocks.vault_block_3820 (by omega) hperm h
    change RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (((_ : UInt256).toByteArray.write 0 ((_ : UInt256).toByteArray.write 0 mem 704 32) (704 + 32) 32).readWithPadding 672 32) at hret
    rwa [hread 704 (by omega) (lt_usize _ (by omega))] at hret
  | withdraw =>
    have hret := vaultBlocks.vault_block_4709 hstack hperm h
    change RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (((_ : UInt256).toByteArray.write 0 ((_ : UInt256).toByteArray.write 0 mem 736 32) (736 + 32) 32).readWithPadding 672 32) at hret
    rwa [hread 736 (by omega) (lt_usize _ (by omega))] at hret
  | redeem =>
    have hret := vaultBlocks.vault_block_5614 hstack hperm h
    change RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨0⟩)
      (((_ : UInt256).toByteArray.write 0 ((_ : UInt256).toByteArray.write 0 mem 736 32) (736 + 32) 32).readWithPadding 672 32) at hret
    rwa [hread 736 (by omega) (lt_usize _ (by omega))] at hret

end Benchmarks.CurveVault
