import Benchmarks.CurveVault.DebitSource
import Benchmarks.CurveVault.SupplyArguments
import Benchmarks.CurveVault.RuntimeBlocks_016
import Benchmarks.CurveVault.RuntimeBlocks_019

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDebitBurnMemory (isWithdraw : Bool) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray) : ByteArray :=
  if isWithdraw then (codeOwnerStorageWord I σ ⟨3⟩).toByteArray.write 0 mem 704 32 else mem

theorem vaultDebitBurnMemory_frame (isWithdraw : Bool) (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray) :
    WordMemoryRange mem (vaultDebitBurnMemory isWithdraw I σ mem) 0 704 := by
  cases isWithdraw
  · exact WordMemoryRange.refl _ _ _
  · exact wordMemoryRange_write _ _ 704 0 704
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega))) (Or.inl (by omega))

theorem vaultDebitBurnSetup (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner assets shares : UInt256} {R : List UInt256}
    (hsize : 704 ≤ mem.size) (ho : memLoad (UInt256.ofNat 608) mem = owner)
    (hresult : memLoad (UInt256.ofNat 672) mem = vaultDebitResult isWithdraw assets shares)
    (hinput : calldataWord I.calldata 4 = vaultDebitInput isWithdraw assets shares)
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (if isWithdraw then 4549 else 5453)) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 8024)
      (UInt256.ofNat (vaultDebitFlow isWithdraw).hookEntry :: R)
      (vaultSupplyArguments (vaultDebitBurnMemory isWithdraw I σ mem) owner shares) aw' rdata σ k' C' := by
  cases isWithdraw with
  | false =>
    change calldataWord I.calldata 4 = shares at hinput
    obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_5453_packed hstack (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 8024) (UInt256.ofNat 5474 :: R)
      (vaultSupplyArguments mem (memLoad (UInt256.ofNat 608) mem) (calldataWord I.calldata 4)) aw' rdata σ k' C' at rd
    rw [ho, hinput] at rd
    exact ⟨aw', k', C', rd⟩
  | true =>
    change memLoad (UInt256.ofNat 672) mem = shares at hresult
    let mem0 := vaultDebitBurnMemory true I σ mem
    have hframe := vaultDebitBurnMemory_frame true I σ mem
    have hsize0 : 704 ≤ mem0.size := le_trans hsize hframe.size
    have ho0 : memLoad (UInt256.ofNat 608) mem0 = owner :=
      (hframe.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans ho
    have hv0 : memLoad (UInt256.ofNat 672) mem0 = shares :=
      (hframe.load 672 (by omega) (by omega) hsize (by decide +kernel)).trans hresult
    have hv1 : memLoad (UInt256.ofNat 672) (owner.toByteArray.write 0 mem0 64 32) = shares := by
      rw [memLoad_above_write _ _ 64 672 (by rw [toByteArray_size]) (by omega) (by omega)
        hsize0 (by decide +kernel), hv0]
    obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_4549_packed hstack (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 8024) (UInt256.ofNat 4578 :: R)
      (vaultSupplyArguments mem0 (memLoad (UInt256.ofNat 608) mem0)
        (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 608) mem0).toByteArray.write 0 mem0 64 32)))
      aw' rdata σ k' C' at rd
    rw [ho0, hv1] at rd
    exact ⟨aw', k', C', rd⟩

end Benchmarks.CurveVault
