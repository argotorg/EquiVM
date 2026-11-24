import Benchmarks.CurveVault.SupplyArguments
import Benchmarks.CurveVault.MutationSites
import Benchmarks.CurveVault.RuntimeBlocks_011
import Benchmarks.CurveVault.RuntimeBlocks_014

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultCreditFlow (isDeposit : Bool) : VaultFlow := if isDeposit then .deposit else .mint
def vaultCreditResult (isDeposit : Bool) (assets shares : UInt256) : UInt256 := if isDeposit then shares else assets
def vaultCreditInput (isDeposit : Bool) (assets shares : UInt256) : UInt256 := if isDeposit then assets else shares

theorem vaultCreditMintSetup (isDeposit : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver assets shares : UInt256} {R : List UInt256}
    (hsize : 704 ≤ mem.size) (hr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hresult : memLoad (UInt256.ofNat 672) mem = vaultCreditResult isDeposit assets shares)
    (hinput : calldataWord I.calldata 4 = vaultCreditInput isDeposit assets shares)
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditFlow isDeposit).tokenNext) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 7682)
      (UInt256.ofNat (vaultCreditFlow isDeposit).saveEntry :: R)
      (vaultSupplyArguments mem receiver shares) aw' rdata σ k' C' := by
  cases isDeposit with
  | false =>
    change calldataWord I.calldata 4 = shares at hinput
    obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_3754_packed hstack (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7682) (UInt256.ofNat 3775 :: R)
      (vaultSupplyArguments mem (memLoad (UInt256.ofNat 576) mem) (calldataWord I.calldata 4)) aw' rdata σ k' C' at rd
    rw [hr, hinput] at rd
    exact ⟨aw', k', C', rd⟩
  | true =>
    change memLoad (UInt256.ofNat 672) mem = shares at hresult
    have hshares : memLoad (UInt256.ofNat 672) (receiver.toByteArray.write 0 mem 64 32) = shares := by
      rw [memLoad_above_write _ _ 64 672 (by rw [toByteArray_size]) (by omega) (by omega) hsize (by decide +kernel), hresult]
    obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_2749_packed hstack (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7682) (UInt256.ofNat 2771 :: R)
      (vaultSupplyArguments mem (memLoad (UInt256.ofNat 576) mem)
        (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 576) mem).toByteArray.write 0 mem 64 32))) aw' rdata σ k' C' at rd
    rw [hr, hshares] at rd
    exact ⟨aw', k', C', rd⟩

end Benchmarks.CurveVault
