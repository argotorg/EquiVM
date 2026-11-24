import Benchmarks.CurveVault.TokenArguments
import Benchmarks.CurveVault.HookLayout
import Benchmarks.CurveVault.RuntimeBlocks_011
import Benchmarks.CurveVault.RuntimeBlocks_014
import Benchmarks.CurveVault.RuntimeBlocks_017
import Benchmarks.CurveVault.RuntimeBlocks_019

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultTokenFlowSender (flow : VaultFlow) (I : ExecutionEnv) (controller : UInt256) : UInt256 :=
  match flow with
  | .deposit | .mint => UInt256.ofNat I.source.val
  | .withdraw | .redeem => controller

def vaultTokenFlowRecipient (flow : VaultFlow) (controller receiver : UInt256) : UInt256 :=
  match flow with
  | .deposit | .mint => controller
  | .withdraw | .redeem => receiver

theorem vaultTokenSetup (flow : VaultFlow) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {controller receiver amount unused : UInt256} {R : List UInt256}
    (hsize : 736 ≤ mem.size)
    (hc : memLoad (UInt256.ofNat flow.controllerOffset) mem = controller)
    (hr : memLoad (UInt256.ofNat 576) mem = receiver)
    (ha : vaultHookAmount flow I mem = amount) (hstack : R.length + 2 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.hookNext) (unused :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 7556) (UInt256.ofNat flow.tokenNext :: R)
      (vaultTokenArguments mem (codeOwnerStorageWord I σ ⟨0⟩)
        (vaultTokenFlowSender flow I controller) (vaultTokenFlowRecipient flow controller receiver) amount)
      aw' rdata σ k' C' := by
  let token := codeOwnerStorageWord I σ ⟨0⟩
  let sender := vaultTokenFlowSender flow I controller
  let recipient := vaultTokenFlowRecipient flow controller receiver
  let mem0 := token.toByteArray.write 0 mem 64 32
  let mem1 := sender.toByteArray.write 0 mem0 96 32
  let mem2 := recipient.toByteArray.write 0 mem1 128 32
  have hgap (m : ByteArray) (off : Nat) (hsmall : off ≤ 128) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hf0 : WordMemoryRange mem mem0 192 UInt256.size :=
    wordMemoryRange_write _ _ 64 192 UInt256.size (hgap _ _ (by omega)) (Or.inr (by omega))
  have hf1 : WordMemoryRange mem mem1 192 UInt256.size := hf0.trans
    (wordMemoryRange_write _ _ 96 192 UInt256.size (hgap _ _ (by omega)) (Or.inr (by omega)))
  have hf2 : WordMemoryRange mem mem2 192 UInt256.size := hf1.trans
    (wordMemoryRange_write _ _ 128 192 UInt256.size (hgap _ _ (by omega)) (Or.inr (by omega)))
  have hc0 : memLoad (UInt256.ofNat flow.controllerOffset) mem0 = controller :=
    (hf0.load _ (by cases flow <;> decide +kernel) (by cases flow <;> decide +kernel)
      (by cases flow <;> dsimp only [VaultFlow.controllerOffset] <;> omega) (by cases flow <;> decide +kernel)).trans hc
  have hc1 : memLoad (UInt256.ofNat flow.controllerOffset) mem1 = controller :=
    (hf1.load _ (by cases flow <;> decide +kernel) (by cases flow <;> decide +kernel)
      (by cases flow <;> dsimp only [VaultFlow.controllerOffset] <;> omega) (by cases flow <;> decide +kernel)).trans hc
  have hr1 : memLoad (UInt256.ofNat 576) mem1 = receiver :=
    (hf1.load 576 (by omega) (by decide +kernel) (by omega) (by decide +kernel)).trans hr
  have ha2 : memLoad (UInt256.ofNat 672) mem2 = memLoad (UInt256.ofNat 672) mem :=
    hf2.load 672 (by omega) (by decide +kernel) (by omega) (by decide +kernel)
  cases flow with
  | deposit =>
    change memLoad (UInt256.ofNat 608) mem1 = controller at hc1
    change calldataWord I.calldata 4 = amount at ha
    obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_2718_packed hstack (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7556) (UInt256.ofNat 2749 :: R)
      (vaultTokenArguments mem token sender (memLoad (UInt256.ofNat 608) mem1) (calldataWord I.calldata 4)) aw' rdata σ k' C' at rd
    rw [hc1, ha] at rd
    exact ⟨aw', k', C', rd⟩
  | mint =>
    change memLoad (UInt256.ofNat 608) mem1 = controller at hc1
    change memLoad (UInt256.ofNat 672) mem = amount at ha
    change memLoad (UInt256.ofNat 672) (controller.toByteArray.write 0 mem1 128 32) = _ at ha2
    obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_3722_packed hstack (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7556) (UInt256.ofNat 3754 :: R)
      (vaultTokenArguments mem token sender (memLoad (UInt256.ofNat 608) mem1)
        (memLoad (UInt256.ofNat 672) ((memLoad (UInt256.ofNat 608) mem1).toByteArray.write 0 mem1 128 32))) aw' rdata σ k' C' at rd
    rw [hc1, ha2, ha] at rd
    exact ⟨aw', k', C', rd⟩
  | withdraw =>
    change memLoad (UInt256.ofNat 704) mem0 = controller at hc0
    change calldataWord I.calldata 4 = amount at ha
    change memLoad (UInt256.ofNat 576) (controller.toByteArray.write 0 mem0 96 32) = receiver at hr1
    obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_4630_packed hstack (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7556) (UInt256.ofNat 4664 :: R)
      (vaultTokenArguments mem token (memLoad (UInt256.ofNat 704) mem0)
        (memLoad (UInt256.ofNat 576) ((memLoad (UInt256.ofNat 704) mem0).toByteArray.write 0 mem0 96 32))
        (calldataWord I.calldata 4)) aw' rdata σ k' C' at rd
    rw [hc0, hr1, ha] at rd
    exact ⟨aw', k', C', rd⟩
  | redeem =>
    change memLoad (UInt256.ofNat 704) mem0 = controller at hc0
    change memLoad (UInt256.ofNat 672) mem = amount at ha
    change memLoad (UInt256.ofNat 576) (controller.toByteArray.write 0 mem0 96 32) = receiver at hr1
    change memLoad (UInt256.ofNat 672)
      (receiver.toByteArray.write 0 (controller.toByteArray.write 0 mem0 96 32) 128 32) = _ at ha2
    obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_5534_packed hstack (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7556) (UInt256.ofNat 5569 :: R)
      (vaultTokenArguments mem token (memLoad (UInt256.ofNat 704) mem0)
        (memLoad (UInt256.ofNat 576) ((memLoad (UInt256.ofNat 704) mem0).toByteArray.write 0 mem0 96 32))
        (memLoad (UInt256.ofNat 672)
          ((memLoad (UInt256.ofNat 576) ((memLoad (UInt256.ofNat 704) mem0).toByteArray.write 0 mem0 96 32)).toByteArray.write 0
            ((memLoad (UInt256.ofNat 704) mem0).toByteArray.write 0 mem0 96 32) 128 32))) aw' rdata σ k' C' at rd
    rw [hc0, hr1, ha2, ha] at rd
    exact ⟨aw', k', C', rd⟩

end Benchmarks.CurveVault
