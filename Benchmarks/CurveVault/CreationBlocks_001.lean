import Reasoning.Reach
import Reasoning.Initcode
import Benchmarks.CurveVault.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace vaultCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Benchmarks.CurveVault.vaultCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Benchmarks.CurveVault.vaultCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem vaultCreation_block_0 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork (Benchmarks.CurveVault.vaultCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RDret fork (Benchmarks.CurveVault.vaultCreationBytecode ++ tail) g s0 σ (((Benchmarks.CurveVault.vaultCreationBytecode ++ tail).write (UInt256.ofNat 17).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 8635).toNat).readWithPadding (UInt256.ofNat 0).toNat (UInt256.ofNat 8635).toNat) := by
  let r0 := h
  have hcreationCodeSize : Benchmarks.CurveVault.vaultCreationBytecode.size = 8717 := by native_decide
  have r1 := r0.push2 (UInt256.ofNat 8635) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 17) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 8635) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r6 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

end vaultCreationBlocks
