import Benchmarks.Safe.ViaIR.ExecTransactionAllocate
import Benchmarks.Safe.ViaIR.ExecTransactionGasMath

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000
set_option maxHeartbeats 800000

private theorem execGasSubtract (gas : UInt256) :
    gas + UInt256.lnot (UInt256.ofNat 2499) = UInt256.sub gas ⟨2500⟩ := by
  have hnot : (UInt256.lnot (UInt256.ofNat 2499)).toNat = 2 ^ 256 - 2500 := by decide +kernel
  have h2500 : (⟨2500⟩ : UInt256).toNat = 2500 := rfl
  have hb : gas.toNat < 2 ^ 256 := gas.val.isLt
  apply u256_inj
  rw [uadd_toNat, hnot]
  by_cases hf : 2500 ≤ gas.toNat
  · rw [usub_toNat (by exact hf), h2500]
    rw [show UInt256.size = 2 ^ 256 from rfl]
    omega
  · rw [usub_toNat_underflow (by change gas.toNat < 2500; omega), h2500]
    rw [show UInt256.size = 2 ^ 256 from rfl]
    omega

private theorem execGasSubtractUnderflow (gas : UInt256) (h : gas.toNat < 2500) :
    UInt256.gt (UInt256.sub gas ⟨2500⟩) gas = ⟨1⟩ := by
  apply ugt_one
  rw [usub_toNat_underflow (by exact h)]
  have h2500 : (⟨2500⟩ : UInt256).toNat = 2500 := rfl
  rw [h2500]
  have : 2500 < UInt256.size := by decide
  omega

private theorem execGasSubtractValid (gas : UInt256) (h : 2500 ≤ gas.toNat) :
    UInt256.gt (UInt256.sub gas ⟨2500⟩) gas = ⟨0⟩ :=
  ugt_zero (by rw [usub_toNat (by exact h)]; omega)

theorem safeExecExecutePrepare (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata src} {guard hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4639⟩
      (execGasSaved p src guard hash (⟨0⟩ :: R)) mem aw rdata σ k C)
    (hc : ExecTransactionCalldataFields I.calldata p) (hov : R.length + 36 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ p.tx.gasPrice = ⟨0⟩ ∧
      ∃ gasLeft : UInt256, gasLeft.toNat < 2500) ∨
    ∃ before gasLeft k' C', (p.tx.gasPrice = ⟨0⟩ → 2500 ≤ gasLeft.toNat) ∧
      RD fork safeBytecode I g s0 ⟨7208⟩
        ([UInt256.ofNat src, UInt256.ofNat p.tx.payload.size, UInt256.ofNat I.calldata.size,
          ⟨4689⟩, execCallGas p gasLeft, UInt256.ofNat p.tx.target.val, ⟨0⟩, ⟨0⟩] ++
          execCallSaved p before guard hash R) mem aw rdata σ k' C' := by
  have hprice : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 196).toNat 32) =
      p.tx.gasPrice := hc.gasPrice
  let before := (g.subNat (C + 2)).toUInt256
  by_cases hz : p.tx.gasPrice = ⟨0⟩
  · have h₁ := safeRuntime_block_4639_fallthrough (by simp; omega)
      (by rw [hprice, hz]; rfl) h
    let gasLeft := (g.subNat (C + 39 + 2 + 2)).toUInt256
    by_cases hfit : 2500 ≤ gasLeft.toNat
    swap
    · have hgt := execGasSubtractUnderflow gasLeft (by omega)
      have h₂ := safeRuntime_block_4653_taken (by
        simp; omega)
        (by rw [execGasSubtract]; rw [hgt]; decide) (by jump_dest) h₁
      have hr := safeRuntime_block_5344 (by
        simp; omega) h₂
      exact .inl ⟨hr, hz, gasLeft, by omega⟩
    have hgt := execGasSubtractValid gasLeft hfit
    have h₂ := safeRuntime_block_4653_fallthrough (by
      simp; omega)
      (by rw [execGasSubtract]; exact hgt) h₁
    have h₃ := safeRuntime_block_4667 (by simp; omega) h₂
    have h₄ := safeRuntime_block_4682 (by simp; omega) (by jump_dest) h₃
    exact .inr ⟨before, gasLeft, _, _, fun _ ↦ hfit, by
      simpa only [safeRuntime_block_4682_stack, safeRuntime_block_4667_stack,
      safeRuntime_block_4653_fallthrough_stack, safeRuntime_block_4639_fallthrough_stack,
      hprice, execCallSaved, execCallGas, if_pos hz, u256_add_comm
        (UInt256.lnot (UInt256.ofNat 2499)), execGasSubtract, before, gasLeft] using h₄⟩
  · have h₁ := safeRuntime_block_4639_taken (by simp; omega)
      (by rw [hprice, isZero_eq_zero_of_ne hz]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_5364 (by
      simp; omega) (by jump_dest) h₁
    have h₃ := safeRuntime_block_4682 (by simp; omega) (by jump_dest) h₂
    exact .inr ⟨before, ⟨0⟩, _, _, fun he ↦ (hz he).elim, by
      simpa only [safeRuntime_block_4682_stack, safeRuntime_block_5364_stack,
      safeRuntime_block_4639_taken_stack, hprice,
      show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 132).toNat 32) =
        p.tx.safeTxGas from hc.safeTxGas,
      execCallSaved, execCallGas, if_neg hz, before] using h₃⟩

end Benchmarks.Safe.ViaIR
