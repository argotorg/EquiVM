import Benchmarks.Safe.ViaIR.Common
import Benchmarks.Safe.ViaIR.Blocks.Runtime_043

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

-- LIBRARY CANDIDATE: injectivity of canonical address-to-word conversion.
theorem addressWord_injective {a b : AccountAddress}
    (h : UInt256.ofNat a.val = UInt256.ofNat b.val) : a = b := by
  apply Fin.ext
  have ha : a.val < UInt256.size := lt_trans a.isLt (by decide)
  have hb : b.val < UInt256.size := lt_trans b.isLt (by decide)
  have hn := congrArg UInt256.toNat h
  simpa only [ulit_toNat' _ ha, ulit_toNat' _ hb] using hn

theorem safeEvalAuthorized (evm : EVM.State) (frame : Frame) :
    evalExpr? config frame evm (eqE sender this) =
      .ok (.bool (decide (evm.executionEnv.source = evm.executionEnv.codeOwner))) := by
  simp [eqE, sender, this, evalExpr?, envValue, evalBinaryOp?,
    EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq]

-- LIBRARY CANDIDATE: compare a decoded canonical address word with an account address.
theorem canonicalAddress_eq_address_iff (w : UInt256) (a : AccountAddress)
    (hcanon : w.toNat < EVM.addressModulus) :
    AccountAddress.ofNat w.toNat = a ↔ w = UInt256.ofNat a.val := by
  constructor
  · intro h
    have hw := congrArg (fun addr ↦ valueToWord (.address addr)) h
    dsimp only at hw
    rw [valueToWord_address_ofNat_canonical w hcanon] at hw
    exact Option.some.inj hw
  · intro h
    rw [h, ulit_toNat' _ (lt_trans a.isLt (by decide))]
    exact Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem safeAuthorizedTrace {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9325⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hauth : I.source = I.codeOwner)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret R mem aw rdata σ k' C' := by
  have h9333 := safeRuntime_block_9325_fallthrough (by simp; omega)
    (by rw [hauth]; exact u256_sub_self _) h
  exact ⟨_, _, safeRuntime_block_9333 (by omega) hret h9333⟩

theorem safeUnauthorizedTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9325⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hauth : I.source ≠ I.codeOwner) :
    RDrev fork safeBytecode g s0 := by
  have h9334 := safeRuntime_block_9325_taken (by omega)
    (u256_sub_ne_zero_of_ne (fun he ↦ hauth (addressWord_injective he))) (by jump_dest) h
  exact safeRuntime_block_9334 (by omega) h9334

end Benchmarks.Safe.ViaIR
