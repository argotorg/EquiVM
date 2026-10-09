import Benchmarks.Safe.Common
import Benchmarks.Safe.Blocks.Runtime_029
import Benchmarks.Safe.Blocks.Runtime_030

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

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
    (h : RD safeBytecode I g s0 ⟨6757⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hauth : I.source = I.codeOwner)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret R mem aw rdata σ k' C' := by
  have h6781 := safeRuntime_block_6757_taken (by simp; omega)
    (by rw [hauth, uInt256_eq_self]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_6781 (by omega) hret h6781⟩

theorem safeUnauthorizedTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6757⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hauth : I.source ≠ I.codeOwner) :
    RDrev safeBytecode g s0 := by
  have h6765 := safeRuntime_block_6757_fallthrough (by omega)
    (uInt256_eq_zero_of_ne (fun he ↦ hauth (addressWord_injective (uInt256_eq_one_eq he)).symm)) h
  have h6898 := safeRuntime_block_6765 (by omega) (by jump_dest) h6765
  exact safeRuntime_block_6898 (by simp; omega) h6898

end Benchmarks.Safe
