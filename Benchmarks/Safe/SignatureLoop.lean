import Benchmarks.Safe.SignatureIteration
import Benchmarks.Safe.Blocks.Runtime_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem evalSignatureLoopCondition {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {i : Nat} {last : UInt256} (hc : SignatureContext p f i last) :
    evalExpr? config f evm signatureLoopCondition =
      .ok (.bool (decide (i < p.required.toNat))) := by
  rw [signatureLoopCondition, ltE, evalExpr_binary_nonshort (by decide) (by decide),
    evalLocalValue hc.index, evalLocalValue hc.required]
  simp [EvalResult.bind, bind, evalBinaryOp?, uint256Value, Int.ofNat_eq_natCast, pure]

theorem safeSignatureLoop (fuel : Nat) (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src i} {s r v current last executor ret : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD safeBytecode I g s0 ⟨2002⟩
      (UInt256.ofNat i :: s :: r :: v :: current :: last :: p.required :: UInt256.ofNat src ::
        p.hash :: executor :: ret :: R) mem aw rdata σ k C)
    (hc : SignatureContext p f i last) (he : p.executor = AccountAddress.ofUInt256 executor)
    (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr + fuel * 2 ^ 140 < 2 ^ 224)
    (hn : p.signatures.size < 2 ^ 64) (hreq : p.requiredBytes ≤ p.signatures.size)
    (hcount : p.required.toNat = i + fuel) (hov : R.length + 44 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev safeBytecode g s0 ∧
      ExecStmt config f evm (.while signatureLoopCondition signatureLoopBody) .reverted) ∨
    ∃ f' evm' σ' mem' ptr' aw' out k' C',
      ExecStmt config f evm (.while signatureLoopCondition signatureLoopBody) (.ok f' evm') ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret R mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + fuel * 2 ^ 140 ∧
      mem'.size ≤ max mem.size (ptr + fuel * 2 ^ 140) ∧ MemoryPreserves mem mem' 96 ptr := by
  induction fuel generalizing i f evm σ k C aw mem rdata ptr s r v current last old with
  | zero =>
      have hib : i < UInt256.size := by
        have hr : p.required.toNat < UInt256.size := p.required.val.isLt
        omega
      have hlt : UInt256.lt (UInt256.ofNat i) p.required = ⟨0⟩ :=
        ult_zero (by rw [ulit_toNat' i hib, hcount]; omega)
      have h₁ := safeRuntime_block_2002_taken (by simp; omega)
        (by rw [hlt]; decide) (by jump_dest) h
      obtain ⟨aw', k', C', h₂⟩ := safeRuntime_block_2790_packed (by omega) hret h₁
      refine .inr ⟨f, evm, σ, mem, ptr, aw', rdata, k', C', .whileFalse ?_, hee, hacc, hworld,
        h₂, hm, hf, hz, Nat.le_refl _, by omega, by omega, MemoryPreserves.refl _ _ _⟩
      simpa only [hcount, Nat.add_zero, lt_self_iff_false, decide_false] using
        evalSignatureLoopCondition (evm := evm) hc
  | succ fuel ih =>
      have hi : i < p.required.toNat := by omega
      have hib : i < UInt256.size := lt_trans hi p.required.val.isLt
      have hlt : UInt256.lt (UInt256.ofNat i) p.required = ⟨1⟩ :=
        ult_one (by rwa [ulit_toNat' i hib])
      have hcond : evalExpr? config f evm signatureLoopCondition = .ok (.bool true) := by
        simpa only [hi, decide_true] using evalSignatureLoopCondition (evm := evm) hc
      have h₁ := safeRuntime_block_2002_fallthrough (by simp; omega) (by rw [hlt]; decide) h
      obtain ⟨hrev, hbody⟩ | ⟨f', evm', σ', mem', ptr', aw', out, s', r', v', owner, k', C',
          hbody, hc', ho', hee', hacc', hw', h₂, hm', hf', hz', hpl, hph, hms, hpres⟩ :=
        safeSignatureIteration p evm h₁ hc he ho hee hacc hworld hm hf hz hsrc ha (by omega)
          hn hreq hi (by simp; omega)
      · exact .inl ⟨hrev, .whileRevert hcond hbody⟩
      obtain ⟨hrev, htail⟩ | ⟨f'', evm'', σ'', mem'', ptr'', aw'', out', k'', C'', htail,
          hee'', hacc'', hw'', h₃, hm'', hf'', hz'', hpl', hph', hms', hpres'⟩ :=
        ih evm' h₂ hc' ho' hee' hacc' hw' hm' hf' hz' (by omega) (by omega) (by omega)
      · exact .inl ⟨hrev, .whileTrue hcond hbody htail⟩
      exact .inr ⟨f'', evm'', σ'', mem'', ptr'', aw'', out', k'', C'',
        .whileTrue hcond hbody htail, hee'', hacc'', hw'', h₃, hm'', hf'', hz'', hpl.trans hpl',
        by omega, by omega, hpres.trans hpres' hpl⟩

end Benchmarks.Safe
