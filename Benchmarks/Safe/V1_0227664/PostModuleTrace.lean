import Benchmarks.Safe.V1_0227664.PostModuleCheck
import Benchmarks.Safe.V1_0227664.PostModuleEvent

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V1_0227664

theorem safePostModuleTrace {I g s0 σ k C aw mem rdata}
    {hash guard ptr ret : UInt256} {R : List UInt256} (z : Bool) (evm : EVM.State)
    (h : RD fork safeBytecode I g s0 ⟨7311⟩
      (z.toUInt256 :: hash :: guard :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 68 < UInt256.size) (hov : R.length + 16 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev fork safeBytecode g s0 ∧
      ExecFuncBody fork config (postModuleFrame (AccountAddress.ofUInt256 guard) hash z) evm
        postModuleExecutionFunction.body .reverted) ∨
    (RDstatic fork safeBytecode g s0 ∧
      ExecFuncBody fork config (postModuleFrame (AccountAddress.ofUInt256 guard) hash z) evm
        postModuleExecutionFunction.body .staticViolation) ∨
    ∃ frame evm' σ' mem' aw' rdata' k' C',
      ExecFuncBody fork config (postModuleFrame (AccountAddress.ofUInt256 guard) hash z) evm
        postModuleExecutionFunction.body (.returned frame evm' none) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ret R mem' aw' rdata' σ' k' C' ∧
      (mem' = mem ∨ mem' = postModuleMemory mem ptr hash z) := by
  rcases safePostModuleCheckTrace z evm h hee hacc hworld hf hm hp hb hov with
    ⟨hr, hs⟩ | ⟨frame, evm', σ', mem', aw', rdata', k', C', hs, hz, he, ha, hw, hr, hmem⟩
  · exact Or.inl ⟨hr, safePostModuleSourceRevert hs⟩
  cases hperm : I.perm
  · exact Or.inr (Or.inl ⟨safePostModuleEventTraceStatic z hr (by omega) hperm,
      safePostModuleSourceStatic hs hz (by simpa only [he] using hperm)⟩)
  · obtain ⟨aw'', k'', C'', hr'⟩ := safePostModuleEventTrace z hr (by omega) hret hperm
    exact Or.inr (Or.inr ⟨frame, evm', σ', mem', aw'', rdata', k'', C'',
      safePostModuleSourceSuccess (hperm := by simpa only [he] using hperm) hs hz, he, ha, hw, hr', hmem⟩)

end Benchmarks.Safe.V1_0227664
