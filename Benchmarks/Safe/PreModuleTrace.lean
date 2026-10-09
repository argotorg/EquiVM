import Benchmarks.Safe.PreModuleCheck
import Benchmarks.Safe.PreModuleAuthorization

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safePreModuleTrace (words : List UInt256) (payload : ByteArray) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {target value operation ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7172⟩
      (operation :: UInt256.ofNat src :: value :: target :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat payload.size)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (payload.size + 31) / 32)
    (hbytes : (wordBytes words).extract 0 payload.size = payload)
    (hm : 96 ≤ mem.size) (hu : mem.size ≤ ptr + 164) (hp : 96 ≤ ptr) (hsrc : 96 ≤ src)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr)
    (hb : ptr + 228 + 32 * words.length < UInt256.size)
    (hsmall : 196 + 32 * words.length ≤ maxReturnDataSizeByGas)
    (ho : operation.toNat < 2) (hov : R.length + 30 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config (preModuleFrame (AccountAddress.ofUInt256 target)
        value payload operation) evm preModuleExecutionFunction.body .reverted) ∨
    ∃ frame evm' σ' mem' aw' rdata' hash k' C',
      ExecFuncBody config (preModuleFrame (AccountAddress.ofUInt256 target)
        value payload operation) evm preModuleExecutionFunction.body
        (.returned frame evm' (some [.address (AccountAddress.ofUInt256 (preModuleGuardWord evm)),
          .fixedBytes bytes32Width (EVM.Word.toBytesBE hash)])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret (hash :: preModuleGuardWord evm :: R)
        mem' aw' rdata' σ' k' C' ∧
      (mem' = twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem ∨
        ∃ out, out.size < 2 ^ 138 ∧ mem' = preModuleReturnMemory
          (preModuleCallMemory (twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem)
            ptr payload.size target value operation (UInt256.ofNat I.source.val) words)
          out (UInt256.ofNat ptr)) := by
  rcases safePreModuleAuthorizationTrace evm h hee hacc (by omega) (by simp; omega) with
    ⟨hr, hn⟩ | ⟨hauth, aw₁, k₁, C₁, h₁⟩
  · exact Or.inl ⟨hr, safePreModuleUnauthorized evm _ value payload operation hn⟩
  let m := twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem
  have hs : m.size = mem.size := twoWordHashMem_size_of_ge64 _ _ (by omega)
  have hread (off : Nat) (hlo : 64 ≤ off) (hin : off + 32 ≤ mem.size) :
      m.readWithPadding off 32 = mem.readWithPadding off 32 :=
    twoWordHashMem_read32_above64 _ _ hlo hin
  have hf' : memLoad ⟨64⟩ m = UInt256.ofNat ptr := by
    simpa only [memLoad, show (⟨64⟩ : UInt256).toNat = 64 from rfl, hs,
      if_neg (show ¬ 64 ≥ mem.size by omega), hread 64 (by omega) hm] using hf
  have hl' : memLoad (UInt256.ofNat src) m = UInt256.ofNat payload.size := by
    have hst : (UInt256.ofNat src).toNat = src := ulit_toNat' _ (by omega)
    simpa only [memLoad, hst, hs, if_neg (show ¬ src ≥ mem.size by omega),
      hread src (by omega) (by omega)] using hl
  have hw' : WordArrayMemory m (src + 32) words := by
    intro i hi
    rw [hread _ (by omega) (by omega)]
    exact hw i hi
  rcases safePreModuleCheckTrace words payload evm h₁ hee hacc hworld hf' hl' hw' hn hbytes
    (by rw [hs]; exact hm) (by rw [hs]; exact hu) hp (by rw [hs]; exact hin)
    ha hb hsmall ho (by simp; omega) with
    ⟨hr, hc⟩ | ⟨frame, evm', σ', mem', aw', rdata', hash, k', C', hc, hg, hh,
      he, hac, hwo, hr, hmem⟩
  · exact Or.inl ⟨hr, safePreModuleSourceRevert hauth hc⟩
  have h₂ := safeRuntime_block_7399 (by simp; omega) hret hr
  exact Or.inr ⟨frame, evm', σ', mem', _, rdata', hash, _, _,
    safePreModuleSourceReturn hauth hc hg hh, he, hac, hwo, h₂, hmem⟩

end Benchmarks.Safe
