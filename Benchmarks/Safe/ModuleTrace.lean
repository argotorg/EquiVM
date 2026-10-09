import Benchmarks.Safe.ModulePreDecoded
import Benchmarks.Safe.ModuleCallerSource
import Benchmarks.Safe.ExecuteTrace
import Benchmarks.Safe.PostModuleTrace
import Benchmarks.Safe.BoolReturnMemory
import Benchmarks.Safe.Blocks.Runtime_017
import Benchmarks.Safe.Blocks.Runtime_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeModuleTrace (evm : EVM.State) (payload : ByteArray)
    {I g s0 σ k C aw rdata} {target value operation : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2914⟩
      (operation :: ⟨128⟩ :: value :: target :: ⟨759⟩ :: R)
      (memoryBytesDecoded payload) aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hn : payload.size ≤ 2 ^ 64 - 192)
    (ho : operation.toNat < 2) (hov : R.length + 38 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecTransitionBody config contract evm
        (moduleArgs (AccountAddress.ofUInt256 target) value payload operation)
        exectransactionfrommoduleTransition.body .reverted) ∨
    (RDstatic safeBytecode g s0 ∧
      ExecTransitionBody config contract evm
        (moduleArgs (AccountAddress.ofUInt256 target) value payload operation)
        exectransactionfrommoduleTransition.body .staticViolation) ∨
    ∃ frame evm' σ' z,
      ExecTransitionBody config contract evm
        (moduleArgs (AccountAddress.ofUInt256 target) value payload operation)
        exectransactionfrommoduleTransition.body (.returned frame evm' (some [.bool z])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RDret safeBytecode g s0 σ' z.toUInt256.toByteArray := by
  have h₁ := safeRuntime_block_2914 (by simp; omega) (by jump_dest) h
  rcases safeModulePreDecodedTrace evm payload h₁ hee hacc hworld hn ho
    (by simp; omega) (by jump_dest) with
    ⟨hr, hs⟩ | ⟨preFrame, evm₁, σ₁, mem₁, aw₁, out₁, hash, k₁, C₁,
      hpre, he₁, ha₁, hw₁, h₂, hmem⟩
  · exact Or.inl ⟨hr, .execBlockRevert (safeModulePrefix hv hn ho
      (.consRevert (safeModulePreCall hs)))⟩
  change modulePreMemoryForm payload target value operation (UInt256.ofNat I.source.val) mem₁
    at hmem
  obtain ⟨hl, hd⟩ := modulePreMemoryData hn hmem
  obtain ⟨ptr, hf, hm, hp, hb⟩ := modulePreMemoryFree hn hmem
  have h₃ := safeRuntime_block_2929 (by simp; omega) (by jump_dest) h₂
  have hdata : mem₁.readWithPadding ((⟨128⟩ : UInt256) + UInt256.ofNat 32).toNat
      (memLoad ⟨128⟩ mem₁).toNat = payload := by
    rw [hl, ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
    exact hd
  rcases safeExecuteTrace evm₁ payload h₃ he₁ ha₁ hw₁ hdata (by omega)
    (by simp; omega) (by jump_dest) with
    ⟨hr, hs⟩ | ⟨evm₂, σ₂, z, out₂, aw₂, k₂, C₂, hexe, he₂, ha₂, hw₂, h₄, hout₂⟩
  · exact Or.inr (Or.inl ⟨hr, .execBlockStatic (safeModulePrefix hv hn ho
      (.consNormal (safeModulePreCall hpre) (.consStatic (safeModuleExecuteCall hs))))⟩)
  have hbool : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
  rw [hbool] at h₄
  have h₅ := safeRuntime_block_2947 (by simp; omega) (by jump_dest) h₄
  rcases safePostModuleTrace z evm₂ h₅ he₂ ha₂ hw₂ hf hm hp
    (by change ptr.toNat + 68 < 2 ^ 256; omega) (by simp; omega) (by jump_dest) with
    ⟨hr, hs⟩ | ⟨hr, hs⟩ |
      ⟨postFrame, evm₃, σ₃, mem₃, aw₃, out₃, k₃, C₃, hpost, he₃, ha₃, hw₃, h₆, hmem₃⟩
  · exact Or.inl ⟨hr, .execBlockRevert (safeModulePrefix hv hn ho
      (.consNormal (safeModulePreCall hpre) (.consNormal (safeModuleExecuteCall hexe)
        (.consRevert (safeModulePostCall hs)))))⟩
  · exact Or.inr (Or.inl ⟨hr, .execBlockStatic (safeModulePrefix hv hn ho
      (.consNormal (safeModulePreCall hpre) (.consNormal (safeModuleExecuteCall hexe)
        (.consStatic (safeModulePostCall hs)))))⟩)
  have h₇ := safeRuntime_block_2960 (by simp; omega) (by jump_dest) h₆
  have hf₃ : memLoad ⟨64⟩ mem₃ = ptr := by
    rcases hmem₃ with rfl | rfl
    · exact hf
    · exact safePostModuleMemoryFree z hf hm hp
  have hm₃ : 96 ≤ mem₃.size := by
    rcases hmem₃ with rfl | rfl
    · exact hm
    · simp only [postModuleMemory, selectorWordPairMemory, writeWord_sparse_size]
      omega
  have hr := safeReturnBoolFromMemory h₇ (by omega) hf₃ hm₃ hp
  exact Or.inr (Or.inr ⟨_, evm₃, σ₃, z, .execBlockRet (safeModulePrefix hv hn ho
    (.consNormal (safeModulePreCall hpre) (.consNormal (safeModuleExecuteCall hexe)
      (.consNormal (safeModulePostCall hpost) (safeModuleReturn _ _ _ _ _ _ _ _))))),
    he₃, ha₃, hw₃, hr⟩)

end Benchmarks.Safe
