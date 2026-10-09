import Benchmarks.Safe.ModulePreDecoded
import Benchmarks.Safe.ModuleReturnDataSource
import Benchmarks.Safe.ModuleReturnDataMemory
import Benchmarks.Safe.ExecuteRawTrace
import Benchmarks.Safe.PostModuleTrace
import Benchmarks.Safe.BoolBytesReturn
import Benchmarks.Safe.Blocks.Runtime_017
import Benchmarks.Safe.Blocks.Runtime_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeModuleReturnDataTrace (evm : EVM.State) (payload : ByteArray)
    {I g s0 σ k C aw rdata} {target value operation : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2970⟩
      (operation :: ⟨128⟩ :: value :: target :: ⟨873⟩ :: R)
      (memoryBytesDecoded payload) aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hn : payload.size ≤ 2 ^ 64 - 192)
    (ho : operation.toNat < 2) (hov : R.length + 39 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecTransitionBody config contract evm
        (moduleArgs (AccountAddress.ofUInt256 target) value payload operation)
        exectransactionfrommodulereturndataTransition.body .reverted) ∨
    (RDstatic safeBytecode g s0 ∧
      ExecTransitionBody config contract evm
        (moduleArgs (AccountAddress.ofUInt256 target) value payload operation)
        exectransactionfrommodulereturndataTransition.body .staticViolation) ∨
    ∃ frame evm' σ' z out,
      ExecTransitionBody config contract evm
        (moduleArgs (AccountAddress.ofUInt256 target) value payload operation)
        exectransactionfrommodulereturndataTransition.body
        (.returned frame evm' (some [.bool z, .bytes out])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RDret safeBytecode g s0 σ' (boolBytesReturnBytes z out) := by
  have h₁ := safeRuntime_block_2970 (by simp; omega) (by jump_dest) h
  rcases safeModulePreDecodedTrace evm payload h₁ hee hacc hworld hn ho
    (by simp; omega) (by jump_dest) with
    ⟨hr, hs⟩ | ⟨preFrame, evm₁, σ₁, mem₁, aw₁, out₁, hash, k₁, C₁,
      hpre, he₁, ha₁, hw₁, h₂, hmem⟩
  · exact Or.inl ⟨hr, .execBlockRevert (safeModuleChecks hv hn ho
      (.consRevert (safeModulePreCall hs)))⟩
  change modulePreMemoryForm payload target value operation (UInt256.ofNat I.source.val) mem₁
    at hmem
  obtain ⟨hl, hd⟩ := modulePreMemoryData hn hmem
  obtain ⟨ptr, hf, hm, hp, hb⟩ := modulePreMemoryFree hn hmem
  have h₃ := safeRuntime_block_2987 (by simp; omega) (by jump_dest) h₂
  have hdata : mem₁.readWithPadding ((⟨128⟩ : UInt256) + UInt256.ofNat 32).toNat
      (memLoad ⟨128⟩ mem₁).toNat = payload := by
    rw [hl, ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
    exact hd
  rcases safeExecuteRawTrace evm₁ payload h₃ he₁ ha₁ hw₁ hdata (by omega)
    (by simp; omega) (by jump_dest) with
    ⟨hr, hne, hperm, hvalue⟩ |
      ⟨evm₂, σ₂, z, out₂, aw₂, k₂, C₂, hcall, he₂, ha₂, hw₂, h₄, hout₂, houtBound⟩
  · exact Or.inr (Or.inl ⟨hr, .execBlockStatic (safeModuleChecks hv hn ho
      (.consNormal (safeModulePreCall hpre) (.consStatic
        (safeExecuteCallStatementStatic (safeModuleExecuteLocals _ _ _ _ _ _)
          hne hperm hvalue))))⟩)
  have hexe := safeExecuteCallStatement (cfg := config)
    (safeModuleExecuteLocals _ (AccountAddress.ofUInt256 (preModuleGuardWord evm))
      _ _ hash _) hcall
  have hsmall : out₂.size < 2 ^ 138 := houtBound (by
    have hbound : 2 ^ 64 ≤ maxReturnDataSizeByGas := by decide +kernel
    omega)
  let dst := ptr.toNat + 32 + out₂.size
  have hdst : dst < 2 ^ 201 := by dsimp [dst]; omega
  have hdstNat : (UInt256.ofNat dst).toNat = dst :=
    ulit_toNat' _ (lt_trans hdst (by decide))
  let copied := moduleReturnDataMemory mem₁ ptr.toNat out₂
  have hcopied : copied.size = max mem₁.size dst := moduleReturnDataMemory_size _ _ _ hp
  have hfree : memLoad ⟨64⟩ copied = UInt256.ofNat dst := moduleReturnDataMemory_free _ _ _ hp
  have hbool : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
  rw [hbool] at h₄
  have h₅ := safeRuntime_block_3005 (by simp; omega)
    (by rw [ulit_toNat' _ hout₂]; change 0 + out₂.size ≤ out₂.size; omega) (by jump_dest) h₄
  rw [safeModuleReturnDataMemory hf (by change dst < 2 ^ 256; omega)] at h₅
  change memLoad (UInt256.ofNat 64) mem₁ = ptr at hf
  simp only [safeRuntime_block_3005_stack, hf] at h₅
  rcases safePostModuleTrace z evm₂ h₅ he₂ ha₂ hw₂ hfree
    (by rw [hcopied]; omega) (by rw [hdstNat]; dsimp [dst]; omega)
    (by rw [hdstNat]; change dst + 68 < 2 ^ 256; omega)
    (by simp; omega) (by jump_dest) with
    ⟨hr, hs⟩ | ⟨hr, hs⟩ |
      ⟨postFrame, evm₃, σ₃, mem₃, aw₃, out₃, k₃, C₃, hpost, he₃, ha₃, hw₃, h₆, hmem₃⟩
  · exact Or.inl ⟨hr, .execBlockRevert (safeModuleChecks hv hn ho
      (.consNormal (safeModulePreCall hpre) (.consNormal hexe
        (.consRevert (safeModuleReturnDataPost hs)))))⟩
  · exact Or.inr (Or.inl ⟨hr, .execBlockStatic (safeModuleChecks hv hn ho
      (.consNormal (safeModulePreCall hpre) (.consNormal hexe
        (.consStatic (safeModuleReturnDataPost hs)))))⟩)
  have h₇ := safeRuntime_block_3042 (by simp; omega) (by jump_dest) h₆
  have hf₃ : memLoad ⟨64⟩ mem₃ = UInt256.ofNat dst := by
    rcases hmem₃ with rfl | rfl
    · exact hfree
    · exact safePostModuleMemoryFree z hfree (by rw [hcopied]; omega)
        (by rw [hdstNat]; dsimp [dst]; omega)
  have hm₃ : dst ≤ mem₃.size := by
    rcases hmem₃ with rfl | rfl
    · rw [hcopied]; omega
    · simp only [postModuleMemory, selectorWordPairMemory, writeWord_sparse_size]
      rw [hdstNat, hcopied]; omega
  have hread (off count : Nat) (hi : off + count ≤ dst) :
      mem₃.readWithPadding off count = copied.readWithPadding off count := by
    rcases hmem₃ with rfl | rfl
    · rfl
    · exact postModuleMemory_readBelow _ _ _ _ _ _ (by rw [hcopied]; omega)
        (by rw [hdstNat]; exact hi)
  have hl₃ : memLoad (UInt256.ofNat ptr.toNat) mem₃ = UInt256.ofNat out₂.size := by
    apply memLoad_of_wordRead
    rw [ulit_toNat' _ (by change ptr.toNat < 2 ^ 256; omega),
      hread _ _ (by dsimp [dst]; omega)]
    exact moduleReturnDataMemory_length _ _ _
  have hd₃ : mem₃.readWithPadding (ptr.toNat + 32) out₂.size = out₂ := by
    rw [hread _ _ (by dsimp [dst]; omega)]
    exact moduleReturnDataMemory_payload _ _ _
  have hptr : UInt256.ofNat ptr.toNat = ptr := u256_ofNat_toNat ptr
  rw [← hptr] at h₇
  have hr := safeBoolBytesReturn z out₂ h₇ hf₃ hl₃ hd₃
    (by dsimp [dst] at hm₃; omega) (by dsimp [dst]; omega) hm₃ (by rfl)
    (by change dst + 160 + out₂.size < 2 ^ 256; omega) (by omega)
  exact Or.inr (Or.inr ⟨_, evm₃, σ₃, z, out₂, .execBlockRet (safeModuleChecks hv hn ho
    (.consNormal (safeModulePreCall hpre) (.consNormal hexe
      (.consNormal (safeModuleReturnDataPost hpost)
        (safeModuleReturnDataReturn _ _ _ _ _ _ _ _ _))))), he₃, ha₃, hw₃, hr⟩)

end Benchmarks.Safe
