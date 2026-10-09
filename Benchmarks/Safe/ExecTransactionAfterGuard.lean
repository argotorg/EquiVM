import Benchmarks.Safe.ExecTransactionFinish
import Benchmarks.Safe.ExecTransactionPaymentTrace
import Benchmarks.Safe.ExecTransactionSuccessCheck
import Benchmarks.Safe.ExecTransactionGasCheck

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem safeExecTransactionAfterGuard (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src ptr locals} {sigPtr guard hash : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3758⟩
      (execGuardSaved p src sigPtr guard hash (⟨759⟩ :: R)) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : ExecTransactionLocals p locals)
    (hg : locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)))
    (hh : locals["txHash"]? = some (wordBytes32Value hash))
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hz : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr) (hb : ptr < 2 ^ 205)
    (hs : src < UInt256.size) (hd : src + p.tx.payload.size ≤ I.calldata.size)
    (hdata : I.calldata.extract src (src + p.tx.payload.size) = p.tx.payload)
    (hn : p.tx.payload.size < 2 ^ 64) (ho : p.tx.operation.toNat < 2)
    (hov : R.length + 48 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 8) .reverted) ∨
    (RDstatic safeBytecode g s0 ∧ ExecBlock config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 8) .staticViolation) ∨
    ∃ frame' evm' σ' z,
      ExecBlock config { contract := contract, locals := locals } evm
        (exectransactionTransition.body.drop 8) (.returned frame' evm' (some [.bool z])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RDret safeBytecode g s0 σ' z.toUInt256.toByteArray := by
  obtain ⟨hr, hs⟩ | ⟨gasCheck, k₁, C₁, prefix₁, h₁⟩ :=
    safeExecGasCheck p evm h hl (by simp; omega)
  · exact .inl ⟨hr, hs⟩
  have hl₁ : ExecTransactionLocals p (execCheckGasFrame locals gasCheck).locals :=
    hl.set _ _ (by decide)
  have hwindow : ptr + 64 + p.tx.payload.size < UInt256.size := by
    change ptr + 64 + p.tx.payload.size < 2 ^ 256; omega
  obtain ⟨hr, hsource⟩ | ⟨hr, hsource⟩ |
      ⟨before, gasLeft, z, evm₂, σ₂, out₂, aw₂, k₂, C₂, prefix₂, he₂, ha₂, hw₂, h₂, _⟩ :=
    safeExecTransactionExecute p evm h₁ hee hacc hworld hl₁ hf (by omega) hwindow hs hd hdata ho
      (by simp; omega)
  · exact .inl ⟨hr, prefix₁ _ hsource⟩
  · exact .inr (.inl ⟨hr, prefix₁ _ hsource⟩)
  let f₂ := execAfterExecute (execCheckGasFrame locals gasCheck).locals before gasLeft z
  have hl₂ : ExecTransactionLocals p f₂.locals := execAfterExecute_locals hl₁ before gasLeft z
  have hbefore : f₂.locals["gasBefore"]? = some (uint256Value before) := by
    simp [f₂, execAfterExecute, execExecuteFrame, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]
  obtain ⟨hr, hsource⟩ | ⟨after, k₃, C₃, prefix₃, h₃⟩ :=
    safeExecGasUsed p evm₂ h₂ hbefore (by simp; omega)
  · exact .inl ⟨hr, prefix₁ _ (prefix₂ _ hsource)⟩
  let f₃ := execGasUsedFrame f₂.locals before after
  have hl₃ : ExecTransactionLocals p f₃.locals :=
    (hl₂.set _ _ (by decide)).set _ _ (by decide)
  have hz₃ : f₃.locals["success"]? = some (.bool z) := by
    simp [f₃, f₂, execGasUsedFrame, execAfterExecute, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]
  have hu₃ : f₃.locals["gasUsed"]? = some (uint256Value (UInt256.sub before after)) := by
    simp [f₃, execGasUsedFrame]
  have hg₃ : f₃.locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)) := by
    simp [f₃, f₂, execGasUsedFrame, execAfterExecute, execExecuteFrame, execCheckGasFrame,
      Std.HashMap.getElem?_insert, hg]
  have hh₃ : f₃.locals["txHash"]? = some (wordBytes32Value hash) := by
    simp [f₃, f₂, execGasUsedFrame, execAfterExecute, execExecuteFrame, execCheckGasFrame,
      Std.HashMap.getElem?_insert, hh]
  obtain ⟨hr, hsource⟩ | ⟨k₄, C₄, prefix₄, h₄⟩ :=
    safeExecSuccessCheck p evm₂ h₃ hl₃ hz₃ (by simp; omega)
  · exact .inl ⟨hr, prefix₁ _ (prefix₂ _ (prefix₃ _ hsource))⟩
  let ptr₂ := ptr + 32 + ABI.paddedSize p.tx.payload.size
  have hf₂ : memLoad ⟨64⟩ (execDataMemory p I.calldata mem src ptr) = UInt256.ofNat ptr₂ :=
    calldataBufferMemory_free _ _ _ _ _ _ _ (by omega) (by omega) hd
  have hpres := calldataBufferMemory_preserved I.calldata mem src ptr p.tx.payload.size
    p.tx.payload.size ptr₂ (by omega) hd
  have hz₂ : memLoad ⟨96⟩ (execDataMemory p I.calldata mem src ptr) = ⟨0⟩ :=
    (hpres.load ⟨96⟩ (by decide) (by change 128 ≤ ptr; omega)
      (by change 128 ≤ mem.size; omega)).trans hz
  have hm₂ : 128 ≤ (execDataMemory p I.calldata mem src ptr).size :=
    hm.trans hpres.size
  have hptr₂ : ptr₂ < 2 ^ 220 := by
    dsimp [ptr₂, ABI.paddedSize]; omega
  have hp₂ : 128 ≤ ptr₂ := by dsimp [ptr₂]; omega
  obtain ⟨hr, hsource⟩ | ⟨hr, hsource⟩ |
      ⟨paid, called, evm₅, σ₅, mem₅, ptr₅, out₅, aw₅, k₅, C₅, prefix₅, he₅, ha₅, hw₅,
        h₅, hf₅, _, hp₅, hb₅, hm₅⟩ :=
    safeExecTransactionPayment p evm₂ h₄ he₂ ha₂ hw₂ hl₃ hu₃ hf₂ hm₂ hp₂ hz₂ hptr₂
      (by simp; omega)
  · exact .inl ⟨hr, prefix₁ _ (prefix₂ _ (prefix₃ _ (prefix₄ _ hsource)))⟩
  · exact .inr (.inl ⟨hr, prefix₁ _ (prefix₂ _ (prefix₃ _ (prefix₄ _ hsource)))⟩)
  let f₅ := execPaymentFinal f₃.locals paid called
  have hg₅ : f₅.locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)) :=
    (execPaymentFinal_get _ _ _ _ (by decide) (by decide)).trans hg₃
  have hh₅ : f₅.locals["txHash"]? = some (wordBytes32Value hash) :=
    (execPaymentFinal_get _ _ _ _ (by decide) (by decide)).trans hh₃
  have hz₅ : f₅.locals["success"]? = some (.bool z) :=
    (execPaymentFinal_get _ _ _ _ (by decide) (by decide)).trans hz₃
  have hpword : (UInt256.ofNat ptr₅).toNat = ptr₅ :=
    ulit_toNat' _ (by change ptr₅ < 2 ^ 256; omega)
  obtain ⟨hr, hsource⟩ | ⟨hr, hsource⟩ | ⟨f', evm', σ', hsource, he', ha', hw', hr⟩ :=
    safeExecTransactionFinish p evm₅ h₅ he₅ ha₅ hw₅ hg₅ hh₅ hz₅
      (execPaymentFinal_paid _ _ _) hf₅ (by omega) (by rw [hpword]; omega)
      (by rw [hpword]; change ptr₅ + 68 < 2 ^ 256; omega) (by omega)
  · exact .inl ⟨hr, prefix₁ _ (prefix₂ _ (prefix₃ _ (prefix₄ _ (prefix₅ _ hsource))))⟩
  · exact .inr (.inl ⟨hr,
      prefix₁ _ (prefix₂ _ (prefix₃ _ (prefix₄ _ (prefix₅ _ hsource))))⟩)
  · exact .inr (.inr ⟨f', evm', σ', z,
      prefix₁ _ (prefix₂ _ (prefix₃ _ (prefix₄ _ (prefix₅ _ hsource)))), he', ha', hw', hr⟩)

end Benchmarks.Safe
