import Benchmarks.Safe.V3_77901a5.SignatureP256BranchSource
import Benchmarks.Safe.V3_77901a5.SignatureP256Bounds
import Benchmarks.Safe.V3_77901a5.SignatureP256Memory
import Benchmarks.Safe.V3_77901a5.SignatureBranchResult
import Benchmarks.Safe.V3_77901a5.P256Trace
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_015
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_016
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_030

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V3_77901a5.RuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem safeSignatureP256Reject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2365⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_2365_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_2371 (by
    simp only [safeRuntime_block_2365_fallthrough_stack]; omega) (by jump_dest) h₁
  exact safeRuntime_block_6898 (by
    simp only [safeRuntime_block_2371_stack, safeRuntime_block_2365_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safeSignatureP256Trace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src i} {s r current last executor : UInt256}
    {R : List UInt256} {f : Frame} {old : Value}
    (h : RD fork safeBytecode I g s0 ⟨2218⟩
      (UInt256.ofNat i :: s :: r :: ⟨2⟩ :: current :: last :: p.required :: UInt256.ofNat src ::
        p.hash :: executor :: R) mem aw rdata σ k C)
    (hc : SignatureContext p f i last)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hn : p.signatures.size < 2 ^ 64) (hreq : p.requiredBytes ≤ p.signatures.size)
    (hov : R.length + 43 ≤ 1024) :
    SignatureBranchResult fork p I g s0 f evm i last executor src ptr mem R signatureP256Body := by
  have hsize : p.signatures.size < UInt256.size := lt_trans hn (by decide)
  have hbound : src + 64 + p.signatures.size < UInt256.size := by
    change src + 64 + p.signatures.size < 2 ^ 256
    omega
  obtain ⟨hrev, hbad⟩ | ⟨aw₁, k₁, C₁, hl, hh, h₁⟩ :=
    safeSignatureP256Bounds p h hm hsize hreq (by simp; omega)
  · exact .inl ⟨hrev, signatureP256BoundsFailed hc.toSignatureCore hr hs ho hbad⟩
  let input := signatureP256Input p s
  have hhash := signatureP256Hash hm hh hbound
  have hword := signatureP256Word hm hh hbound
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide +kernel
  by_cases hsign : UInt256.land solcAddrMask r = UInt256.land solcAddrMask (p256SignerWord input)
  swap
  · have heq : UInt256.eq (UInt256.land (p256SignerWord input) solcAddrMask)
        (UInt256.land solcAddrMask r) = ⟨0⟩ :=
      u256_eq_of_ne (by rw [u256_land_comm]; exact Ne.symm hsign)
    simp only [input] at heq
    obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_2293_taken_packed (by simp; omega)
      (by rw [hhash, hmask, heq]; decide) (by jump_dest) h₁
    simp only [safeRuntime_block_2293_taken_stack, hhash, hmask, heq] at h₂
    exact .inl ⟨safeSignatureP256Reject h₂ (by simp; omega),
      signatureP256SignerRejected hc.toSignatureCore hr hs ho hl hh hsize hsign⟩
  have heq : UInt256.eq (UInt256.land (p256SignerWord input) solcAddrMask)
      (UInt256.land solcAddrMask r) = ⟨1⟩ := by
    rw [u256_land_comm, ← hsign]
    exact u256_eq_refl _
  simp only [input] at heq
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_2293_fallthrough_packed (by simp; omega)
    (by rw [hhash, hmask, heq]; decide) h₁
  simp only [safeRuntime_block_2293_fallthrough_stack, hhash, hmask, heq,
    hword 0 (by decide), hword 32 (by decide), hword 64 (by decide), hword 96 (by decide)] at h₂
  have h₃ := safeRuntime_block_2350 (by simp; omega) (by jump_dest) h₂
  obtain ⟨evm', σ', out, z, aw₄, k₄, C₄, hbody, hee', hacc', hw', h₄⟩ :=
    safeP256Trace input evm h₃ hee hacc hworld hf
      (by change ptr + 160 < 2 ^ 256; omega) (by simp; omega) (by jump_dest)
  have hsource := signatureP256Source hc.toSignatureCore hr hs ho hl hh hsize hsign hbody
  have h₅ := safeRuntime_block_2363 (by simp; omega) h₄
  cases hvalid : p256Result z out
  · rw [hvalid] at hsource h₅
    exact .inl ⟨safeSignatureP256Reject h₅ (by simp; omega), hsource⟩
  · rw [hvalid] at hsource h₅
    have h₆ := safeRuntime_block_2365_taken (by simp; omega) (by decide) (by jump_dest) h₅
    have h₇ := safeRuntime_block_2387 (by simp; omega) (by jump_dest) h₆
    refine .inr ⟨signatureP256FinalFrame p f r s, evm', σ',
      p256OutputMemory mem ptr input out, ptr, _, out, input.s, input.r, ⟨2⟩, r, _, _,
      hsource, (hc.p256Decoded r s).set _ _ (by decide), ?_, hee', hacc', hw', h₇, ?_, ?_, ?_,
      le_refl _, by omega, ?_, ?_⟩
    · simp [signatureP256FinalFrame, signatureP256Frame, signatureP256SignerFrame,
        signatureP256ReadFrame, signatureP256EndFrame, signatureP256OffsetFrame,
        signatureDynamicFrame, signatureCurrentFrame, signatureSet,
        Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
    · exact p256OutputMemory_bytes hm out input (by omega) (by omega) ha
    · rw [p256OutputMemory_free _ _ _ _ (by have := hm.available; omega) (by omega), hf]
    · rw [p256OutputMemory_zero _ _ _ _ (by have := hm.available; omega) (by omega), hz]
    · rw [p256OutputMemory_size]; omega
    · exact ⟨(p256OutputMemory_preserves mem out ptr input).size,
        fun off count hlo hhi hin ↦ (p256OutputMemory_preserves mem out ptr input).read
          off count (by omega) hhi hin⟩

end Benchmarks.Safe.V3_77901a5
