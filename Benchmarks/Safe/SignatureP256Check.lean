import Benchmarks.Safe.SignatureP256Source
import Benchmarks.Safe.SignatureP256Memory
import Benchmarks.Safe.P256Trace
import Benchmarks.Safe.MemoryPreserves
import Benchmarks.Safe.Blocks.Runtime_015
import Benchmarks.Safe.Blocks.Runtime_016
import Benchmarks.Safe.Blocks.Runtime_030

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSignatureP256Reject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2365⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_2365_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_2371
    (by simp only [safeRuntime_block_2365_fallthrough_stack]; omega) (by jump_dest) h₁
  exact safeRuntime_block_6898 (by
    simp only [safeRuntime_block_2371_stack, safeRuntime_block_2365_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safeSignatureP256Check (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {i off oldR v owner last : UInt256}
    {R : List UInt256} {f : Frame}
    (h : RD safeBytecode I g s0 ⟨2293⟩
      (i :: off :: oldR :: v :: owner :: last :: p.required :: UInt256.ofNat src :: p.hash :: R)
      mem aw rdata σ k C)
    (hc : SignatureCore p f) (hoff : f.locals["p256Offset"]? = some (uint256Value off))
    (ho : f.locals["currentOwner"]? = some (.address (AccountAddress.ofUInt256 owner)))
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 224)
    (hbound : off.toNat + 128 ≤ p.signatures.size) (hov : R.length + 26 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config f evm (signatureP256Body.drop 5) .reverted) ∨
    ∃ evm' σ' mem' aw' out k' C',
      ExecBlock config f evm (signatureP256Body.drop 5)
        (.ok (signatureSet (signatureP256SignerFrame f (signatureP256Input p off))
          "p256Ok" (.bool true)) evm') ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨2679⟩
        (i :: (signatureP256Input p off).s :: (signatureP256Input p off).r :: v :: owner :: last ::
          p.required :: UInt256.ofNat src :: p.hash :: R) mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ mem'.size ≤ max mem.size (ptr + 2 ^ 140) ∧
      MemoryPreserves mem mem' 96 ptr := by
  have hptr : 128 ≤ ptr := by omega
  have hmem : 128 ≤ mem.size := by have := hm.available; omega
  have hb : ptr + 160 < UInt256.size := by change _ < 2 ^ 256; omega
  obtain ⟨hr, hs, hx, hy, hh⟩ := signatureP256Reads hm hbound (by omega)
  by_cases hv : signatureP256Valid owner (signatureP256Input p off)
  swap
  · have heq : UInt256.eq
        (UInt256.land (signatureP256Signer (signatureP256Input p off)) solcAddrMask)
        (UInt256.land solcAddrMask owner) = ⟨0⟩ := by
      apply u256_eq_of_ne
      rw [u256_land_comm]
      exact Ne.symm hv
    have h₁ := safeRuntime_block_2293_taken (by simp; omega)
      (by rw [safeAddressMask, hh, heq]; decide) (by jump_dest) h
    simp only [safeRuntime_block_2293_taken_stack, safeAddressMask, hh, heq] at h₁
    exact .inl ⟨safeSignatureP256Reject h₁ (by simp; omega),
      signatureP256SourceSignerFailed hc hoff ho hbound hv⟩
  have heq : UInt256.eq
      (UInt256.land (signatureP256Signer (signatureP256Input p off)) solcAddrMask)
      (UInt256.land solcAddrMask owner) = ⟨1⟩ := by
    rw [u256_land_comm, ← hv]
    exact uInt256_eq_self _
  have h₁ := safeRuntime_block_2293_fallthrough (by simp; omega)
    (by rw [safeAddressMask, hh, heq]; decide) h
  simp only [safeRuntime_block_2293_fallthrough_stack, safeAddressMask, hh, heq, hr, hs, hx, hy]
    at h₁
  have h₂ := safeRuntime_block_2350 (by omega) (by jump_dest) h₁
  obtain ⟨evm', σ', z, out, aw', k', C', hcall, he, hac, hw, h₃⟩ :=
    safeP256Trace (p := signatureP256Input p off) evm h₂ hee hacc hworld hf hb
      (by simp; omega) (by jump_dest)
  have hsource := signatureP256SourceVerified hc hoff ho hbound hv hcall
  have h₄ := safeRuntime_block_2363 (by simp; omega) h₃
  simp only [safeRuntime_block_2363_stack] at h₄
  cases hzout : p256Result z out with
  | false =>
      rw [hzout] at h₄
      exact .inl ⟨safeSignatureP256Reject h₄ (by simp; omega), by
        simpa only [hzout, Bool.false_eq_true, if_false] using hsource⟩
  | true =>
      rw [hzout] at h₄
      have h₅ := safeRuntime_block_2365_taken (by simp; omega) (by decide) (by jump_dest) h₄
      obtain ⟨aw'', k'', C'', h₆⟩ := safeRuntime_block_2387_packed (by simp; omega)
        (by jump_dest) h₅
      refine .inr ⟨evm', σ', _, aw'', out, k'', C'', ?_, he, hac, hw, h₆, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hzout, if_true] using hsource
      · exact p256OutputMemory_bytes hm (by omega) ha (by omega)
      · exact (p256OutputMemory_free (by omega) (by omega)).trans hf
      · exact p256OutputMemory_zeroSlot hmem hptr hz
      · rw [p256OutputMemory_size]
        omega
      · exact ⟨p256OutputMemory_lower _ _ _ _, fun off count hl hh hin ↦
          p256OutputMemory_readBelow _ _ _ _ _ _ hin (by omega) hh⟩

end Benchmarks.Safe
