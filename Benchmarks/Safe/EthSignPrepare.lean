import Benchmarks.Safe.EthSignMemory
import Benchmarks.Safe.CheckedSubtract
import Benchmarks.Safe.Blocks.Runtime_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem ethSignPayloadAddresses {mem : ByteArray} {ptr : Nat} {hash : UInt256}
    (hb : ptr + 92 < UInt256.size) :
    hash.toByteArray.write 0
      ((UInt256.ofNat
        11430537079145650693387304458692941425836787954612963690241153482819318579200
          ).toByteArray.write
          0 mem (UInt256.ofNat ptr + UInt256.ofNat 32).toNat 32)
      (UInt256.ofNat ptr + UInt256.ofNat 60).toNat 32 = ethSignPayloadMemory mem ptr hash := by
  have hadd (j : Nat) (hj : j ≤ 92) :
      (UInt256.ofNat ptr + UInt256.ofNat j).toNat = ptr + j :=
    uadd_ofNat_toNat (by omega) (by omega) (by omega)
  rw [hadd 32 (by decide), hadd 60 (by decide)]
  rfl

theorem safeEthSignMemory {mem : ByteArray} {ptr : Nat} {hash : UInt256}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hb : ptr + 92 < UInt256.size) :
    safeRuntime_block_2405_memory (mem := mem) (x8 := hash) = ethSignMemory mem ptr hash := by
  have hadd (j : Nat) (hj : j ≤ 92) :
      UInt256.ofNat ptr + UInt256.ofNat j = UInt256.ofNat (ptr + j) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    exact uadd_ofNat_toNat (by omega) (by omega) (by omega)
  have h92 : UInt256.ofNat 92 + UInt256.ofNat ptr = UInt256.ofNat (ptr + 92) := by
    rw [u256_add_comm]; exact hadd 92 (by omega)
  have hpay := ethSignPayloadAddresses (mem := mem) (hash := hash) hb
  have hfree := ethSignPayloadMemory_free (hash := hash) hm hp hf
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  change memLoad (UInt256.ofNat 64) _ = UInt256.ofNat ptr at hfree
  have hlen : UInt256.sub (UInt256.sub (UInt256.ofNat (ptr + 92)) (UInt256.ofNat ptr))
      (UInt256.ofNat 32) = ⟨60⟩ := by
    apply u256_inj
    have he : UInt256.sub (UInt256.ofNat (ptr + 92)) (UInt256.ofNat ptr) = ⟨92⟩ := by
      apply u256_inj
      rw [usub_ofNat_lit_toNat (by omega) hb]
      change ptr + 92 - ptr = 92
      omega
    rw [he]
    rfl
  simp only [safeRuntime_block_2405_memory, hf]
  change (UInt256.ofNat 92 + UInt256.ofNat ptr).toByteArray.write 0
    ((UInt256.sub (UInt256.sub (UInt256.ofNat 92 + UInt256.ofNat ptr)
      (memLoad (UInt256.ofNat 64) _)) (UInt256.ofNat 32)).toByteArray.write 0 _
        (memLoad (UInt256.ofNat 64) _).toNat 32) (UInt256.ofNat 64).toNat 32 = _
  rw [hpay, hfree, h92, hlen, ulit_toNat' ptr (by omega)]
  rfl

theorem safeEthSignPrepare {I g s0 σ k C aw mem rdata ptr}
    {i s r v current last required src hash : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2405⟩
      (i :: s :: r :: v :: current :: last :: required :: src :: hash :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hb : ptr + 92 < UInt256.size) (hv : 4 ≤ v.toNat) (hov : R.length + 17 ≤ 1024) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨2493⟩
      (UInt256.sub v ⟨4⟩ :: ethSignWord hash :: ⟨1⟩ :: i :: s :: r :: v :: current :: last ::
        required :: src :: hash :: R) (ethSignMemory mem ptr hash) aw' rdata σ k' C' := by
  have hpay := ethSignPayloadAddresses (mem := mem) (hash := hash) hb
  have hfree := ethSignPayloadMemory_free (hash := hash) hm hp hf
  have hmemory := safeEthSignMemory (hash := hash) hf hm hp hb
  have hlength := ethSignMemory_length mem ptr hash hp (by omega)
  have h32 : UInt256.ofNat 32 + UInt256.ofNat ptr = UInt256.ofNat (ptr + 32) :=
    u256_32_add_ofNat ptr
  have hhash : keccakWord (UInt256.ofNat (ptr + 32)) ⟨60⟩ (ethSignMemory mem ptr hash) =
      ethSignWord hash := by
    simp only [keccakWord, ethSignWord, uInt256OfByteArray_eq]
    rw [ulit_toNat' _ (by omega), show (⟨60⟩ : UInt256).toNat = 60 from rfl,
      ethSignMemory_read _ _ _ hp]
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_2405_packed (by omega) (by jump_dest) h
  simp only [safeRuntime_block_2405_stack] at h₁
  rw [← safeRuntime_block_2405_memory, hmemory] at h₁
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  change memLoad (UInt256.ofNat 64) _ = UInt256.ofNat ptr at hfree
  rw [hf, hpay, hfree, hlength, h32, hhash] at h₁
  obtain ⟨k', C', h₂⟩ := safeSubtractTrace h₁ (by simp; omega) hv (by jump_dest)
  exact ⟨aw₁, k', C', h₂⟩

end Benchmarks.Safe
