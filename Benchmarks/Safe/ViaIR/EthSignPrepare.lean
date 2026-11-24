import Benchmarks.Safe.ViaIR.EthSignMemory
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034
import Benchmarks.Safe.ViaIR.Blocks.Runtime_040

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

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
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hb : ptr + 92 < UInt256.size) :
    safeRuntime_block_8539_memory (mem := mem) (x5 := hash) =
      writeWord (ethSignPayloadMemory mem ptr hash) ptr ⟨60⟩ := by
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_8539_memory, hf, ethSignPayloadAddresses hb,
    ulit_toNat' ptr (by omega)]
  rfl

theorem safeEthSignPrepare {I g s0 σ k C aw mem rdata ptr}
    {s r v last src hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8539⟩ (r :: s :: v :: last :: src :: hash :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hp : 96 ≤ ptr)
    (hb : ptr + 96 < UInt256.size) (hv : 4 ≤ v.toNat) (hov : R.length + 17 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨8619⟩
      (UInt256.sub v ⟨4⟩ :: r :: s :: ethSignWord hash :: last :: src :: hash :: R)
      (ethSignMemory mem ptr hash) aw' rdata σ k' C' ∧ ptr + 96 < 2 ^ 64 := by
  have hadd (j : Nat) (hj : j ≤ 96) :
      UInt256.ofNat ptr + UInt256.ofNat j = UInt256.ofNat (ptr + j) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    exact uadd_ofNat_toNat (by omega) (by omega) (by omega)
  have hr : UInt256.land (UInt256.ofNat 92 + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31)) = UInt256.ofNat 96 := by decide +kernel
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hl : UInt256.lt (UInt256.ofNat (ptr + 96)) (UInt256.ofNat ptr) = ⟨0⟩ :=
    ult_zero (by rw [ulit_toNat' _ hb, ulit_toNat' _ (by omega)]; omega)
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_8539_packed (by omega) (by jump_dest) h
  rw [safeEthSignMemory hf (by omega)] at h₁
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_8539_stack, hf, hadd 32 (by decide)] at h₁
  by_cases halloc : ptr + 96 < 2 ^ 64
  swap
  · have hg : UInt256.gt (UInt256.ofNat (ptr + 96)) (UInt256.ofNat (2 ^ 64 - 1)) =
        ⟨1⟩ := ugt_one (by
          rw [ulit_toNat' _ hb, ulit_toNat' _ (by change _ < 2 ^ 256; omega)]; omega)
    have h₂ := safeRuntime_block_7128_taken (by simp; omega)
      (by rw [hr, hadd 96 (by decide), hmax, hg, hl]; decide) (by jump_dest) h₁
    exact .inl (safeRuntime_block_7161 (by
      simp [safeRuntime_block_7128_taken_stack]; omega) h₂)
  have hg : UInt256.gt (UInt256.ofNat (ptr + 96)) (UInt256.ofNat (2 ^ 64 - 1)) =
      ⟨0⟩ := ugt_zero (by
        rw [ulit_toNat' _ hb, ulit_toNat' _ (by change _ < 2 ^ 256; omega)]; omega)
  have h₂ := safeRuntime_block_7128_fallthrough (by simp; omega)
    (by rw [hr, hadd 96 (by decide), hmax, hg, hl]; rfl) h₁
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_7157_packed (by simp; omega)
    (by jump_dest) h₂
  simp only [safeRuntime_block_7157_memory, safeRuntime_block_7157_stack] at h₃
  rw [hr, hadd 96 (by decide)] at h₃
  change RD fork safeBytecode I g s0 ⟨8602⟩
    (UInt256.ofNat ptr :: UInt256.ofNat (ptr + 32) :: r :: s :: v :: last :: src :: hash :: R)
    (ethSignMemory mem ptr hash) aw₃ rdata σ k₃ C₃ at h₃
  have hvword : UInt256.ofNat v.toNat = v := by
    apply u256_inj
    exact ulit_toNat' _ v.val.isLt
  have hsub : v + UInt256.lnot (UInt256.ofNat 3) = UInt256.sub v ⟨4⟩ := by
    rw [u256_add_comm]
    have hh := safeIRArgumentSizeSub hv v.val.isLt
    rwa [hvword] at hh
  have hgt : UInt256.gt (UInt256.sub v ⟨4⟩) v = ⟨0⟩ :=
    ugt_zero (by rw [usub_toNat (a := v) (b := ⟨4⟩) hv]; omega)
  obtain ⟨aw', k', C', h₄⟩ := safeRuntime_block_8602_fallthrough_packed (by simp; omega)
    (by rw [hsub]; exact hgt) h₃
  have hhash : keccakWord (UInt256.ofNat (ptr + 32)) ⟨60⟩ (ethSignMemory mem ptr hash) =
      ethSignWord hash := by
    simp only [keccakWord, ethSignWord, uInt256OfByteArray_eq]
    rw [ulit_toNat' _ (by omega), show (⟨60⟩ : UInt256).toNat = 60 from rfl,
      ethSignMemory_read _ _ _ hp]
  simp only [safeRuntime_block_8602_fallthrough_stack, hsub,
    ethSignMemory_length _ _ _ hp (by omega), hhash] at h₄
  exact .inr ⟨aw', k', C', h₄, halloc⟩

end Benchmarks.Safe.ViaIR
