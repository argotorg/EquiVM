import Benchmarks.Safe.SetupCalldataFacts
import Benchmarks.Safe.CalldataDecodeArithmetic
import Benchmarks.Safe.Blocks.Runtime_045
import Benchmarks.Safe.Blocks.Runtime_046

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def setupDecodeZeros (cd : ByteArray) (ret : UInt256) (R : List UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
    ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def setupDecodeOwnersStack (cd : ByteArray) (n : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  UInt256.ofNat n :: UInt256.ofNat (4 + (calldataWord cd 4).toNat) ::
    setupDecodeZeros cd ret R

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem safeSetupDecodeOwnersValid {I g s0 σ k C aw mem rdata n} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10399⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hh : 260 ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (ho : (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = UInt256.ofNat n)
    (hn : n ≤ 2 ^ 64 - 1) (hin : setupOwnersStart I.calldata + 32 * n ≤ I.calldata.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨10503⟩ (setupDecodeOwnersStack I.calldata n ret R)
      mem aw rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hsize : I.calldata.size < UInt256.size := by omega
  have h₁ := safeRuntime_block_10399_taken (by simp; omega) (by
    rw [solcDecodeLenCheckOk (by exact hh) (by omega) hsize (by decide)]
    decide) (by jump_dest) h
  simp only [safeRuntime_block_10399_taken_stack] at h₁
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₂ := safeRuntime_block_10425_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 4) _) ≠ _
    rw [hmax, ugt_zero ho]; decide) (by jump_dest) h₁
  have hoff : (⟨4⟩ : UInt256) + calldataWord I.calldata 4 =
      UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 4).toNat (by omega)
  have h₃ := safeRuntime_block_10446_taken (by simp; omega) (by
    change UInt256.sgt (UInt256.ofNat I.calldata.size)
      ((⟨4⟩ + calldataWord I.calldata 4) + UInt256.ofNat 31) ≠ _
    rw [hoff, wordOfNatAdd _ 31 (by omega)]
    rw [wordSgtReverse,
      slt_ofNat_lit_one_low hs (by dsimp only [setupOwnersStart] at hin; omega)]
    decide) (by jump_dest) h₂
  change RD safeBytecode I g s0 ⟨10462⟩
    ((⟨4⟩ + calldataWord I.calldata 4) :: setupDecodeZeros I.calldata ret R)
    mem aw rdata σ _ _ at h₃
  rw [hoff] at h₃
  have hoNat : (UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat)).toNat =
      4 + (calldataWord I.calldata 4).toNat := ulit_toNat' _ (by omega)
  have hnNat : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (by omega)
  have h₄ := safeRuntime_block_10462_taken (by simp [setupDecodeZeros]; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata _) _) ≠ _
    rw [hoNat, hw, hmax, ugt_zero (by rw [hnNat]; exact hn)]
    decide) (by jump_dest) h₃
  change RD safeBytecode I g s0 ⟨10483⟩
    (calldataWord I.calldata (UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat)).toNat ::
      UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat) ::
      setupDecodeZeros I.calldata ret R) mem aw rdata σ _ _ at h₄
  rw [hoNat, hw] at h₄
  have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * n) := shiftLeft5_ofNat_eq (by omega)
  have h₅ := safeRuntime_block_10483_taken (by simp; omega) (by
    rw [hshift, wordOfNatAdd _ _ (by omega), wordOfNatAdd _ 32 (by omega), ugt_zero (by
      rw [ulit_toNat' _ (by omega), ulit_toNat' _ hsize]
      dsimp only [setupOwnersStart] at hin
      omega)]
    decide) (by jump_dest) h₄
  exact ⟨_, _, h₅⟩

end Benchmarks.Safe
