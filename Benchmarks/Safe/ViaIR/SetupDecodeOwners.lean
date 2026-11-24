import Benchmarks.Safe.ViaIR.SetupCalldataFacts
import Benchmarks.Safe.ViaIR.CalldataDecodeArithmetic
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_015
import Benchmarks.Safe.ViaIR.Blocks.Runtime_018

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def setupDecodeOwnersStack (cd : ByteArray) (n : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat (setupOwnersStart cd + 32 * n), UInt256.ofNat (setupOwnersStart cd),
    UInt256.ofNat n] ++ R

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

theorem safeSetupDecodeOwnersValid {I g s0 σ k C aw mem rdata n} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2980⟩ R mem aw rdata σ k C)
    (hh : 260 ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (ho : (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = UInt256.ofNat n)
    (hn : n ≤ 2 ^ 64 - 1) (hin : setupOwnersStart I.calldata + 32 * n ≤ I.calldata.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨3060⟩ (setupDecodeOwnersStack I.calldata n R)
      mem aw rdata σ k' C' := by
  have hu : UInt256.size = 2 ^ 256 := rfl
  have hsize : I.calldata.size < UInt256.size := by omega
  have hmax : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide +kernel
  have hmaxWord : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hnNat : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (by omega)
  have hoff (a : Nat) (hb : (calldataWord I.calldata 4).toNat + a < UInt256.size) :
      calldataWord I.calldata 4 + UInt256.ofNat a =
        UInt256.ofNat ((calldataWord I.calldata 4).toNat + a) := by
    conv_lhs => lhs; rw [← u256_ofNat_toNat (calldataWord I.calldata 4)]
    exact wordOfNatAdd _ _ hb
  have h₁ := safeRuntime_block_2980_fallthrough (by omega) (by
    rw [safeIRArgumentSizeSub (by omega) hsize,
      solcDecodeLenCheckOk hh (by omega) hsize (by decide)]
    rfl) h
  have h₂ := safeRuntime_block_2993_fallthrough (by omega) (by
    rw [hmaxWord]
    change UInt256.gt (calldataWord I.calldata 4) (UInt256.ofNat (2 ^ 64 - 1)) = _
    exact ugt_zero (by rwa [hmax])) h₁
  change RD fork safeBytecode I g s0 ⟨3010⟩ (calldataWord I.calldata 4 :: R)
    mem aw rdata σ _ _ at h₂
  have h₃ := safeRuntime_block_3010_fallthrough (by omega) (by
    rw [hoff 35 (by omega), slt_ofNat_lit_one_low hs (by
      dsimp only [setupOwnersStart] at hin; omega)]
    rfl) h₂
  have ho4 : ((UInt256.ofNat 4) + calldataWord I.calldata 4).toNat =
      4 + (calldataWord I.calldata 4).toNat := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by change 4 + _ < 2 ^ 256; omega)
  have h₄ := safeRuntime_block_3021_fallthrough (by omega) (by
    rw [hmaxWord]
    change UInt256.gt (calldataWord I.calldata _) (UInt256.ofNat (2 ^ 64 - 1)) = _
    rw [ho4, hw]
    exact ugt_zero (by rwa [hnNat, hmax])) h₃
  change RD fork safeBytecode I g s0 ⟨3041⟩
    (calldataWord I.calldata 4 :: calldataWord I.calldata _ :: R)
    mem aw rdata σ _ _ at h₄
  rw [ho4, hw] at h₄
  have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * n) := shiftLeft5_ofNat_eq (by omega)
  have hend : (UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) +
      calldataWord I.calldata 4) + UInt256.ofNat 36 =
      UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) := by
    rw [hshift, u256_add_comm (UInt256.ofNat (32 * n)), hoff (32 * n) (by omega),
      wordOfNatAdd _ 36 (by omega)]
    apply congrArg UInt256.ofNat
    dsimp only [setupOwnersStart]
    omega
  have h₅ := safeRuntime_block_3041_fallthrough (by omega) (by
    rw [hend]
    exact ugt_zero (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hsize]; exact hin)) h₄
  have hstart : calldataWord I.calldata 4 + UInt256.ofNat 36 =
      UInt256.ofNat (setupOwnersStart I.calldata) := by
    rw [hoff 36 (by omega)]
    apply congrArg UInt256.ofNat
    dsimp only [setupOwnersStart]
    omega
  simp only [safeRuntime_block_3041_fallthrough_stack, hend, hstart] at h₅
  exact ⟨_, _, h₅⟩

end Benchmarks.Safe.ViaIR
