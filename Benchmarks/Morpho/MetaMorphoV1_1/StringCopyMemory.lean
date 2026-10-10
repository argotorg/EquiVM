import Benchmarks.Morpho.MetaMorphoV1_1.StringCopyLoop
import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageSource
import Benchmarks.Morpho.MetaMorphoV1_1.StringAllocation

/-! Memory layouts produced by copying a short or long storage string. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def shortStringDataWord (header : UInt256) : UInt256 :=
  UInt256.land (UInt256.lnot ⟨255⟩) header

def shortStringCopyMemory (mem : ByteArray) (header len : UInt256) : ByteArray :=
  writeWord (writeWord mem 128 len) 160 (shortStringDataWord header)

def longStringCopyMemory (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base len : UInt256) : ByteArray :=
  wordSequenceMemory (writeWord (writeWord mem 128 len) 0 base) 160
    (stringStorageWords I σ (solidityBytesDataBaseSlot base) (stringWordCount len))

def stringCopyMemory (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (base header len : UInt256) : ByteArray :=
  if UInt256.land header ⟨1⟩ = ⟨0⟩ then shortStringCopyMemory mem header len
  else longStringCopyMemory I σ mem base len

def stringAllocationStack (len : UInt256) (R : List UInt256) : List UInt256 :=
  [⟨128⟩, stringCopySize len, ⟨2379⟩, ⟨128⟩, ⟨4335⟩, ⟨2379⟩,
    stringCopyEnd len, ⟨128⟩] ++ R

theorem shortStringEnd (len : UInt256) (hlen : len.toNat < 32) :
    (UInt256.ofNat 32) + ((UInt256.ofNat 128) +
      UInt256.shiftLeft (UInt256.isZero (UInt256.isZero len)) (UInt256.ofNat 5)) =
      stringCopyEnd len := by
  by_cases hz : len = ⟨0⟩
  · subst len
    rfl
  · have hn : len.toNat ≠ 0 := fun h ↦ hz (uint256_toNat_eq_zero h)
    have hc : stringWordCount len = 1 := by unfold stringWordCount; omega
    rw [isZero_eq_zero_of_ne hz, stringCopyEnd, hc]
    rfl

theorem stringStorageWords_bytes (evm : State) (base : UInt256) (idx n : Nat) :
    wordBytes (stringStorageWords evm.executionEnv evm.accountMap
      (solidityBytesDataSlot base idx) n) = readSolidityBytesDataWordsFrom evm base idx n := by
  induction n generalizing idx with
  | zero => rfl
  | succ n ih =>
      rw [stringStorageWords, wordBytes, readSolidityBytesDataWordsFrom]
      have hk : solidityBytesDataSlot base idx + ⟨1⟩ =
          solidityBytesDataSlot base (idx + 1) := by
        unfold solidityBytesDataSlot
        rw [u256_add_assoc]
        change _ + (UInt256.ofNat idx + UInt256.ofNat 1) = _
        rw [ofNat_add_words]
      rw [hk, ih]
      rfl

theorem shortStringDataWord_toNat (header : UInt256) :
    (shortStringDataWord header).toNat = header.toNat / 256 * 256 := by
  rw [shortStringDataWord, u256_land_comm, uland_toNat]
  change Nat.land header.toNat (2 ^ 256 - 2 ^ 8) = _
  exact natLandClearLow header.toNat 8 (by decide) header.val.isLt

theorem shortStringDataWord_prefix (header : UInt256) (len : Nat) (hlen : len ≤ 31) :
    (shortStringDataWord header).toByteArray.extract 0 len = header.toByteArray.extract 0 len := by
  apply byteArray_eq_of_toList_eq
  apply fromBytesBigEndian_inj_of_length
  · simp only [byteArray_toList_eq, Array.length_toList]
    change ((shortStringDataWord header).toByteArray.extract 0 len).size =
      (header.toByteArray.extract 0 len).size
    simp only [ByteArray.size_extract, toByteArray_size]
  · rw [bytesBE_extract_high _ _ (by omega), bytesBE_extract_high _ _ (by omega),
      shortStringDataWord_toNat]
    have he : (2 : Nat) ^ (8 * (32 - len)) = 256 * 2 ^ (8 * (32 - len) - 8) := by
      change 2 ^ (8 * (32 - len)) = 2 ^ 8 * 2 ^ (8 * (32 - len) - 8)
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [he, Nat.mul_comm (header.toNat / 256) 256,
      Nat.mul_div_mul_left _ _ (by decide : 0 < 256), ← Nat.div_div_eq_div_mul]

end Benchmarks.Morpho.MetaMorphoV1_1
