import Examples.Precompiles.Modexp.WideWordBaseLoop
import Examples.Precompiles.Modexp.WordLoopBridge

/-!
# Trusted-model bridge for the arbitrary-base, one-word-modulus helper

The definitions in the execution files describe concrete stack values produced by the deployed
bytecode.  This file relates those values to the unchanged ModExp parser copied from
evm-semantics.  In particular, it does not introduce another specification of the operands.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem addMod_toNat {a b m : UInt256} (hm : m.toNat ≠ 0) :
    (UInt256.addMod a b m).toNat = (a.toNat + b.toNat) % m.toNat := by
  unfold UInt256.addMod UInt256.eq0
  rw [if_neg]
  . apply UInt256.toNat_ofNat_of_lt
    exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hm)) m.val.isLt.le
  . intro h
    have hm0 : m = ⟨0⟩ := beq_iff_eq.mp h
    subst m
    exact hm rfl

/-- In an already-active concrete memory window, `wideLoadWord` is just the EVM's big-endian
32-byte decoder. -/
theorem wideLoadWord_eq_decode {mem : ByteArray} {aw off : UInt256}
    (hmem : off.toNat < mem.size) (haw : ¬ off ≥ aw * ⟨32⟩) :
    wideLoadWord mem aw off =
      uInt256OfByteArray (mem.readWithPadding off.toNat 32) := by
  unfold wideLoadWord
  rw [if_neg (not_or.mpr (And.intro (by omega) haw))]
  exact (uInt256OfByteArray_eq _).symm

/-- The same decoding fact also covers a logically active word beyond the concrete byte-array
end: both the EVM read and `wideLoadWord` are then zero. -/
theorem wideLoadWord_eq_decode_bounded {mem : ByteArray} {aw off : UInt256}
    (haw : ¬ off ≥ aw * ⟨32⟩) :
    wideLoadWord mem aw off =
      uInt256OfByteArray (mem.readWithPadding off.toNat 32) := by
  by_cases hmem : off.toNat < mem.size
  · exact wideLoadWord_eq_decode hmem haw
  · have hpast : off.toNat ≥ mem.size := by omega
    unfold wideLoadWord
    rw [if_pos (Or.inl hpast)]
    rw [readWithPadding_past_end mem off.toNat 32 hpast (by decide)]
    rw [← zero_toByteArray_eq_zeroes32, uInt256OfByteArray_eq,
      fromByteArrayBigEndian_toByteArray]
    rfl

private theorem operandWordsBound32
    {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 32) :
    operandModulusWords baseSize exponentSize modulusSize < UInt256.size := by
  apply lt_of_le_of_lt
    (show operandModulusWords baseSize exponentSize modulusSize <= 72 by
      unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega)
  decide

theorem operandAddressBelowActive
    {baseSize exponentSize modulusSize addr : Nat}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 32)
    (haddr : addr + 32 <= 32 * operandModulusWords baseSize exponentSize modulusSize)
    (haddr256 : addr < UInt256.size) :
    ¬ UInt256.ofNat addr ≥
      operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩ := by
  intro h
  change (operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩).toNat ≤
    (UInt256.ofNat addr).toNat at h
  rw [umul_toNat, UInt256.toNat_ofNat_of_lt haddr256] at h
  . unfold operandModulusActiveWords at h
    rw [UInt256.toNat_ofNat_of_lt (operandWordsBound32 hb he hm)] at h
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide] at h
    omega
  . unfold operandModulusActiveWords
    rw [UInt256.toNat_ofNat_of_lt (operandWordsBound32 hb he hm)]
    norm_num
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize * 32 <= 2304 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
    decide

/-- Every full base word loaded by the helper is the corresponding 32-byte field of the trusted
zero-padded input parser. -/
theorem wideBaseChunk_toNat_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start : Nat)
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 32)
    (hwindow : start + 32 <= baseSize) :
    (wideLoadWord (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      (UInt256.ofNat (operandBasePtr + 32 + start))).toNat =
      Model.bytesToNatPadded I.calldata (96 + start) 32 := by
  let addr := operandBasePtr + 32 + start
  have haddr256 : addr < UInt256.size := by
    apply lt_of_le_of_lt
      (show addr <= 1184 by unfold addr operandBasePtr; omega)
    decide
  have hmem : (UInt256.ofNat addr).toNat <
      (operandCopiedMemory I baseSize exponentSize modulusSize).size := by
    rw [UInt256.toNat_ofNat_of_lt haddr256]
    have hs := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    unfold addr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at *
    omega
  have haw : ¬ UInt256.ofNat addr ≥
      operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩ := by
    apply operandAddressBelowActive hb he hm
    . unfold addr operandModulusWords operandExponentWords operandBaseWords operandBasePtr
        bytesAllocationWords
      omega
    . exact haddr256
  rw [show UInt256.ofNat (operandBasePtr + 32 + start) = UInt256.ofNat addr by rfl]
  rw [wideLoadWord_eq_decode hmem haw]
  have hread :
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding addr 32 =
      Model.readPadded I.calldata (96 + start) 32 := by
    exact operandCopiedBaseWindow I baseSize exponentSize modulusSize start 32 hb he hwindow
  rw [UInt256.toNat_ofNat_of_lt haddr256, hread]
  have hcd := calldataWord_toNat_eq_model I.calldata (96 + start) (by omega)
  rw [readBytes_eq_model_readPadded I.calldata (96 + start) 32 (by omega) (by decide)] at hcd
  exact hcd

/-- The modulus word assembled by the helper is exactly the trusted modulus operand whenever the
declared modulus length is at most one word. -/
theorem wideWordModulus_toNat_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32) :
    (wideWordModulus I baseSize exponentSize modulusSize).toNat =
      Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let addr := operandModulusPtr baseSize exponentSize + 32
  have haddr256 : addr < UInt256.size := by
    apply lt_of_le_of_lt
      (show addr ≤ 2272 by
        unfold addr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  have haddr64 : addr < 2 ^ 64 := by
    unfold addr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have haw : ¬ UInt256.ofNat addr ≥
      operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩ := by
    apply operandAddressBelowActive hb he hm
    · unfold addr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      have : 1 ≤ (modulusSize + 31) / 32 := by omega
      omega
    · exact haddr256
  have hload :
      wideLoadWord mem (operandModulusActiveWords baseSize exponentSize modulusSize)
          (UInt256.ofNat addr) =
        uInt256OfByteArray (mem.readBytes addr 32) := by
    rw [wideLoadWord_eq_decode_bounded haw]
    congr 1
    rw [UInt256.toNat_ofNat_of_lt haddr256,
      readWithPadding_eq_model_readPadded mem addr 32 haddr64 (by decide),
      readBytes_eq_model_readPadded mem addr 32 haddr64 (by decide)]
  have hopen := operandWord_toNat_eq_model mem addr (UInt256.ofNat modulusSize)
    haddr64 (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; exact hm)
  have hfield : Model.bytesToNatPadded mem addr modulusSize =
      Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize := by
    unfold Model.bytesToNatPadded
    have hwindow := operandCopiedModulusWindow I baseSize exponentSize modulusSize 0 modulusSize
      hb he (by omega) (by omega)
    have hmemRead : Model.readPadded mem addr modulusSize =
        mem.readWithPadding addr modulusSize := by
      symm
      exact readWithPadding_eq_model_readPadded mem addr modulusSize haddr64 (by omega)
    rw [hmemRead]
    exact congrArg Model.bytesToBigEndianNat (by simpa [addr] using hwindow)
  unfold wideWordModulus wideWordModulusAt
  rw [show UInt256.ofNat (operandModulusPtr baseSize exponentSize) + ⟨32⟩ =
      UInt256.ofNat addr by
    unfold addr
    simpa using (ofNat_add_bounded
      (a := operandModulusPtr baseSize exponentSize) (b := 32) haddr256)]
  rw [hload]
  have hsizeNat : (UInt256.ofNat modulusSize).toNat = modulusSize := by
    rw [UInt256.toNat_ofNat_of_lt (by omega)]
  rw [hsizeNat] at hopen
  exact hopen.trans hfield

/-- The bytecode expression used as the radix multiplier is `2^256 mod m`. -/
theorem wideR256_toNat (m : UInt256) (hm : 1 < m.toNat) :
    (wideR256 m).toNat = UInt256.size % m.toNat := by
  have hm0 : m.toNat ≠ 0 := by omega
  unfold wideR256
  rw [addMod_toNat hm0, umod_toNat hm0]
  rw [show (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 by
    unfold UInt256.lnot
    native_decide]
  change (((UInt256.size - 1) % m.toNat) + 1) % m.toNat = UInt256.size % m.toNat
  rw [Nat.mod_add_mod]
  rw [show UInt256.size - 1 + 1 = UInt256.size by
    have : 0 < UInt256.size := by decide
    omega]

/-- The optional leading partial base chunk is the corresponding trusted prefix, reduced by the
trusted modulus. -/
theorem widePartialBase_toNat_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hrem : baseSize % 32 ≠ 0)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize) :
    (widePartialBase I baseSize exponentSize modulusSize).toNat =
      Model.bytesToNatPadded I.calldata 96 (baseSize % 32) %
        Model.bytesToNatPadded I.calldata
          (96 + baseSize + exponentSize) modulusSize := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let rem := baseSize % 32
  let addr := operandBasePtr + 32
  have hremPos : 0 < rem := by unfold rem; omega
  have hremLe : rem ≤ baseSize := by
    unfold rem
    exact le_trans (Nat.mod_le _ _) (by omega)
  have haddr256 : addr < UInt256.size := by unfold addr operandBasePtr; decide
  have haddr64 : addr < 2 ^ 64 := by unfold addr operandBasePtr; decide
  have haw : ¬ UInt256.ofNat addr ≥
      operandModulusActiveWords baseSize exponentSize modulusSize * ⟨32⟩ := by
    apply operandAddressBelowActive hb he hm
    · unfold addr operandBasePtr operandModulusWords operandExponentWords operandBaseWords
        bytesAllocationWords
      have : 1 ≤ (baseSize + 31) / 32 := by omega
      omega
    · exact haddr256
  have hload :
      wideBaseFirstWord I baseSize exponentSize modulusSize =
        uInt256OfByteArray (mem.readBytes addr 32) := by
    unfold wideBaseFirstWord wideBaseFirstWordAt wideBaseDataPtr
    rw [show UInt256.ofNat operandBasePtr + ⟨32⟩ = UInt256.ofNat addr by
      unfold addr
      simpa using (ofNat_add_bounded (a := operandBasePtr) (b := 32) haddr256)]
    rw [wideLoadWord_eq_decode_bounded haw]
    congr 1
    change mem.readWithPadding (UInt256.ofNat addr).toNat 32 = mem.readBytes addr 32
    rw [UInt256.toNat_ofNat_of_lt haddr256]
    rw [readWithPadding_eq_model_readPadded mem addr 32 haddr64 (by decide),
      readBytes_eq_model_readPadded mem addr 32 haddr64 (by decide)]
  have hopen := operandWord_toNat_eq_model mem addr (UInt256.ofNat rem)
    haddr64 (by rw [UInt256.toNat_ofNat_of_lt (by unfold rem; omega)]; omega)
  have hfield : Model.bytesToNatPadded mem addr rem =
      Model.bytesToNatPadded I.calldata 96 rem := by
    unfold Model.bytesToNatPadded
    have hwindow := operandCopiedBaseWindow I baseSize exponentSize modulusSize 0 rem
      hb he (by omega)
    have hmemRead : Model.readPadded mem addr rem = mem.readWithPadding addr rem := by
      symm
      exact readWithPadding_eq_model_readPadded mem addr rem haddr64 (by omega)
    rw [hmemRead]
    exact congrArg Model.bytesToBigEndianNat (by simpa [addr] using hwindow)
  have hshift :
      (UInt256.shiftRight (wideBaseFirstWord I baseSize exponentSize modulusSize)
        (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (wideBaseRemainder baseSize)) ⟨3⟩)).toNat =
        Model.bytesToNatPadded I.calldata 96 rem := by
    unfold wideBaseRemainder
    rw [show UInt256.ofNat (baseSize % 32) = UInt256.ofNat rem by rfl, hload]
    have hremNat : (UInt256.ofNat rem).toNat = rem := by
      rw [UInt256.toNat_ofNat_of_lt (by unfold rem; omega)]
    rw [hremNat] at hopen
    exact hopen.trans hfield
  have hmodWord := wideWordModulus_toNat_eq_model I baseSize exponentSize modulusSize
    hb he hmodPos hm
  unfold widePartialBase widePartialBaseAt
  change (UInt256.mod
    (UInt256.shiftRight (wideBaseFirstWord I baseSize exponentSize modulusSize)
      (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (wideBaseRemainder baseSize)) ⟨3⟩))
    (wideWordModulus I baseSize exponentSize modulusSize)).toNat = _
  rw [umod_toNat (by rw [hmodWord]; omega), hshift, hmodWord]

/-- Folding full 32-byte base chunks appends precisely those bytes to the trusted big-endian
prefix and reduces after every append. -/
theorem wideBaseFold_toNat_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize n start : Nat) (baseAcc : UInt256)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hwindow : start + 32 * n ≤ baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hacc : baseAcc.toNat =
      Model.bytesToNatPadded I.calldata 96 start %
        Model.bytesToNatPadded I.calldata
          (96 + baseSize + exponentSize) modulusSize) :
    (wideBaseFold (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      (wideR256 (wideWordModulus I baseSize exponentSize modulusSize))
      (wideWordModulus I baseSize exponentSize modulusSize) n
      (operandBasePtr + 32 + start) baseAcc).toNat =
      Model.bytesToNatPadded I.calldata 96 (start + 32 * n) %
        Model.bytesToNatPadded I.calldata
          (96 + baseSize + exponentSize) modulusSize := by
  induction n generalizing start baseAcc with
  | zero =>
      simpa [wideBaseFold] using hacc
  | succ n ih =>
      let modulusNat := Model.bytesToNatPadded I.calldata
        (96 + baseSize + exponentSize) modulusSize
      let modulusWord := wideWordModulus I baseSize exponentSize modulusSize
      let r256 := wideR256 modulusWord
      let chunk := wideLoadWord
        (operandCopiedMemory I baseSize exponentSize modulusSize)
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandBasePtr + 32 + start))
      let nextAcc := UInt256.addMod (UInt256.mulMod baseAcc r256 modulusWord)
        chunk modulusWord
      have hmodWord : modulusWord.toNat = modulusNat := by
        exact wideWordModulus_toNat_eq_model I baseSize exponentSize modulusSize
          hb he hmodPos hm
      have hm0 : modulusWord.toNat ≠ 0 := by rw [hmodWord]; omega
      have hr256 : r256.toNat = UInt256.size % modulusNat := by
        unfold r256
        rw [wideR256_toNat modulusWord (by rw [hmodWord]; exact hmod), hmodWord]
      have hchunk : chunk.toNat = Model.bytesToNatPadded I.calldata (96 + start) 32 := by
        exact wideBaseChunk_toNat_eq_model I baseSize exponentSize modulusSize start
          hb he hm (by omega)
      have hnextAcc : nextAcc.toNat =
          Model.bytesToNatPadded I.calldata 96 (start + 32) % modulusNat := by
        unfold nextAcc
        rw [addMod_toNat hm0, mulMod_toNat hm0, hmodWord, hacc, hr256, hchunk]
        rw [show UInt256.size = 256 ^ 32 by native_decide]
        rw [model_bytesToNatPadded_split I.calldata 96 start 32]
        simp [modulusNat, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
      have hrec := ih (start := start + 32) (baseAcc := nextAcc)
        (by omega) hnextAcc
      unfold wideBaseFold
      change
        (wideBaseFold (operandCopiedMemory I baseSize exponentSize modulusSize)
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          r256 modulusWord n ((operandBasePtr + 32 + start) + 32) nextAcc).toNat = _
      simpa [r256, modulusWord, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Nat.mul_succ] using hrec

end Modexp
