import Examples.Precompiles.Modexp.Model
import Reasoning.Memory

/-!
# Trusted ModExp model bridges

This file is deliberately outside `Model.lean`. It proves that EVMLean's byte/word operations used
by symbolic execution denote the unchanged parser and encoding operations copied from the
EEST-tested evm-semantics model, and connects the proof-facing output projection to the copied
trusted runner.
-/

open Ethereum

namespace Modexp

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Proof-oriented bundle of the three operand lengths parsed by the trusted model. -/
structure Lengths where
  base : Nat
  exponent : Nat
  modulus : Nat
deriving DecidableEq, Repr

def lengths (input : ByteArray) : Lengths where
  base := Model.bytesToNatPadded input 0 32
  exponent := Model.bytesToNatPadded input 32 32
  modulus := Model.bytesToNatPadded input 64 32

def base (input : ByteArray) : Nat :=
  let l := lengths input
  Model.bytesToNatPadded input 96 l.base

def exponent (input : ByteArray) : Nat :=
  let l := lengths input
  Model.bytesToNatPadded input (96 + l.base) l.exponent

def modulus (input : ByteArray) : Nat :=
  let l := lengths input
  Model.bytesToNatPadded input (96 + l.base + l.exponent) l.modulus

/-- Proof-oriented factoring of the trusted output.  This is EquiVM vocabulary, deliberately kept
outside the copied model file. -/
def factoredOutput (input : ByteArray) : ByteArray :=
  let l := lengths input
  if l.modulus = 0 then ByteArray.empty
  else Model.natToBytes
    (Model.modPow (base input) (exponent input) (modulus input)) l.modulus

theorem model_output_eq_factoredOutput (input : ByteArray) :
    Model.output input = factoredOutput input := by
  rfl

theorem model_modPow_exponent_zero (b m : Nat) :
    Model.modPow b 0 m = if 1 < m then 1 else 0 := by
  by_cases hm0 : m = 0
  · subst m
    simp [Model.modPow]
  · by_cases hm1 : m = 1
    · subst m
      simp [Model.modPow]
    · have hgt : 1 < m := by omega
      simp [Model.modPow, Model.modPowAux, hm0, hm1, hgt]

private theorem model_modPowAux_zero (m acc e : Nat) (hm : 0 < m) :
    Model.modPowAux 0 acc m e = if e = 0 then acc else 0 := by
  induction e using Nat.strong_induction_on generalizing acc with
  | h e ih =>
      rw [Model.modPowAux]
      split
      next he => simp [he]
      next he =>
        simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_mod]
        rw [ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))]
        by_cases he1 : e = 1
        · subst e
          simp
        · have hdiv : e / 2 ≠ 0 := by omega
          simp [hdiv]

private theorem model_modPowAux_one (m e : Nat) (hm : 1 < m) :
    Model.modPowAux 1 1 m e = 1 := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
      rw [Model.modPowAux]
      split
      next => rfl
      next he =>
        have hone : 1 % m = 1 := Nat.mod_eq_of_lt hm
        simp only [Nat.one_mul, hone, ite_self]
        exact ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))

/-- Trusted ModExp specialized to the base-zero/base-one fast path used by the bytecode. -/
theorem model_modPow_base_le_one (b e m : Nat) (hb : b ≤ 1) (he : e ≠ 0) :
    Model.modPow b e m = if b = 1 ∧ 1 < m then 1 else 0 := by
  interval_cases b
  · simp only [Model.modPow]
    by_cases hm0 : m = 0
    · simp [hm0]
    · by_cases hm1 : m = 1
      · simp [hm1]
      · have hm : 0 < m := Nat.pos_of_ne_zero hm0
        simp [hm0, hm1, model_modPowAux_zero m 1 e hm, he]
  · by_cases hm0 : m = 0
    · simp [Model.modPow, hm0]
    · by_cases hm1 : m = 1
      · simp [Model.modPow, hm1]
      · have hm : 1 < m := by omega
        simp [Model.modPow, hm0, hm1, Nat.mod_eq_of_lt hm,
          model_modPowAux_one m e hm, hm]

/-- Successful trusted output specialized to a zero exponent, with the three parsed lengths made
explicit for direct use by the bytecode dispatcher proof. -/
theorem model_output_of_exponent_zero (input : ByteArray)
    {baseSize exponentSize modulusSize : Nat}
    (hb : Model.bytesToNatPadded input 0 32 = baseSize)
    (he : Model.bytesToNatPadded input 32 32 = exponentSize)
    (hm : Model.bytesToNatPadded input 64 32 = modulusSize)
    (hexp : Model.bytesToNatPadded input (96 + baseSize) exponentSize = 0) :
    Model.output input =
      Model.natToBytes
        (if 1 < Model.bytesToNatPadded input (96 + baseSize + exponentSize) modulusSize
          then 1 else 0)
        modulusSize := by
  unfold Model.output
  rw [hb, he, hm]
  by_cases hmsize : modulusSize = 0
  · simp [hmsize, Model.natToBytes, Model.natToBytesPadded]
    rfl
  · rw [if_neg hmsize]
    simp only [hexp]
    rw [model_modPow_exponent_zero]

/-- Successful trusted output with parsed lengths exposed, for any already-proved modular-power
result.  This is the direct bridge used by bytecode paths after they establish the three operand
values from calldata. -/
theorem model_output_of_lengths (input : ByteArray)
    {baseSize exponentSize modulusSize : Nat}
    (hb : Model.bytesToNatPadded input 0 32 = baseSize)
    (he : Model.bytesToNatPadded input 32 32 = exponentSize)
    (hm : Model.bytesToNatPadded input 64 32 = modulusSize) :
    Model.output input =
      Model.natToBytes
        (Model.modPow
          (Model.bytesToNatPadded input 96 baseSize)
          (Model.bytesToNatPadded input (96 + baseSize) exponentSize)
          (Model.bytesToNatPadded input (96 + baseSize + exponentSize) modulusSize))
        modulusSize := by
  unfold Model.output
  rw [hb, he, hm]
  by_cases hzero : modulusSize = 0
  · subst modulusSize
    simp_all [Model.natToBytes, Model.natToBytesPadded]
    rfl
  · rw [if_neg hzero]

/-- EIP-7823/Osaka operand-length validity condition implemented by the replacement bytecode. -/
def validOsaka (input : ByteArray) : Prop :=
  let l := lengths input
  l.base ≤ 1024 ∧ l.exponent ≤ 1024 ∧ l.modulus ≤ 1024

/-- The fork-dependent native MODEXP charge from the trusted model.  This is not the gas consumed
by the replacement bytecode. -/
def nativeGas (fork : Model.Fork) (input : ByteArray) : Nat :=
  let l := lengths input
  let expHead := Model.bytesToNatPadded input (96 + l.base) (Nat.min l.exponent 32)
  Model.modexpGas fork l.base l.exponent l.modulus expHead

/-- On an Osaka-valid input with enough forwarded gas, `Model.output` is not merely an adapted
formula: it is definitionally the byte array returned by the copied EEST-tested `runModexp`.
The native precompile charge and the bytecode instruction charge remain separate quantities. -/
theorem model_runModexp_osaka_success (input : ByteArray) (childGas : Nat)
    (hvalid : validOsaka input) (hgas : nativeGas .Osaka input ≤ childGas) :
    Model.runModexp .Osaka input childGas =
      .success (Model.output input) (nativeGas .Osaka input) := by
  apply Model.runModexp_eq_success_output
  · intro htoo
    rcases htoo with ⟨_, htoo⟩
    change Model.bytesToNatPadded input 0 32 ≤ 1024 ∧
      Model.bytesToNatPadded input 32 32 ≤ 1024 ∧
      Model.bytesToNatPadded input 64 32 ≤ 1024 at hvalid
    rcases hvalid with ⟨hb, he, hm⟩
    simp [Model.modexpOsakaInputTooLarge] at htoo
    omega
  · simpa [nativeGas, lengths] using hgas

/-- The stack-only implementation path: every operand fits one EVM word. -/
def wordSized (input : ByteArray) : Prop :=
  let l := lengths input
  l.base ≤ 32 ∧ l.exponent ≤ 32 ∧ l.modulus ≤ 32

/-- EVMLean's padded calldata reader agrees with the trusted model's copied `readPadded` for EVM
word-sized requests and offsets. -/
theorem readBytes_eq_model_readPadded (bs : ByteArray) (start n : Nat)
    (hstart : start < 2 ^ 64) (hn : n < 2 ^ 64) :
    bs.readBytes start n = Model.readPadded bs start n := by
  let start' := Nat.min start bs.size
  let take := Nat.min (bs.size - start') n
  have hprefix : bs.copySlice start ByteArray.empty 0 n =
      bs.extract start' (start' + take) := by
    apply ByteArray.ext
    simp only [ByteArray.data_copySlice, ByteArray.data_extract, start', take]
    by_cases hle : start ≤ bs.size
    · simp [hle]
      rw [Array.extract_eq_extract_right]
      simp only [ByteArray.size, Nat.add_sub_cancel_left]
      have htake : (bs.data.size - start).min n ≤ bs.data.size - start :=
        Nat.min_le_left _ _
      rw [Nat.min_eq_left htake, Nat.min_comm]
    · have hge : bs.size ≤ start := Nat.le_of_not_ge hle
      simp [hge]
  unfold ByteArray.readBytes
  have hcond : (decide (start < 2 ^ 64) && decide (n < 2 ^ 64)) = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using And.intro hstart hn
  rw [if_pos hcond, hprefix]
  have hpSize : (bs.extract start' (start' + take)).size = take := by
    have hstart' : start' ≤ bs.size := Nat.min_le_right _ _
    have htake : take ≤ bs.size - start' := Nat.min_le_left _ _
    have hend : start' + take ≤ bs.size := by omega
    rw [ByteArray.size_extract]
    rw [Nat.min_eq_left hend, Nat.add_sub_cancel_left]
  simp only [hpSize]
  unfold Model.readPadded
  dsimp only
  rw [show Nat.min start bs.size = start' from rfl,
    show Nat.min (bs.size - start') n = take from rfl]
  simp [ffi.ByteArray.zeroes]

/-- EVMLean's memory padded reader agrees with the trusted padded-reader model on bounded
addresses and lengths. -/
theorem readWithPadding_eq_model_readPadded (bs : ByteArray) (start n : Nat)
    (hstart : start < 2 ^ 64) (hn : n < 2 ^ 64) :
    bs.readWithPadding start n = Model.readPadded bs start n := by
  rw [← readBytes_eq_model_readPadded bs start n hstart hn]
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega : ¬n ≥ 2 ^ 64)]
  unfold ByteArray.readBytes
  rw [if_pos (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using And.intro hstart hn)]
  unfold ByteArray.readWithoutPadding
  by_cases hs : start ≥ bs.size
  · rw [if_pos hs]
    have hcopy : bs.copySlice start ByteArray.empty 0 n = ByteArray.empty := by
      apply ByteArray.ext
      simp [ByteArray.data_copySlice, hs]
    rw [hcopy]
  · rw [if_neg hs]
    have hstartLe : start ≤ bs.size := by omega
    have hextract : bs.extract start (start + min n bs.size) =
        bs.copySlice start ByteArray.empty 0 n := by
      apply ByteArray.ext
      simp only [ByteArray.data_extract, ByteArray.data_copySlice]
      simp [hstartLe]
      rw [Array.extract_eq_extract_right]
      simp [Nat.min_assoc, Nat.min_comm, Nat.min_left_comm]
    rw [hextract]

/-- Equal EVM-style padded reads have equal trusted big-endian natural decodings. -/
theorem model_bytesToNatPadded_eq_of_readWithPadding
    {a b : ByteArray} {offA offB width : Nat}
    (hoffA : offA < 2 ^ 64) (hoffB : offB < 2 ^ 64)
    (hwidth : width < 2 ^ 64)
    (hread : a.readWithPadding offA width = b.readWithPadding offB width) :
    Model.bytesToNatPadded a offA width =
      Model.bytesToNatPadded b offB width := by
  unfold Model.bytesToNatPadded
  rw [← readWithPadding_eq_model_readPadded a offA width hoffA hwidth,
    ← readWithPadding_eq_model_readPadded b offB width hoffB hwidth]
  exact congrArg Model.bytesToBigEndianNat hread

/-- The copied padded reader always returns the requested number of bytes. -/
theorem model_readPadded_size (bs : ByteArray) (start n : Nat) :
    (Model.readPadded bs start n).size = n := by
  let start' := Nat.min start bs.size
  let take := Nat.min (bs.size - start') n
  have hstart' : start' ≤ bs.size := Nat.min_le_right _ _
  have htake : take ≤ bs.size - start' := Nat.min_le_left _ _
  have hend : start' + take ≤ bs.size := by omega
  unfold Model.readPadded
  rw [ByteArray.size_append, ByteArray.size_extract]
  simp only [ByteArray.size, Array.size_replicate]
  change min (start' + take) bs.size - start' + (n - take) = n
  rw [Nat.min_eq_left hend, Nat.add_sub_cancel_left]
  exact Nat.add_sub_of_le (Nat.min_le_right _ _)

/-- Explicit prefix-plus-zero-tail shape of the trusted padded reader. -/
theorem model_readPadded_eq_extract_zeroes (bs : ByteArray) (start n : Nat) :
    Model.readPadded bs start n =
      let start' := Nat.min start bs.size
      let take := Nat.min (bs.size - start') n
      bs.extract start' (start' + take) ++ ffi.ByteArray.zeroes (n - take) := by
  unfold Model.readPadded
  simp [ffi.ByteArray.zeroes]

@[simp] theorem model_bytesToNatPadded_zero_width (bs : ByteArray) (offset : Nat) :
    Model.bytesToNatPadded bs offset 0 = 0 := by
  have hread : Model.readPadded bs offset 0 = ByteArray.empty :=
    Reasoning.Theory.byteArray_eq_empty_of_size_eq_zero _ (model_readPadded_size _ _ _)
  simp [Model.bytesToNatPadded, Model.bytesToBigEndianNat, hread,
    Reasoning.Theory.byteArray_toList_eq]

/-- Elementwise view of the trusted padded reader. -/
theorem model_readPadded_getElem (bs : ByteArray) (start n i : Nat) (hi : i < n) :
    (Model.readPadded bs start n)[i]'(by rw [model_readPadded_size]; exact hi) =
      if h : start + i < bs.size then bs[start + i] else 0 := by
  by_cases hidx : start + i < bs.size
  · rw [dif_pos hidx]
    have hstart : start < bs.size := lt_of_le_of_lt (Nat.le_add_right _ _) hidx
    have hiAvail : i < bs.size - start := by omega
    have hiTake : i < Nat.min (bs.size - start) n := Nat.lt_min.mpr ⟨hiAvail, hi⟩
    unfold Model.readPadded
    dsimp only
    simp only [Nat.min_eq_left hstart.le]
    rw [ByteArray.get_append_left (by
      rw [ByteArray.size_extract]
      omega)]
    rw [ByteArray.get_extract]
  · rw [dif_neg hidx]
    let start' := Nat.min start bs.size
    let take := Nat.min (bs.size - start') n
    have hstart' : start' ≤ bs.size := Nat.min_le_right _ _
    have htake : take ≤ bs.size - start' := Nat.min_le_left _ _
    have hprefixSize : (bs.extract start' (start' + take)).size = take := by
      rw [ByteArray.size_extract]
      omega
    have hafter : take ≤ i := by
      by_cases hs : start ≤ bs.size
      · simp only [take, start']
        change min (bs.size - min start bs.size) n ≤ i
        simp [hs]
        omega
      · have hs' : bs.size ≤ start := Nat.le_of_not_ge hs
        simp [start', Nat.min_eq_right hs', take]
    unfold Model.readPadded
    have htotalSize : (bs.extract start' (start' + take) ++
        ByteArray.mk (Array.replicate (n - take) 0)).size = n := by
      rw [ByteArray.size_append, hprefixSize]
      simp only [ByteArray.size, Array.size_replicate]
      exact Nat.add_sub_of_le (Nat.min_le_right _ _)
    change (bs.extract start' (start' + take) ++
      ByteArray.mk (Array.replicate (n - take) 0))[i]'(by rw [htotalSize]; exact hi) = 0
    rw [ByteArray.get_append_right (by simpa [hprefixSize] using hafter)
      (by rw [htotalSize]; exact hi)]
    simp [ByteArray.getElem_eq_data_getElem, hprefixSize]

/-- A subwindow of a trusted padded read is the trusted padded read at the shifted source
position. -/
theorem model_readPadded_window (bs : ByteArray) (off width start len : Nat)
    (hwindow : start + len ≤ width) :
    (Model.readPadded bs off width).extract start (start + len) =
      Model.readPadded bs (off + start) len := by
  have hfullSize := model_readPadded_size bs off width
  have hleftSize :
      ((Model.readPadded bs off width).extract start (start + len)).size = len := by
    rw [ByteArray.size_extract, hfullSize]
    omega
  have hrightSize := model_readPadded_size bs (off + start) len
  apply ByteArray.ext
  apply Array.ext
  · change ((Model.readPadded bs off width).extract start (start + len)).size =
      (Model.readPadded bs (off + start) len).size
    rw [hleftSize, hrightSize]
  · intro i hli hri
    have hi : i < len := by
      change i < ((Model.readPadded bs off width).extract start (start + len)).size at hli
      rwa [hleftSize] at hli
    rw [show ((Model.readPadded bs off width).extract start (start + len)).data[i] =
        ((Model.readPadded bs off width).extract start (start + len))[i]'(by
          rw [hleftSize]
          exact hi) by rfl,
      ByteArray.get_extract]
    rw [model_readPadded_getElem bs off width (start + i) (by omega)]
    rw [show (Model.readPadded bs (off + start) len).data[i] =
        (Model.readPadded bs (off + start) len)[i]'(by
          rw [hrightSize]
          exact hi) by rfl,
      model_readPadded_getElem bs (off + start) len i hi]
    simp only [Nat.add_assoc]

/-- Subwindows of EVMLean padded memory reads compose, including windows that lie partly or wholly
past the concrete byte-array end. -/
theorem readWithPadding_window (bs : ByteArray) (off width start len : Nat)
    (hoff : off < 2 ^ 64) (hwidth : width < 2 ^ 64)
    (hshift : off + start < 2 ^ 64) (hlen : len < 2 ^ 64)
    (hwindow : start + len ≤ width) :
    (bs.readWithPadding off width).extract start (start + len) =
      bs.readWithPadding (off + start) len := by
  rw [readWithPadding_eq_model_readPadded bs off width hoff hwidth,
    readWithPadding_eq_model_readPadded bs (off + start) len hshift hlen]
  exact model_readPadded_window bs off width start len hwindow

/-- Padded reads compose at adjacent byte ranges. -/
theorem model_readPadded_append (bs : ByteArray) (start a b : Nat) :
    Model.readPadded bs start (a + b) =
      Model.readPadded bs start a ++ Model.readPadded bs (start + a) b := by
  have hleftSize : (Model.readPadded bs start (a + b)).size = a + b :=
    model_readPadded_size _ _ _
  have hfirstSize : (Model.readPadded bs start a).size = a :=
    model_readPadded_size _ _ _
  have hsecondSize : (Model.readPadded bs (start + a) b).size = b :=
    model_readPadded_size _ _ _
  apply ByteArray.ext
  apply Array.ext
  · change (Model.readPadded bs start (a + b)).size =
      (Model.readPadded bs start a ++ Model.readPadded bs (start + a) b).size
    rw [hleftSize, ByteArray.size_append, hfirstSize, hsecondSize]
  · intro i hli hri
    have hli' : i < a + b := by
      change i < (Model.readPadded bs start (a + b)).size at hli
      rwa [hleftSize] at hli
    by_cases hi : i < a
    · rw [show (Model.readPadded bs start (a + b)).data[i] =
          (Model.readPadded bs start (a + b))[i]'(by
            rw [hleftSize]; omega) by rfl,
        model_readPadded_getElem _ _ _ _ (by omega)]
      rw [show (Model.readPadded bs start a ++
            Model.readPadded bs (start + a) b).data[i] =
          (Model.readPadded bs start a ++
            Model.readPadded bs (start + a) b)[i]'(by
              rw [ByteArray.size_append, hfirstSize, hsecondSize]; omega) by rfl,
        ByteArray.get_append_left (by rw [hfirstSize]; exact hi),
        model_readPadded_getElem _ _ _ _ hi]
    · have hai : a ≤ i := Nat.le_of_not_gt hi
      have hj : i - a < b := by omega
      rw [show (Model.readPadded bs start (a + b)).data[i] =
          (Model.readPadded bs start (a + b))[i]'(by
            rw [hleftSize]; omega) by rfl,
        model_readPadded_getElem _ _ _ _ (by omega)]
      rw [show (Model.readPadded bs start a ++
            Model.readPadded bs (start + a) b).data[i] =
          (Model.readPadded bs start a ++
            Model.readPadded bs (start + a) b)[i]'(by
              rw [ByteArray.size_append, hfirstSize, hsecondSize]; omega) by rfl,
        ByteArray.get_append_right (by rw [hfirstSize]; exact hai)
          (by rw [ByteArray.size_append, hfirstSize, hsecondSize]; omega)]
      have hr := model_readPadded_getElem bs (start + a) b (i - a) hj
      simpa only [hfirstSize, Nat.add_sub_of_le hai, Nat.add_assoc] using hr.symm

private theorem bytesToBigEndianNat_list (l : List UInt8) :
    l.foldl (fun acc b => acc * 256 + b.toNat) 0 = fromBytesBigEndian l := by
  have be_cons (b : UInt8) (bs : List UInt8) :
      fromBytesBigEndian (b :: bs) =
        b.toNat * 256 ^ bs.length + fromBytesBigEndian bs := by
    unfold fromBytesBigEndian Function.comp
    rw [List.reverse_cons, Reasoning.Theory.fromBytes'_append]
    simp only [List.length_reverse, fromBytes']
    rw [show 2 ^ (8 * bs.length) = 256 ^ bs.length by
      rw [show (256 : Nat) = 2 ^ 8 by decide, pow_mul]]
    rw [UInt8.toFin_val]
    ring
  have aux (l : List UInt8) (acc : Nat) :
      l.foldl (fun acc b => acc * 256 + b.toNat) acc =
        acc * 256 ^ l.length + fromBytesBigEndian l := by
    induction l generalizing acc with
    | nil => simp [fromBytesBigEndian, Function.comp, fromBytes']
    | cons b bs ih =>
      rw [List.foldl_cons, ih, be_cons]
      simp only [List.length_cons, pow_succ]
      ring
  simpa using aux l 0

/-- The copied trusted big-endian decoder agrees with EVMLean's decoder. -/
theorem bytesToBigEndianNat_eq_fromByteArrayBigEndian (bs : ByteArray) :
    Model.bytesToBigEndianNat bs = fromByteArrayBigEndian bs := by
  unfold Model.bytesToBigEndianNat fromByteArrayBigEndian
  exact bytesToBigEndianNat_list bs.toList

/-- A big-endian byte string denotes a value smaller than its byte width. -/
theorem model_bytesToBigEndianNat_lt_pow (bs : ByteArray) :
    Model.bytesToBigEndianNat bs < 256 ^ bs.size := by
  rw [bytesToBigEndianNat_eq_fromByteArrayBigEndian]
  unfold fromByteArrayBigEndian fromBytesBigEndian Function.comp
  have h := Ethereum.fromBytes'_le (bs := bs.toList.reverse)
  rw [List.length_reverse, Reasoning.Theory.byteArray_toList_eq,
    Array.length_toList] at h
  rw [Reasoning.Theory.byteArray_toList_eq]
  simpa [show (256 : Nat) = 2 ^ 8 by decide, pow_mul] using h

/-- A trusted padded field is bounded by the requested byte width. -/
theorem model_bytesToNatPadded_lt_pow (bs : ByteArray) (offset width : Nat) :
    Model.bytesToNatPadded bs offset width < 256 ^ width := by
  unfold Model.bytesToNatPadded
  have h := model_bytesToBigEndianNat_lt_pow (Model.readPadded bs offset width)
  rw [model_readPadded_size] at h
  exact h

/-- The trusted 32-byte decoder is exactly the natural-number view of EVMLean's
`CALLDATALOAD` word. -/
theorem calldataWord_toNat_eq_model (bs : ByteArray) (off : Nat) (hoff : off < 2 ^ 64) :
    (uInt256OfByteArray (bs.readBytes off 32)).toNat =
      Model.bytesToNatPadded bs off 32 := by
  rw [readBytes_eq_model_readPadded bs off 32 hoff (by decide)]
  rw [Reasoning.Theory.uInt256OfByteArray_eq]
  unfold Model.bytesToNatPadded
  rw [Reasoning.Theory.ulit_toNat']
  · exact (bytesToBigEndianNat_eq_fromByteArrayBigEndian _).symm
  · have hsize : (Model.readPadded bs off 32).size = 32 := model_readPadded_size _ _ _
    have hlt := Ethereum.fromBytes'_le
      (bs := (Model.readPadded bs off 32).toList.reverse)
    rw [List.length_reverse, Reasoning.Theory.byteArray_toList_eq,
      Array.length_toList] at hlt
    change (Model.readPadded bs off 32).data.size = 32 at hsize
    rw [hsize] at hlt
    unfold fromByteArrayBigEndian fromBytesBigEndian Function.comp
    rw [Reasoning.Theory.byteArray_toList_eq]
    simpa [UInt256.size] using hlt

/-- Taking a shorter prefix of a trusted padded read is the same as asking the trusted reader for
that shorter width. -/
theorem model_readPadded_prefix (bs : ByteArray) (off n width : Nat) (hn : n ≤ width) :
    (Model.readPadded bs off width).extract 0 n = Model.readPadded bs off n := by
  let start := Nat.min off bs.size
  let avail := bs.size - start
  have hstart : start ≤ bs.size := Nat.min_le_right _ _
  have hsum : start + avail = bs.size := Nat.add_sub_of_le hstart
  by_cases hna : n ≤ avail
  · have hnTake : n ≤ Nat.min avail width := Nat.le_min.mpr ⟨hna, hn⟩
    have hend : start + Nat.min avail width ≤ bs.size := by
      calc
        start + Nat.min avail width ≤ start + avail :=
          Nat.add_le_add_left (Nat.min_le_left _ _) _
        _ = bs.size := hsum
    apply ByteArray.ext
    simp [Model.readPadded, start, avail, Nat.min_eq_right hna, hnTake,
      Nat.min_eq_left hend]
  · have havn : avail < n := Nat.lt_of_not_ge hna
    have havw : avail ≤ width := le_trans havn.le hn
    have hrep : n - avail ≤ width - avail := Nat.sub_le_sub_right hn avail
    have hnend : bs.size ≤ start + n := by omega
    apply ByteArray.ext
    simp [Model.readPadded, start, avail, Nat.min_eq_left havw, Nat.min_eq_left havn.le,
      Nat.min_eq_right hnend, Nat.min_eq_left hrep]

/-- Equal positive-width EVM-style padded reads have equal trusted one-byte prefixes. -/
theorem model_bytesToNatPadded_first_eq_of_readWithPadding
    {a b : ByteArray} {offA offB width : Nat}
    (hoffA : offA < 2 ^ 64) (hoffB : offB < 2 ^ 64)
    (hwidth : width < 2 ^ 64) (hpos : 0 < width)
    (hread : a.readWithPadding offA width = b.readWithPadding offB width) :
    Model.bytesToNatPadded a offA 1 =
      Model.bytesToNatPadded b offB 1 := by
  have hreadModel :
      Model.readPadded a offA width = Model.readPadded b offB width := by
    rw [← readWithPadding_eq_model_readPadded a offA width hoffA hwidth,
      ← readWithPadding_eq_model_readPadded b offB width hoffB hwidth]
    exact hread
  have hprefix := congrArg (fun bs : ByteArray => bs.extract 0 1) hreadModel
  dsimp only at hprefix
  rw [model_readPadded_prefix a offA 1 width (by omega),
    model_readPadded_prefix b offB 1 width (by omega)] at hprefix
  unfold Model.bytesToNatPadded
  rw [hprefix]

/-- Natural-number semantics of `SHR` when the shift is below the EVM word width. -/
theorem shiftRight_toNat_of_lt256 (w shift : UInt256) (hshift : shift.toNat < 256) :
    (UInt256.shiftRight w shift).toNat = w.toNat / 2 ^ shift.toNat := by
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg (by simpa [UInt256.toNat] using hshift)]
  rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]

/-- The implementation's byte-padding shift has the expected, non-wrapping bit count. -/
theorem paddingShift_toNat {size : UInt256} (hsize : size.toNat ≤ 32) :
    (UInt256.shiftLeft (⟨32⟩ - size) ⟨3⟩).toNat = 8 * (32 - size.toNat) := by
  have hsub : (UInt256.sub ⟨32⟩ size).toNat = 32 - size.toNat :=
    Reasoning.Theory.usub_ofNat_word_toNat hsize (by decide)
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨3⟩ : UInt256).val ≥ 256))]
  show (Fin.shiftLeft (UInt256.sub ⟨32⟩ size).val (⟨3⟩ : UInt256).val).val = _
  unfold Fin.shiftLeft
  show ((UInt256.sub ⟨32⟩ size).toNat <<< (3 : Nat)) % UInt256.size = _
  rw [hsub, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by
    have : 32 - size.toNat ≤ 32 := Nat.sub_le _ _
    calc
      (32 - size.toNat) * 2 ^ 3 ≤ 32 * 2 ^ 3 := Nat.mul_le_mul_right _ this
      _ < UInt256.size := by decide)]
  ring

/-- `CALLDATALOAD; SHL 3; SHR` on a width at most one word is exactly the trusted padded
big-endian field reader. -/
theorem operandWord_toNat_eq_model (bs : ByteArray) (off : Nat) (size : UInt256)
    (hoff : off < 2 ^ 64) (hsize : size.toNat ≤ 32) :
    (UInt256.shiftRight
      (uInt256OfByteArray (bs.readBytes off 32))
      (UInt256.shiftLeft (⟨32⟩ - size) ⟨3⟩)).toNat =
      Model.bytesToNatPadded bs off size.toNat := by
  by_cases hzero : size.toNat = 0
  · have hsizeZero : size = ⟨0⟩ := Reasoning.Theory.uint256_toNat_eq_zero hzero
    subst size
    rw [show UInt256.shiftLeft (⟨32⟩ - ⟨0⟩) ⟨3⟩ = ⟨256⟩ by native_decide]
    unfold UInt256.shiftRight
    rw [if_pos (by decide)]
    have hread0 : Model.readPadded bs off 0 = ByteArray.empty :=
      Reasoning.Theory.byteArray_eq_empty_of_size_eq_zero _ (model_readPadded_size bs off 0)
    simp [Model.bytesToNatPadded, Model.bytesToBigEndianNat, hread0,
      Reasoning.Theory.byteArray_toList_eq]
  let full := Model.readPadded bs off 32
  let short := Model.readPadded bs off size.toNat
  have hfullSize : full.size = 32 := model_readPadded_size _ _ _
  have hfullLen : full.toList.length = 32 := by
    rw [Reasoning.Theory.byteArray_toList_eq, Array.length_toList]
    exact hfullSize
  have hprefixBA := model_readPadded_prefix bs off size.toNat 32 hsize
  have hprefix : full.toList.take size.toNat = short.toList := by
    have h := congrArg ByteArray.toList hprefixBA
    rw [Reasoning.Theory.byteArray_toList_eq] at hfullLen
    rw [Reasoning.Theory.byteArray_toList_eq]
    rw [Reasoning.Theory.byteArray_toList_eq]
    rw [Reasoning.Theory.byteArray_toList_eq] at h
    simpa [full, short, Reasoning.Theory.byteArray_toList_eq,
      ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
      hfullLen, hsize] using h
  have hshift := paddingShift_toNat hsize
  have hshiftLt :
      (UInt256.shiftLeft (⟨32⟩ - size) ⟨3⟩).toNat < 256 := by
    rw [hshift]
    omega
  rw [shiftRight_toNat_of_lt256 _ _ hshiftLt, hshift,
    calldataWord_toNat_eq_model bs off hoff]
  unfold Model.bytesToNatPadded
  rw [bytesToBigEndianNat_eq_fromByteArrayBigEndian,
    bytesToBigEndianNat_eq_fromByteArrayBigEndian]
  unfold fromByteArrayBigEndian
  change fromBytesBigEndian full.toList / 2 ^ (8 * (32 - size.toNat)) =
    fromBytesBigEndian short.toList
  conv_lhs => rw [← List.take_append_drop size.toNat full.toList]
  rw [show 8 * (32 - size.toNat) = 8 * (full.toList.drop size.toNat).length by
      rw [List.length_drop, hfullLen],
    Reasoning.Theory.fromBytesBigEndian_append_div, hprefix]

/-- `BYTE 0` is the most-significant byte of an EVM word. -/
theorem byteAt_zero_toNat (w : UInt256) :
    (UInt256.byteAt ⟨0⟩ w).toNat =
      (UInt256.shiftRight w (UInt256.ofNat 248)).toNat := by
  unfold UInt256.byteAt
  rw [if_neg (by decide)]
  rw [show UInt256.ofNat ((31 - (⟨0⟩ : UInt256).toNat) * 8) =
      UInt256.ofNat 248 by decide]
  rw [show w >>> UInt256.ofNat 248 =
      UInt256.shiftRight w (UInt256.ofNat 248) by rfl]
  rw [show UInt256.shiftRight w (UInt256.ofNat 248) &&& (⟨0xff⟩ : UInt256) =
      UInt256.land (UInt256.shiftRight w (UInt256.ofNat 248)) ⟨0xff⟩ by rfl]
  rw [Reasoning.Theory.uland_toNat,
    shiftRight_toNat_of_lt256 w (UInt256.ofNat 248) (by decide)]
  rw [show (UInt256.ofNat 248).toNat = 248 by decide,
    show (⟨0xff⟩ : UInt256).toNat = 255 by decide]
  rw [show (255 : Nat) = 2 ^ 8 - 1 by decide]
  change Nat.land (w.toNat / 2 ^ 248) (2 ^ 8 - 1) = w.toNat / 2 ^ 248
  rw [Reasoning.Theory.nat_land_mask_eq_mod]
  have hq : w.toNat / 2 ^ 248 < 256 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have hw := w.val.isLt
    change w.toNat < UInt256.size at hw
    exact lt_of_lt_of_eq hw (by native_decide)
  rw [show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt hq]

/-- The byte tested by `isGt1` is exactly the trusted one-byte padded read. -/
theorem calldataByte0_toNat_eq_model (bs : ByteArray) (off : Nat) (hoff : off < 2 ^ 64) :
    (UInt256.byteAt ⟨0⟩
      (uInt256OfByteArray (bs.readBytes off 32))).toNat =
      Model.bytesToNatPadded bs off 1 := by
  rw [byteAt_zero_toNat]
  have h := operandWord_toNat_eq_model bs off (UInt256.ofNat 1) hoff (by decide)
  simpa [show UInt256.shiftLeft ((⟨32⟩ : UInt256) - UInt256.ofNat 1) ⟨3⟩ =
      UInt256.ofNat 248 by native_decide] using h

/-! ## Trusted fixed-width encoder semantics

These lemmas reason about the copied `natToBytesPadded` loop as written.  They do not replace it
with an EquiVM encoding definition. -/

private def modelLEBytes : Nat → Nat → List UInt8
  | _, 0 => []
  | n, width + 1 => UInt8.ofNat (n % 256) :: modelLEBytes (n / 256) width

private theorem model_encoder_fold_snd (n start width : Nat) (acc : Array UInt8) :
    (List.foldl
      (fun (b : MProd Nat (Array UInt8)) (_ : Nat) =>
        ⟨b.fst / 256, b.snd.push (UInt8.ofNat (b.fst % 256))⟩)
      (⟨n, acc⟩ : MProd Nat (Array UInt8)) (List.range' start width)).snd =
      acc ++ (modelLEBytes n width).toArray := by
  induction width generalizing n start acc with
  | zero => simp [modelLEBytes]
  | succ width ih =>
      rw [List.range'_succ, List.foldl_cons, ih]
      simp [modelLEBytes]

private theorem modelLEBytes_length (n width : Nat) :
    (modelLEBytes n width).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [modelLEBytes, ih]

private theorem fromBytes'_modelLEBytes (n width : Nat) :
    fromBytes' (modelLEBytes n width) = n % 256 ^ width := by
  induction width generalizing n with
  | zero => simp [modelLEBytes, fromBytes', Nat.mod_one]
  | succ width ih =>
      rw [modelLEBytes, fromBytes', ih, UInt8.toFin_val]
      change (n % 256) % 256 + 256 * (n / 256 % 256 ^ width) = _
      rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)), pow_succ']
      have h := Nat.mod_add_div (n % (256 * 256 ^ width)) 256
      rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self] at h
      exact h

private theorem model_natToBytesPadded_eq (n width : Nat) :
    Model.natToBytesPadded n width =
      ByteArray.mk (modelLEBytes n width).reverse.toArray := by
  simp [Model.natToBytesPadded]
  rw [model_encoder_fold_snd]
  simp only [Array.empty_append]
  apply List.ext_getElem
  · simp [modelLEBytes_length]
  · intro i hleft hright
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, List.getElem_reverse]
    have hi : width - 1 - i < (modelLEBytes n width).length := by
      rw [modelLEBytes_length]
      have : i < width := by simpa [modelLEBytes_length] using hright
      omega
    simp [hi]
    congr 1
    rw [modelLEBytes_length]

/-- The copied trusted encoder produces exactly `width` bytes. -/
theorem model_natToBytes_size (n width : Nat) :
    (Model.natToBytes n width).size = width := by
  rw [Model.natToBytes, model_natToBytesPadded_eq]
  change (modelLEBytes n width).reverse.toArray.size = width
  simp [modelLEBytes_length]

/-- Decoding the copied trusted fixed-width encoder yields the low `width` bytes of `n`. -/
theorem model_bytesToBigEndianNat_natToBytes (n width : Nat) :
    Model.bytesToBigEndianNat (Model.natToBytes n width) = n % 256 ^ width := by
  rw [Model.natToBytes, model_natToBytesPadded_eq,
    bytesToBigEndianNat_eq_fromByteArrayBigEndian]
  unfold fromByteArrayBigEndian fromBytesBigEndian Function.comp
  rw [Reasoning.Theory.byteArray_toList_eq]
  simp only [List.reverse_reverse]
  exact fromBytes'_modelLEBytes n width

private theorem fromBytesBigEndian_append (a b : List UInt8) :
    fromBytesBigEndian (a ++ b) =
      fromBytesBigEndian a * 256 ^ b.length + fromBytesBigEndian b := by
  unfold fromBytesBigEndian Function.comp
  rw [List.reverse_append, Reasoning.Theory.fromBytes'_append, List.length_reverse]
  rw [show 2 ^ (8 * b.length) = 256 ^ b.length by
    rw [show (256 : Nat) = 2 ^ 8 by decide, pow_mul]]
  ring

/-- Big-endian decoding of a byte-array append. -/
theorem model_bytesToBigEndianNat_append (a b : ByteArray) :
    Model.bytesToBigEndianNat (a ++ b) =
      Model.bytesToBigEndianNat a * 256 ^ b.size + Model.bytesToBigEndianNat b := by
  rw [bytesToBigEndianNat_eq_fromByteArrayBigEndian,
    bytesToBigEndianNat_eq_fromByteArrayBigEndian,
    bytesToBigEndianNat_eq_fromByteArrayBigEndian]
  unfold fromByteArrayBigEndian
  rw [Reasoning.Theory.byteArray_toList_eq]
  simp only [ByteArray.data_append, Array.toList_append]
  rw [fromBytesBigEndian_append]
  rw [Reasoning.Theory.byteArray_toList_eq, Array.length_toList]
  rw [Reasoning.Theory.byteArray_toList_eq]
  simp only [ByteArray.size]

/-- Split a trusted padded integer read at an arbitrary byte boundary. -/
theorem model_bytesToNatPadded_split (bs : ByteArray) (start a b : Nat) :
    Model.bytesToNatPadded bs start (a + b) =
      Model.bytesToNatPadded bs start a * 256 ^ b +
        Model.bytesToNatPadded bs (start + a) b := by
  unfold Model.bytesToNatPadded
  rw [model_readPadded_append, model_bytesToBigEndianNat_append,
    model_readPadded_size]

/-- If each byte in a trusted padded field decodes as zero, the whole field decodes as zero. -/
theorem model_bytesToNatPadded_eq_zero_of_bytes
    (bs : ByteArray) (start width : Nat)
    (hbytes : ∀ i, i < width → Model.bytesToNatPadded bs (start + i) 1 = 0) :
    Model.bytesToNatPadded bs start width = 0 := by
  induction width generalizing start with
  | zero =>
      simp [model_bytesToNatPadded_zero_width]
  | succ width ih =>
      have hsplit := model_bytesToNatPadded_split bs start 1 width
      have hfirst : Model.bytesToNatPadded bs start 1 = 0 := by
        simpa using hbytes 0 (by omega)
      have htail : Model.bytesToNatPadded bs (start + 1) width = 0 := by
        apply ih
        intro i hi
        have h := hbytes (i + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      rw [show 1 + width = width + 1 by omega] at hsplit
      rw [hsplit, hfirst, htail]
      simp

private theorem fromBytesBigEndian_drop (l : List UInt8) (width : Nat)
    (hw : width ≤ l.length) :
    fromBytesBigEndian (l.drop (l.length - width)) =
      fromBytesBigEndian l % 256 ^ width := by
  let k := l.length - width
  let a := l.take k
  let b := l.drop k
  have hsplit : a ++ b = l := by simp [a, b, k]
  have hblen : b.length = width := by
    simp [b, k]
    omega
  have hblt : fromBytesBigEndian b < 256 ^ width := by
    unfold fromBytesBigEndian Function.comp
    have h := Ethereum.fromBytes'_le (bs := b.reverse)
    rw [List.length_reverse, hblen] at h
    simpa [show (256 : Nat) = 2 ^ 8 by decide, pow_mul] using h
  change fromBytesBigEndian b = fromBytesBigEndian l % 256 ^ width
  conv_rhs => rw [← hsplit, fromBytesBigEndian_append, hblen]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hblt]

private theorem fromByteArrayBigEndian_toByteArray_suffix (v : UInt256) (width : Nat)
    (hw : width ≤ 32) :
    fromByteArrayBigEndian ((UInt256.toByteArray v).extract (32 - width) 32) =
      v.toNat % 256 ^ width := by
  unfold fromByteArrayBigEndian
  rw [Reasoning.Theory.byteArray_toList_eq, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop]
  have hlen : (UInt256.toByteArray v).data.toList.length = 32 := by
    simpa [Reasoning.Theory.byteArray_toList_eq] using
      Reasoning.Theory.toByteArray_size v
  rw [show ((UInt256.toByteArray v).data.toList.drop (32 - width)).take (32 - (32 - width)) =
      (UInt256.toByteArray v).data.toList.drop (32 - width) by
    apply List.take_of_length_le
    simp [hlen]]
  have hsuffix := fromBytesBigEndian_drop
    (UInt256.toByteArray v).data.toList width (by omega)
  rw [hlen] at hsuffix
  rw [hsuffix]
  have hfull := Reasoning.Theory.fromByteArrayBigEndian_toByteArray v
  unfold fromByteArrayBigEndian at hfull
  rw [Reasoning.Theory.byteArray_toList_eq] at hfull
  rw [hfull]

/-- When a word value fits in `width` bytes, the trusted encoder is exactly the corresponding
suffix of the EVM's 32-byte `MSTORE` encoding. -/
theorem model_natToBytes_eq_toByteArray_suffix (v : UInt256) (width : Nat)
    (hw : width ≤ 32) (hfit : v.toNat < 256 ^ width) :
    Model.natToBytes v.toNat width =
      (UInt256.toByteArray v).extract (32 - width) 32 := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  apply Reasoning.Theory.fromBytesBigEndian_inj_of_length
  · simp only [Array.length_toList]
    change (Model.natToBytes v.toNat width).size =
      ((UInt256.toByteArray v).extract (32 - width) 32).size
    rw [model_natToBytes_size, ByteArray.size_extract,
      Reasoning.Theory.toByteArray_size, Nat.min_eq_left (by decide)]
    omega
  · rw [← Reasoning.Theory.byteArray_toList_eq, ← Reasoning.Theory.byteArray_toList_eq]
    change fromByteArrayBigEndian (Model.natToBytes v.toNat width) =
      fromByteArrayBigEndian ((UInt256.toByteArray v).extract (32 - width) 32)
    rw [← bytesToBigEndianNat_eq_fromByteArrayBigEndian,
      model_bytesToBigEndianNat_natToBytes,
      fromByteArrayBigEndian_toByteArray_suffix v width hw,
      Nat.mod_eq_of_lt hfit]

/-- Trusted fixed-width encoding of zero is the corresponding zero byte array. -/
theorem model_natToBytes_zero (width : Nat) :
    Model.natToBytes 0 width = ByteArray.mk (Array.replicate width 0) := by
  have fold_zero (xs : List Nat) (acc : Array UInt8) :
      List.foldl
        (fun (b : MProd Nat (Array UInt8)) (_ : Nat) =>
          ⟨b.fst / 256, b.snd.push (UInt8.ofNat (b.fst % 256))⟩)
        (⟨0, acc⟩ : MProd Nat (Array UInt8)) xs =
          (⟨0, acc ++ Array.replicate xs.length 0⟩ : MProd Nat (Array UInt8)) := by
    induction xs generalizing acc with
    | nil => simp
    | cons _ xs ih =>
        simp only [List.foldl_cons, Nat.zero_div, Nat.zero_mod]
        rw [show UInt8.ofNat 0 = 0 by decide, ih]
        congr 1
        apply Array.toList_inj.mp
        simp [List.replicate_succ, Array.toList_append]
  have hleSnd :
      (List.foldl
        (fun (b : MProd Nat (Array UInt8)) (_ : Nat) =>
          ⟨b.fst / 256, b.snd.push (UInt8.ofNat (b.fst % 256))⟩)
        (⟨0, #[]⟩ : MProd Nat (Array UInt8)) (List.range' 0 width)).snd =
          Array.replicate width 0 := by
    have h := congrArg MProd.snd (fold_zero (List.range' 0 width) #[])
    simpa using h
  simp [Model.natToBytes, Model.natToBytesPadded]
  rw [hleSnd]
  apply Array.toList_inj.mp
  simp only [Array.toList_replicate]
  apply List.eq_replicate_iff.mpr
  constructor
  · simp
  · intro b hb
    simp only [List.mem_map] at hb
    rcases hb with ⟨x, hx, rfl⟩
    have hxlt : x < width := by simpa using hx
    have hi : width - 1 - x < width := by omega
    simp [hi]

/-- The trusted zero encoding is the EVM memory library's zero block. -/
theorem model_natToBytes_zero_eq_zeroes (width : Nat) :
    Model.natToBytes 0 width = ffi.ByteArray.zeroes width := by
  rw [model_natToBytes_zero]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [Reasoning.Theory.byteArray_zeroes_toList]
  simp only [Array.toList_replicate]

/-- Prefixing a fitted fixed-width encoding with zero bytes is the wider fixed-width encoding. -/
theorem model_natToBytes_leftPad (v k n : Nat) (hfit : v < 256 ^ n) :
    ffi.ByteArray.zeroes k ++ Model.natToBytes v n =
      Model.natToBytes v (k + n) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  apply Reasoning.Theory.fromBytesBigEndian_inj_of_length
  · simp only [Array.length_toList]
    change (ffi.ByteArray.zeroes k ++ Model.natToBytes v n).size =
      (Model.natToBytes v (k + n)).size
    rw [ByteArray.size_append, ByteArray_zeroes_size, model_natToBytes_size,
      model_natToBytes_size]
  · rw [← Reasoning.Theory.byteArray_toList_eq, ← Reasoning.Theory.byteArray_toList_eq]
    change fromByteArrayBigEndian (ffi.ByteArray.zeroes k ++ Model.natToBytes v n) =
      fromByteArrayBigEndian (Model.natToBytes v (k + n))
    rw [← bytesToBigEndianNat_eq_fromByteArrayBigEndian,
      ← bytesToBigEndianNat_eq_fromByteArrayBigEndian,
      model_bytesToBigEndianNat_append,
      model_bytesToBigEndianNat_natToBytes,
      model_bytesToBigEndianNat_natToBytes]
    have hzero : Model.bytesToBigEndianNat (ffi.ByteArray.zeroes k) = 0 := by
      rw [← model_natToBytes_zero_eq_zeroes k, model_bytesToBigEndianNat_natToBytes]
      simp
    have hfitWide : v < 256 ^ (k + n) := by
      exact lt_of_lt_of_le hfit
        (Nat.pow_le_pow_right (by decide : 1 ≤ 256) (by omega : n ≤ k + n))
    rw [hzero, model_natToBytes_size]
    simp [Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt hfitWide]

/-- Trusted fixed-width encoding of one: zeros followed by the low byte, for a nonempty width. -/
theorem model_natToBytes_one {width : Nat} (hwidth : 0 < width) :
    Model.natToBytes 1 width =
      ByteArray.mk (Array.replicate (width - 1) 0) ++ ⟨#[1]⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  apply Reasoning.Theory.fromBytesBigEndian_inj_of_length
  · simp only [Array.length_toList]
    change (Model.natToBytes 1 width).size =
      (ByteArray.mk (Array.replicate (width - 1) 0) ++ ⟨#[1]⟩).size
    rw [model_natToBytes_size, ByteArray.size_append]
    change width = (Array.replicate (width - 1) 0).size + #[1].size
    simp only [Array.size_replicate]
    change width = width - 1 + 1
    omega
  · rw [← Reasoning.Theory.byteArray_toList_eq, ← Reasoning.Theory.byteArray_toList_eq]
    change fromByteArrayBigEndian (Model.natToBytes 1 width) =
      fromByteArrayBigEndian
        (ByteArray.mk (Array.replicate (width - 1) 0) ++ ⟨#[1]⟩)
    rw [← bytesToBigEndianNat_eq_fromByteArrayBigEndian,
      ← bytesToBigEndianNat_eq_fromByteArrayBigEndian,
      model_bytesToBigEndianNat_natToBytes,
      model_bytesToBigEndianNat_append]
    have hzero : Model.bytesToBigEndianNat
        (ByteArray.mk (Array.replicate (width - 1) 0)) = 0 := by
      rw [← model_natToBytes_zero]
      rw [model_bytesToBigEndianNat_natToBytes]
      simp
    rw [hzero]
    have hpow : 1 < 256 ^ width :=
      Nat.one_lt_pow (Nat.ne_of_gt hwidth) (by decide)
    rw [Nat.mod_eq_of_lt hpow]
    simp only [zero_mul, zero_add]
    unfold Model.bytesToBigEndianNat
    rw [Reasoning.Theory.byteArray_toList_eq]
    change 1 = List.foldl (fun acc b => acc * 256 + b.toNat) 0 ([1] : List UInt8)
    rfl

theorem zeroes32_extract_window (start len : Nat) (hwindow : start + len ≤ 32) :
    (ffi.ByteArray.zeroes 32).extract start (start + len) =
      ByteArray.mk (Array.replicate len 0) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract,
    Reasoning.Theory.byteArray_zeroes_toList]
  simp only [List.extract_eq_take_drop]
  rw [Nat.add_sub_cancel_left, Array.toList_replicate]
  rw [List.drop_replicate, List.take_replicate]
  congr 1
  omega

end Modexp
