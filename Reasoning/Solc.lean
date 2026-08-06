import Reasoning.ABI
import Reasoning.Memory
import Reasoning.Stepping
import Reasoning.Reach

/-!
# Solc — reusable boilerplate shared by every solc-compiled contract

Solidity's compiler emits the same code shapes in every contract; this file proves them once,
generically, so per-contract proofs only instantiate them.  Contents:

- the **4-byte selector dispatch** (selector word, big-endian decode, the generic dispatch lemma,
  the dispatcher scaffold and one-level binary dispatch);
- ABI decoder length checks for calldata and returndata tuples;
- the recurring memory shapes: free-memory-pointer store, `Error(string)` revert memory, mapping
  scratch memory, dynamic bytes/string return and calldata-copy memory;
- the 160-bit **address-cleanup mask** and its canonicality facts;
- getter thunks, mapping getter/store routines, reentrancy-lock prefixes, checked-arithmetic
  success tails, boolean-success continuations, event-log suffixes, one-word return wrappers;
- high-level external-call combinators (EXTCODESIZE guard, call-success guard, STATICCALL).

Everything in this file is contract-agnostic.
-/

namespace Reasoning.Theory

open ABI Ethereum Ethereum.EVM Reasoning.Reach

/-! ## Selector word -/

/-- The 4-byte selector word computed by solc's `CALLDATALOAD(0); SHR 224` sequence. -/
abbrev solcSelectorWord (ee : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes 0 32)) ⟨224⟩

/-! ## Generic `UInt256.eq` facts -/

/-- `EQ` of equal words is `1`. -/
theorem u256_eq_refl (a : UInt256) : UInt256.eq a a = ⟨1⟩ := by
  simp only [UInt256.eq, Bool.toUInt256]; rfl

/-- `EQ` of distinct words is `0`. -/
theorem u256_eq_of_ne {a b : UInt256} (h : a ≠ b) : UInt256.eq a b = ⟨0⟩ := by
  simp only [UInt256.eq, Bool.toUInt256, decide_eq_false h]; rfl

/-! ## Big-endian decode of the 4 selector bytes -/

/-- Evaluate `fromBytesBigEndian` on four bytes as a base-256 numeral. -/
theorem fromBytesBigEndian_four (a0 a1 a2 a3 : UInt8) :
    fromBytesBigEndian [a0, a1, a2, a3]
      = a3.toNat + 256 * (a2.toNat + 256 * (a1.toNat + 256 * a0.toNat)) := by
  simp only [fromBytesBigEndian, Function.comp, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, fromBytes', Nat.mul_zero, Nat.add_zero]
  rfl

/-- `fromBytesBigEndian` is injective on 4-byte lists (the selector decode is lossless). -/
theorem fromBytesBigEndian_inj4 {l l' : List UInt8} (hl : l.length = 4) (hl' : l'.length = 4)
    (h : fromBytesBigEndian l = fromBytesBigEndian l') : l = l' := by
  match l, hl, l', hl' with
  | [a0, a1, a2, a3], _, [b0, b1, b2, b3], _ =>
    rw [fromBytesBigEndian_four, fromBytesBigEndian_four] at h
    have ba0 : a0.toNat < 256 := a0.toFin.isLt
    have ba1 : a1.toNat < 256 := a1.toFin.isLt
    have ba2 : a2.toNat < 256 := a2.toFin.isLt
    have ba3 : a3.toNat < 256 := a3.toFin.isLt
    have bb0 : b0.toNat < 256 := b0.toFin.isLt
    have bb1 : b1.toNat < 256 := b1.toFin.isLt
    have bb2 : b2.toNat < 256 := b2.toFin.isLt
    have bb3 : b3.toNat < 256 := b3.toFin.isLt
    have e0 : a0 = b0 := UInt8.toNat_inj.mp (by omega)
    have e1 : a1 = b1 := UInt8.toNat_inj.mp (by omega)
    have e2 : a2 = b2 := UInt8.toNat_inj.mp (by omega)
    have e3 : a3 = b3 := UInt8.toNat_inj.mp (by omega)
    rw [e0, e1, e2, e3]

/-- The dispatcher's `ByteArray` selector compare `#[c0,c1,c2,c3] == calldata[0:4]` equals the
    list condition on the first four calldata bytes. -/
theorem extract4_eq_iff (cd : ByteArray) (c0 c1 c2 c3 : UInt8) (_hsz : 4 ≤ cd.size) :
    ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == cd.extract 0 4) = true
      ↔ cd.data.toList.take 4 = [c0, c1, c2, c3] := by
  rw [show ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == cd.extract 0 4)
        = ((#[c0, c1, c2, c3] : Array UInt8) == (cd.extract 0 4).data) from rfl,
      beq_iff_eq, ByteArray.data_extract, ← Array.toList_inj, Array.toList_extract]
  show ([c0, c1, c2, c3] : List UInt8) = (cd.data.toList.drop 0).take (0 + 4 - 0) ↔ _
  rw [List.drop_zero]
  constructor
  · intro he; rw [← he]
  · intro he; rw [he]

/-! ## The generic selector-decode lemma -/

/-- **Selector decode** (contract-agnostic).  The EVM selector test
    `eq(sel, SHR(calldataload(0), 224))` agrees with the dispatcher's byte compare
    `#[c0,c1,c2,c3] == calldata.extract 0 4`, given `sel`'s bytes are `[c0,c1,c2,c3]`.
    Both `truthEvmSelector` and `powEvmSelector` are instances. -/
theorem evmSelectorDecode {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat) :
    UInt256.eq sel (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  have hsv : (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩).toNat
             = fromBytesBigEndian (cd.data.toList.take 4) := selector_toNat cd hsz
  by_cases hc : cd.data.toList.take 4 = [c0, c1, c2, c3]
  · have h1 : UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩ = sel :=
      u256_inj (by rw [hsv, hc, hsel])
    rw [if_pos ((extract4_eq_iff cd c0 c1 c2 c3 hsz).mpr hc), h1, u256_eq_refl]
  · rw [if_neg (fun he => hc ((extract4_eq_iff cd c0 c1 c2 c3 hsz).mp he))]
    apply u256_eq_of_ne
    intro he
    apply hc
    have hlen4 : (cd.data.toList.take 4).length = 4 := by
      rw [List.length_take]
      have : 4 ≤ cd.data.toList.length := by rw [Array.length_toList]; exact hsz
      omega
    exact fromBytesBigEndian_inj4 hlen4 rfl (by rw [← hsv, ← he]; exact hsel.symm)

theorem solcSelectorWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    solcSelectorWord I = sel := by
  apply u256_inj
  dsimp [solcSelectorWord]
  rw [selector_toNat I.calldata hsz]
  rw [(extract4_eq_iff I.calldata c0 c1 c2 c3 hsz).mp hmatch, hsel]

/-! ## Solc ABI decoder length checks

Solc's ABI decoders check static calldata/returndata availability with a signed comparison of the
form `SLT(dataEnd - headStart, neededBytes)`.  These lemmas expose that compiler pattern directly,
so contract proofs do not need to spell out the `UInt256`/`Nat` subtraction bridge.
-/

/-- The solc decoder length check passes when `head + need ≤ size` and the length word is below the
    signed boundary. -/
theorem solcDecodeLenCheckOk {sz : ℕ} {head need : UInt256}
    (hlen : head.toNat + need.toNat ≤ sz)
    (hhi : sz < 2 ^ 255 + head.toNat)
    (hsz : sz < UInt256.size)
    (hneed : need.toNat < 2 ^ 255) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) head) need = ⟨0⟩ := by
  rw [← u256_ofNat_toNat need]
  apply slt_lit_zero hneed
  · rw [usub_ofNat_word_toNat (by omega : head.toNat ≤ sz) hsz]
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hlen)
  · rw [usub_ofNat_word_toNat (by omega : head.toNat ≤ sz) hsz]
    exact Nat.sub_lt_right_of_lt_add (by omega : head.toNat ≤ sz) hhi

/-- Unsigned variant of `solcDecodeLenCheckOk`, for compiler guards emitted as `LT`. -/
theorem solcDecodeLenCheckOkUnsigned {sz : ℕ} {head need : UInt256}
    (hlen : head.toNat + need.toNat ≤ sz)
    (hsz : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) head) need = ⟨0⟩ := by
  apply ult_zero
  rw [usub_ofNat_word_toNat (by omega : head.toNat ≤ sz) hsz]
  exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hlen)

/-- The solc decoder length check fails in the ordinary short-buffer case:
    `head ≤ size < head + need`. -/
theorem solcDecodeLenCheckShort {sz : ℕ} {head need : UInt256}
    (hhead : head.toNat ≤ sz)
    (hshort : sz < head.toNat + need.toNat)
    (hsz : sz < UInt256.size)
    (hneed : need.toNat < 2 ^ 255) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) head) need = ⟨1⟩ := by
  rw [← u256_ofNat_toNat need]
  apply slt_lit_one_low hneed
  rw [usub_ofNat_word_toNat hhead hsz]
  exact Nat.sub_lt_right_of_lt_add hhead (by simpa [Nat.add_comm] using hshort)

/-- The solc decoder length check also fails when `size - head` has the sign bit set. -/
theorem solcDecodeLenCheckHuge {sz : ℕ} {head need : UInt256}
    (hbig : 2 ^ 255 + head.toNat ≤ sz)
    (hsz : sz < UInt256.size)
    (hneed : need.toNat < 2 ^ 255) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) head) need = ⟨1⟩ := by
  rw [← u256_ofNat_toNat need]
  apply slt_lit_one_high hneed
  rw [usub_ofNat_word_toNat (by omega : head.toNat ≤ sz) hsz]
  exact Nat.le_sub_of_add_le hbig

/-! ### Static calldata tuple length checks

External function calldata has a 4-byte selector followed by ABI words.  A static tuple of
`words` ABI words needs `32 * words` bytes after the selector.
-/

theorem solcCalldataStaticLenCheckOk {sz words : ℕ}
    (hlen : 4 + 32 * words ≤ sz)
    (hhi : sz < 2 ^ 255 + 4)
    (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) (UInt256.ofNat (32 * words)) = ⟨0⟩ := by
  have hneed : 32 * words < 2 ^ 255 := by omega
  have h4 : ((⟨4⟩ : UInt256).toNat = 4) := by decide
  have hneedNat : (UInt256.ofNat (32 * words)).toNat = 32 * words :=
    ulit_toNat' _ (lt_size_of_lt_sign hneed)
  exact solcDecodeLenCheckOk
    (head := (⟨4⟩ : UInt256)) (need := UInt256.ofNat (32 * words))
    (by rw [h4, hneedNat]; exact hlen)
    (by simpa [h4] using hhi)
    hsz
    (by rw [hneedNat]; exact hneed)

theorem solcCalldataStaticLenCheckShort {sz words : ℕ}
    (hhead : 4 ≤ sz)
    (hshort : sz < 4 + 32 * words)
    (hsz : sz < UInt256.size)
    (hneed : 32 * words < 2 ^ 255) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) (UInt256.ofNat (32 * words)) = ⟨1⟩ := by
  have h4 : ((⟨4⟩ : UInt256).toNat = 4) := by decide
  have hneedNat : (UInt256.ofNat (32 * words)).toNat = 32 * words :=
    ulit_toNat' _ (lt_size_of_lt_sign hneed)
  exact solcDecodeLenCheckShort
    (head := (⟨4⟩ : UInt256)) (need := UInt256.ofNat (32 * words))
    (by rw [h4]; exact hhead)
    (by rw [h4, hneedNat]; exact hshort)
    hsz
    (by rw [hneedNat]; exact hneed)

theorem solcCalldataStaticLenCheckHuge {sz words : ℕ}
    (hbig : 2 ^ 255 + 4 ≤ sz)
    (hsz : sz < UInt256.size)
    (hneed : 32 * words < 2 ^ 255) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) (UInt256.ofNat (32 * words)) = ⟨1⟩ := by
  have h4 : ((⟨4⟩ : UInt256).toNat = 4) := by decide
  have hneedNat : (UInt256.ofNat (32 * words)).toNat = 32 * words :=
    ulit_toNat' _ (lt_size_of_lt_sign hneed)
  exact solcDecodeLenCheckHuge
    (head := (⟨4⟩ : UInt256)) (need := UInt256.ofNat (32 * words))
    (by simpa [h4] using hbig)
    hsz
    (by rw [hneedNat]; exact hneed)

/-! ### Common solc ABI calldata specializations

These are the usual external-call decoder checks after the 4-byte selector: one static word needs
`32` bytes and two static words need `64` bytes.
-/

theorem solcDecodeLenCheckOk_4_32 {sz : ℕ}
    (hlen : 36 ≤ sz) (hhi : sz < 2 ^ 255 + 4) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
  exact solcCalldataStaticLenCheckOk (words := 1) (by simpa using hlen) hhi hsz

theorem solcDecodeLenCheckShort_4_32 {sz : ℕ}
    (hhead : 4 ≤ sz) (hshort : sz < 36) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckShort (words := 1) hhead (by simpa using hshort) hsz
    (by norm_num)

theorem solcDecodeLenCheckHuge_4_32 {sz : ℕ}
    (hbig : 2 ^ 255 + 4 ≤ sz) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckHuge (words := 1) hbig hsz (by norm_num)

theorem solcDecodeLenCheckOk_4_64 {sz : ℕ}
    (hlen : 68 ≤ sz) (hhi : sz < 2 ^ 255 + 4) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨64⟩ = ⟨0⟩ := by
  exact solcCalldataStaticLenCheckOk (words := 2) (by simpa using hlen) hhi hsz

theorem solcDecodeLenCheckShort_4_64 {sz : ℕ}
    (hhead : 4 ≤ sz) (hshort : sz < 68) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckShort (words := 2) hhead (by simpa using hshort) hsz
    (by norm_num)

theorem solcDecodeLenCheckHuge_4_64 {sz : ℕ}
    (hbig : 2 ^ 255 + 4 ≤ sz) (hsz : sz < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
  exact solcCalldataStaticLenCheckHuge (words := 2) hbig hsz (by norm_num)

/-! ### Static returndata tuple length checks -/

theorem solcReturnStaticLenCheckOk {base len words : ℕ}
    (hlen : 32 * words ≤ len)
    (hhi : len < 2 ^ 255)
    (hbase : base < UInt256.size)
    (hadd : base + len < UInt256.size) :
    UInt256.slt
      (UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat len)) (UInt256.ofNat base))
      (UInt256.ofNat (32 * words)) = ⟨0⟩ := by
  have hneed : 32 * words < 2 ^ 255 := lt_of_le_of_lt hlen hhi
  have hsub :
      UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat len)) (UInt256.ofNat base)
        = UInt256.ofNat len :=
    usub_uadd_lit_cancel hbase (lt_size_of_lt_sign hhi) hadd
  rw [hsub, slt_ofNat_lit_zero hneed hlen hhi]

theorem solcReturnStaticLenCheckShort {base len words : ℕ}
    (hshort : len < 32 * words)
    (hbase : base < UInt256.size)
    (hadd : base + len < UInt256.size)
    (hneed : 32 * words < 2 ^ 255) :
    UInt256.slt
      (UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat len)) (UInt256.ofNat base))
      (UInt256.ofNat (32 * words)) = ⟨1⟩ := by
  have hhi : len < 2 ^ 255 := lt_trans hshort hneed
  have hsub :
      UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat len)) (UInt256.ofNat base)
        = UInt256.ofNat len :=
    usub_uadd_lit_cancel hbase (lt_size_of_lt_sign hhi) hadd
  rw [hsub, slt_ofNat_lit_one_low hneed hshort]

theorem solcReturnStaticLenCheckHuge {base len words : ℕ}
    (hhi : 2 ^ 255 ≤ len)
    (hlo : len < UInt256.size)
    (hbase : base < UInt256.size)
    (hneed : 32 * words < 2 ^ 255) :
    UInt256.slt
      (UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat len)) (UInt256.ofNat base))
      (UInt256.ofNat (32 * words)) = ⟨1⟩ := by
  have hsub :
      UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat len)) (UInt256.ofNat base)
        = UInt256.ofNat len :=
    usub_uadd_lit_cancel_mod hbase hlo
  rw [hsub]
  apply slt_lit_one_high hneed
  rw [ulit_toNat' len hlo]
  exact hhi

/-! ### Common solc ABI returndata specialization -/

theorem solcDecodeEndLenCheckOk_128_32 {len : ℕ}
    (hlen : 32 ≤ len) (hhi : len < 2 ^ 255) :
    UInt256.slt (UInt256.sub (UInt256.add ⟨128⟩ (UInt256.ofNat len)) ⟨128⟩) ⟨32⟩
      = ⟨0⟩ := by
  exact solcReturnStaticLenCheckOk (base := 128) (words := 1) (by simpa using hlen) hhi
    (by norm_num [UInt256.size])
    (by
      have hcap : (2 : ℕ) ^ 255 + 128 < UInt256.size := by norm_num [UInt256.size]
      omega)

theorem solcDecodeEndLenCheckShort_128_32 {len : ℕ} (hshort : len < 32) :
    UInt256.slt (UInt256.sub (UInt256.add ⟨128⟩ (UInt256.ofNat len)) ⟨128⟩) ⟨32⟩
      = ⟨1⟩ := by
  exact solcReturnStaticLenCheckShort (base := 128) (words := 1) (by simpa using hshort)
    (by norm_num [UInt256.size])
    (by
      have hcap : (2 : ℕ) ^ 255 + 128 < UInt256.size := by norm_num [UInt256.size]
      omega)
    (by norm_num)

theorem solcDecodeEndLenCheckHuge_128_32 {len : ℕ}
    (hhi : 2 ^ 255 ≤ len) (hlo : len < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.add ⟨128⟩ (UInt256.ofNat len)) ⟨128⟩) ⟨32⟩
      = ⟨1⟩ := by
  exact solcReturnStaticLenCheckHuge (base := 128) (words := 1) hhi
    hlo
    (by norm_num [UInt256.size])
    (by norm_num)

/-! ## The free-memory-pointer memory

Every solc contract opens with `PUSH1 0x80; PUSH1 0x40; MSTORE`, storing the initial free pointer
`0x80` at `0x40`.  This is the resulting memory and the read-back lemma the epilogue's
`MLOAD 0x40` needs — contract-agnostic. -/

/-- Memory after solc stores the free pointer `0x80` at `0x40`. -/
def solcFreePtrMem : ByteArray :=
  (UInt256.toByteArray ⟨128⟩).write 0 ByteArray.empty 64 32

theorem solcFreePtrMem_eq :
    solcFreePtrMem
      = (ByteArray.empty ++ ffi.ByteArray.zeroes 64) ++ UInt256.toByteArray ⟨128⟩ := by
  rw [solcFreePtrMem, toByteArray_write_eq _ _ _ (by decide) (by exact lt_usize _ (by norm_num))]; rfl

theorem solcFreePtrMem_size : solcFreePtrMem.size = 96 := by
  rw [solcFreePtrMem_eq, ByteArray.size_append, ByteArray.size_append,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]; decide

theorem solcFreePtrMem_read64 : solcFreePtrMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := solcFreePtrMem_size; omega), solcFreePtrMem_eq,
      extract_append_right' _ _ _ _
        (by rw [ByteArray.size_append, zeroes_ofNat_size _ (by norm_num)]; rfl)
        (by rw [ByteArray.size_append, zeroes_ofNat_size _ (by norm_num), toByteArray_size]; rfl)]

/-- The value pushed by a solc-style `MLOAD 0x40` when memory still stores free pointer `0x80`. -/
theorem mloadFreePtrValue {mem : ByteArray} {aw : UInt256}
    (hmem : 64 < mem.size) (haw : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := aw) (v := (⟨128⟩ : UInt256))
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem)
    haw
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread)

/-- `MLOAD 0x40` over the initial solc free-pointer memory pushes `0x80`. -/
theorem solcFreePtrMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64

theorem solcFreePtrMem_pad_size :
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
  rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size _ (by norm_num)]

/-- Memory after solc stores a 32-byte return word `val` at `0x80`, over the free-pointer memory —
    the shape every solc ABI-encoder's epilogue produces (its `RETURN`s `mem[0x80 .. 0xa0] = val`). -/
def solcReturnMem (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 solcFreePtrMem 128 32

theorem solcReturnMem_eq (val : UInt256) :
    solcReturnMem val = (solcFreePtrMem ++ ffi.ByteArray.zeroes 32) ++ UInt256.toByteArray val := by
  rw [solcReturnMem, toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
        (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [solcFreePtrMem_size]

theorem solcReturnMem_size (val : UInt256) : (solcReturnMem val).size = 160 := by
  rw [solcReturnMem_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem solcReturnMem_read64 (val : UInt256) :
    (solcReturnMem val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := solcReturnMem_size val; omega), solcReturnMem_eq,
      extract_append_left _ _ _ _ (by have := solcFreePtrMem_pad_size; omega),
      extract_append_left _ _ _ _ (by have := solcFreePtrMem_size; omega),
      ← readWithPadding_eq_extract _ _ (by have := solcFreePtrMem_size; omega), solcFreePtrMem_read64]

/-- `MLOAD 0x40` over solc return memory still pushes the free pointer `0x80`. -/
theorem solcReturnMem_mload64 (val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcReturnMem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((solcReturnMem val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcReturnMem_size]; decide) (by decide) (solcReturnMem_read64 val)

theorem solcReturnMem_read128 (val : UInt256) :
    (solcReturnMem val).readWithPadding 128 32 = UInt256.toByteArray val := by
  rw [readWithPadding_eq_extract _ _ (by have := solcReturnMem_size val; omega), solcReturnMem_eq,
      extract_append_right' _ _ _ _ (by have := solcFreePtrMem_pad_size; omega)
        (by have := solcFreePtrMem_pad_size; have := toByteArray_size val; omega)]

/-! ## `Error(string)` revert memory -/

def solcErrorStringSelector : UInt256 :=
  UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩

noncomputable def solcErrorStringMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray solcErrorStringSelector).write 0 mem 128 32

noncomputable def solcErrorStringMem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 (solcErrorStringMem0 mem) 132 32

noncomputable def solcErrorStringMem2 (len : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray len).write 0 (solcErrorStringMem1 mem) 164 32

noncomputable def solcErrorStringMem3 (len word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 (solcErrorStringMem2 len mem) 196 32

theorem solcErrorStringMem0_size {mem : ByteArray} (hmem : mem.size = 96) :
    (solcErrorStringMem0 mem).size = 160 := by
  unfold solcErrorStringMem0
  rw [toByteArray_write_eq _ _ _ (by rw [hmem]; omega)
      (by rw [hmem]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hmem, ByteArray_zeroes_size,
    toByteArray_size]

theorem solcErrorStringMem1_size {mem : ByteArray} (hmem : mem.size = 96) :
    (solcErrorStringMem1 mem).size = 164 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcErrorStringMem0_size hmem,
    toByteArray_size]
  omega

/-- Everything above `Mem1` only depends on `(solcErrorStringMem1 mem).size = 164`, so the
    `Mem2`/`Mem3` facts are proved once here and instantiated by both the 96- and 164-byte base
    cases. -/
theorem solcErrorStringMem2_size_of_mem1 (len : UInt256) {mem : ByteArray}
    (h1 : (solcErrorStringMem1 mem).size = 164) :
    (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [h1]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, h1, toByteArray_size]
  omega

theorem solcErrorStringMem3_size_of_mem1 (len word : UInt256) {mem : ByteArray}
    (h1 : (solcErrorStringMem1 mem).size = 164) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_mem1 len h1]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcErrorStringMem2_size_of_mem1 len h1,
    toByteArray_size]
  omega

theorem solcErrorStringMem3_read64_of_mem1 (len word : UInt256) {mem : ByteArray}
    (h1 : (solcErrorStringMem1 mem).size = 164)
    (h1read : (solcErrorStringMem1 mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_mem1 len h1]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_mem1 len h1]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [h1]; omega) (by omega)
      (by rw [h1]; exact lt_usize _ (by norm_num))]
  exact h1read

theorem solcErrorStringMem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (solcErrorStringMem2 len mem).size = 196 :=
  solcErrorStringMem2_size_of_mem1 len (solcErrorStringMem1_size hmem)

theorem solcErrorStringMem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (solcErrorStringMem3 len word mem).size = 228 :=
  solcErrorStringMem3_size_of_mem1 len word (solcErrorStringMem1_size hmem)

theorem solcErrorStringMem1_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem1 mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  solcErrorStringMem3_read64_of_mem1 len word (solcErrorStringMem1_size hmem)
    (solcErrorStringMem1_read64 hmem hread64)

theorem solcErrorStringMem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size len word hmem]; decide)
    (by decide) (solcErrorStringMem3_read64 len word hmem hread64)

theorem solcErrorStringMem0_size_of_size164 {mem : ByteArray} (hmem : mem.size = 164) :
    (solcErrorStringMem0 mem).size = 164 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem, toByteArray_size]

theorem solcErrorStringMem1_size_of_size164 {mem : ByteArray} (hmem : mem.size = 164) :
    (solcErrorStringMem1 mem).size = 164 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size164 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem0_size_of_size164 hmem,
    toByteArray_size]

theorem solcErrorStringMem2_size_of_size164 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (solcErrorStringMem2 len mem).size = 196 :=
  solcErrorStringMem2_size_of_mem1 len (solcErrorStringMem1_size_of_size164 hmem)

theorem solcErrorStringMem3_size_of_size164 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (solcErrorStringMem3 len word mem).size = 228 :=
  solcErrorStringMem3_size_of_mem1 len word (solcErrorStringMem1_size_of_size164 hmem)

theorem solcErrorStringMem1_read64_of_size164 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem1 mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size164 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size164 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_read64_of_size164 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  solcErrorStringMem3_read64_of_mem1 len word (solcErrorStringMem1_size_of_size164 hmem)
    (solcErrorStringMem1_read64_of_size164 hmem hread64)

theorem solcErrorStringMem3_mload64_of_size164 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size164 len word hmem]; decide)
    (by decide) (solcErrorStringMem3_read64_of_size164 len word hmem hread64)

/-! ## Mapping scratch memory -/

noncomputable def solcMappingBaseSlotMem (baseSlot : UInt256) : ByteArray :=
  wordAt32Mem baseSlot solcFreePtrMem

noncomputable def solcMappingHashMem (baseSlot key : UInt256) : ByteArray :=
  wordAt0Mem key (solcMappingBaseSlotMem baseSlot)

theorem solcMappingBaseSlotMem_size (baseSlot : UInt256) :
    (solcMappingBaseSlotMem baseSlot).size = 96 := by
  simpa [solcMappingBaseSlotMem] using
    (wordAt32Mem_size_96 (mem := solcFreePtrMem) baseSlot solcFreePtrMem_size)

theorem solcMappingBaseSlotMem_read32 (baseSlot : UInt256) :
    (solcMappingBaseSlotMem baseSlot).readWithPadding 32 32 =
      UInt256.toByteArray baseSlot := by
  unfold solcMappingBaseSlotMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray baseSlot).size ≤ 32
    rw [toByteArray_size])

theorem solcMappingBaseSlotMem_read64 (baseSlot : UInt256) :
    (solcMappingBaseSlotMem baseSlot).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcMappingBaseSlotMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]), solcFreePtrMem_read64]

theorem solcMappingHashMem_size (baseSlot key : UInt256) :
    (solcMappingHashMem baseSlot key).size = 96 := by
  simpa [solcMappingHashMem] using
    (wordAt0Mem_size_96 (mem := solcMappingBaseSlotMem baseSlot) key
      (solcMappingBaseSlotMem_size baseSlot))

theorem solcMappingHashMem_read0 (baseSlot key : UInt256) :
    (solcMappingHashMem baseSlot key).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold solcMappingHashMem wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [solcMappingBaseSlotMem_size baseSlot]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem solcMappingHashMem_read32 (baseSlot key : UInt256) :
    (solcMappingHashMem baseSlot key).readWithPadding 32 32 =
      UInt256.toByteArray baseSlot := by
  unfold solcMappingHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [solcMappingBaseSlotMem_size baseSlot]; omega) (by omega)
      (by rw [solcMappingBaseSlotMem_size baseSlot]; omega),
    solcMappingBaseSlotMem_read32]

theorem solcMappingHashMem_read64 (baseSlot key : UInt256) :
    (solcMappingHashMem baseSlot key).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcMappingHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcMappingBaseSlotMem_size baseSlot]; omega) (by omega)
      (by rw [solcMappingBaseSlotMem_size baseSlot]),
    solcMappingBaseSlotMem_read64]

theorem solcMappingHashMem_mload64 (baseSlot key : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcMappingHashMem baseSlot key).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcMappingHashMem baseSlot key).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcMappingHashMem_size]; decide) (by decide)
    (solcMappingHashMem_read64 baseSlot key)

set_option maxHeartbeats 800000 in
theorem solcMappingHashMem_read0_64 (baseSlot key : UInt256) :
    (solcMappingHashMem baseSlot key).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray baseSlot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [solcMappingHashMem_size baseSlot key]; omega)]
  have hleft :
      (solcMappingHashMem baseSlot key).extract 0 32 =
        UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [solcMappingHashMem_size baseSlot key]; omega),
      solcMappingHashMem_read0]
  have hright :
      (solcMappingHashMem baseSlot key).extract 32 64 =
        UInt256.toByteArray baseSlot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [solcMappingHashMem_size baseSlot key]; omega),
      solcMappingHashMem_read32]
  rw [show (solcMappingHashMem baseSlot key).extract 0 64 =
      (solcMappingHashMem baseSlot key).extract 0 32 ++
        (solcMappingHashMem baseSlot key).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

def solcMappingSlot (baseSlot key : UInt256) : UInt256 :=
  uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

theorem solcMappingKeccakSlot (baseSlot key : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((solcMappingHashMem baseSlot key).readWithPadding 0 64)))
      = solcMappingSlot baseSlot key := by
  rw [solcMappingHashMem_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

noncomputable def solcNestedMappingOuterBaseMem (baseSlot owner : UInt256) : ByteArray :=
  wordAt32Mem (solcMappingSlot baseSlot owner) (solcMappingHashMem baseSlot owner)

noncomputable def solcNestedMappingHashMem
    (baseSlot owner spender : UInt256) : ByteArray :=
  wordAt0Mem spender (solcNestedMappingOuterBaseMem baseSlot owner)

theorem solcNestedMappingOuterBaseMem_size (baseSlot owner : UInt256) :
    (solcNestedMappingOuterBaseMem baseSlot owner).size = 96 := by
  simpa [solcNestedMappingOuterBaseMem] using
    (wordAt32Mem_size_96 (mem := solcMappingHashMem baseSlot owner)
      (solcMappingSlot baseSlot owner) (solcMappingHashMem_size baseSlot owner))

theorem solcNestedMappingHashMem_size (baseSlot owner spender : UInt256) :
    (solcNestedMappingHashMem baseSlot owner spender).size = 96 := by
  simpa [solcNestedMappingHashMem] using
    (wordAt0Mem_size_96 (mem := solcNestedMappingOuterBaseMem baseSlot owner)
      spender (solcNestedMappingOuterBaseMem_size baseSlot owner))

theorem solcNestedMappingOuterBaseMem_read32 (baseSlot owner : UInt256) :
    (solcNestedMappingOuterBaseMem baseSlot owner).readWithPadding 32 32 =
      UInt256.toByteArray (solcMappingSlot baseSlot owner) := by
  unfold solcNestedMappingOuterBaseMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [solcMappingHashMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (solcMappingSlot baseSlot owner)).size ≤ 32
    rw [toByteArray_size])

theorem solcNestedMappingOuterBaseMem_read64 (baseSlot owner : UInt256) :
    (solcNestedMappingOuterBaseMem baseSlot owner).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcNestedMappingOuterBaseMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [solcMappingHashMem_size]; omega) (by omega)
      (by rw [solcMappingHashMem_size]),
    solcMappingHashMem_read64]

theorem solcNestedMappingHashMem_read0 (baseSlot owner spender : UInt256) :
    (solcNestedMappingHashMem baseSlot owner spender).readWithPadding 0 32 =
      UInt256.toByteArray spender := by
  unfold solcNestedMappingHashMem wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [solcNestedMappingOuterBaseMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray spender).size ≤ 32
    rw [toByteArray_size])

theorem solcNestedMappingHashMem_read32 (baseSlot owner spender : UInt256) :
    (solcNestedMappingHashMem baseSlot owner spender).readWithPadding 32 32 =
      UInt256.toByteArray (solcMappingSlot baseSlot owner) := by
  unfold solcNestedMappingHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [solcNestedMappingOuterBaseMem_size]; omega) (by omega)
      (by rw [solcNestedMappingOuterBaseMem_size]; omega),
    solcNestedMappingOuterBaseMem_read32]

theorem solcNestedMappingHashMem_read64 (baseSlot owner spender : UInt256) :
    (solcNestedMappingHashMem baseSlot owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcNestedMappingHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcNestedMappingOuterBaseMem_size]; omega) (by omega)
      (by rw [solcNestedMappingOuterBaseMem_size]),
    solcNestedMappingOuterBaseMem_read64]

theorem solcNestedMappingHashMem_mload64 (baseSlot owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcNestedMappingHashMem baseSlot owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcNestedMappingHashMem baseSlot owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcNestedMappingHashMem_size]; decide) (by decide)
    (solcNestedMappingHashMem_read64 baseSlot owner spender)

set_option maxHeartbeats 800000 in
theorem solcNestedMappingHashMem_read0_64 (baseSlot owner spender : UInt256) :
    (solcNestedMappingHashMem baseSlot owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (solcMappingSlot baseSlot owner) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [solcNestedMappingHashMem_size baseSlot owner spender]; omega)]
  have hleft :
      (solcNestedMappingHashMem baseSlot owner spender).extract 0 32 =
        UInt256.toByteArray spender := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [solcNestedMappingHashMem_size baseSlot owner spender]; omega),
      solcNestedMappingHashMem_read0]
  have hright :
      (solcNestedMappingHashMem baseSlot owner spender).extract 32 64 =
        UInt256.toByteArray (solcMappingSlot baseSlot owner) := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [solcNestedMappingHashMem_size baseSlot owner spender]; omega),
      solcNestedMappingHashMem_read32]
  rw [show (solcNestedMappingHashMem baseSlot owner spender).extract 0 64 =
      (solcNestedMappingHashMem baseSlot owner spender).extract 0 32 ++
        (solcNestedMappingHashMem baseSlot owner spender).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem solcNestedMappingKeccakSlot (baseSlot owner spender : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((solcNestedMappingHashMem baseSlot owner spender).readWithPadding 0 64)))
      = solcMappingSlot (solcMappingSlot baseSlot owner) spender := by
  rw [solcNestedMappingHashMem_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single spender (solcMappingSlot baseSlot owner)

noncomputable def solcScratchReturnMem (scratch : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 scratch 128 32

theorem solcScratchReturnMem_size {scratch : ByteArray} (val : UInt256)
    (hscratch : scratch.size = 96) :
    (solcScratchReturnMem scratch val).size = 160 := by
  unfold solcScratchReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hscratch]; omega)
      (by rw [hscratch]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hscratch, ByteArray_zeroes_size,
    toByteArray_size]

theorem solcScratchReturnMem_read64 {scratch : ByteArray} (val : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcScratchReturnMem scratch val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcScratchReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hscratch]; omega)
      (by rw [hscratch]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hscratch, ByteArray_zeroes_size,
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hscratch, ByteArray_zeroes_size]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [hscratch]),
    ← readWithPadding_eq_extract _ 64 (by rw [hscratch]), hread64]

theorem solcScratchReturnMem_mload64 {scratch : ByteArray} (val : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcScratchReturnMem scratch val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcScratchReturnMem scratch val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcScratchReturnMem_size val hscratch]; decide) (by decide)
    (solcScratchReturnMem_read64 val hscratch hread64)

theorem solcScratchReturnMem_read128 {scratch : ByteArray} (val : UInt256)
    (hscratch : scratch.size = 96) :
    (solcScratchReturnMem scratch val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  unfold solcScratchReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hscratch]; omega)
      (by rw [hscratch]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, hscratch, ByteArray_zeroes_size,
        toByteArray_size])]
  rw [extract_append_right_window
      (scratch ++ ffi.ByteArray.zeroes (128 - scratch.size))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, hscratch, ByteArray_zeroes_size])]
  rw [ByteArray.size_append, hscratch, ByteArray_zeroes_size]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

/-! ## Dynamic bytes/string return memory -/

/- Source note: these memory constructors are computable.  They are built from `ByteArray.write`
and word arithmetic; the bytearray layer may still contain FFI-adjacent names, but these helpers
should not be marked `noncomputable` merely because of that naming. -/

def solcBytesReturnAllocSize (len : UInt256) : UInt256 :=
  ⟨32⟩ + (((⟨31⟩ + len) / ⟨32⟩) * ⟨32⟩)

def solcBytesReturnFreePtr (len : UInt256) : UInt256 :=
  ⟨128⟩ + solcBytesReturnAllocSize len

def solcBytesReturnAllocMem (len : UInt256) : ByteArray :=
  (solcBytesReturnFreePtr len).toByteArray.write 0 solcFreePtrMem 64 32

def solcBytesReturnLengthMem (len : UInt256) : ByteArray :=
  len.toByteArray.write 0 (solcBytesReturnAllocMem len) 128 32

def solcBytesReturnPayloadMem (len payloadWord : UInt256) : ByteArray :=
  payloadWord.toByteArray.write 0 (solcBytesReturnLengthMem len) 160 32

def solcBytesReturnPayloadReturnMem (len payloadWord : UInt256) : ByteArray :=
  len.toByteArray.write 0 (solcBytesReturnPayloadMem len payloadWord) 192 32

theorem solcBytesReturnAllocMem_size (len : UInt256) :
    (solcBytesReturnAllocMem len).size = 96 := by
  have hEq :
      solcBytesReturnAllocMem len =
        solcFreePtrMem.extract 0 64 ++ UInt256.toByteArray (solcBytesReturnFreePtr len) ++
          solcFreePtrMem.extract 96 solcFreePtrMem.size := by
    rw [solcBytesReturnAllocMem,
      write32_eq (UInt256.toByteArray (solcBytesReturnFreePtr len)) solcFreePtrMem 64
        (by rw [toByteArray_size])
        (by rw [solcFreePtrMem_size]; decide)]
    rw [toByteArray_extract_all]
  rw [hEq, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, solcFreePtrMem_size]
  omega

theorem solcBytesReturnLengthMem_size (len : UInt256) :
    (solcBytesReturnLengthMem len).size = 160 := by
  rw [solcBytesReturnLengthMem,
    toByteArray_write_eq _ _ _ (by rw [solcBytesReturnAllocMem_size]; decide)
      (by rw [solcBytesReturnAllocMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, solcBytesReturnAllocMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem solcBytesReturnLengthMem_read128 (len : UInt256) :
    (solcBytesReturnLengthMem len).readWithPadding 128 32 = UInt256.toByteArray len := by
  rw [readWithPadding_eq_extract _ _ (by have := solcBytesReturnLengthMem_size len; omega),
    solcBytesReturnLengthMem,
    toByteArray_write_eq _ _ _
      (by rw [solcBytesReturnAllocMem_size]; decide)
      (by rw [solcBytesReturnAllocMem_size]; exact lt_usize _ (by norm_num)),
    extract_append_right' _ _ _ _
      (by
        rw [ByteArray.size_append, solcBytesReturnAllocMem_size,
          zeroes_ofNat_size _ (by norm_num)])
      (by
        rw [ByteArray.size_append, solcBytesReturnAllocMem_size,
          zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

theorem solcBytesReturnAllocMem_read64 (len : UInt256) :
    (solcBytesReturnAllocMem len).readWithPadding 64 32 =
      UInt256.toByteArray (solcBytesReturnFreePtr len) := by
  rw [solcBytesReturnAllocMem]
  rw [write32_read_back (UInt256.toByteArray (solcBytesReturnFreePtr len)) solcFreePtrMem 64
    (by rw [toByteArray_size])
    (by rw [solcFreePtrMem_size]; decide)]
  rw [toByteArray_extract_all]

theorem solcBytesReturnLengthMem_read64 (len : UInt256) :
    (solcBytesReturnLengthMem len).readWithPadding 64 32 =
      UInt256.toByteArray (solcBytesReturnFreePtr len) := by
  rw [readWithPadding_eq_extract _ _ (by have := solcBytesReturnLengthMem_size len; omega),
    solcBytesReturnLengthMem,
    toByteArray_write_eq _ _ _
      (by rw [solcBytesReturnAllocMem_size]; decide)
      (by rw [solcBytesReturnAllocMem_size]; exact lt_usize _ (by norm_num)),
    extract_append_left _ _ _ _
      (by
        rw [ByteArray.size_append, solcBytesReturnAllocMem_size,
          zeroes_ofNat_size _ (by norm_num)]
        omega),
    extract_append_left _ _ _ _
      (by rw [solcBytesReturnAllocMem_size]),
    ← readWithPadding_eq_extract _ _ (by have := solcBytesReturnAllocMem_size len; omega),
    solcBytesReturnAllocMem_read64]

theorem solcBytesReturnPayloadMem_read128 (len payloadWord : UInt256) :
    (solcBytesReturnPayloadMem len payloadWord).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  rw [solcBytesReturnPayloadMem]
  rw [write32_read_below (UInt256.toByteArray payloadWord)
    (solcBytesReturnLengthMem len) 160 128
    (by rw [toByteArray_size])
    (by rw [solcBytesReturnLengthMem_size])
    (by decide)]
  exact solcBytesReturnLengthMem_read128 len

theorem solcBytesReturnPayloadMem_size (len payloadWord : UInt256) :
    (solcBytesReturnPayloadMem len payloadWord).size = 192 := by
  rw [solcBytesReturnPayloadMem,
    toByteArray_write_eq _ _ _ (by rw [solcBytesReturnLengthMem_size])
      (by rw [solcBytesReturnLengthMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, solcBytesReturnLengthMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem solcBytesReturnPayloadMem_read64 (len payloadWord : UInt256) :
    (solcBytesReturnPayloadMem len payloadWord).readWithPadding 64 32 =
      UInt256.toByteArray (solcBytesReturnFreePtr len) := by
  rw [solcBytesReturnPayloadMem]
  rw [write32_read_below (UInt256.toByteArray payloadWord)
    (solcBytesReturnLengthMem len) 160 64
    (by rw [toByteArray_size])
    (by rw [solcBytesReturnLengthMem_size])
    (by decide)]
  exact solcBytesReturnLengthMem_read64 len

theorem solcBytesReturnPayloadMem_mload64 (len payloadWord freePtr aw : UInt256)
    (hfree : solcBytesReturnFreePtr len = freePtr)
    (haw : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcBytesReturnPayloadMem len payloadWord).size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((solcBytesReturnPayloadMem len payloadWord).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := aw) (v := freePtr)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      solcBytesReturnPayloadMem_size]; decide)
    haw
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hfree] using
      solcBytesReturnPayloadMem_read64 len payloadWord)

theorem solcBytesReturnPayloadMem_mload128 (len payloadWord aw : UInt256)
    (haw : ¬ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩) :
    (if (⟨128⟩ : UInt256).toNat ≥ (solcBytesReturnPayloadMem len payloadWord).size
        ∨ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((solcBytesReturnPayloadMem len payloadWord).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := aw) (v := len)
    (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      solcBytesReturnPayloadMem_size]; decide)
    haw
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      solcBytesReturnPayloadMem_read128 len payloadWord)

theorem solcBytesReturnPayloadReturnMem_size (len payloadWord : UInt256) :
    (solcBytesReturnPayloadReturnMem len payloadWord).size = 224 := by
  rw [solcBytesReturnPayloadReturnMem,
    toByteArray_write_eq _ _ _ (by rw [solcBytesReturnPayloadMem_size])
      (by rw [solcBytesReturnPayloadMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, solcBytesReturnPayloadMem_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem solcBytesReturnPayloadReturnMem_read64 (len payloadWord : UInt256) :
    (solcBytesReturnPayloadReturnMem len payloadWord).readWithPadding 64 32 =
      UInt256.toByteArray (solcBytesReturnFreePtr len) := by
  rw [solcBytesReturnPayloadReturnMem]
  rw [write32_read_below (UInt256.toByteArray len)
    (solcBytesReturnPayloadMem len payloadWord) 192 64
    (by rw [toByteArray_size])
    (by rw [solcBytesReturnPayloadMem_size])
    (by decide)]
  exact solcBytesReturnPayloadMem_read64 len payloadWord

theorem solcBytesReturnPayloadReturnMem_mload64 (len payloadWord freePtr aw : UInt256)
    (hfree : solcBytesReturnFreePtr len = freePtr)
    (haw : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcBytesReturnPayloadReturnMem len payloadWord).size
        ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((solcBytesReturnPayloadReturnMem len payloadWord).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = freePtr := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := aw) (v := freePtr)
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      solcBytesReturnPayloadReturnMem_size]; decide)
    haw
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hfree] using
      solcBytesReturnPayloadReturnMem_read64 len payloadWord)

theorem solcBytesReturnPayloadReturnMem_read192 (len payloadWord : UInt256) :
    (solcBytesReturnPayloadReturnMem len payloadWord).readWithPadding 192 32 =
      UInt256.toByteArray len := by
  rw [readWithPadding_eq_extract _ _ (by
      have := solcBytesReturnPayloadReturnMem_size len payloadWord
      omega),
    solcBytesReturnPayloadReturnMem,
    toByteArray_write_eq _ _ _
      (by rw [solcBytesReturnPayloadMem_size])
      (by rw [solcBytesReturnPayloadMem_size]; exact lt_usize _ (by norm_num)),
    extract_append_right' _ _ _ _
      (by
        rw [ByteArray.size_append, solcBytesReturnPayloadMem_size,
          zeroes_ofNat_size _ (by norm_num)])
      (by
        rw [ByteArray.size_append, solcBytesReturnPayloadMem_size,
          zeroes_ofNat_size _ (by norm_num), toByteArray_size])]

theorem solcBytesReturnFreePtr_eq_192_of_short_nonzero {len : UInt256}
    (hnonzero : len ≠ ⟨0⟩) (hlt32 : len.toNat < 32) :
    solcBytesReturnFreePtr len = ⟨192⟩ := by
  have hpos : 0 < len.toNat := by
    cases hzero : len.toNat
    · exact False.elim (hnonzero (uint256_toNat_eq_zero hzero))
    · omega
  have h31len :
      ((⟨31⟩ : UInt256) + len).toNat = 31 + len.toNat := by
    rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_eq_of_lt (by norm_num [UInt256.size]; omega)
  have hdivNat :
      (((⟨31⟩ : UInt256) + len) / ⟨32⟩).toNat = 1 := by
    change (((⟨31⟩ : UInt256) + len).toNat / 32) = 1
    rw [h31len]
    have hge : 32 ≤ 31 + len.toNat := by omega
    have hlt : 31 + len.toNat < 64 := by omega
    have hposDiv : 0 < (31 + len.toNat) / 32 := Nat.div_pos hge (by decide)
    have hltDiv : (31 + len.toNat) / 32 < 2 := by
      exact Nat.div_lt_of_lt_mul (by omega)
    omega
  have hdiv :
      (((⟨31⟩ : UInt256) + len) / ⟨32⟩) = ⟨1⟩ := by
    apply u256_inj
    simpa [show (⟨1⟩ : UInt256).toNat = 1 from rfl] using hdivNat
  rw [solcBytesReturnFreePtr, solcBytesReturnAllocSize, hdiv]
  native_decide

/-! ## Dynamic bytes/string calldata copy memory -/

def solcBytesSetCalldataMem
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  cd.write payloadStart.toNat (solcBytesReturnLengthMem len) 160 len.toNat

def solcBytesSetPaddedMem
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (solcBytesSetCalldataMem cd len payloadStart) (((⟨160⟩ : UInt256) + len).toNat) 32

theorem solcBytesSetCalldataMem_read128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (solcBytesSetCalldataMem cd len payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  have hpres := write_read_below_end_from cd (solcBytesReturnLengthMem len)
    payloadStart.toNat len.toNat 128 hlen hsrc (by
      rw [solcBytesReturnLengthMem_size])
  rw [solcBytesSetCalldataMem, ← solcBytesReturnLengthMem_size len]
  exact hpres.trans (solcBytesReturnLengthMem_read128 len)

theorem solcBytesSetCalldataMem_read64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (solcBytesSetCalldataMem cd len payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (solcBytesReturnFreePtr len) := by
  have hpres := write_read_below_end_from cd (solcBytesReturnLengthMem len)
    payloadStart.toNat len.toNat 64 hlen hsrc (by
      rw [solcBytesReturnLengthMem_size]
      decide)
  rw [solcBytesSetCalldataMem, ← solcBytesReturnLengthMem_size len]
  exact hpres.trans (solcBytesReturnLengthMem_read64 len)

theorem solcBytesSetCalldataMem_size
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (solcBytesSetCalldataMem cd len payloadStart).size = 160 + len.toNat := by
  rw [solcBytesSetCalldataMem]
  have hsize := write_end_size_from cd (solcBytesReturnLengthMem len)
    payloadStart.toNat len.toNat hlen hsrc
  rw [solcBytesReturnLengthMem_size] at hsize
  simpa using hsize

set_option maxHeartbeats 800000 in
theorem solcBytesSetCalldataMem_extract_payload
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (solcBytesSetCalldataMem cd len payloadStart).extract 160 (160 + len.toNat) =
      cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat) := by
  rw [solcBytesSetCalldataMem, ← solcBytesReturnLengthMem_size len]
  exact write_end_extract_tail_from cd (solcBytesReturnLengthMem len)
    payloadStart.toNat len.toNat hlen hsrc

theorem solcBytesSetCalldataMem_read_payload_word
    (cd : ByteArray) (len payloadStart : UInt256) (i : Nat)
    (hnz : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hi : i < len.toNat / 32) :
    (solcBytesSetCalldataMem cd len payloadStart).readWithPadding (160 + 32 * i) 32 =
      (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).extract
        (32 * i) (32 * i + 32) := by
  have hfull : 32 * i + 32 ≤ len.toNat := by
    have hlt : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
      Nat.mul_le_mul_left 32 hlt
    have hle : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    nlinarith
  have hreadIn :
      160 + 32 * i + 32 ≤ (solcBytesSetCalldataMem cd len payloadStart).size := by
    rw [solcBytesSetCalldataMem_size cd len payloadStart hnz hsrc]
    omega
  rw [readWithPadding_eq_extract _ (160 + 32 * i) hreadIn]
  have hleft :
      (solcBytesSetCalldataMem cd len payloadStart).extract (160 + 32 * i)
          (160 + 32 * i + 32) =
        ((solcBytesSetCalldataMem cd len payloadStart).extract 160
          (160 + len.toNat)).extract (32 * i) (32 * i + 32) := by
    rw [extract_extract_BA]
    rw [show 160 + 32 * i = 160 + (32 * i) by omega]
    rw [show min (160 + (32 * i + 32)) (160 + len.toNat) =
        160 + 32 * i + 32 by omega]
  rw [hleft]
  rw [solcBytesSetCalldataMem_extract_payload cd len payloadStart hnz hsrc]

theorem solcBytesSetDataEnd_toNat_of_short {len : UInt256}
    (hshort : len.toNat < 32) :
    (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat := by
  rw [uadd_toNat]
  rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
  exact Nat.mod_eq_of_lt (by
    have hle : 160 + len.toNat < 192 := by omega
    exact lt_of_lt_of_le hle (by norm_num [UInt256.size]))

theorem solcBytesSetDataEnd_toNat_of_u64 {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat := by
  rw [uadd_toNat]
  rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
  exact Nat.mod_eq_of_lt (by
    have hmax : ABI.solcMaxU64 + 160 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega)

theorem solcBytesSetPaddedMem_read128
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (solcBytesSetPaddedMem cd len payloadStart).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  rw [solcBytesSetPaddedMem]
  rw [write32_read_below (UInt256.toByteArray (⟨0⟩ : UInt256))
    (solcBytesSetCalldataMem cd len payloadStart)
    (((⟨160⟩ : UInt256) + len).toNat) 128
    (by rw [toByteArray_size])
    (by
      rw [hadd, solcBytesSetCalldataMem_size cd len payloadStart hlen hsrc])
    (by rw [hadd]; omega)]
  exact solcBytesSetCalldataMem_read128 cd len payloadStart hlen hsrc

theorem solcBytesSetPaddedMem_read64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (solcBytesSetPaddedMem cd len payloadStart).readWithPadding 64 32 =
      UInt256.toByteArray (solcBytesReturnFreePtr len) := by
  rw [solcBytesSetPaddedMem]
  rw [write32_read_below (UInt256.toByteArray (⟨0⟩ : UInt256))
    (solcBytesSetCalldataMem cd len payloadStart)
    (((⟨160⟩ : UInt256) + len).toNat) 64
    (by rw [toByteArray_size])
    (by
      rw [hadd, solcBytesSetCalldataMem_size cd len payloadStart hlen hsrc])
    (by rw [hadd]; omega)]
  exact solcBytesSetCalldataMem_read64 cd len payloadStart hlen hsrc

theorem solcBytesSetPaddedMem_size_ge160
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    160 ≤ (solcBytesSetPaddedMem cd len payloadStart).size := by
  rw [solcBytesSetPaddedMem]
  have hbase := solcBytesSetCalldataMem_size cd len payloadStart hlen hsrc
  rw [toByteArray_write_eq (⟨0⟩ : UInt256)
    (solcBytesSetCalldataMem cd len payloadStart)
    (((⟨160⟩ : UInt256) + len).toNat)
    (by rw [hadd, hbase])
    (by
      rw [hadd, hbase]
      rw [show 160 + len.toNat - (160 + len.toNat) = 0 by omega]
      exact lt_usize 0 (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, hbase, toByteArray_size, hadd]
  rw [show ffi.ByteArray.zeroes (160 + len.toNat - (160 + len.toNat)) =
      ByteArray.empty by
        rw [show 160 + len.toNat - (160 + len.toNat) = 0 by omega]
        exact zeroes_zero (n := 0) (by rfl),
    ByteArray.size_empty]
  omega

theorem solcBytesSetPaddedMem_size
    (cd : ByteArray) (len payloadStart : UInt256)
    (hlen : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hadd : (((⟨160⟩ : UInt256) + len).toNat) = 160 + len.toNat) :
    (solcBytesSetPaddedMem cd len payloadStart).size = 192 + len.toNat := by
  rw [solcBytesSetPaddedMem]
  have hbase := solcBytesSetCalldataMem_size cd len payloadStart hlen hsrc
  rw [toByteArray_write_eq (⟨0⟩ : UInt256)
    (solcBytesSetCalldataMem cd len payloadStart)
    (((⟨160⟩ : UInt256) + len).toNat)
    (by rw [hadd, hbase])
    (by
      rw [hadd, hbase]
      rw [show 160 + len.toNat - (160 + len.toNat) = 0 by omega]
      exact lt_usize 0 (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, hbase, toByteArray_size, hadd]
  rw [show ffi.ByteArray.zeroes (160 + len.toNat - (160 + len.toNat)) =
      ByteArray.empty by
        rw [show 160 + len.toNat - (160 + len.toNat) = 0 by omega]
        exact zeroes_zero (n := 0) (by rfl),
    ByteArray.size_empty]
  omega

theorem solcBytesSetPaddedMem_read_payload_word
    (cd : ByteArray) (len payloadStart : UInt256) (i : Nat)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hi : i < len.toNat / 32) :
    (solcBytesSetPaddedMem cd len payloadStart).readWithPadding (160 + 32 * i) 32 =
      (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).extract
        (32 * i) (32 * i + 32) := by
  have hfull : 32 * i + 32 ≤ len.toNat := by
    have hlt : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
      Nat.mul_le_mul_left 32 hlt
    have hle : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    nlinarith
  rw [solcBytesSetPaddedMem]
  rw [write32_read_below (UInt256.toByteArray (⟨0⟩ : UInt256))
    (solcBytesSetCalldataMem cd len payloadStart) (((⟨160⟩ : UInt256) + len).toNat)
    (160 + 32 * i)
    (by rw [toByteArray_size])
    (by rw [solcBytesSetDataEnd_toNat_of_u64 hlenMax,
      solcBytesSetCalldataMem_size cd len payloadStart hnz hsrc])
    (by rw [solcBytesSetDataEnd_toNat_of_u64 hlenMax]; omega)]
  exact solcBytesSetCalldataMem_read_payload_word cd len payloadStart i hnz hsrc hi

set_option maxHeartbeats 800000 in
theorem solcBytesSetPaddedMem_read160_short_toList
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    ((solcBytesSetPaddedMem cd len payloadStart).readWithPadding 160 32).toList =
      (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).toList ++
        List.replicate (32 - len.toNat) 0 := by
  have hadd := solcBytesSetDataEnd_toNat_of_short (len := len) hshort
  have hbaseSize := solcBytesSetCalldataMem_size cd len payloadStart hnz hsrc
  have hread :
      (solcBytesSetPaddedMem cd len payloadStart).readWithPadding 160 32 =
        ((solcBytesSetCalldataMem cd len payloadStart).extract 160 (160 + len.toNat) ++
          (UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 (32 - len.toNat)) := by
    rw [solcBytesSetPaddedMem]
    simpa [hadd, hbaseSize, show 160 + 32 - (160 + len.toNat) = 32 - len.toNat by omega]
      using
        write32_read_span_end (UInt256.toByteArray (⟨0⟩ : UInt256))
          (solcBytesSetCalldataMem cd len payloadStart) 160
          (by rw [toByteArray_size])
          (by rw [hbaseSize]; omega)
          (by rw [hbaseSize]; omega)
  rw [hread]
  rw [solcBytesSetCalldataMem_extract_payload cd len payloadStart hnz hsrc]
  rw [byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append]
  rw [byteArray_toList_eq (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat))]
  rw [zero_toByteArray_eq_zeroes32]
  rw [zeroes32_extract_zeroes (32 - len.toNat) (by omega)]
  rw [byteArray_zeroes_toList]

/-! ## Shared bytecode-sequence lemmas

Trace segments that recur byte-for-byte across solc output, factored once so every contract reuses
them.  The non-payable guard prologue is exposed as an `RD` producer (`solcGuardPrologueRD`) that
chains directly into an `evm_run` dispatcher fold; the rest are supporting cost/selector facts. -/

/-- The `revert(0,0)` memory-expansion cost is `0` for any state whose top two stack words are `0`
    (offset/size `0` ⇒ `M` does not grow ⇒ cost `0`), independent of `activeWords`. -/
theorem memExpRevert0 (s : State) {t : List UInt256}
    (hstk : s.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: t) :
    memoryExpansionCost s .REVERT = 0 := by
  have hlt : s.machineState.activeWords.toNat < UInt256.size := by
    show s.machineState.activeWords.val.val < UInt256.size
    exact s.machineState.activeWords.val.isLt
  have hof : UInt256.ofNat s.machineState.activeWords.toNat = s.machineState.activeWords :=
    u256_inj (by show (Fin.ofNat _ _).val = _
                 simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hlt)
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk,
    List.getElem!_cons_zero, List.getElem!_cons_succ,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, MachineState.M, hof, Nat.sub_self]

/-- `REVERT` (or `RETURN`) memory-expansion cost when the **offset is zero** and the length `len` is
    arbitrary (e.g. the post-call `RETURNDATACOPY`+`REVERT` failure tail copies/reverts the whole
    return buffer at offset 0).  Unlike `memExpRevert0` the cost is *not* zero, so it is returned
    symbolically in terms of the carried active-words. -/
theorem memExpRevertZeroOff (s : State) {len : UInt256} {t : List UInt256}
    (hstk : s.machineState.stack = ⟨0⟩ :: len :: t) :
    memoryExpansionCost s .REVERT
      = Cₘ (UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat 0 len.toNat))
        - Cₘ s.machineState.activeWords := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk,
    List.getElem!_cons_zero, List.getElem!_cons_succ, show (⟨0⟩ : UInt256).toNat = 0 from rfl]

/-- **The solc guard prologue** (`PUSH1 0x80; PUSH1 0x40; MSTORE; CALLVALUE; DUP1; ISZERO`, byte-
    identical for every solc contract) as a **producer of the `RD` invariant** (compositional):
    `initState → RD … ⟨8⟩ [isZero(callvalue), callvalue]` so a dispatcher fold can chain straight off
    it. -/
theorem solcGuardPrologueRD {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (hd0 : decode code ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)))
    (hd2 : decode code ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd4 : decode code ⟨4⟩ = some (.MSTORE, .none))
    (hd5 : decode code ⟨5⟩ = some (.CALLVALUE, .none))
    (hd6 : decode code ⟨6⟩ = some (.DUP1, .none))
    (hd7 : decode code ⟨7⟩ = some (.ISZERO, .none)) :
    RD code I g (initState cA gh bl σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) 6 26 := by
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]
  have hcode0 : s0.executionEnv.code = code := by rw [hee0]; exact hcode
  have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hgas0 : s0.machineState.gasAvailable = g.subNat 0 := by rw [hs0]; simp [initState, Sat256.subNat]
  have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl
  have haw0 : s0.machineState.activeWords = UInt256.ofNat 0 := by rw [hs0]; simp [initState]; rfl
  have hmem0 : s0.machineState.memory = ByteArray.empty := by rw [hs0]; simp [initState]; rfl
  have hrdata0 : s0.machineState.returnData = ByteArray.empty := by rw [hs0]; simp [initState]; rfl
  have hacc0 : (s0.createdAccounts, s0.accountMap) = (cA, σ) := by rw [hs0]; simp [initState]
  have hX0 : X (g.toNat + 1) (D_J code 0) s0 = X (g.toNat + 1 - 0) (D_J code 0) s0 := rfl
  -- PUSH1 0x80 · PUSH1 0x40 · MSTORE (install free pointer) · CALLVALUE · DUP1 · ISZERO ⇒ pc 8
  exact RD.startWith (rdata := ByteArray.empty) hcode0 hpc0 hstk0 hgas0 (by omega) (by omega) hX0
        hmem0 haw0 hrdata0 hacc0 hee0 ⟨rfl, rfl, rfl⟩
      |>.push1 ⟨128⟩ hd0 (by decide)
      |>.push1 ⟨64⟩ hd2 (by decide)
      |>.mstore 9 solcFreePtrMem (UInt256.ofNat 3) hd4
        mem_cost
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
        (by decide) (by decide)
      |>.callvalue hd5 (by decide)
      |>.dup1 hd6 (by simp only [List.length_nil]; omega)
      |>.iszero hd7 (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## solc address cleanup (the 160-bit mask)

Every solc-compiled function masks `address` values with the 160-bit mask `0xff…ff` (built by the
optimizer as `PUSH1 1; PUSH1 160; SHL; SUB`) to clean the high 96 bits.  These facts couple that
mask to address canonicality (`< 2^160`). -/

/-- The address-cleanup mask literal `2^160 - 1`, shared by every solc contract. -/
def solcAddrMask : UInt256 := ⟨1461501637330902918203684832716283019655932542975⟩

/-- The canonical EVM word for `CALLER`/`msg.sender`. -/
abbrev solcSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

theorem solcSourceWord_toNat (I : ExecutionEnv) :
    (solcSourceWord I).toNat = I.source.val := by
  unfold solcSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem solcSourceWord_canonical (I : ExecutionEnv) :
    (solcSourceWord I).toNat < EVM.addressModulus := by
  rw [solcSourceWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem solcSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (solcSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [solcSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem solcMaskedAddress_eq_source_of_word_eq {w : UInt256} {I : ExecutionEnv}
    (h : UInt256.land w solcAddrMask = solcSourceWord I) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source := by
  rw [h, solcSource_ofNat]

@[reducible] def solcCallerTransferThunkWf
    (code : ByteArray) (pc contPc routinePc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p6 := p3 + UInt256.ofNat 3
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p12 := p9 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH2, some (contPc, 2))
  ∧ decode code p6 = some (.CALLER, .none)
  ∧ decode code p7 = some (.DUP5, .none)
  ∧ decode code p8 = some (.DUP5, .none)
  ∧ decode code p9 = some (.Push .PUSH2, some (routinePc, 2))
  ∧ decode code p12 = some (.JUMP, .none)

theorem RD.solcCallerTransferThunk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc contPc routinePc value toWord ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (value :: toWord :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCallerTransferThunkWf code pc contPc routinePc)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routinePc
      (value :: toWord :: solcSourceWord ee :: contPc :: ⟨0⟩ :: value :: toWord :: ret :: R)
      mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd6, hd7, hd8, hd9, hd12⟩
  have rd12 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨0⟩ hd1 (by evm_ov),
    raw push2 contPc hd3 (by evm_ov),
    raw caller hd6 (by evm_ov),
    raw dup5 hd7 (by evm_ov),
    raw dup5 hd8 (by evm_ov),
    raw push2 routinePc hd9 (by evm_ov)]
  exact ⟨_, _, by simpa [solcSourceWord] using rd12.jump hd12 hroutine (by evm_ov)⟩

@[reducible] def solcInternalCallSetup3Wf
    (code : ByteArray) (pc contPc routinePc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (contPc, 2))
  ∧ decode code p4 = some (.DUP5, .none)
  ∧ decode code p5 = some (.DUP5, .none)
  ∧ decode code p6 = some (.DUP5, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (routinePc, 2))
  ∧ decode code p10 = some (.JUMP, .none)

theorem RD.solcInternalCallSetup3 {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc contPc routinePc discard a b c ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (discard :: a :: b :: c :: ret :: R) mem aw rdata acc k C)
    (hwf : solcInternalCallSetup3Wf code pc contPc routinePc)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routinePc
      (a :: b :: c :: contPc :: discard :: a :: b :: c :: ret :: R)
      mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd4, hd5, hd6, hd7, hd10⟩
  have rd10 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push2 contPc hd1 (by evm_ov),
    raw dup5 hd4 (by evm_ov),
    raw dup5 hd5 (by evm_ov),
    raw dup5 hd6 (by evm_ov),
    raw push2 routinePc hd7 (by evm_ov)]
  exact ⟨_, _, rd10.jump hd10 hroutine (by evm_ov)⟩

/-- Reading the low 20 bytes of a little-endian EVM word is the solc address mask. -/
theorem fromBytes'_take20_wordLE_solcAddrMask (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 20) =
      (UInt256.land w solcAddrMask).toNat := by
  simpa [solcAddrMask] using
    fromBytes'_take_wordLE_land_mask w 20 (by decide)

set_option maxHeartbeats 1000000 in
/-- Reading an arbitrary little-endian byte window of an EVM word is the corresponding
    divide-and-mask operation. -/
theorem fromBytes'_drop_take_wordLE_land_div_mask (w : UInt256) (off size : Nat)
    (hoff : 8 * off < 256) (hsize : 8 * size ≤ 256) :
    fromBytes' (((EVM.Word.toBytesLEWithSizeProof w).1.drop off).take size) =
      (UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ off)))
        (UInt256.ofNat (256 ^ size - 1))).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have hdrop := Nat.ofDigits_div_pow_eq_ofDigits_drop (p := 256) off (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) size (by decide)
    ((bs.map (fun b : UInt8 => b.toNat)).drop off)
    (fun l hl => hlt l (List.mem_of_mem_drop hl))
  rw [fromBytes'_eq_ofDigits (((EVM.Word.toBytesLEWithSizeProof w).1.drop off).take size)]
  change Nat.ofDigits 256 ((((bs.drop off).take size).map fun b : UInt8 => b.toNat)) = _
  rw [List.map_take, List.map_drop, ← htake, ← hdrop, hfull]
  have hshiftNat : (UInt256.ofNat (256 ^ off)).toNat = 256 ^ off := by
    rw [show 256 ^ off = (2 : Nat) ^ (8 * off) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    exact ofNat_pow_toNat hoff
  have hdivNat : (UInt256.div w (UInt256.ofNat (256 ^ off))).toNat =
      w.toNat / 256 ^ off := by
    unfold UInt256.div UInt256.toNat
    simp only
    change w.toNat / (UInt256.ofNat (256 ^ off)).toNat = w.toNat / 256 ^ off
    rw [hshiftNat]
  rw [uland_toNat, hdivNat]
  have hmaskNat : (UInt256.ofNat (256 ^ size - 1)).toNat = 256 ^ size - 1 := by
    have hmaskLt : 256 ^ size - 1 < UInt256.size := by
      have hpow : 256 ^ size ≤ UInt256.size := by
        rw [show 256 ^ size = (2 : Nat) ^ (8 * size) by
          rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
        simpa [UInt256.size] using
          Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) hsize
      have hpos : 0 < 256 ^ size := by positivity
      omega
    exact ulit_toNat' _ hmaskLt
  rw [hmaskNat]
  rw [show 256 ^ size = (2 : Nat) ^ (8 * size) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
  symm
  exact nat_land_mask_eq_mod (w.toNat / 256 ^ off) (8 * size)

/-- Reading bytes `[1, 21)` of a little-endian EVM word is the address mask after dropping
    the low byte. -/
theorem fromBytes'_drop1_take20_wordLE_solcAddrMask (w : UInt256) :
    fromBytes' (((EVM.Word.toBytesLEWithSizeProof w).1.drop 1).take 20) =
      (UInt256.land (UInt256.div w ⟨256⟩) solcAddrMask).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have hdrop := Nat.ofDigits_div_pow_eq_ofDigits_drop (p := 256) 1 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 20 (by decide)
    ((bs.map (fun b : UInt8 => b.toNat)).drop 1)
    (fun l hl => hlt l (List.mem_of_mem_drop hl))
  rw [fromBytes'_eq_ofDigits (((EVM.Word.toBytesLEWithSizeProof w).1.drop 1).take 20)]
  change Nat.ofDigits 256 ((((bs.drop 1).take 20).map fun b : UInt8 => b.toNat)) = _
  rw [List.map_take, List.map_drop, ← htake, ← hdrop, hfull]
  show w.toNat / 256 % 256 ^ 20 =
    (Nat.land (UInt256.div w ⟨256⟩).toNat solcAddrMask.toNat) % UInt256.size
  unfold UInt256.div UInt256.toNat
  simp only
  change w.toNat / 256 % 256 ^ 20 = Nat.land (w.toNat / 256) solcAddrMask.toNat % UInt256.size
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  have hsmall : w.toNat / 256 % 2 ^ 160 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160)) (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

/-- A canonical address word (`< 2^160`) is unchanged by the solc address mask, so `EQ` returns `1`. -/
theorem solcAddrCanon_eq {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.eq w (UInt256.land w solcAddrMask) = ⟨1⟩ := by
  have hland : UInt256.land w solcAddrMask = w := by
    apply u256_inj
    show Nat.land w.toNat solcAddrMask.toNat % EVM.twoPow 256 = w.toNat
    rw [show solcAddrMask.toNat = 2 ^ 160 - 1 from by decide,
      land_mask160 _ (by
        rw [show EVM.addressModulus = 2 ^ 160 from by decide] at hcanon
        exact hcanon)]
    exact Nat.mod_eq_of_lt (by
      change w.val.val < EVM.twoPow 256
      exact w.val.isLt)
  rw [hland]; exact uInt256_eq_self w

/-- Conversely, a word the mask leaves unchanged (solc's `EQ = 1`) is a canonical address. -/
theorem solcAddrCanonical_of_clean {w : UInt256}
    (hclean : UInt256.eq w (UInt256.land w solcAddrMask) = ⟨1⟩) :
    w.toNat < EVM.addressModulus := by
  have heq : w = UInt256.land w solcAddrMask := by
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
      Bool.false_eq_true, ↓reduceIte] at hclean
    exact absurd hclean (by decide)
  have hland : w.toNat = Nat.land w.toNat solcAddrMask.toNat % EVM.twoPow 256 := by
    conv_lhs => rw [heq]
    rfl
  have hlandle := nat_land_le_right w.toNat solcAddrMask.toNat
  have hmod : Nat.land w.toNat solcAddrMask.toNat % EVM.twoPow 256 =
      Nat.land w.toNat solcAddrMask.toNat :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt hlandle (by decide))
  have hmask : solcAddrMask.toNat < EVM.addressModulus := by decide
  rw [hland, hmod]; exact lt_of_le_of_lt hlandle hmask

/-- Applying solc's address mask always yields a canonical address-sized word. -/
theorem solcAddrMask_result_canonical (w : UInt256) :
    (UInt256.land w solcAddrMask).toNat < EVM.addressModulus := by
  show Nat.land w.toNat solcAddrMask.toNat % UInt256.size < EVM.addressModulus
  have hle := nat_land_le_right w.toNat solcAddrMask.toNat
  have hltSize : Nat.land w.toNat solcAddrMask.toNat < UInt256.size :=
    lt_of_le_of_lt hle (by decide)
  rw [Nat.mod_eq_of_lt hltSize]
  exact lt_of_le_of_lt hle (by decide)

/-- ABI-encoding a solc-masked address return is exactly the masked 32-byte word. -/
theorem solcAddressReturnEncoding {addrTy : ABIType} (haddr : addrTy = .elem .address)
    (w : UInt256) :
    encodeReturnValue? addrTy
        (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask)) := by
  subst addrTy
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask :=
    u256_ofNat_toNat _
  refine scalarReturnEncoding (t := .address) (w := UInt256.land w solcAddrMask) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

/-- A canonical address word is left unchanged by the solc address mask (mask on the right). -/
theorem solcAddrMask_clean {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.land w solcAddrMask = w := by
  apply u256_inj
  show Nat.land w.toNat solcAddrMask.toNat % EVM.twoPow 256 = w.toNat
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 from by decide,
    land_mask160 _ (by
      rw [show EVM.addressModulus = 2 ^ 160 from by decide] at hcanon
      exact hcanon)]
  exact Nat.mod_eq_of_lt (by
    change w.val.val < EVM.twoPow 256
    exact w.val.isLt)

/-- Same, with the mask on the left (`AND` is commutative). -/
theorem solcAddrMask_clean_left {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.land solcAddrMask w = w := by
  apply u256_inj
  show Nat.land solcAddrMask.toNat w.toNat % EVM.twoPow 256 = w.toNat
  rw [show Nat.land solcAddrMask.toNat w.toNat = Nat.land w.toNat solcAddrMask.toNat
    from Nat.and_comm _ _]
  show Nat.land w.toNat solcAddrMask.toNat % EVM.twoPow 256 = w.toNat
  exact congrArg UInt256.toNat (solcAddrMask_clean hcanon)

set_option maxHeartbeats 1000000 in
theorem RD.solcExternalStaticArgsLenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {sel entry ret decoded need : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.Push .PUSH2, some (ret, 2)))
    (hd4 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3) =
        some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd6 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hd7 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATASIZE, .none))
    (hd8 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.SUB, .none))
    (hd9 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (need, 1)))
    (hd11 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hd12 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hd13 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hd14 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (decoded, 2)))
    (hd17 :
      decode code
          ((entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hdecoded : (D_J code 0).contains decoded = true)
    (hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) need = ⟨0⟩) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) decoded
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) need) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 need hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13 := rd12.lt hd12 (by evm_ov)
  have rd14 := rd13.iszero hd13 (by evm_ov)
  have rd17 := rd14.push2 decoded hd14 (by evm_ov)
  exact ⟨_, _, rd17.jumpiT hd17 hjumpCond hdecoded (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcOneAddressExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {sel entry ret decoded : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.Push .PUSH2, some (ret, 2)))
    (hd4 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3) =
        some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd6 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hd7 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATASIZE, .none))
    (hd8 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.SUB, .none))
    (hd9 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd11 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hd12 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hd13 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hd14 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (decoded, 2)))
    (hd17 :
      decode code
          ((entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hdecoded : (D_J code 0).contains decoded = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) decoded
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize
  exact RD.solcExternalStaticArgsLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hlt

set_option maxHeartbeats 1000000 in
theorem RD.solcOneAddressExternalMaskAndJumpMasked {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 : decode code (decoded + ⟨1⟩ + ⟨1⟩) = some (.CALLDATALOAD, .none))
    (hd3 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd5 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd7 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd9 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd10 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd11 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd12 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd15 :
      decode code
          ((decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.calldataload hd2 (by evm_ov)
  have rd5 := rd3.push1 ⟨1⟩ hd3 (by evm_ov)
  have rd7 := rd5.push1 ⟨1⟩ hd5 (by evm_ov)
  have rd9 := rd7.push1 ⟨160⟩ hd7 (by evm_ov)
  have rd10 := rd9.shl hd9 (by evm_ov)
  have rd11 := rd10.sub hd10 (by evm_ov)
  have rd12 := rd11.and hd11 (by evm_ov)
  have rd15 := rd12.push2 routine hd12 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide, solcAddrMask]
      using rd15.jump hd15 hroutine (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcOneAddressExternalMaskAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 : decode code (decoded + ⟨1⟩ + ⟨1⟩) = some (.CALLDATALOAD, .none))
    (hd3 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd5 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd7 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd9 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd10 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd11 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd12 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd15 :
      decode code
          ((decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨k', C', h'⟩ :=
    RD.solcOneAddressExternalMaskAndJumpMasked h hd0 hd1 hd2 hd3 hd5 hd7 hd9 hd10 hd11
      hd12 hd15 hroutine hov
  have hmask :
      UInt256.land solcAddrMask (calldataWord ee.calldata 4) =
        calldataWord ee.calldata 4 :=
    solcAddrMask_clean_left hcanon
  exact ⟨k', C', by simpa [hmask] using h'⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcTwoAddressExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {sel entry ret decoded : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.Push .PUSH2, some (ret, 2)))
    (hd4 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3) =
        some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd6 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hd7 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATASIZE, .none))
    (hd8 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.SUB, .none))
    (hd9 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd11 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hd12 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hd13 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hd14 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (decoded, 2)))
    (hd17 :
      decode code
          ((entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hdecoded : (D_J code 0).contains decoded = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) decoded
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize
  exact RD.solcExternalStaticArgsLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hlt

set_option maxHeartbeats 1000000 in
theorem RD.solcExternalStaticArgsShortReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {sel entry ret decoded need : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hd0 : decode code entry = some (.JUMPDEST, .none))
    (hd1 : decode code (entry + ⟨1⟩) = some (.Push .PUSH2, some (ret, 2)))
    (hd4 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3) =
        some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd6 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hd7 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATASIZE, .none))
    (hd8 :
      decode code (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.SUB, .none))
    (hd9 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (need, 1)))
    (hd11 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hd12 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hd13 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hd14 :
      decode code
          (entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (decoded, 2)))
    (hd17 :
      decode code
          ((entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hd18 :
      decode code
          (((entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd20 :
      decode code
          ((((entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) +
            UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hd21 :
      decode code
          ((((entry + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.REVERT, .none))
    (hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) need = ⟨1⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 need hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13₀ := rd12.lt hd12 (by evm_ov)
  have rd13 := rd13₀
  rw [hlt] at rd13
  have rd14₀ := rd13.iszero hd13 (by evm_ov)
  have rd14 := rd14₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd14
  have rd17 := rd14.push2 decoded hd14 (by evm_ov)
  have rd18 := rd17.jumpiNT hd17 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd20 := rd18.push1 ⟨0⟩ hd18 (by evm_ov)
  have rd21 := rd20.dup1 hd20 (by evm_ov)
  exact rd21.rev 0 hd21 mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.solcTwoAddressExternalMaskAndJumpMasked {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd4 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd6 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd8 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd9 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd10 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd11 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd12 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd13 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd14 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP2, .none))
    (hd15 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd17 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.ADD, .none))
    (hd18 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd19 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd20 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd23 :
      decode code
          ((decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd4 := rd2.push1 ⟨1⟩ hd2 (by evm_ov)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd8 := rd6.push1 ⟨160⟩ hd6 (by evm_ov)
  have rd9 := rd8.shl hd8 (by evm_ov)
  have rd10 := rd9.sub hd9 (by evm_ov)
  have rd11 := rd10.dup2 hd10 (by evm_ov)
  have rd12 := rd11.calldataload hd11 (by evm_ov)
  have rd13 := rd12.dup2 hd12 (by evm_ov)
  have rd14 := rd13.and hd13 (by evm_ov)
  have rd15 := rd14.swap2 hd14 (by evm_ov)
  have rd17 := rd15.push1 ⟨32⟩ hd15 (by evm_ov)
  have rd18 := rd17.add hd17 (by evm_ov)
  have rd19 := rd18.calldataload hd18 (by evm_ov)
  have rd20 := rd19.and hd19 (by evm_ov)
  have rd23 := rd20.push2 routine hd20 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd23.jump hd23 hroutine (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcTwoAddressExternalMaskAndJump {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd4 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd6 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd8 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd9 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd10 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd11 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd12 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd13 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd14 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP2, .none))
    (hd15 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd17 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.ADD, .none))
    (hd18 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd19 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd20 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd23 :
      decode code
          ((decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hcanon0 : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨k', C', h'⟩ :=
    RD.solcTwoAddressExternalMaskAndJumpMasked h hd0 hd1 hd2 hd4 hd6 hd8 hd9 hd10 hd11
      hd12 hd13 hd14 hd15 hd17 hd18 hd19 hd20 hd23 hroutine hov
  have hmask0 :
      UInt256.land solcAddrMask (calldataWord ee.calldata 4) =
        calldataWord ee.calldata 4 :=
    solcAddrMask_clean_left hcanon0
  have hmask1 :
      UInt256.land solcAddrMask (calldataWord ee.calldata 36) =
        calldataWord ee.calldata 36 :=
    solcAddrMask_clean_left hcanon1
  exact ⟨k', C', by simpa [hmask0, hmask1] using h'⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcAddressUint256ExternalMaskAndJumpMasked {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd4 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd6 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd8 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd9 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd10 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd11 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd12 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd13 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP1, .none))
    (hd14 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd16 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.ADD, .none))
    (hd17 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd18 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd21 :
      decode code
          ((decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 36 :: UInt256.land solcAddrMask (calldataWord ee.calldata 4) ::
        ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd4 := rd2.push1 ⟨1⟩ hd2 (by evm_ov)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd8 := rd6.push1 ⟨160⟩ hd6 (by evm_ov)
  have rd9 := rd8.shl hd8 (by evm_ov)
  have rd10 := rd9.sub hd9 (by evm_ov)
  have rd11 := rd10.dup2 hd10 (by evm_ov)
  have rd12 := rd11.calldataload hd11 (by evm_ov)
  have rd13 := rd12.and hd12 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have rd16 := rd14.push1 ⟨32⟩ hd14 (by evm_ov)
  have rd17 := rd16.add hd16 (by evm_ov)
  have rd18 := rd17.calldataload hd17 (by evm_ov)
  have rd21 := rd18.push2 routine hd18 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd21.jump hd21 hroutine (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcAddressUint256ExternalMaskAndJump {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd4 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd6 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd8 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd9 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd10 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd11 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd12 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd13 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP1, .none))
    (hd14 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd16 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.ADD, .none))
    (hd17 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd18 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd21 :
      decode code
          ((decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨k', C', h'⟩ :=
    RD.solcAddressUint256ExternalMaskAndJumpMasked h hd0 hd1 hd2 hd4 hd6 hd8 hd9 hd10
      hd11 hd12 hd13 hd14 hd16 hd17 hd18 hd21 hroutine hov
  have hmask :
      UInt256.land solcAddrMask (calldataWord ee.calldata 4) =
        calldataWord ee.calldata 4 :=
    solcAddrMask_clean_left hcanon
  exact ⟨k', C', by simpa [hmask] using h'⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcAddressAddressUint256ExternalMaskAndJumpMasked {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {decoded ret routine de : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd4 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd6 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd8 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd9 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd10 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd11 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd12 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd13 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd14 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP2, .none))
    (hd15 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd17 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hd18 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.ADD, .none))
    (hd19 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd20 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP1, .none))
    (hd21 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP2, .none))
    (hd22 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd23 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP1, .none))
    (hd24 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd26 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.ADD, .none))
    (hd27 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd28 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd31 :
      decode code
          ((decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 68 :: UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd4 := rd2.push1 ⟨1⟩ hd2 (by evm_ov)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by evm_ov)
  have rd8 := rd6.push1 ⟨160⟩ hd6 (by evm_ov)
  have rd9 := rd8.shl hd8 (by evm_ov)
  have rd10 := rd9.sub hd9 (by evm_ov)
  have rd11 := rd10.dup2 hd10 (by evm_ov)
  have rd12 := rd11.calldataload hd11 (by evm_ov)
  have rd13 := rd12.dup2 hd12 (by evm_ov)
  have rd14 := rd13.and hd13 (by evm_ov)
  have rd15 := rd14.swap2 hd14 (by evm_ov)
  have rd17 := rd15.push1 ⟨32⟩ hd15 (by evm_ov)
  have rd18 := rd17.dup2 hd17 (by evm_ov)
  have rd19 := rd18.add hd18 (by evm_ov)
  have rd20 := rd19.calldataload hd19 (by evm_ov)
  have rd21 := rd20.swap1 hd20 (by evm_ov)
  have rd22 := rd21.swap2 hd21 (by evm_ov)
  have rd23 := rd22.and hd22 (by evm_ov)
  have rd24 := rd23.swap1 hd23 (by evm_ov)
  have rd26 := rd24.push1 ⟨64⟩ hd24 (by evm_ov)
  have rd27 := rd26.add hd26 (by evm_ov)
  have rd28 := rd27.calldataload hd27 (by evm_ov)
  have rd31 := rd28.push2 routine hd28 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show ((⟨64⟩ : UInt256) + ⟨4⟩).toNat = 68 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd31.jump hd31 hroutine (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcAddressAddressUint256ExternalMaskAndJump {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd4 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd6 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) =
        some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd8 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2) =
        some (.SHL, .none))
    (hd9 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.SUB, .none))
    (hd10 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd11 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd12 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.DUP2, .none))
    (hd13 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd14 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP2, .none))
    (hd15 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hd17 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hd18 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.ADD, .none))
    (hd19 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd20 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP1, .none))
    (hd21 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP2, .none))
    (hd22 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.AND, .none))
    (hd23 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.SWAP1, .none))
    (hd24 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd26 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.ADD, .none))
    (hd27 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.CALLDATALOAD, .none))
    (hd28 :
      decode code
          (decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd31 :
      decode code
          ((decoded + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hcanon0 : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨k', C', h'⟩ :=
    RD.solcAddressAddressUint256ExternalMaskAndJumpMasked h hd0 hd1 hd2 hd4 hd6 hd8 hd9
      hd10 hd11 hd12 hd13 hd14 hd15 hd17 hd18 hd19 hd20 hd21 hd22 hd23 hd24 hd26
      hd27 hd28 hd31 hroutine hov
  have hmask0 :
      UInt256.land solcAddrMask (calldataWord ee.calldata 4) =
        calldataWord ee.calldata 4 :=
    solcAddrMask_clean_left hcanon0
  have hmask1 :
      UInt256.land solcAddrMask (calldataWord ee.calldata 36) =
        calldataWord ee.calldata 36 :=
    solcAddrMask_clean_left hcanon1
  exact ⟨k', C', by simpa [hmask0, hmask1] using h'⟩

/-- Decoding an EVM word as an address only depends on the low 160 bits, so applying solc's
    address-cleanup mask before `AccountAddress.ofNat` is value-preserving. -/
theorem solcAddressValue_masked (w : UInt256) :
    (Solm.Value.address (AccountAddress.ofNat w.toNat)) =
      Solm.Value.address (AccountAddress.ofNat (UInt256.land solcAddrMask w).toNat) := by
  apply congrArg Solm.Value.address
  apply Fin.ext
  unfold AccountAddress.ofNat
  simp only [Fin.val_ofNat]
  rw [uland_toNat]
  change w.val.val % AccountAddress.size =
    Nat.land solcAddrMask.toNat w.val.val % AccountAddress.size
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_comm]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 by rfl]
  rw [Nat.mod_mod]

end Reasoning.Theory

namespace Reasoning.Reach
open Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Solc getter thunks and simple getter routines -/

@[reducible] def solcAddressSlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.SUB, .none)
  ∧ decode code p12 = some (.AND, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.JUMP, .none)

@[reducible] def solcGetterEntryWf
    (code : ByteArray) (pc returnPc routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p7 := p4 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (returnPc, 2))
  ∧ decode code p4 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p7 = some (.JUMP, .none)

@[reducible] def solcWordSlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.DUP2, .none)
  ∧ decode code p5 = some (.JUMP, .none)

@[reducible] def solcConstGetterWf
    (code : ByteArray) (pc val : UInt256) (width : Nat) (op : Operation.POp) : Prop :=
  let p1 := pc + ⟨1⟩
  let pNext := p1 + UInt256.ofNat width.succ
  decode code pc = some (.JUMPDEST, .none)
  ∧ op ≠ .PUSH0
  ∧ decode code p1 = some (.Push op, some (val, width))
  ∧ decode code pNext = some (.DUP2, .none)
  ∧ decode code (pNext + ⟨1⟩) = some (.JUMP, .none)

theorem RD.solcGetterThunk {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {entry returnPc routine : UInt256}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hroutine : (D_J code 0).contains routine = true) :
    ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) routine
      (returnPc :: [sel]) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hentry with ⟨hd0, hd1, hd4, hd7⟩
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 returnPc hd1 (by simp only [List.length_singleton]; omega)
  have rd7 := rd4.push2 routine hd4
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRoutine := rd7.jump hd7 hroutine
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rdRoutine⟩

theorem RD.solcAddressSlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : solcAddressSlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land solcAddrMask
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd2 (by simp only [List.length_cons]; omega)
  have rd6 := rd4.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd10 := rd8.push1 ⟨160⟩ hd5 (by simp only [List.length_cons]; omega)
  have rd11 := rd10.shl hd6 (by simp only [List.length_cons]; omega)
  have rd12 := rd11.sub hd7 (by simp only [List.length_cons]; omega)
  have rd13 := rd12.and hd8 (by simp only [List.length_cons]; omega)
  have rd14 := rd13.dup2 hd9 (by omega)
  have rdRet := rd14.jump hd10 hret (by simp only [List.length_cons]; omega)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  exact ⟨_, _, by simpa [hmask] using rdRet⟩

theorem RD.solcWordSlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : solcWordSlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd2 (by simp only [List.length_cons]; omega)
  have rd5 := rd4.dup2 hd3 (by omega)
  have rdRet := rd5.jump hd4 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdRet⟩

theorem RD.solcConstGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {width : Nat}
    {op : Operation.POp} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : solcConstGetterWf code pc val width op)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (val :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hop, hd1, hdNext, hdJump⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rdNext := rd1.pushConst val (width := width) (op := op) hop hd1
    (by simp only [List.length_cons]; omega)
  have rdDup := rdNext.dup2 hdNext (by omega)
  have rdRet := rdDup.jump hdJump hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdRet⟩

/-! ## Solc mapping getter and store routines -/

abbrev solcSlotWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

theorem twoWordHashMem_solcMappingSlot (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

@[reducible] def solcSingleMappingLoadToRoutineMemWf
    (code : ByteArray) (pc baseSlot afterLoadPc routinePc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p23 := p21 + UInt256.ofNat 2
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p29 := p26 + UInt256.ofNat 3
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p36 := p31 + UInt256.ofNat 5
  let p39 := p36 + UInt256.ofNat 3
  let p40 := p39 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.DUP4, .none)
  ∧ decode code p10 = some (.AND, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.DUP2, .none)
  ∧ decode code p15 = some (.MSTORE, .none)
  ∧ decode code p16 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p20 = some (.MSTORE, .none)
  ∧ decode code p21 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p23 = some (.SWAP1, .none)
  ∧ decode code p24 = some (.KECCAK256, .none)
  ∧ decode code p25 = some (.SLOAD, .none)
  ∧ decode code p26 = some (.Push .PUSH2, some (afterLoadPc, 2))
  ∧ decode code p29 = some (.SWAP1, .none)
  ∧ decode code p30 = some (.DUP3, .none)
  ∧ decode code p31 = some (.Push .PUSH4, some (⟨0xffffffff⟩, 4))
  ∧ decode code p36 = some (.Push .PUSH2, some (routinePc, 2))
  ∧ decode code p39 = some (.AND, .none)
  ∧ decode code p40 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcSingleMappingLoadToRoutineMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot afterLoadPc routinePc value aux key ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (value :: aux :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcSingleMappingLoadToRoutineMemWf code pc baseSlot afterLoadPc routinePc)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routinePc
      (value :: solcSlotWord σ ee (solcMappingSlot baseSlot key) ::
        afterLoadPc :: value :: aux :: key :: ret :: R)
      (twoWordHashMem key baseSlot mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15, hd16,
      hd18, hd20, hd21, hd23, hd24, hd25, hd26, hd29, hd30, hd31, hd36, hd39,
      hd40⟩
  have hmask : UInt256.land key solcAddrMask = key :=
    solcAddrMask_clean hcanonKey
  have hmaskLiteral :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key :=
    twoWordHashMem_solcMappingSlot baseSlot key hmem
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup4 hd9 (by evm_ov),
    raw and hd10 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd15 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 baseSlot hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd18 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key baseSlot mem)
    (UInt256.ofNat 3) hd20 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd21 (by evm_ov),
    raw swap1 hd23 (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd24 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoaded⟩ := rdSlot.sload hd25 (by simp only [List.length_cons]; omega)
  have rdJump := evm_run rdLoaded with [
    raw push2 afterLoadPc hd26 (by evm_ov),
    raw swap1 hd29 (by evm_ov),
    raw dup3 hd30 (by evm_ov),
    raw push4 ⟨0xffffffff⟩ hd31 (by evm_ov),
    raw push2 routinePc hd36 (by evm_ov),
    raw and hd39 (by evm_ov)]
  rw [hroutineMask] at rdJump
  exact ⟨_, _, by simpa [solcSlotWord] using rdJump.jump hd40 hroutine (by evm_ov)⟩

@[reducible] def solcSingleMappingStoreDebitMemWf
    (code : ByteArray) (pc baseSlot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.DUP1, .none)
  ∧ decode code p10 = some (.DUP6, .none)
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.DUP2, .none)
  ∧ decode code p16 = some (.MSTORE, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p19 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p21 = some (.MSTORE, .none)
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p24 = some (.DUP1, .none)
  ∧ decode code p25 = some (.DUP3, .none)
  ∧ decode code p26 = some (.KECCAK256, .none)
  ∧ decode code p27 = some (.SWAP4, .none)
  ∧ decode code p28 = some (.SWAP1, .none)
  ∧ decode code p29 = some (.SWAP4, .none)
  ∧ decode code p30 = some (.SSTORE, .none)

@[reducible] def solcSingleMappingStoreDebitOutPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  p30 + ⟨1⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcSingleMappingStoreDebitMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc baseSlot newValue value aux key ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (newValue :: value :: aux :: key :: ret :: R)
      (twoWordHashMem key baseSlot mem) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcSingleMappingStoreDebitMemWf code pc baseSlot)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (solcSingleMappingStoreDebitOutPc pc)
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: aux :: key :: ret :: R)
      (twoWordHashMem key baseSlot (twoWordHashMem key baseSlot mem))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot baseSlot key) newValue) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd21, hd22, hd24, hd25, hd26, hd27, hd28, hd29, hd30⟩
  have hmask : UInt256.land key solcAddrMask = key :=
    solcAddrMask_clean hcanonKey
  have hmaskLiteral :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hbaseSize : (twoWordHashMem key baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 key baseSlot hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem key baseSlot
            (twoWordHashMem key baseSlot mem)).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key :=
    twoWordHashMem_solcMappingSlot baseSlot key hbaseSize
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup1 hd9 (by evm_ov),
    raw dup6 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd12 (by evm_ov),
    raw swap1 hd14 (by evm_ov),
    raw dup2 hd15 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0
    (wordAt0Mem key (twoWordHashMem key baseSlot mem))
    (UInt256.ofNat 3) hd16 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 baseSlot hd17 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0
    (twoWordHashMem key baseSlot (twoWordHashMem key baseSlot mem))
    (UInt256.ofNat 3) hd21 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd22 (by evm_ov),
    raw dup1 hd24 (by evm_ov),
    raw dup3 hd25 (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd26 mem_cost hslot (by native_decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw swap4 hd27 (by evm_ov),
    raw swap1 hd28 (by evm_ov),
    raw swap4 hd29 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd30
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcSingleMappingStoreDebitOutPc] using rdOut⟩

@[reducible] def solcSingleMappingStoreCreditMemWf
    (code : ByteArray) (pc baseSlot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.DUP1, .none)
  ∧ decode code p10 = some (.DUP5, .none)
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p14 = some (.DUP2, .none)
  ∧ decode code p15 = some (.DUP2, .none)
  ∧ decode code p16 = some (.MSTORE, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p19 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p21 = some (.SWAP1, .none)
  ∧ decode code p22 = some (.DUP2, .none)
  ∧ decode code p23 = some (.MSTORE, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p26 = some (.SWAP2, .none)
  ∧ decode code p27 = some (.DUP3, .none)
  ∧ decode code p28 = some (.SWAP1, .none)
  ∧ decode code p29 = some (.KECCAK256, .none)
  ∧ decode code p30 = some (.SWAP5, .none)
  ∧ decode code p31 = some (.SWAP1, .none)
  ∧ decode code p32 = some (.SWAP5, .none)
  ∧ decode code p33 = some (.SSTORE, .none)

@[reducible] def solcSingleMappingStoreCreditOutPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  p33 + ⟨1⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcSingleMappingStoreCreditMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc baseSlot newValue value key aux ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (newValue :: value :: key :: aux :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcSingleMappingStoreCreditMemWf code pc baseSlot)
    (hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key)
    (hperm : ee.perm = true)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (solcSingleMappingStoreCreditOutPc pc)
      (⟨64⟩ :: key :: solcAddrMask :: ⟨32⟩ :: value :: key :: aux :: ret :: R)
      (twoWordHashMem key baseSlot mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot baseSlot key) newValue) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd21, hd22, hd23, hd24, hd26, hd27, hd28, hd29, hd30, hd31,
      hd32, hd33⟩
  have hmask : UInt256.land key solcAddrMask = key :=
    solcAddrMask_clean hcanonKey
  have hmaskLiteral :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup1 hd9 (by evm_ov),
    raw dup5 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd12 (by evm_ov),
    raw dup2 hd14 (by evm_ov),
    raw dup2 hd15 (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd16 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 baseSlot hd17 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key baseSlot mem)
    (UInt256.ofNat 3) hd23 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ hd24 (by evm_ov),
    raw swap2 hd26 (by evm_ov),
    raw dup3 hd27 (by evm_ov),
    raw swap1 hd28 (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd29 mem_cost hslot (by native_decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw swap5 hd30 (by evm_ov),
    raw swap1 hd31 (by evm_ov),
    raw swap5 hd32 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd33
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcSingleMappingStoreCreditOutPc] using rdOut⟩

@[reducible] def solcNestedMappingStoreInnerHashWf
    (code : ByteArray) (pc baseSlot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.DUP1, .none)
  ∧ decode code p10 = some (.DUP5, .none)
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p14 = some (.DUP2, .none)
  ∧ decode code p15 = some (.DUP2, .none)
  ∧ decode code p16 = some (.MSTORE, .none)
  ∧ decode code p17 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p19 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p21 = some (.SWAP1, .none)
  ∧ decode code p22 = some (.DUP2, .none)
  ∧ decode code p23 = some (.MSTORE, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p26 = some (.DUP1, .none)
  ∧ decode code p27 = some (.DUP4, .none)
  ∧ decode code p28 = some (.KECCAK256, .none)

@[reducible] def solcNestedMappingStoreInnerHashOutPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p21 := p19 + UInt256.ofNat 2
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  p28 + ⟨1⟩

theorem RD.solcNestedMappingStoreInnerHash {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc baseSlot value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingStoreInnerHashWf code pc baseSlot)
    (hmem : mem.size = 96)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (solcNestedMappingStoreInnerHashOutPc pc)
      (solcMappingSlot baseSlot owner :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner ::
        solcAddrMask :: value :: spender :: owner :: ret :: R)
      (twoWordHashMem owner baseSlot mem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd21, hd22, hd23, hd24, hd26, hd27, hd28⟩
  have hmask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner =
        owner := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonOwner
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot owner :=
    twoWordHashMem_solcMappingSlot baseSlot owner hmem
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup1 hd9 (by evm_ov),
    raw dup5 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [u256_land_comm owner (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩),
    hmask] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd12 (by evm_ov),
    raw dup2 hd14 (by evm_ov),
    raw dup2 hd15 (by evm_ov)]
  have rdInnerKey := rdMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 3) hd16 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 baseSlot hd17 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0 (twoWordHashMem owner baseSlot mem)
    (UInt256.ofNat 3) hd23 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ hd24 (by evm_ov),
    raw dup1 hd26 (by evm_ov),
    raw dup4 hd27 (by evm_ov)]
  exact ⟨_, _, by
    simpa [solcNestedMappingStoreInnerHashOutPc] using
      rdInnerHashPrefix.keccak256 0 (solcMappingSlot baseSlot owner)
        (UInt256.ofNat 3) hd28 mem_cost hslot (by native_decide) (by evm_ov)⟩

@[reducible] def solcNestedMappingStoreOuterSstoreWf
    (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  decode code pc = some (.SWAP5, .none)
  ∧ decode code p1 = some (.DUP8, .none)
  ∧ decode code p2 = some (.AND, .none)
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.DUP5, .none)
  ∧ decode code p5 = some (.MSTORE, .none)
  ∧ decode code p6 = some (.SWAP5, .none)
  ∧ decode code p7 = some (.DUP3, .none)
  ∧ decode code p8 = some (.MSTORE, .none)
  ∧ decode code p9 = some (.SWAP2, .none)
  ∧ decode code p10 = some (.DUP3, .none)
  ∧ decode code p11 = some (.SWAP1, .none)
  ∧ decode code p12 = some (.KECCAK256, .none)
  ∧ decode code p13 = some (.DUP6, .none)
  ∧ decode code p14 = some (.SWAP1, .none)
  ∧ decode code p15 = some (.SSTORE, .none)

@[reducible] def solcNestedMappingStoreOuterSstoreOutPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  p15 + ⟨1⟩

theorem RD.solcNestedMappingStoreOuterSstore {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc innerSlot value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc
      (innerSlot :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingStoreOuterSstoreWf code pc)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (solcNestedMappingStoreOuterSstoreOutPc pc)
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      (twoWordHashMem spender innerSlot mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot innerSlot spender) value)
      k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12,
      hd13, hd14, hd15⟩
  have hmask : UInt256.land spender solcAddrMask = spender :=
    solcAddrMask_clean hcanonSpender
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem spender innerSlot mem).readWithPadding 0 64))) =
        solcMappingSlot innerSlot spender :=
    twoWordHashMem_solcMappingSlot innerSlot spender hmem
  have rdMasked := evm_run h with [
    raw swap5 hd0 (by evm_ov),
    raw dup8 hd1 (by evm_ov),
    raw and hd2 (by evm_ov)]
  rw [hmask] at rdMasked
  have rdOuterKeyPrefix := evm_run rdMasked with [
    raw dup1 hd3 (by evm_ov),
    raw dup5 hd4 (by evm_ov)]
  have rdOuterKey := rdOuterKeyPrefix.mstore 0 (wordAt0Mem spender mem)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap5 hd6 (by evm_ov),
    raw dup3 hd7 (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (twoWordHashMem spender innerSlot mem)
    (UInt256.ofNat 3) hd8 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdHashPrefix := evm_run rdOuterMem with [
    raw swap2 hd9 (by evm_ov),
    raw dup3 hd10 (by evm_ov),
    raw swap1 hd11 (by evm_ov)]
  have rdSlot := rdHashPrefix.keccak256 0 (solcMappingSlot innerSlot spender)
    (UInt256.ofNat 3) hd12 mem_cost hslot (by native_decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw dup6 hd13 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd15
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcNestedMappingStoreOuterSstoreOutPc] using rdOut⟩

noncomputable def solcNestedMappingCallerHashMem
    (baseSlot owner : UInt256) (ee : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  twoWordHashMem (solcSourceWord ee) (solcMappingSlot baseSlot owner)
    (twoWordHashMem owner baseSlot mem)

@[reducible] def solcNestedMappingCallerStoreMemWf
    (code : ByteArray) (pc baseSlot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p25 := p23 + UInt256.ofNat 2
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.DUP6, .none)
  ∧ decode code p10 = some (.AND, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.DUP2, .none)
  ∧ decode code p15 = some (.MSTORE, .none)
  ∧ decode code p16 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.DUP2, .none)
  ∧ decode code p22 = some (.MSTORE, .none)
  ∧ decode code p23 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p25 = some (.DUP1, .none)
  ∧ decode code p26 = some (.DUP4, .none)
  ∧ decode code p27 = some (.KECCAK256, .none)
  ∧ decode code p28 = some (.CALLER, .none)
  ∧ decode code p29 = some (.DUP5, .none)
  ∧ decode code p30 = some (.MSTORE, .none)
  ∧ decode code p31 = some (.SWAP1, .none)
  ∧ decode code p32 = some (.SWAP2, .none)
  ∧ decode code p33 = some (.MSTORE, .none)
  ∧ decode code p34 = some (.SWAP1, .none)
  ∧ decode code p35 = some (.KECCAK256, .none)
  ∧ decode code p36 = some (.SSTORE, .none)

@[reducible] def solcNestedMappingCallerStoreMemOutPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p25 := p23 + UInt256.ofNat 2
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  p36 + ⟨1⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcNestedMappingCallerStoreMem
    {code : ByteArray} {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot newValue discard value aux owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (newValue :: discard :: value :: aux :: owner :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingCallerStoreMemWf code pc baseSlot)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (solcNestedMappingCallerStoreMemOutPc pc)
      (discard :: value :: aux :: owner :: ret :: R)
      (solcNestedMappingCallerHashMem baseSlot owner ee mem)
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ
        (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee)) newValue)
      k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd18, hd20, hd21, hd22, hd23, hd25, hd26, hd27, hd28, hd29,
      hd30, hd31, hd32, hd33, hd34, hd35, hd36⟩
  have hmask : UInt256.land owner solcAddrMask = owner :=
    solcAddrMask_clean hcanonOwner
  have hmaskLiteral :
      UInt256.land owner (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        owner := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot owner :=
    twoWordHashMem_solcMappingSlot baseSlot owner hmem
  have hinnerSize : (twoWordHashMem owner baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 owner baseSlot hmem
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((solcNestedMappingCallerHashMem baseSlot owner ee mem).readWithPadding 0 64))) =
        solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee) := by
    unfold solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee)
      hinnerSize
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup6 hd9 (by evm_ov),
    raw and hd10 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov)]
  have rdInnerKey := rdMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 3) hd15 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 baseSlot hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd18 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw dup2 hd21 (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0 (twoWordHashMem owner baseSlot mem)
    (UInt256.ofNat 3) hd22 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ hd23 (by evm_ov),
    raw dup1 hd25 (by evm_ov),
    raw dup4 hd26 (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd27 mem_cost hinner (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller hd28 (by evm_ov),
    raw dup5 hd29 (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord ee) (twoWordHashMem owner baseSlot mem))
    (UInt256.ofNat 3) hd30 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 hd31 (by evm_ov),
    raw swap2 hd32 (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (solcNestedMappingCallerHashMem baseSlot owner ee mem)
    (UInt256.ofNat 3) hd33 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 hd34 (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0
    (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee))
    (UInt256.ofNat 3) hd35 mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdOut⟩ := rdOuterHash.sstore hperm hd36
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcNestedMappingCallerStoreMemOutPc] using rdOut⟩

@[reducible] def solcNestedMappingCallerLoadWf
    (code : ByteArray) (pc baseSlot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p25 := p23 + UInt256.ofNat 2
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p7 = some (.SHL, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.DUP4, .none)
  ∧ decode code p10 = some (.AND, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.DUP2, .none)
  ∧ decode code p15 = some (.MSTORE, .none)
  ∧ decode code p16 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p20 = some (.SWAP1, .none)
  ∧ decode code p21 = some (.DUP2, .none)
  ∧ decode code p22 = some (.MSTORE, .none)
  ∧ decode code p23 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p25 = some (.DUP1, .none)
  ∧ decode code p26 = some (.DUP4, .none)
  ∧ decode code p27 = some (.KECCAK256, .none)
  ∧ decode code p28 = some (.CALLER, .none)
  ∧ decode code p29 = some (.DUP5, .none)
  ∧ decode code p30 = some (.MSTORE, .none)
  ∧ decode code p31 = some (.SWAP1, .none)
  ∧ decode code p32 = some (.SWAP2, .none)
  ∧ decode code p33 = some (.MSTORE, .none)
  ∧ decode code p34 = some (.DUP2, .none)
  ∧ decode code p35 = some (.KECCAK256, .none)
  ∧ decode code p36 = some (.SLOAD, .none)

@[reducible] def solcNestedMappingCallerLoadOutPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p25 := p23 + UInt256.ofNat 2
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  p36 + ⟨1⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcNestedMappingCallerLoad {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot value aux owner ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (value :: aux :: owner :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingCallerLoadWf code pc baseSlot)
    (hmem : mem.size = 96)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (solcNestedMappingCallerLoadOutPc pc)
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee)) ::
        ⟨0⟩ :: value :: aux :: owner :: ret :: R)
      (solcNestedMappingCallerHashMem baseSlot owner ee mem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd18, hd20, hd21, hd22, hd23, hd25, hd26, hd27, hd28, hd29,
      hd30, hd31, hd32, hd33, hd34, hd35, hd36⟩
  have hmask : UInt256.land owner solcAddrMask = owner :=
    solcAddrMask_clean hcanonOwner
  have hmaskLiteral :
      UInt256.land owner (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        owner := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot owner :=
    twoWordHashMem_solcMappingSlot baseSlot owner hmem
  have hinnerSize : (twoWordHashMem owner baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 owner baseSlot hmem
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((solcNestedMappingCallerHashMem baseSlot owner ee mem).readWithPadding 0 64))) =
        solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee) := by
    unfold solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee)
      hinnerSize
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup4 hd9 (by evm_ov),
    raw and hd10 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd11 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov)]
  have rdInnerKey := rdMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 3) hd15 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 baseSlot hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd18 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw dup2 hd21 (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0 (twoWordHashMem owner baseSlot mem)
    (UInt256.ofNat 3) hd22 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ hd23 (by evm_ov),
    raw dup1 hd25 (by evm_ov),
    raw dup4 hd26 (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd27 mem_cost hinner (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller hd28 (by evm_ov),
    raw dup5 hd29 (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord ee) (twoWordHashMem owner baseSlot mem))
    (UInt256.ofNat 3) hd30 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 hd31 (by evm_ov),
    raw swap2 hd32 (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (solcNestedMappingCallerHashMem baseSlot owner ee mem)
    (UInt256.ofNat 3) hd33 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw dup2 hd34 (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0
    (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee))
    (UInt256.ofNat 3) hd35 mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoaded⟩ := rdOuterHash.sload hd36
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [solcNestedMappingCallerLoadOutPc, solcSlotWord, solcSourceWord] using rdLoaded⟩

@[reducible] def solcUintMaxEqBranchWf
    (code : ByteArray) (pc targetPc : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p7 := p4 + UInt256.ofNat 3
  decode code pc = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p2 = some (.NOT, .none)
  ∧ decode code p3 = some (.EQ, .none)
  ∧ decode code p4 = some (.Push .PUSH2, some (targetPc, 2))
  ∧ decode code p7 = some (.JUMPI, .none)

theorem RD.solcUintMaxEqBranchTrue {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc targetPc word discard : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (word :: discard :: R) mem aw rdata acc k C)
    (hwf : solcUintMaxEqBranchWf code pc targetPc)
    (hmax : word.toNat = UInt256.size - 1)
    (htarget : (D_J code 0).contains targetPc = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 targetPc (discard :: R) mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd2, hd3, hd4, hd7⟩
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hword : word = UInt256.lnot (⟨0⟩ : UInt256) := by
    apply u256_inj
    rw [hmax, hlnot0]
  have heq : UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) word = ⟨1⟩ := by
    rw [hword]
    exact u256_eq_refl _
  have rdEq := evm_run h with [
    raw push1 ⟨0⟩ hd0 (by evm_ov),
    raw not hd2 (by evm_ov),
    raw eq hd3 (by evm_ov)]
  rw [heq] at rdEq
  have rdTarget := evm_run rdEq with [
    raw push2 targetPc hd4 (by evm_ov),
    raw jumpiT hd7 one_ne_zero_uint htarget (by evm_ov)]
  exact ⟨_, _, rdTarget⟩

@[reducible] def solcUintMaxEqBranchFallthroughPc (pc : UInt256) : UInt256 :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p7 := p4 + UInt256.ofNat 3
  p7 + ⟨1⟩

theorem RD.solcUintMaxEqBranchFalse {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc targetPc word discard : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (word :: discard :: R) mem aw rdata acc k C)
    (hwf : solcUintMaxEqBranchWf code pc targetPc)
    (hnotMax : word.toNat ≠ UInt256.size - 1)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (solcUintMaxEqBranchFallthroughPc pc)
      (discard :: R) mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd2, hd3, hd4, hd7⟩
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hneq : UInt256.lnot (⟨0⟩ : UInt256) ≠ word := by
    intro hword
    apply hnotMax
    rw [← hword, hlnot0]
  have heq : UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) word = ⟨0⟩ :=
    u256_eq_of_ne hneq
  have rdEq := evm_run h with [
    raw push1 ⟨0⟩ hd0 (by evm_ov),
    raw not hd2 (by evm_ov),
    raw eq hd3 (by evm_ov)]
  rw [heq] at rdEq
  have rdTarget := evm_run rdEq with [raw push2 targetPc hd4 (by evm_ov)]
  have rdFallthrough := rdTarget.jumpiNT hd7 (by decide) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcUintMaxEqBranchFallthroughPc] using rdFallthrough⟩

@[reducible] def solcNestedMappingCallerReloadToRoutineMemWf
    (code : ByteArray) (pc baseSlot contPc routinePc : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p4 := p2 + UInt256.ofNat 2
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p12 := p10 + UInt256.ofNat 2
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p39 := p36 + UInt256.ofNat 3
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p46 := p41 + UInt256.ofNat 5
  let p49 := p46 + UInt256.ofNat 3
  let p50 := p49 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p2 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p6 = some (.SHL, .none)
  ∧ decode code p7 = some (.SUB, .none)
  ∧ decode code p8 = some (.DUP5, .none)
  ∧ decode code p9 = some (.AND, .none)
  ∧ decode code p10 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p12 = some (.SWAP1, .none)
  ∧ decode code p13 = some (.DUP2, .none)
  ∧ decode code p14 = some (.MSTORE, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p17 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p19 = some (.SWAP1, .none)
  ∧ decode code p20 = some (.DUP2, .none)
  ∧ decode code p21 = some (.MSTORE, .none)
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p24 = some (.DUP1, .none)
  ∧ decode code p25 = some (.DUP4, .none)
  ∧ decode code p26 = some (.KECCAK256, .none)
  ∧ decode code p27 = some (.CALLER, .none)
  ∧ decode code p28 = some (.DUP5, .none)
  ∧ decode code p29 = some (.MSTORE, .none)
  ∧ decode code p30 = some (.SWAP1, .none)
  ∧ decode code p31 = some (.SWAP2, .none)
  ∧ decode code p32 = some (.MSTORE, .none)
  ∧ decode code p33 = some (.SWAP1, .none)
  ∧ decode code p34 = some (.KECCAK256, .none)
  ∧ decode code p35 = some (.SLOAD, .none)
  ∧ decode code p36 = some (.Push .PUSH2, some (contPc, 2))
  ∧ decode code p39 = some (.SWAP1, .none)
  ∧ decode code p40 = some (.DUP4, .none)
  ∧ decode code p41 = some (.Push .PUSH4, some (⟨0xffffffff⟩, 4))
  ∧ decode code p46 = some (.Push .PUSH2, some (routinePc, 2))
  ∧ decode code p49 = some (.AND, .none)
  ∧ decode code p50 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcNestedMappingCallerReloadToRoutineMem
    {code : ByteArray} {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot contPc routinePc discard value aux owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (discard :: value :: aux :: owner :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingCallerReloadToRoutineMemWf code pc baseSlot contPc routinePc)
    (hmem : mem.size = 96)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routinePc
      (value ::
        solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee)) ::
        contPc :: discard :: value :: aux :: owner :: ret :: R)
      (solcNestedMappingCallerHashMem baseSlot owner ee mem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd2, hd4, hd6, hd7, hd8, hd9, hd10, hd12, hd13, hd14, hd15, hd17,
      hd19, hd20, hd21, hd22, hd24, hd25, hd26, hd27, hd28, hd29, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd39, hd40, hd41, hd46, hd49, hd50⟩
  have hmask : UInt256.land owner solcAddrMask = owner :=
    solcAddrMask_clean hcanonOwner
  have hmaskLiteral :
      UInt256.land owner (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        owner := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner baseSlot mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot owner :=
    twoWordHashMem_solcMappingSlot baseSlot owner hmem
  have hinnerSize : (twoWordHashMem owner baseSlot mem).size = 96 :=
    twoWordHashMem_size_96 owner baseSlot hmem
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((solcNestedMappingCallerHashMem baseSlot owner ee mem).readWithPadding 0 64))) =
        solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee) := by
    unfold solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee)
      hinnerSize
  have rdMasked := evm_run h with [
    raw push1 ⟨1⟩ hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw push1 ⟨160⟩ hd4 (by evm_ov),
    raw shl hd6 (by evm_ov),
    raw sub hd7 (by evm_ov),
    raw dup5 hd8 (by evm_ov),
    raw and hd9 (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd10 (by evm_ov),
    raw swap1 hd12 (by evm_ov),
    raw dup2 hd13 (by evm_ov)]
  have rdInnerKey := rdMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 3) hd14 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 baseSlot hd15 (by evm_ov),
    raw push1 ⟨32⟩ hd17 (by evm_ov),
    raw swap1 hd19 (by evm_ov),
    raw dup2 hd20 (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0 (twoWordHashMem owner baseSlot mem)
    (UInt256.ofNat 3) hd21 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ hd22 (by evm_ov),
    raw dup1 hd24 (by evm_ov),
    raw dup4 hd25 (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd26 mem_cost hinner (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller hd27 (by evm_ov),
    raw dup5 hd28 (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord ee) (twoWordHashMem owner baseSlot mem))
    (UInt256.ofNat 3) hd29 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 hd30 (by evm_ov),
    raw swap2 hd31 (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (solcNestedMappingCallerHashMem baseSlot owner ee mem)
    (UInt256.ofNat 3) hd32 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 hd33 (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0
    (solcMappingSlot (solcMappingSlot baseSlot owner) (solcSourceWord ee))
    (UInt256.ofNat 3) hd34 mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoaded⟩ := rdOuterHash.sload hd35
    (by simp only [List.length_cons]; omega)
  have rdJump := evm_run rdLoaded with [
    raw push2 contPc hd36 (by evm_ov),
    raw swap1 hd39 (by evm_ov),
    raw dup4 hd40 (by evm_ov),
    raw push4 ⟨0xffffffff⟩ hd41 (by evm_ov),
    raw push2 routinePc hd46 (by evm_ov),
    raw and hd49 (by evm_ov)]
  rw [hroutineMask] at rdJump
  exact ⟨_, _, by
    simpa [solcSlotWord, solcSourceWord] using rdJump.jump hd50 hroutine (by evm_ov)⟩

@[reducible] def solcPreparedSingleMappingLoadToRoutineMemWf
    (code : ByteArray) (pc afterLoadPc routinePc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p17 := p12 + UInt256.ofNat 5
  let p20 := p17 + UInt256.ofNat 3
  let p21 := p20 + ⟨1⟩
  decode code pc = some (.SWAP1, .none)
  ∧ decode code p1 = some (.DUP5, .none)
  ∧ decode code p2 = some (.AND, .none)
  ∧ decode code p3 = some (.DUP2, .none)
  ∧ decode code p4 = some (.MSTORE, .none)
  ∧ decode code p5 = some (.KECCAK256, .none)
  ∧ decode code p6 = some (.SLOAD, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (afterLoadPc, 2))
  ∧ decode code p10 = some (.SWAP1, .none)
  ∧ decode code p11 = some (.DUP3, .none)
  ∧ decode code p12 = some (.Push .PUSH4, some (⟨0xffffffff⟩, 4))
  ∧ decode code p17 = some (.Push .PUSH2, some (routinePc, 2))
  ∧ decode code p20 = some (.AND, .none)
  ∧ decode code p21 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcPreparedSingleMappingLoadToRoutineMem
    {code : ByteArray} {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot afterLoadPc routinePc value key other ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: key :: other :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcPreparedSingleMappingLoadToRoutineMemWf code pc afterLoadPc routinePc)
    (hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem key mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routinePc
      (value :: solcSlotWord σ ee (solcMappingSlot baseSlot key) ::
        afterLoadPc :: value :: key :: other :: ret :: R)
      (wordAt0Mem key mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd10, hd11, hd12, hd17, hd20,
      hd21⟩
  have hmask : UInt256.land key solcAddrMask = key :=
    solcAddrMask_clean hcanonKey
  have rdMasked := evm_run h with [
    raw swap1 hd0 (by evm_ov),
    raw dup5 hd1 (by evm_ov),
    raw and hd2 (by evm_ov)]
  rw [hmask] at rdMasked
  have rdBeforeHash := evm_run rdMasked with [raw dup2 hd3 (by evm_ov)]
  have rdHashMem := rdBeforeHash.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) hd4 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSlot := rdHashMem.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd5 mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoaded⟩ := rdSlot.sload hd6 (by simp only [List.length_cons]; omega)
  have rdJump := evm_run rdLoaded with [
    raw push2 afterLoadPc hd7 (by evm_ov),
    raw swap1 hd10 (by evm_ov),
    raw dup3 hd11 (by evm_ov),
    raw push4 ⟨0xffffffff⟩ hd12 (by evm_ov),
    raw push2 routinePc hd17 (by evm_ov),
    raw and hd20 (by evm_ov)]
  rw [hroutineMask] at rdJump
  exact ⟨_, _, by simpa [solcSlotWord] using rdJump.jump hd21 hroutine (by evm_ov)⟩

@[reducible] def solcSingleMappingGetterWf
    (code : ByteArray) (pc baseSlot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.MSTORE, .none)
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p8 = some (.SWAP1, .none)
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.SLOAD, .none)
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.JUMP, .none)

@[reducible] def solcNestedMappingGetterWf
    (code : ByteArray) (pc baseSlot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (baseSlot, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.SWAP1, .none)
  ∧ decode code p6 = some (.DUP2, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p10 = some (.SWAP3, .none)
  ∧ decode code p11 = some (.DUP4, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p15 = some (.DUP1, .none)
  ∧ decode code p16 = some (.DUP5, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.SWAP1, .none)
  ∧ decode code p19 = some (.SWAP2, .none)
  ∧ decode code p20 = some (.MSTORE, .none)
  ∧ decode code p21 = some (.SWAP1, .none)
  ∧ decode code p22 = some (.DUP3, .none)
  ∧ decode code p23 = some (.MSTORE, .none)
  ∧ decode code p24 = some (.SWAP1, .none)
  ∧ decode code p25 = some (.KECCAK256, .none)
  ∧ decode code p26 = some (.SLOAD, .none)
  ∧ decode code p27 = some (.DUP2, .none)
  ∧ decode code p28 = some (.JUMP, .none)

@[reducible] def solcNestedMappingGetterSloadPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  p25 + ⟨1⟩

@[reducible] def solcNestedMappingGetterAfterInnerHashPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  p17 + ⟨1⟩

theorem RD.solcSingleMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc baseSlot key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcSingleMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot baseSlot key) :: ret :: R)
      (solcMappingHashMem baseSlot key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd8, hd9, hd10, hd11, hd13, hd14, hd15, hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 baseSlot hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.mstore 0 (solcMappingBaseSlotMem baseSlot)
    (UInt256.ofNat 3) hd5 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd8 := rd6.push1 ⟨0⟩ hd6 (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem baseSlot key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot baseSlot key
  have rd15 := rd14.keccak256 0 (solcMappingSlot baseSlot key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  exact ⟨_, _, rd17.jump hd17 hret (by evm_ov)⟩

set_option maxHeartbeats 2000000 in
theorem RD.solcNestedMappingInnerHash {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0
      (solcNestedMappingGetterAfterInnerHashPc pc)
      (solcMappingSlot baseSlot owner :: ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: ret :: R)
      (solcMappingHashMem baseSlot owner) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16, hd17,
      _hd18, _hd19, _hd20, _hd21, _hd22, _hd23, _hd24, _hd25, _hd26, _hd27,
      _hd28⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 baseSlot hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.swap1 hd5 (by evm_ov)
  have rd7 := rd6.dup2 hd6 (by evm_ov)
  have rd9 := rd7.mstore 0 (solcMappingBaseSlotMem baseSlot)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd10 := rd9.push1 ⟨0⟩ hd8 (by evm_ov)
  have rd11 := rd10.swap3 hd10 (by evm_ov)
  have rd12 := rd11.dup4 hd11 (by evm_ov)
  have rd14 := rd12.mstore 0 (solcMappingHashMem baseSlot owner)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := rd14.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.dup1 hd15 (by evm_ov)
  have rd17 := rd16.dup5 hd16 (by evm_ov)
  have hinner := solcMappingKeccakSlot baseSlot owner
  have rd18 := rd17.keccak256 0 (solcMappingSlot baseSlot owner)
    (UInt256.ofNat 3) hd17 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hinner)
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [solcNestedMappingGetterAfterInnerHashPc] using rd18⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcNestedMappingOuterHash {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0
      (solcNestedMappingGetterAfterInnerHashPc pc)
      (solcMappingSlot baseSlot owner :: ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: ret :: R)
      (solcMappingHashMem baseSlot owner) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0
      (solcNestedMappingGetterSloadPc pc)
      (solcMappingSlot (solcMappingSlot baseSlot owner) spender :: ret :: R)
      (solcNestedMappingHashMem baseSlot owner spender)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd3, _hd5, _hd6, _hd7, _hd8, _hd10, _hd11, _hd12, _hd13,
      _hd15, _hd16, _hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd24, hd25,
      _hd26, _hd27, _hd28⟩
  have rd19 := h.swap1 hd18 (by evm_ov)
  have rd20 := rd19.swap2 hd19 (by evm_ov)
  have rd21 := rd20.mstore 0 (solcNestedMappingOuterBaseMem baseSlot owner)
    (UInt256.ofNat 3) hd20 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd22 := rd21.swap1 hd21 (by evm_ov)
  have rd23 := rd22.dup3 hd22 (by evm_ov)
  have rd24 := rd23.mstore 0 (solcNestedMappingHashMem baseSlot owner spender)
    (UInt256.ofNat 3) hd23 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd25 := rd24.swap1 hd24 (by evm_ov)
  have hslot := solcNestedMappingKeccakSlot baseSlot owner spender
  have rd26 := rd25.keccak256 0
    (solcMappingSlot (solcMappingSlot baseSlot owner) spender)
    (UInt256.ofNat 3) hd25 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [solcNestedMappingGetterSloadPc] using rd26⟩

theorem RD.solcNestedMappingLoadAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc baseSlot slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (solcNestedMappingGetterSloadPc pc) (slot :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (solcSlotWord σ ee slot :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd3, _hd5, _hd6, _hd7, _hd8, _hd10, _hd11, _hd12, _hd13,
      _hd15, _hd16, _hd17, _hd18, _hd19, _hd20, _hd21, _hd22, _hd23, _hd24,
      _hd25, hd26, hd27, hd28⟩
  obtain ⟨_, _, rd27⟩ := h.sload hd26 (by evm_ov)
  have rd28 := rd27.dup2 hd27 (by evm_ov)
  exact ⟨_, _, rd28.jump hd28 hret (by evm_ov)⟩

/-! ## Solc reentrancy-lock prefixes -/

@[reducible] def solcLockEnterOkWf
    (code : ByteArray) (pc okPc slot unlocked locked : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  let pOk1 := okPc + ⟨1⟩
  let pOk3 := pOk1 + UInt256.ofNat 2
  let pOk5 := pOk3 + UInt256.ofNat 2
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (unlocked, 1))
  ∧ decode code p6 = some (.EQ, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p10 = some (.JUMPI, .none)
  ∧ decode code okPc = some (.JUMPDEST, .none)
  ∧ decode code pOk1 = some (.Push .PUSH1, some (locked, 1))
  ∧ decode code pOk3 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code pOk5 = some (.SSTORE, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcLockEnterOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc slot unlocked locked : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc R mem aw rdata (cA, σ) k C)
    (hwf : solcLockEnterOkWf code pc okPc slot unlocked locked)
    (hperm : ee.perm = true)
    (hunlocked : solcSlotWord σ ee slot = unlocked)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + UInt256.ofNat 6) R mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ slot locked) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10, hdOk, hdOk1, hdOk3, hdOk5⟩
  have rd1 := h.jumpdest hd0 (by omega)
  have rd3 := rd1.push1 slot hd1 (by omega)
  obtain ⟨_, _, rd4₀⟩ := rd3.sload hd3 (by omega)
  have rd4 := rd4₀
  have hunlockedRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) =
        unlocked := by
    simpa [solcSlotWord] using hunlocked
  rw [hunlockedRaw] at rd4
  have rd6 := rd4.push1 unlocked hd4 (by simp only [List.length_cons]; omega)
  have rd7₀ := rd6.eq hd6 (by omega)
  have rd7 := rd7₀
  rw [uInt256_eq_self] at rd7
  have rd10 := rd7.push2 okPc hd7 (by simp only [List.length_cons]; omega)
  have rdOk := rd10.jumpiT hd10 one_ne_zero_uint hok (by omega)
  have rdOk1 := rdOk.jumpdest hdOk (by omega)
  have rdOk3 := rdOk1.push1 locked hdOk1 (by omega)
  have rdOk5 := rdOk3.push1 slot hdOk3 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdAfter⟩ := rdOk5.sstore hperm hdOk5 (by omega)
  have hpcOut :
      okPc + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ =
        okPc + UInt256.ofNat 6 := by
    rw [u256_add_assoc okPc ⟨1⟩ (UInt256.ofNat 2)]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2) (UInt256.ofNat 2)]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) ⟨1⟩]
    congr 1
  exact ⟨_, _, by simpa [hpcOut] using rdAfter⟩

/-! ## Solc checked arithmetic success tails -/

@[reducible] def solcCheckedSubSuccessWf
    (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p11 := p8 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.DUP1, .none)
  ∧ decode code p2 = some (.DUP3, .none)
  ∧ decode code p3 = some (.SUB, .none)
  ∧ decode code p4 = some (.DUP3, .none)
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.GT, .none)
  ∧ decode code p7 = some (.ISZERO, .none)
  ∧ decode code p8 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p11 = some (.JUMPI, .none)
  ∧ decode code okPc = some (.JUMPDEST, .none)
  ∧ decode code (okPc + ⟨1⟩) = some (.SWAP3, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.SWAP2, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.JUMP, .none)

@[reducible] def solcCheckedAddSuccessWf
    (code : ByteArray) (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p11 := p8 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.DUP1, .none)
  ∧ decode code p2 = some (.DUP3, .none)
  ∧ decode code p3 = some (.ADD, .none)
  ∧ decode code p4 = some (.DUP3, .none)
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.LT, .none)
  ∧ decode code p7 = some (.ISZERO, .none)
  ∧ decode code p8 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p11 = some (.JUMPI, .none)
  ∧ decode code okPc = some (.JUMPDEST, .none)
  ∧ decode code (okPc + ⟨1⟩) = some (.SWAP3, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.SWAP2, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedSubSuccess {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCheckedSubSuccessWf code pc okPc)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J code 0).contains ret = true)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (UInt256.sub a b :: R) mem aw rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, hdOk, hdOk1, hdOk2,
      hdOk3, hdOk4, hdOk5⟩
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    ugt_zero (by rw [hsubNat]; omega)
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8
  have rdOk := evm_run rd8 with [
    raw push2 okPc hd8 (by evm_ov),
    raw jumpiT hd11 one_ne_zero_uint hok (by evm_ov)]
  exact ⟨_, _, evm_run rdOk with [
    raw jumpdest hdOk (by evm_ov),
    raw swap3 hdOk1 (by evm_ov),
    raw swap2 hdOk2 (by evm_ov),
    raw pop hdOk3 (by evm_ov),
    raw pop hdOk4 (by evm_ov),
    raw jump hdOk5 hret (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedAddSuccess {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCheckedAddSuccessWf code pc okPc)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J code 0).contains ret = true)
    (hok : (D_J code 0).contains okPc = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret ((a + b) :: R) mem aw rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, hdOk, hdOk1, hdOk2,
      hdOk3, hdOk4, hdOk5⟩
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hlt : UInt256.lt (a + b) a = ⟨0⟩ :=
    ult_zero (by rw [haddNat]; omega)
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8
  have rdOk := evm_run rd8 with [
    raw push2 okPc hd8 (by evm_ov),
    raw jumpiT hd11 one_ne_zero_uint hok (by evm_ov)]
  exact ⟨_, _, evm_run rdOk with [
    raw jumpdest hdOk (by evm_ov),
    raw swap3 hdOk1 (by evm_ov),
    raw swap2 hdOk2 (by evm_ov),
    raw pop hdOk3 (by evm_ov),
    raw pop hdOk4 (by evm_ov),
    raw jump hdOk5 hret (by evm_ov)]⟩

@[reducible] def solcCheckedArithmeticRevertPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p11 := p8 + UInt256.ofNat 3
  p11 + ⟨1⟩

@[reducible] def solcErrorStringRevertTailWf
    (code : ByteArray) (pc len rawWord shift : UInt256) (op : Operation.POp)
    (width : ℕ) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let pRawOut := p27 + UInt256.ofNat width.succ
  let pShl := pRawOut + UInt256.ofNat 2
  let p68 := pShl + ⟨1⟩
  let pDup3 := p68 + UInt256.ofNat 2
  let pAdd := pDup3 + ⟨1⟩
  let pMstore3 := pAdd + ⟨1⟩
  let pSwap := pMstore3 + ⟨1⟩
  let pMload := pSwap + ⟨1⟩
  let pSwap2 := pMload + ⟨1⟩
  let pDup2 := pSwap2 + ⟨1⟩
  let pSwap3 := pDup2 + ⟨1⟩
  let pSub := pSwap3 + ⟨1⟩
  let p100 := pSub + ⟨1⟩
  let pAdd2 := p100 + UInt256.ofNat 2
  let pSwap4 := pAdd2 + ⟨1⟩
  let pRev := pSwap4 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push op, some (rawWord, width))
  ∧ decode code pRawOut = some (.Push .PUSH1, some (shift, 1))
  ∧ decode code pShl = some (.SHL, .none)
  ∧ decode code p68 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code pDup3 = some (.DUP3, .none)
  ∧ decode code pAdd = some (.ADD, .none)
  ∧ decode code pMstore3 = some (.MSTORE, .none)
  ∧ decode code pSwap = some (.SWAP1, .none)
  ∧ decode code pMload = some (.MLOAD, .none)
  ∧ decode code pSwap2 = some (.SWAP1, .none)
  ∧ decode code pDup2 = some (.DUP2, .none)
  ∧ decode code pSwap3 = some (.SWAP1, .none)
  ∧ decode code pSub = some (.SUB, .none)
  ∧ decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code pAdd2 = some (.ADD, .none)
  ∧ decode code pSwap4 = some (.SWAP1, .none)
  ∧ decode code pRev = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTail {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (solcErrorStringMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

@[reducible] def solcLockEnterGuardWf
    (code : ByteArray) (pc okPc slot unlocked : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (unlocked, 1))
  ∧ decode code p6 = some (.EQ, .none)
  ∧ decode code p7 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code p10 = some (.JUMPI, .none)

@[reducible] def solcLockEnterRevertPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  p10 + ⟨1⟩

set_option maxHeartbeats 1000000 in
theorem RD.solcLockEnterLockedStringRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc slot unlocked len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc R solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hlock : solcLockEnterGuardWf code pc okPc slot unlocked)
    (htail : solcErrorStringRevertTailWf code (solcLockEnterRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hlocked : solcSlotWord σ ee slot ≠ unlocked)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hov : R.length + 6 ≤ 1024) :
    RDrev code g s0 := by
  rcases hlock with ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10⟩
  set lockedWord := solcSlotWord σ ee slot with hlockedWord
  have hlockedWord_ne : lockedWord ≠ unlocked := by
    simpa [hlockedWord] using hlocked
  have heqZero : UInt256.eq unlocked lockedWord = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlockedWord_ne hbad.symm)
  have rd1 := h.jumpdest hd0 (by omega)
  have rd3 := rd1.push1 slot hd1 (by omega)
  obtain ⟨_, _, rd4₀⟩ := rd3.sload hd3 (by omega)
  have rd4 := rd4₀
  have hraw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) =
        lockedWord := by
    simpa [solcSlotWord] using hlockedWord.symm
  rw [hraw] at rd4
  have rd6 := rd4.push1 unlocked hd4 (by simp only [List.length_cons]; omega)
  have rd7₀ := rd6.eq hd6 (by omega)
  have rd7 := rd7₀
  rw [heqZero] at rd7
  have rd10 := rd7.push2 okPc hd7 (by simp only [List.length_cons]; omega)
  have rdRevert₀ := rd10.jumpiNT hd10 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by omega)
  have rdRevert := by
    simpa [solcLockEnterRevertPc] using rdRevert₀
  exact RD.solcErrorStringRevertTail rdRevert htail hpush hword
    solcFreePtrMem_size solcFreePtrMem_read64 (by omega)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedSubStringRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hsub : solcCheckedSubSuccessWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcCheckedArithmeticRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hlt : a.toNat < b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hsub with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact RD.solcErrorStringRevertTail rdTail htail hpush hword hmem hread64
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedAddStringRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hadd : solcCheckedAddSuccessWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcCheckedArithmeticRevertPc pc)
      len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact RD.solcErrorStringRevertTail rdTail htail hpush hword hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.solcSingleMappingLoadCheckedSubMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot afterLoadPc routinePc checkedOkPc value aux key ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (value :: aux :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hload : solcSingleMappingLoadToRoutineMemWf code pc baseSlot afterLoadPc routinePc)
    (hsub : solcCheckedSubSuccessWf code routinePc checkedOkPc)
    (hmem : mem.size = 96)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hbalance : value.toNat ≤ (solcSlotWord σ ee (solcMappingSlot baseSlot key)).toNat)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hafterLoad : (D_J code 0).contains afterLoadPc = true)
    (hcheckedOk : (D_J code 0).contains checkedOkPc = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 afterLoadPc
      (UInt256.sub (solcSlotWord σ ee (solcMappingSlot baseSlot key)) value ::
        value :: aux :: key :: ret :: R)
      (twoWordHashMem key baseSlot mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcSingleMappingLoadToRoutineMem
    (pc := pc) (baseSlot := baseSlot) (afterLoadPc := afterLoadPc)
    (routinePc := routinePc) (value := value) (aux := aux) (key := key)
    (ret := ret) (R := R) h hload hmem hcanonKey hroutine hroutineMask hov
  obtain ⟨_, _, rdAfterLoad⟩ := RD.solcCheckedSubSuccess
    (pc := routinePc) (okPc := checkedOkPc)
    (a := solcSlotWord σ ee (solcMappingSlot baseSlot key)) (b := value)
    (ret := afterLoadPc) (R := value :: aux :: key :: ret :: R)
    rdRoutine hsub hbalance hafterLoad hcheckedOk
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdAfterLoad⟩

theorem RD.solcPreparedSingleMappingLoadCheckedAddMem
    {code : ByteArray} {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot afterLoadPc routinePc checkedOkPc value key other ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: key :: other :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hload : solcPreparedSingleMappingLoadToRoutineMemWf code pc afterLoadPc routinePc)
    (hadd : solcCheckedAddSuccessWf code routinePc checkedOkPc)
    (hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem key mem).readWithPadding 0 64))) =
        solcMappingSlot baseSlot key)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hfit : (solcSlotWord σ ee (solcMappingSlot baseSlot key)).toNat + value.toNat <
      UInt256.size)
    (hroutine : (D_J code 0).contains routinePc = true)
    (hroutineMask : UInt256.land routinePc ⟨0xffffffff⟩ = routinePc)
    (hafterLoad : (D_J code 0).contains afterLoadPc = true)
    (hcheckedOk : (D_J code 0).contains checkedOkPc = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 afterLoadPc
      ((solcSlotWord σ ee (solcMappingSlot baseSlot key) + value) ::
        value :: key :: other :: ret :: R)
      (wordAt0Mem key mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcPreparedSingleMappingLoadToRoutineMem
    (pc := pc) (baseSlot := baseSlot) (afterLoadPc := afterLoadPc)
    (routinePc := routinePc) (value := value) (key := key) (other := other)
    (ret := ret) (R := R) h hload hslot hcanonKey hroutine hroutineMask hov
  obtain ⟨_, _, rdAfterLoad⟩ := RD.solcCheckedAddSuccess
    (pc := routinePc) (okPc := checkedOkPc)
    (a := solcSlotWord σ ee (solcMappingSlot baseSlot key)) (b := value)
    (ret := afterLoadPc) (R := value :: key :: other :: ret :: R)
    rdRoutine hadd hfit hafterLoad hcheckedOk
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdAfterLoad⟩

/-! ## Solc boolean-success continuations -/

@[reducible] def solcDiscard2ReturnTrueWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP3, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP2, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.POP, .none)
  ∧ decode code
      (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.POP, .none)
  ∧ decode code
      (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩) =
      some (.JUMP, .none)

@[reducible] def solcDiscard4ReturnTrueWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.SWAP4, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP3, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.POP, .none)
  ∧ decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.POP, .none)
  ∧ decode code
      (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.POP, .none)
  ∧ decode code
      (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩) =
      some (.JUMP, .none)

theorem RD.solcDiscard2ReturnTrue {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc discard a b ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (discard :: a :: b :: ret :: R) mem aw rdata acc k C)
    (hwf : solcDiscard2ReturnTrueWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (⟨1⟩ :: R) mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd8, hd9⟩
  exact ⟨_, _, evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw pop hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw jumpdest hd4 (by evm_ov),
    raw swap3 hd5 (by evm_ov),
    raw swap2 hd6 (by evm_ov),
    raw pop hd7 (by evm_ov),
    raw pop hd8 (by evm_ov),
    raw jump hd9 hret (by evm_ov)]⟩

theorem RD.solcDiscard4ReturnTrue {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc discard value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (discard :: value :: toWord :: src :: ret :: R) mem aw rdata
      acc k C)
    (hwf : solcDiscard4ReturnTrueWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (⟨1⟩ :: R) mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd4, hd5, hd6, hd7, hd8, hd9⟩
  exact ⟨_, _, evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw pop hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd2 (by evm_ov),
    raw swap4 hd4 (by evm_ov),
    raw swap3 hd5 (by evm_ov),
    raw pop hd6 (by evm_ov),
    raw pop hd7 (by evm_ov),
    raw pop hd8 (by evm_ov),
    raw jump hd9 hret (by evm_ov)]⟩

/-! ## Solc event-log suffixes -/

@[reducible] def solcMaskedTransferLog3AndJumpWf
    (code : ByteArray) (pc topic : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p46 := p13 + UInt256.ofNat 33
  let p47 := p46 + ⟨1⟩
  let p48 := p47 + ⟨1⟩
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  let p53 := p52 + ⟨1⟩
  let p54 := p53 + ⟨1⟩
  let p55 := p54 + ⟨1⟩
  let p56 := p55 + ⟨1⟩
  let p57 := p56 + ⟨1⟩
  decode code pc = some (.DUP1, .none)
  ∧ decode code p1 = some (.MLOAD, .none)
  ∧ decode code p2 = some (.DUP6, .none)
  ∧ decode code p3 = some (.DUP2, .none)
  ∧ decode code p4 = some (.MSTORE, .none)
  ∧ decode code p5 = some (.SWAP1, .none)
  ∧ decode code p6 = some (.MLOAD, .none)
  ∧ decode code p7 = some (.SWAP2, .none)
  ∧ decode code p8 = some (.SWAP4, .none)
  ∧ decode code p9 = some (.SWAP3, .none)
  ∧ decode code p10 = some (.DUP8, .none)
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.SWAP3, .none)
  ∧ decode code p13 = some (.Push .PUSH32, some (topic, 32))
  ∧ decode code p46 = some (.SWAP3, .none)
  ∧ decode code p47 = some (.SWAP2, .none)
  ∧ decode code p48 = some (.DUP3, .none)
  ∧ decode code p49 = some (.SWAP1, .none)
  ∧ decode code p50 = some (.SUB, .none)
  ∧ decode code p51 = some (.ADD, .none)
  ∧ decode code p52 = some (.SWAP1, .none)
  ∧ decode code p53 = some (.LOG3, .none)
  ∧ decode code p54 = some (.POP, .none)
  ∧ decode code p55 = some (.POP, .none)
  ∧ decode code p56 = some (.POP, .none)
  ∧ decode code p57 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcMaskedTransferLog3AndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc topic value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc
      (⟨64⟩ :: toWord :: solcAddrMask :: ⟨32⟩ :: value :: toWord :: src :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcMaskedTransferLog3AndJumpWf code pc topic)
    (hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hlogMload :
      (if (⟨64⟩ : UInt256).toNat ≥
            ((UInt256.toByteArray value).write 0 mem 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (((UInt256.toByteArray value).write 0 mem 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R
      ((UInt256.toByteArray value).write 0 mem 128 32) (UInt256.ofNat 5) rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12,
      hd13, hd46, hd47, hd48, hd49, hd50, hd51, hd52, hd53, hd54, hd55, hd56,
      hd57⟩
  have hmask : UInt256.land src solcAddrMask = src :=
    solcAddrMask_clean hcanonSrc
  have rd2 := evm_run h with [
    raw dup1 hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd1
      mem_cost hmload (by decide) (by evm_ov)]
  have rd4 := evm_run rd2 with [raw dup6 hd2 (by evm_ov), raw dup2 hd3 (by evm_ov)]
  have rd5 := rd4.mstore 6 ((UInt256.toByteArray value).write 0 mem 128 32)
    (UInt256.ofNat 5) hd4 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd12 := evm_run rd5 with [
    raw swap1 hd5 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd6
      mem_cost hlogMload (by decide) (by evm_ov),
    raw swap2 hd7 (by evm_ov),
    raw swap4 hd8 (by evm_ov),
    raw swap3 hd9 (by evm_ov),
    raw dup8 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [hmask] at rd12
  have rd13 := evm_run rd12 with [raw swap3 hd12 (by evm_ov)]
  have rd46 := rd13.pushConst topic (width := 32) (op := .PUSH32)
    (by decide) hd13 (by evm_ov)
  have rd53 := evm_run rd46 with [
    raw swap3 hd46 (by evm_ov),
    raw swap2 hd47 (by evm_ov),
    raw dup3 hd48 (by evm_ov),
    raw swap1 hd49 (by evm_ov),
    raw sub hd50 (by evm_ov),
    raw add hd51 (by evm_ov),
    raw swap1 hd52 (by evm_ov)]
  have rd54 := rd53.log3 0 (UInt256.ofNat 5) hd53 hperm mem_cost
    (by decide) (by simp only [List.length_cons]; omega)
  have rd57 := evm_run rd54 with [
    raw pop hd54 (by evm_ov),
    raw pop hd55 (by evm_ov),
    raw pop hd56 (by evm_ov)]
  exact ⟨_, _, rd57.jump hd57 hret (by evm_ov)⟩

@[reducible] def solcPlainLog3AndJumpWf
    (code : ByteArray) (pc topic : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p40 := p7 + UInt256.ofNat 33
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p43 := p42 + ⟨1⟩
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p47 := p46 + ⟨1⟩
  let p48 := p47 + ⟨1⟩
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  decode code pc = some (.DUP2, .none)
  ∧ decode code p1 = some (.MLOAD, .none)
  ∧ decode code p2 = some (.DUP6, .none)
  ∧ decode code p3 = some (.DUP2, .none)
  ∧ decode code p4 = some (.MSTORE, .none)
  ∧ decode code p5 = some (.SWAP2, .none)
  ∧ decode code p6 = some (.MLOAD, .none)
  ∧ decode code p7 = some (.Push .PUSH32, some (topic, 32))
  ∧ decode code p40 = some (.SWAP3, .none)
  ∧ decode code p41 = some (.DUP2, .none)
  ∧ decode code p42 = some (.SWAP1, .none)
  ∧ decode code p43 = some (.SUB, .none)
  ∧ decode code p44 = some (.SWAP1, .none)
  ∧ decode code p45 = some (.SWAP2, .none)
  ∧ decode code p46 = some (.ADD, .none)
  ∧ decode code p47 = some (.SWAP1, .none)
  ∧ decode code p48 = some (.LOG3, .none)
  ∧ decode code p49 = some (.POP, .none)
  ∧ decode code p50 = some (.POP, .none)
  ∧ decode code p51 = some (.POP, .none)
  ∧ decode code p52 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcPlainLog3AndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc topic value topic1 topic2 ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc
      (⟨32⟩ :: ⟨64⟩ :: topic1 :: topic2 :: value :: topic2 :: topic1 :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcPlainLog3AndJumpWf code pc topic)
    (hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hlogMload :
      (if (⟨64⟩ : UInt256).toNat ≥
            ((UInt256.toByteArray value).write 0 mem 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (((UInt256.toByteArray value).write 0 mem 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hperm : ee.perm = true)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R
      ((UInt256.toByteArray value).write 0 mem 128 32) (UInt256.ofNat 5) rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd40, hd41, hd42, hd43, hd44,
      hd45, hd46, hd47, hd48, hd49, hd50, hd51, hd52⟩
  have rd2 := evm_run h with [
    raw dup2 hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd1
      mem_cost hmload (by decide) (by evm_ov)]
  have rd4 := evm_run rd2 with [raw dup6 hd2 (by evm_ov), raw dup2 hd3 (by evm_ov)]
  have rd5 := rd4.mstore 6 ((UInt256.toByteArray value).write 0 mem 128 32)
    (UInt256.ofNat 5) hd4 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7 := evm_run rd5 with [
    raw swap2 hd5 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd6
      mem_cost hlogMload (by decide) (by evm_ov)]
  have rd40 := rd7.pushConst topic (width := 32) (op := .PUSH32)
    (by decide) hd7 (by evm_ov)
  have rd48 := evm_run rd40 with [
    raw swap3 hd40 (by evm_ov),
    raw dup2 hd41 (by evm_ov),
    raw swap1 hd42 (by evm_ov),
    raw sub hd43 (by evm_ov),
    raw swap1 hd44 (by evm_ov),
    raw swap2 hd45 (by evm_ov),
    raw add hd46 (by evm_ov),
    raw swap1 hd47 (by evm_ov)]
  have rd49 := rd48.log3 0 (UInt256.ofNat 5) hd48 hperm mem_cost
    (by decide) (by simp only [List.length_cons]; omega)
  have rd52 := evm_run rd49 with [
    raw pop hd49 (by evm_ov),
    raw pop hd50 (by evm_ov),
    raw pop hd51 (by evm_ov)]
  exact ⟨_, _, rd52.jump hd52 hret (by evm_ov)⟩

/-! ## Solc one-word return wrappers from scratch memory -/

@[reducible] def solcReturnWordFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP2, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP3, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
      some (.ADD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

theorem RD.solcReturnWordFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnWordFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray val) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd15,
      hd16, hd17⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 hd5 (by evm_ov),
    raw dup3 hd6 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd7 mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd8 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw swap1 hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw add hd15 (by evm_ov),
    raw swap1 hd16 (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) hd17 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

@[reducible] def solcReturnAddressFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2) =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2) =
      some (.SHL, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.AND, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩) =
      some (.DUP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2) =
      some (.ADD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

theorem RD.solcReturnAddressFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnAddressFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val solcAddrMask)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val solcAddrMask))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd14, hd15, hd16, hd17,
      hd18, hd19, hd20, hd21, hd22, hd23, hd25, hd26, hd27⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd5 (by evm_ov),
    raw push1 ⟨1⟩ hd7 (by evm_ov),
    raw push1 ⟨160⟩ hd9 (by evm_ov),
    raw shl hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap3 hd14 (by evm_ov),
    raw and hd15 (by evm_ov),
    raw dup3 hd16 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd17 mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide,
          show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd18 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd19 (by evm_ov),
    raw dup2 hd20 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw sub hd22 (by evm_ov),
    raw push1 ⟨32⟩ hd23 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw swap1 hd26 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val solcAddrMask)) hd27 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

@[reducible] def solcReturnUint8FromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨255⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩) =
      some (.AND, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩) =
      some (.DUP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2) =
      some (.ADD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

theorem RD.solcReturnUint8FromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcReturnUint8FromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val ⟨255⟩))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
      hd16, hd17, hd19, hd20, hd21⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨255⟩ hd5 (by evm_ov),
    raw swap1 hd7 (by evm_ov),
    raw swap3 hd8 (by evm_ov),
    raw and hd9 (by evm_ov),
    raw dup3 hd10 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd11 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd12 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw dup2 hd14 (by evm_ov),
    raw swap1 hd15 (by evm_ov),
    raw sub hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd17 (by evm_ov),
    raw add hd19 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val ⟨255⟩)) hd21 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

@[reducible] def solcReturnBoolFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP2, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.ISZERO, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.ISZERO, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
      some (.ADD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

theorem RD.solcReturnBoolFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: R) mem (UInt256.ofNat 5) rdata acc k C)
    (hwf : solcReturnBoolFromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0 mem 128 32 =
        memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero val)))
    (hov : R.length + 5 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14,
      hd15, hd17, hd18, hd19⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw swap2 hd5 (by evm_ov),
    raw iszero hd6 (by evm_ov),
    raw iszero hd7 (by evm_ov),
    raw dup3 hd8 (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 5) hd9 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd10 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd11 (by evm_ov),
    raw dup2 hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw sub hd14 (by evm_ov),
    raw push1 ⟨32⟩ hd15 (by evm_ov),
    raw add hd17 (by evm_ov),
    raw swap1 hd18 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) hd19 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem RD.solcAddressGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine slot returnPc : UInt256}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnAddressFromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.land (solcSlotWord σ I slot) solcAddrMask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcAddressSlotGetter (slot := slot) (R := [sel])
    rdRoutine hgetter hret (by simp only [List.length_singleton]; omega)
  have hrd := RD.solcReturnAddressFromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64
      (UInt256.land (UInt256.land solcAddrMask (solcSlotWord σ I slot)) solcAddrMask))
    (solcReturnMem_read128
      (UInt256.land (UInt256.land solcAddrMask (solcSlotWord σ I slot)) solcAddrMask))
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land (UInt256.land solcAddrMask (solcSlotWord σ I slot)) solcAddrMask =
        UInt256.land (solcSlotWord σ I slot) solcAddrMask := by
    rw [u256_land_comm solcAddrMask (solcSlotWord σ I slot)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (solcSlotWord σ I slot))
  simpa [hclean] using hrd

theorem RD.solcWordGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine slot returnPc : UInt256}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcWordSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnWordFromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (solcSlotWord σ I slot)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcWordSlotGetter (slot := slot) (R := [sel])
    rdRoutine hgetter hret (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnWordFromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (solcSlotWord σ I slot))
    (solcReturnMem_read128 (solcSlotWord σ I slot))
    (by simp only [List.length_singleton]; omega)

theorem RD.solcWordConstGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnWordFromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnWordFromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 val)
    (solcReturnMem_read128 val)
    (by simp only [List.length_singleton]; omega)

theorem RD.solcUint8ConstGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      entry [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnUint8FromMemWf code returnPc) :
    RDret code g (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnUint8FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val ⟨255⟩))
    (solcReturnMem_read128 (UInt256.land val ⟨255⟩))
    (by simp only [List.length_singleton]; omega)

/-- The solc `revert(0,0)` stub `PUSH0·PUSH0·REVERT` as an **`RD → RDrev` combinator**: from a
    cursor at the first `PUSH0`, push the two zero words and `REVERT` (memory-expansion cost `0`).
    Recurs at the end of every revert path. -/
theorem RD.revertStub {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hd0 : decode code pc = some (.PUSH0, .none))
    (hd1 : decode code (pc + ⟨1⟩) = some (.PUSH0, .none))
    (hd2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) :
    RDrev code g s0 :=
  h.push0 hd0 (by omega)
    |>.push0 hd1 (by simp only [List.length_cons]; omega)
    |>.rev 0 hd2 (fun s _ hstks => memExpRevert0 s hstks) (by omega)

/-- Legacy solc `revert(0,0)` terminal emitted as `PUSH1 0; DUP1; REVERT`. -/
theorem RD.solcPush1Dup1Revert0 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hd0 : decode code pc = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hd1 : decode code (pc + UInt256.ofNat 2) = some (.DUP1, .none))
    (hd2 : decode code (pc + UInt256.ofNat 2 + ⟨1⟩) = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) :
    RDrev code g s0 :=
  h.push1 ⟨0⟩ hd0 (by omega)
    |>.dup1 hd1 (by omega)
    |>.rev 0 hd2 (fun s _ hstks => memExpRevert0 s hstks) (by omega)

set_option maxHeartbeats 2000000 in
/-- Generic solc high-level-call uint256 return decoder after a successful CALL-like opcode. -/
theorem RD.solcUint256ReturnWordDecodeOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem o : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 retWord : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hMload64Cost :
      ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R →
        memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord)
    (hMload128Cost :
      ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨128⟩ : UInt256) :: R →
        memoryExpansionCost s .MLOAD = 0)
    (hMload128Aw : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMload128 : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) (retWord :: R)
      mem aw o acc k' C' := by
  have rdPop0 := RD.pop h hPop0 (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 hPop1 (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 hPop2 (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ hPush64 (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ aw rdPush64 hMload64
    hMload64Cost
    hMload64Value
    hMload64Aw
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ hPush32
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 hDup2 (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 hLt (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hlo
  have rdIszero := RD.iszero rdLt hIszero (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero okPc hPushOk
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk hJumpi hcond hjd
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi hJumpdest
    (by simp only [List.length_cons]; omega)
  have rdPopLen := RD.pop rdJumpdest hPopLen (by simp only [List.length_cons]; omega)
  have rdMload128 := RD.mload 0 retWord aw rdPopLen hMload128
    hMload128Cost
    hMload128Value
    hMload128Aw
    (by omega)
  exact ⟨_, _, rdMload128⟩

set_option maxHeartbeats 2000000 in
theorem RD.solcUint256ReturnWordDecodeShortReverts {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem o : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size)
    (hMload64Cost :
      ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R →
        memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code
          (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
            ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
              ⟨1⟩) + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                  UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
                ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop h hPop0 (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 hPop1 (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 hPop2 (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ hPush64 (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ aw rdPush64 hMload64
    hMload64Cost
    hMload64Value
    hMload64Aw
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ hPush32
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 hDup2 (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 hLt (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hshort
  have rdIszero := RD.iszero rdLt hIszero (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero okPc hPushOk
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk hJumpi hcond
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough hPush0 hDupZero hRevert
    (by simp only [List.length_cons]; omega)

/-! ## Legacy solc high-level-call combinators -/

/-- Generic solc high-level-call `EXTCODESIZE` guard for the branch where the target account has
    deployed code. -/
theorem RD.solcExtcodesizeGuardOk {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc okPc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {target : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩) (target :: R) mem aw rdata
      (cA, σ) k' C' := by
  obtain ⟨_, _, rdExt⟩ :=
    RD.extcodesize h hExt
      (by simp only [List.length_cons]; omega)
  have rdIszero0 := RD.iszero rdExt hIszero0
    (by simp only [List.length_cons]; omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by simp only [List.length_cons]; omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.isZero
          (Reasoning.Theory.extCodeSizeWord σ target)) ≠ ⟨0⟩ := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hcodeSize]
    decide
  have rdJumpi := RD.jumpiT rdPush hJumpi hcond hjd
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi hJumpdest
    (by simp only [List.length_cons]; omega)
  have rdPop := RD.pop rdJumpdest hPop
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdPop⟩

/-- Generic solc high-level-call `EXTCODESIZE` guard plus `GAS`, stopping at the call opcode with
    existential gas. -/
theorem RD.solcExtcodesizeGuardOkGas {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {target : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hGas : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.GAS, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ gasWord k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      (gasWord :: target :: R) mem aw rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rdReady⟩ :=
    RD.solcExtcodesizeGuardOk h hcodeSize hExt hIszero0 hDup1 hIszero1 hPush hJumpi
      hjd hJumpdest hPop hov
  obtain ⟨gasWord, rdGas⟩ :=
    RD.gas rdReady hGas (by simp only [List.length_cons]; omega)
  exact ⟨gasWord, _, _, rdGas⟩

/-- Generic solc high-level-call `EXTCODESIZE` guard for the branch where the target account has no
    deployed code. -/
theorem RD.solcExtcodesizeGuardMissing {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {target : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (target :: target :: R) mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩)
    (hExt : decode code pc = some (.EXTCODESIZE, .none))
    (hIszero0 : decode code (pc + ⟨1⟩) = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) +
            UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) +
              UInt256.ofNat 2) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rdExt⟩ :=
    RD.extcodesize h hExt
      (by simp only [List.length_cons]; omega)
  have rdIszero0 := RD.iszero rdExt hIszero0
    (by simp only [List.length_cons]; omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by simp only [List.length_cons]; omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.isZero
          (Reasoning.Theory.extCodeSizeWord σ target)) = ⟨0⟩ := by
    rw [hcodeSize]
    decide
  have rdFallthrough := RD.jumpiNT rdPush hJumpi hcond
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough hPush0 hDupZero hRevert
    (by simp only [List.length_cons]; omega)

/-- Generic solc high-level-call success guard for the branch where a CALL-like status word is
    nonzero. -/
theorem RD.solcCallSuccessGuardOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {status : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (status :: R) mem aw rdata acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hIszero0 : decode code pc = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
      some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPop : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩) R mem aw rdata acc k' C' := by
  have rdIszero0 := RD.iszero h hIszero0
    (by omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.isZero status) ≠ ⟨0⟩ := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hstatus]
    decide
  have rdJumpi := RD.jumpiT rdPush hJumpi hcond hjd
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi hJumpdest
    (by simp only [List.length_cons]; omega)
  have rdPop := RD.pop rdJumpdest hPop
    (by omega)
  exact ⟨_, _, rdPop⟩

/-- Generic solc high-level-call success guard for the branch where a CALL-like status word is zero
    and the revert-data bubbling tail is executed. -/
theorem RD.solcCallSuccessGuardMissing {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {status : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (status :: R) mem aw rdata acc k C)
    (hstatus : status = ⟨0⟩)
    (hIszero0 : decode code pc = some (.ISZERO, .none))
    (hDup1 : decode code (pc + ⟨1⟩) = some (.DUP1, .none))
    (hIszero1 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none))
    (hPush : decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi : decode code ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
      some (.JUMPI, .none))
    (hReturndatasize :
      decode code (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush0 :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
            UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hReturndatacopy :
      decode code
          ((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
              UInt256.ofNat 2) + ⟨1⟩) =
        some (.RETURNDATACOPY, .none))
    (hReturndatasizeRevert :
      decode code
          (((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPushRevert0 :
      decode code
          ((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                  UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hRevert :
      decode code
          (((((((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) +
                    UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) =
        some (.REVERT, .none))
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  have rdIszero0 := RD.iszero h hIszero0
    (by omega)
  have rdDup1 := RD.dup1 rdIszero0 hDup1
    (by omega)
  have rdIszero1 := RD.iszero rdDup1 hIszero1
    (by simp only [List.length_cons]; omega)
  have rdPush := RD.push2 rdIszero1 okPc hPush
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.isZero status) = ⟨0⟩ := by
    rw [hstatus]
    decide
  have rdFallthrough := RD.jumpiNT rdPush hJumpi hcond
    (by simp only [List.length_cons]; omega)
  have rdReturndatasize := RD.returndatasize rdFallthrough hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush0 := RD.push1 rdReturndatasize ⟨0⟩ hPush0
    (by simp only [List.length_cons]; omega)
  have rdDupZero := RD.dup1 rdPush0 hDupZero
    (by simp only [List.length_cons]; omega)
  let len := UInt256.ofNat rdata.size
  let memout := rdata.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rdCopy := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rdDupZero hReturndatacopy
    (by
      change 0 + len.toNat ≤ rdata.size
      dsimp [len]
      rw [ulit_toNat' rdata.size hrdataSize]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rdReturndatasizeRevert := RD.returndatasize rdCopy hReturndatasizeRevert
    (by simp only [List.length_cons]; omega)
  have rdPushRevert0 := RD.push1 rdReturndatasizeRevert ⟨0⟩ hPushRevert0
    (by simp only [List.length_cons]; omega)
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rdPushRevert0 hRevert
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
/-- Same opaque `Θ` reach proof shape as `RD.call`, specialized to `STATICCALL`. -/
theorem RD.solcStaticcall {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1) ee.header false)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          (o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            outOffset.toNat outSize.toNat))
          o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
      (by unfold RD; exact Or.inl hoog),
      (by
        exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _))⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.STATICCALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_staticcall s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False :=
      eq_false (by omega)
    have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
    have hbal : ∀ y : UInt256, ((⟨0⟩ : UInt256) ≤ y) = True :=
      fun _ => eq_true (Fin.zero_le _)
    have hgtF : ∀ y : UInt256, ((⟨0⟩ : UInt256) > y) = False :=
      fun _ => eq_false (Fin.not_lt_zero _)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hdepthLt, hbal, hgtF, hdeqF, and_true, if_true,
      Bool.or_false] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    split at hXP
    · exact ⟨_, _, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
        (by unfold RD; exact Or.inl hXP),
        (by
          exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _))⟩
    · rename_i hP
      set mc := memoryExpansionCost s Operation.STATICCALL with hmc
      set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        (⟨0⟩ : UInt256) gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate with hgc
      set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        (⟨0⟩ : UInt256) gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate with hG
      set cg := UInt256.ofNat G with hcg
      set ce := Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        (⟨0⟩ : UInt256) s.accountMap s.substate with hce
      set θs := Θ s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader
        s.blocks s.accountMap s.σ₀
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
        s.executionEnv.sender (AccountAddress.ofUInt256 target)
        (toExecute s.accountMap (AccountAddress.ofUInt256 target)) cg
        (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth + 1) s.executionEnv.header false with hθs
      set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.2.1.toNat)
        with hgv
      have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
      have hσ : s.accountMap = σ := congrArg Prod.snd hacc
      have hw1 : s.σ₀ = s0.σ₀ := hworld.1
      have hw2 : s.genesisBlockHeader = s0.genesisBlockHeader := hworld.2.1
      have hw3 : s.blocks = s0.blocks := hworld.2.2
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hretle : θs.2.2.1.toNat ≤ cg.toNat := by
        rw [hθs]
        exact Theta_returnedGas_le s.executionEnv.blobVersionedHashes s.createdAccounts
          s.genesisBlockHeader s.blocks s.accountMap s.σ₀
          (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
          s.executionEnv.sender (AccountAddress.ofUInt256 target)
          (toExecute s.accountMap (AccountAddress.ofUInt256 target)) cg
          (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (s.executionEnv.depth + 1) s.executionEnv.header false
      have hcgle : cg.toNat ≤ G := by
        have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
        rw [h]; exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by rw [hgc, hG, hce]; rfl
      have hce1 : 1 ≤ ce := by
        rw [hce]
        have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra; omega
      have hg''le : θs.2.2.1.toNat + 1 ≤ gc := by omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]; omega
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      have hrefundCostPos : 1 ≤ gc - θs.2.2.1.toNat := by omega
      set callCharge := mc + (gc - θs.2.2.1.toNat) with hcallCharge
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - θs.2.2.1.toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨θs.1, θs.2.1, θs.2.2.2.2.1, θs.2.2.2.2.2,
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate, cg, k + 1,
        C + callCharge, ⟨θs.2.2.1, θs.2.2.2.1, ?_⟩, ?_, ?_⟩
      · rw [← hee, ← hcA, ← hσ, ← hmem, ← hw1, ← hw2, ← hw3, ← hθs]
      · unfold RD
        refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hcode
        · rw [hpc]
        · cases θs.2.2.2.2.1 <;> rfl
        · show gv = g.subNat (C + callCharge)
          exact hgvGas
        · show k + 1 ≤ C + callCharge
          rw [hcallCharge]
          omega
        · exact hCcallCharge
        · rw [hmem]
        · rw [haw]
        · rfl
        · rfl
        · exact hee
        · exact hworld
      · rw [hθs]
        exact Ethereum.EVM.theta_projection_output_size_lt_uint256
          s.executionEnv.blobVersionedHashes s.createdAccounts s.genesisBlockHeader s.blocks
          s.accountMap s.σ₀
          (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
          s.executionEnv.sender (AccountAddress.ofUInt256 target)
          (toExecute s.accountMap (AccountAddress.ofUInt256 target))
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          cg (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
          (s.executionEnv.depth + 1) s.executionEnv.header false
          (Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)

/-- Generic `STATICCALL` depth-limit `RD` combinator. -/
theorem RD.solcStaticcallDepthLimit {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.STATICCALL, .none))
    (hdepth : ee.depth = 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
        (ByteArray.empty.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat))
        ByteArray.empty (cA, σ) k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
    hworld⟩
  · exact ⟨k, C, by unfold RD; exact Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.STATICCALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth1024 : s.executionEnv.depth = 1024 := by rw [hee]; exact hdepth
    have st := step_staticcall s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False :=
      eq_false (by omega)
    have hdepthF : (s.executionEnv.depth < 1024) = False :=
      eq_false (by rw [hdepth1024]; exact lt_irrefl _)
    have hbal : ∀ y : UInt256, ((⟨0⟩ : UInt256) ≤ y) = True :=
      fun _ => eq_true (Fin.zero_le _)
    have hgtF : ∀ y : UInt256, ((⟨0⟩ : UInt256) > y) = False :=
      fun _ => eq_false (Fin.not_lt_zero _)
    have hdeqT : (s.executionEnv.depth == 1024) = true := by
      rw [beq_iff_eq]; exact hdepth1024
    simp only [List.length_cons, hovF, hdepthF, hbal, hgtF, hdeqT, and_false,
      Bool.or_true, if_true] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.STATICCALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return }
      s.substate with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return }
      s.substate with hG
    set ce := Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      (⟨0⟩ : UInt256) s.accountMap s.substate with hce
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat)
      with hgv
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G
        exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by
        rw [hgc, hG, hce]
        rfl
      have hce1 : 1 ≤ ce := by
        rw [hce]
        have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra
        omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]
        omega
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - (UInt256.ofNat G).toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨k + 1, C + callCharge, ?_⟩
      unfold RD
      refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcode
      · rw [hpc]
      · rfl
      · show gv = g.subNat (C + callCharge)
        exact hgvGas
      · show k + 1 ≤ C + callCharge
        rw [hcallCharge]
        omega
      · exact hCcallCharge
      · simp [hmem]
      · rw [haw]
      · rfl
      · simp [hcA, hσ]
      · exact hee
      · exact hworld

/-! ## Inlined solc address decoder

Newer optimized solc output can inline the usual address canonicality check instead of sharing a
small cleanup subroutine.  The block shape is:

`JUMPDEST; DUP1; CALLDATALOAD; PUSH1 1; PUSH1 1; PUSH1 160; SHL; SUB; DUP2; AND; DUP2; EQ;
PUSH2 ok; JUMPI; PUSH0; PUSH0; REVERT; JUMPDEST; SWAP2; SWAP1; POP; JUMP`.
-/

@[reducible] def solcInlinedDecodeAddrPc1 (pc : UInt256) : UInt256 := pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc2 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc1 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc3 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc2 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc5 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc3 pc + UInt256.ofNat 2
@[reducible] def solcInlinedDecodeAddrPc7 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc5 pc + UInt256.ofNat 2
@[reducible] def solcInlinedDecodeAddrPc9 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc7 pc + UInt256.ofNat 2
@[reducible] def solcInlinedDecodeAddrPc10 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc9 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc11 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc10 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc12 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc11 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc13 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc12 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc14 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc13 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc15 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc14 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc18 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc15 pc + UInt256.ofNat 3
@[reducible] def solcInlinedDecodeAddrPc19 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc18 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc22 (pc : UInt256) : UInt256 :=
  pc + UInt256.ofNat 22
@[reducible] def solcInlinedDecodeAddrPc23 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc22 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc24 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc23 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc25 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc24 pc + ⟨1⟩
@[reducible] def solcInlinedDecodeAddrPc26 (pc : UInt256) : UInt256 :=
  solcInlinedDecodeAddrPc25 pc + ⟨1⟩

set_option maxHeartbeats 400000 in
theorem RD.solcInlinedDecodeAddrOk {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD code ee g s0 pc (off :: ret :: R) mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
        < EVM.addressModulus)
    (hret : (D_J code 0).contains ret = true)
    (hd0 : decode code pc = some (.JUMPDEST, .none))
    (hd1 : decode code (solcInlinedDecodeAddrPc1 pc) = some (.DUP1, .none))
    (hd2 : decode code (solcInlinedDecodeAddrPc2 pc) = some (.CALLDATALOAD, .none))
    (hd3 : decode code (solcInlinedDecodeAddrPc3 pc) = some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd5 : decode code (solcInlinedDecodeAddrPc5 pc) = some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd7 : decode code (solcInlinedDecodeAddrPc7 pc) = some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd9 : decode code (solcInlinedDecodeAddrPc9 pc) = some (.SHL, .none))
    (hd10 : decode code (solcInlinedDecodeAddrPc10 pc) = some (.SUB, .none))
    (hd11 : decode code (solcInlinedDecodeAddrPc11 pc) = some (.DUP2, .none))
    (hd12 : decode code (solcInlinedDecodeAddrPc12 pc) = some (.AND, .none))
    (hd13 : decode code (solcInlinedDecodeAddrPc13 pc) = some (.DUP2, .none))
    (hd14 : decode code (solcInlinedDecodeAddrPc14 pc) = some (.EQ, .none))
    (hd15 : decode code (solcInlinedDecodeAddrPc15 pc)
        = some (.Push .PUSH2, some (solcInlinedDecodeAddrPc22 pc, 2)))
    (hd18 : decode code (solcInlinedDecodeAddrPc18 pc) = some (.JUMPI, .none))
    (hd22 : decode code (solcInlinedDecodeAddrPc22 pc) = some (.JUMPDEST, .none))
    (hjd22 : (D_J code 0).contains (solcInlinedDecodeAddrPc22 pc) = true)
    (hd23 : decode code (solcInlinedDecodeAddrPc23 pc) = some (.SWAP2, .none))
    (hd24 : decode code (solcInlinedDecodeAddrPc24 pc) = some (.SWAP1, .none))
    (hd25 : decode code (solcInlinedDecodeAddrPc25 pc) = some (.POP, .none))
    (hd26 : decode code (solcInlinedDecodeAddrPc26 pc) = some (.JUMP, .none))
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R) mem aw rdata acc k' C' := by
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hb : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) ≠ ⟨0⟩ := by
    rw [hmask, solcAddrCanon_eq hcanon]
    decide
  exact ⟨_, _, h.jumpdest hd0 (by simp only [List.length_cons]; omega)
    |>.dup1 hd1 (by simp only [List.length_cons]; omega)
    |>.calldataload hd2 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ hd5 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ hd7 (by simp only [List.length_cons]; omega)
    |>.shl hd9 (by simp only [List.length_cons]; omega)
    |>.sub hd10 (by simp only [List.length_cons]; omega)
    |>.dup2 hd11 (by simp only [List.length_cons]; omega)
    |>.and hd12 (by simp only [List.length_cons]; omega)
    |>.dup2 hd13 (by simp only [List.length_cons]; omega)
    |>.eq hd14 (by simp only [List.length_cons]; omega)
    |>.push2 (solcInlinedDecodeAddrPc22 pc) hd15 (by simp only [List.length_cons]; omega)
    |>.jumpiT hd18 hb hjd22 (by simp only [List.length_cons]; omega)
    |>.jumpdest hd22 (by simp only [List.length_cons]; omega)
    |>.swap2 hd23 (by omega)
    |>.swap1 hd24 (by simp only [List.length_cons]; omega)
    |>.pop hd25 (by simp only [List.length_cons]; omega)
    |>.jump hd26 hret (by simp only [List.length_cons]; omega)⟩

set_option maxHeartbeats 400000 in
theorem RD.solcInlinedDecodeAddrRevert {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD code ee g s0 pc (off :: ret :: R) mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          solcAddrMask) = ⟨0⟩)
    (hd0 : decode code pc = some (.JUMPDEST, .none))
    (hd1 : decode code (solcInlinedDecodeAddrPc1 pc) = some (.DUP1, .none))
    (hd2 : decode code (solcInlinedDecodeAddrPc2 pc) = some (.CALLDATALOAD, .none))
    (hd3 : decode code (solcInlinedDecodeAddrPc3 pc) = some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd5 : decode code (solcInlinedDecodeAddrPc5 pc) = some (.Push .PUSH1, some (⟨1⟩, 1)))
    (hd7 : decode code (solcInlinedDecodeAddrPc7 pc) = some (.Push .PUSH1, some (⟨160⟩, 1)))
    (hd9 : decode code (solcInlinedDecodeAddrPc9 pc) = some (.SHL, .none))
    (hd10 : decode code (solcInlinedDecodeAddrPc10 pc) = some (.SUB, .none))
    (hd11 : decode code (solcInlinedDecodeAddrPc11 pc) = some (.DUP2, .none))
    (hd12 : decode code (solcInlinedDecodeAddrPc12 pc) = some (.AND, .none))
    (hd13 : decode code (solcInlinedDecodeAddrPc13 pc) = some (.DUP2, .none))
    (hd14 : decode code (solcInlinedDecodeAddrPc14 pc) = some (.EQ, .none))
    (hd15 : decode code (solcInlinedDecodeAddrPc15 pc)
        = some (.Push .PUSH2, some (solcInlinedDecodeAddrPc22 pc, 2)))
    (hd18 : decode code (solcInlinedDecodeAddrPc18 pc) = some (.JUMPI, .none))
    (hr0 : decode code (solcInlinedDecodeAddrPc19 pc) = some (.PUSH0, .none))
    (hr1 : decode code (solcInlinedDecodeAddrPc19 pc + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (solcInlinedDecodeAddrPc19 pc + ⟨1⟩ + ⟨1⟩)
        = some (.REVERT, .none))
    (hov : R.length + 6 ≤ 1024) :
    RDrev code g s0 := by
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hb : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hmask]
    exact hnc
  exact (h.jumpdest hd0 (by simp only [List.length_cons]; omega)
    |>.dup1 hd1 (by simp only [List.length_cons]; omega)
    |>.calldataload hd2 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ hd5 (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ hd7 (by simp only [List.length_cons]; omega)
    |>.shl hd9 (by simp only [List.length_cons]; omega)
    |>.sub hd10 (by simp only [List.length_cons]; omega)
    |>.dup2 hd11 (by simp only [List.length_cons]; omega)
    |>.and hd12 (by simp only [List.length_cons]; omega)
    |>.dup2 hd13 (by simp only [List.length_cons]; omega)
    |>.eq hd14 (by simp only [List.length_cons]; omega)
    |>.push2 (solcInlinedDecodeAddrPc22 pc) hd15 (by simp only [List.length_cons]; omega)
    |>.jumpiNT hd18 hb (by simp only [List.length_cons]; omega)
    |>.revertStub hr0 hr1 hr2 (by simp only [List.length_cons]; omega) :
    RDrev code g s0)

/-! ## Solc dispatcher scaffold — small staged lemmas off the prologue

`solcGuardPrologueRD` lands at pc 8 with `[isZero(callvalue), callvalue]`.  These peel the standard
solc dispatcher: the callvalue guard (zero → continue, nonzero → revert), the calldatasize check
(`< 4` → revert), and the selector load (`PUSH0; CALLDATALOAD; PUSH1 0xe0; SHR` → `selWord`).  All
width-generic in the guard-target push (`pushConst`); concrete callers discharge the decode facts
with `by decide`.  Chain `selectorArmTaken`/`selectorArmNotTaken` after `solcSelectorLoad`. -/

/-- The callvalue-guard target push at pc 8, read from bytecode. -/
@[reducible] def solcGuardTgtOp (code : ByteArray) : Operation.POp := (pushAt code ⟨8⟩).1
@[reducible] def solcGuardTgt (code : ByteArray) : UInt256 := (pushAt code ⟨8⟩).2.1
@[reducible] def solcGuardTgtWidth (code : ByteArray) : ℕ := (pushAt code ⟨8⟩).2.2

/-- The pc of the callvalue guard's `JUMPI`. -/
@[reducible] def solcGuardJumpiPc (code : ByteArray) : UInt256 :=
  ⟨8⟩ + UInt256.ofNat (solcGuardTgtWidth code).succ

/-- The dispatcher body pc after the callvalue guard's `JUMPDEST; POP`. -/
@[reducible] def solcDispatchBodyPc (code : ByteArray) : UInt256 :=
  solcGuardTgt code + ⟨1⟩ + ⟨1⟩

/-- The short-calldata revert-target push in the dispatcher body, read from bytecode. -/
@[reducible] def solcCalldataRevertPushPc (code : ByteArray) : UInt256 :=
  solcDispatchBodyPc code + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩
@[reducible] def solcCalldataRevertTgtOp (code : ByteArray) : Operation.POp :=
  (pushAt code (solcCalldataRevertPushPc code)).1
@[reducible] def solcCalldataRevertTgt (code : ByteArray) : UInt256 :=
  (pushAt code (solcCalldataRevertPushPc code)).2.1
@[reducible] def solcCalldataRevertTgtWidth (code : ByteArray) : ℕ :=
  (pushAt code (solcCalldataRevertPushPc code)).2.2

/-- The pc of the calldata-size check's `JUMPI`. -/
@[reducible] def solcCalldataJumpiPc (code : ByteArray) : UInt256 :=
  solcCalldataRevertPushPc code + UInt256.ofNat (solcCalldataRevertTgtWidth code).succ

/-- The selector-load block pc (`PUSH0; CALLDATALOAD; PUSH1 0xe0; SHR`). -/
@[reducible] def solcSelectorLoadPc (code : ByteArray) : UInt256 :=
  solcCalldataJumpiPc code + ⟨1⟩

/-- The first selector-arm pc immediately after the selector-load block. -/
@[reducible] def solcFirstArmPcFromPrefix (code : ByteArray) : UInt256 :=
  solcSelectorLoadPc code + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩

/-- The standard solc external-entry prefix through selector load.

This bundles only bytecode shape.  The guard jump target's membership in `D_J` is kept as a separate
hypothesis because concrete examples usually discharge it with `jump_dest`, not pure computation. -/
@[reducible] def solcDispatchPrefixWellFormed (code : ByteArray) (firstArmPc : UInt256) : Prop :=
  decode code ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code ⟨4⟩ = some (.MSTORE, .none)
  ∧ decode code ⟨5⟩ = some (.CALLVALUE, .none)
  ∧ decode code ⟨6⟩ = some (.DUP1, .none)
  ∧ decode code ⟨7⟩ = some (.ISZERO, .none)
  ∧ solcGuardTgtOp code ≠ .PUSH0
  ∧ decode code ⟨8⟩
      = some (.Push (solcGuardTgtOp code), some (solcGuardTgt code, solcGuardTgtWidth code))
  ∧ decode code (solcGuardJumpiPc code) = some (.JUMPI, .none)
  ∧ decode code (solcGuardTgt code) = some (.JUMPDEST, .none)
  ∧ decode code (solcGuardTgt code + ⟨1⟩) = some (.POP, .none)
  ∧ decode code (solcDispatchBodyPc code) = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code (solcDispatchBodyPc code + UInt256.ofNat 2) = some (.CALLDATASIZE, .none)
  ∧ decode code (solcDispatchBodyPc code + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none)
  ∧ solcCalldataRevertTgtOp code ≠ .PUSH0
  ∧ decode code (solcCalldataRevertPushPc code)
      = some (.Push (solcCalldataRevertTgtOp code),
          some (solcCalldataRevertTgt code, solcCalldataRevertTgtWidth code))
  ∧ decode code (solcCalldataJumpiPc code) = some (.JUMPI, .none)
  ∧ decode code (solcSelectorLoadPc code) = some (.PUSH0, .none)
  ∧ decode code (solcSelectorLoadPc code + ⟨1⟩) = some (.CALLDATALOAD, .none)
  ∧ decode code (solcSelectorLoadPc code + ⟨1⟩ + ⟨1⟩)
      = some (.Push .PUSH1, some (⟨224⟩, 1))
  ∧ decode code (solcSelectorLoadPc code + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2)
      = some (.SHR, .none)
  ∧ solcFirstArmPcFromPrefix code = firstArmPc

/-- Discharge a concrete `solcDispatchPrefixWellFormed` proof by splitting the bundled bytecode
    facts and evaluating each closed decode equation. -/
macro "solc_dispatch_prefix" : tactic =>
  `(tactic|
    (dsimp [solcDispatchPrefixWellFormed]
     repeat' first | apply And.intro | decide))

/-- **Callvalue-zero guard.**  From the prologue cursor (`cv = 0`): take the guard `JUMPI` to its
    `JUMPDEST` and `POP` the call value, reaching the dispatcher body at `ctgt + 2` with empty stack. -/
theorem solcGuardCallvalueZero {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    {ctgt : UInt256} {wC : ℕ} {opC : Operation.POp} {k0 C0 : ℕ}
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨8⟩
          [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) k0 C0)
    (hwv : I.weiValue = ⟨0⟩) (hopC : opC ≠ .PUSH0)
    (hpushC : decode code ⟨8⟩ = some (.Push opC, some (ctgt, wC)))
    (hjumpi : decode code (⟨8⟩ + UInt256.ofNat wC.succ) = some (.JUMPI, .none))
    (hjmpdest : decode code ctgt = some (.JUMPDEST, .none))
    (hpop : decode code (ctgt + ⟨1⟩) = some (.POP, .none))
    (hjd : (D_J code 0).contains ctgt = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (ctgt + ⟨1⟩ + ⟨1⟩)
          [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C :=
  ⟨_, _, h.pushConst ctgt hopC hpushC (by simp only [List.length]; omega)
    |>.jumpiT hjumpi (by rw [hwv]; decide) hjd (by simp only [List.length]; omega)
    |>.jumpdest hjmpdest (by simp only [List.length]; omega)
    |>.pop hpop (by simp only [List.length]; omega)⟩

/-- **Callvalue-nonzero revert.**  `cv ≠ 0` ⇒ the guard `JUMPI` is not taken and falls into the
    `revert(0,0)` stub — the whole run reverts. -/
theorem solcGuardCallvalueNonzeroRevert {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    {ctgt : UInt256} {wC : ℕ} {opC : Operation.POp} {k0 C0 : ℕ}
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨8⟩
          [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
          (cA, σ) k0 C0)
    (hwv : I.weiValue ≠ ⟨0⟩) (hopC : opC ≠ .PUSH0)
    (hpushC : decode code ⟨8⟩ = some (.Push opC, some (ctgt, wC)))
    (hjumpi : decode code (⟨8⟩ + UInt256.ofNat wC.succ) = some (.JUMPI, .none))
    (hr0 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩) = some (.PUSH0, .none))
    (hr1 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) :=
  (h.pushConst ctgt hopC hpushC (by simp only [List.length]; omega)
    |>.jumpiNT hjumpi (isZero_eq_zero_of_ne hwv) (by simp only [List.length]; omega)).revertStub
    hr0 hr1 hr2 (by simp only [List.length]; omega)

/-- **Short-calldata revert.**  From the dispatcher body (post-`POP`, empty stack) with
    `calldatasize < 4`: `PUSH1 4; CALLDATASIZE; LT` is `1`, so the size `JUMPI` jumps to the
    `revert(0,0)` stub.  Width-generic in the revert-target push. -/
theorem solcCalldataShortRevert {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    {bodyPc rtgt : UInt256} {wR : ℕ} {opR : Operation.POp} {k0 C0 : ℕ}
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) bodyPc [] solcFreePtrMem (UInt256.ofNat 3)
          ByteArray.empty (cA, σ) k0 C0)
    (hsz : I.calldata.size < 4)
    (hd_p4 : decode code bodyPc = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd_cds : decode code (bodyPc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none))
    (hd_lt : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
    (hopR : opR ≠ .PUSH0)
    (hd_pR : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.Push opR, some (rtgt, wR)))
    (hd_ji : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat wR.succ)
              = some (.JUMPI, .none))
    (hd_jd : decode code rtgt = some (.JUMPDEST, .none)) (hjd : (D_J code 0).contains rtgt = true)
    (hr0 : decode code (rtgt + ⟨1⟩) = some (.PUSH0, .none))
    (hr1 : decode code (rtgt + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none))
    (hr2 : decode code (rtgt + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none)) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) :=
  (h.push1 ⟨4⟩ hd_p4 (by simp only [List.length]; omega)
    |>.calldatasize hd_cds (by simp only [List.length]; omega)
    |>.lt hd_lt (by simp only [List.length]; omega)
    |>.pushConst rtgt hopR hd_pR (by simp only [List.length]; omega)
    |>.jumpiT hd_ji (lt_four_ne_zero_of_lt hsz) hjd (by simp only [List.length]; omega)
    |>.jumpdest hd_jd (by simp only [List.length]; omega)).revertStub
    hr0 hr1 hr2 (by simp only [List.length]; omega)

/-- **Calldata-ok continue** (dual of `solcCalldataShortRevert`).  From the dispatcher body with
    `calldatasize ≥ 4`: `PUSH1 4; CALLDATASIZE; LT` is `0`, so the size `JUMPI` is not taken and
    falls through to the selector load (the `PUSH0` at the returned pc) with an empty stack. -/
theorem solcCalldataOk {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    {bodyPc selLoadTgt : UInt256} {wR : ℕ} {opR : Operation.POp} {k0 C0 : ℕ}
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) bodyPc [] solcFreePtrMem (UInt256.ofNat 3)
          ByteArray.empty (cA, σ) k0 C0)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hd_p4 : decode code bodyPc = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd_cds : decode code (bodyPc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none))
    (hd_lt : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
    (hopR : opR ≠ .PUSH0)
    (hd_pR : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.Push opR, some (selLoadTgt, wR)))
    (hd_ji : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat wR.succ)
              = some (.JUMPI, .none)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
        (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat wR.succ + ⟨1⟩)
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C :=
  ⟨_, _, h.push1 ⟨4⟩ hd_p4 (by simp only [List.length]; omega)
    |>.calldatasize hd_cds (by simp only [List.length]; omega)
    |>.lt hd_lt (by simp only [List.length]; omega)
    |>.pushConst selLoadTgt hopR hd_pR (by simp only [List.length]; omega)
    |>.jumpiNT hd_ji (lt_four_eq_zero_of_ge hsz hsize) (by simp only [List.length]; omega)⟩

/-- **Selector load.**  `PUSH0; CALLDATALOAD; PUSH1 0xe0; SHR` — load `calldata[0:32]` and shift
    right by 224, leaving the 4-byte function selector word on top.  The `selectorArm*` lemmas
    consume the result. -/
theorem solcSelectorLoad {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {loadPc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k0 C0 : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 loadPc rest mem aw rdata acc k0 C0)
    (hp0 : decode code loadPc = some (.PUSH0, .none))
    (hcdl : decode code (loadPc + ⟨1⟩) = some (.CALLDATALOAD, .none))
    (hp1 : decode code (loadPc + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨224⟩, 1)))
    (hshr : decode code (loadPc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.SHR, .none))
    (hov : rest.length + 2 ≤ 1024) :
    ∃ k C, RD code ee g s0 (loadPc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes 0 32)) ⟨224⟩ :: rest)
        mem aw rdata acc k C :=
  ⟨_, _, h.push0 hp0 (by omega)
    |>.calldataload hcdl (by omega)
    |>.push1 ⟨224⟩ hp1 (by simp only [List.length]; omega)
    |>.shr hshr (by omega)⟩

/-- Legacy solc selector load emitted as `PUSH1 0; CALLDATALOAD; PUSH1 0xe0; SHR`. -/
theorem solcLegacySelectorLoad {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {loadPc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k0 C0 : ℕ} {rest : List UInt256}
    (h : RD code ee g s0 loadPc rest mem aw rdata acc k0 C0)
    (hp0 : decode code loadPc = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hcdl : decode code (loadPc + UInt256.ofNat 2) = some (.CALLDATALOAD, .none))
    (hp1 : decode code (loadPc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨224⟩, 1)))
    (hshr : decode code (loadPc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) =
      some (.SHR, .none))
    (hov : rest.length + 2 ≤ 1024) :
    ∃ k C, RD code ee g s0
        (loadPc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
        (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes 0 32)) ⟨224⟩ :: rest)
        mem aw rdata acc k C :=
  ⟨_, _, h.push1 ⟨0⟩ hp0 (by omega)
    |>.calldataload hcdl (by omega)
    |>.push1 ⟨224⟩ hp1 (by simp only [List.length]; omega)
    |>.shr hshr (by omega)⟩

/-- **Standard solc dispatcher prefix.**  From `initState`, with zero callvalue and enough calldata
    for selector dispatch, run the free-pointer prologue, non-payable guard, calldata-size guard,
    and selector load, stopping at the first selector-dispatch pc with the selector word on stack.

This is the shared front half for both linear `EQ` selector chains and solc's one-level binary
`GT` split dispatcher. -/
theorem solcDispatchReachSelector {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    {firstPc : UInt256}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code firstPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) firstPc
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨hd0, hd2, hd4, hd5, hd6, hd7,
    hguardOp, hguardPush, hguardJumpi, hguardDest, hguardPop,
    hcdPush4, hcdSize, hcdLt, hcdOp, hcdPushRevert, hcdJumpi,
    hselPush0, hselLoad, hselPush224, hselShr, hfirst⟩ := hprefix
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode hd0 hd2 hd4 hd5 hd6 hd7
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt code) (opC := solcGuardTgtOp code) (wC := solcGuardTgtWidth code)
    h0 hwv hguardOp hguardPush hguardJumpi hguardDest hguardPop hguardJd
  obtain ⟨_, _, h2⟩ := solcCalldataOk
    (selLoadTgt := solcCalldataRevertTgt code)
    (opR := solcCalldataRevertTgtOp code) (wR := solcCalldataRevertTgtWidth code)
    h1 hsz hsize hcdPush4 hcdSize hcdLt hcdOp hcdPushRevert hcdJumpi
  obtain ⟨k3, C3, h3⟩ := solcSelectorLoad h2 hselPush0 hselLoad hselPush224 hselShr (by simp)
  refine ⟨k3, C3, ?_⟩
  simpa [solcSelectorWord, solcFirstArmPcFromPrefix, solcSelectorLoadPc,
    solcCalldataJumpiPc, solcCalldataRevertPushPc, solcDispatchBodyPc, hfirst] using h3

theorem solcLegacyDispatchReachSelector {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {bodyPc loadPc firstPc guardTgt revertTgt : UInt256}
    {guardWidth revertWidth : ℕ} {guardOp revertOp : Operation.POp}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hd0 : decode code ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)))
    (hd2 : decode code ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd4 : decode code ⟨4⟩ = some (.MSTORE, .none))
    (hd5 : decode code ⟨5⟩ = some (.CALLVALUE, .none))
    (hd6 : decode code ⟨6⟩ = some (.DUP1, .none))
    (hd7 : decode code ⟨7⟩ = some (.ISZERO, .none))
    (hguardOp : guardOp ≠ .PUSH0)
    (hguardPush : decode code ⟨8⟩ = some (.Push guardOp, some (guardTgt, guardWidth)))
    (hguardJumpi :
      decode code (⟨8⟩ + UInt256.ofNat guardWidth.succ) = some (.JUMPI, .none))
    (hguardDest : decode code guardTgt = some (.JUMPDEST, .none))
    (hguardPop : decode code (guardTgt + ⟨1⟩) = some (.POP, .none))
    (hguardJd : (D_J code 0).contains guardTgt = true)
    (hbody : guardTgt + ⟨1⟩ + ⟨1⟩ = bodyPc)
    (hcdPush4 : decode code bodyPc = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hcdSize : decode code (bodyPc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none))
    (hcdLt : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
    (hrevertOp : revertOp ≠ .PUSH0)
    (hrevertPush :
      decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push revertOp, some (revertTgt, revertWidth)))
    (hcdJumpi :
      decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat revertWidth.succ) =
        some (.JUMPI, .none))
    (hload :
      bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat revertWidth.succ + ⟨1⟩ =
        loadPc)
    (hselPush0 : decode code loadPc = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hselLoad : decode code (loadPc + UInt256.ofNat 2) = some (.CALLDATALOAD, .none))
    (hselPush224 :
      decode code (loadPc + UInt256.ofNat 2 + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨224⟩, 1)))
    (hselShr :
      decode code (loadPc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) =
        some (.SHR, .none))
    (hfirst : loadPc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ = firstPc) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) firstPc
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode hd0 hd2 hd4 hd5 hd6 hd7
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := guardTgt) (opC := guardOp) (wC := guardWidth)
    h0 hwv hguardOp hguardPush hguardJumpi hguardDest hguardPop hguardJd
  have h1body := by
    simpa [hbody] using h1
  obtain ⟨_, _, h2⟩ := solcCalldataOk
    (selLoadTgt := revertTgt) (opR := revertOp) (wR := revertWidth)
    h1body hsz hsize hcdPush4 hcdSize hcdLt hrevertOp hrevertPush hcdJumpi
  have h2load := by
    simpa [hload] using h2
  obtain ⟨k3, C3, h3⟩ :=
    solcLegacySelectorLoad h2load hselPush0 hselLoad hselPush224 hselShr (by simp)
  exact ⟨k3, C3, by simpa [solcSelectorWord, hfirst] using h3⟩

/-- **Standard solc dispatcher reach.**  From `initState`, with `callvalue = 0`, enough calldata for
    selector dispatch, and a matching selector arm `i`, run the whole external-entry scaffold:
    free-pointer prologue, callvalue guard, calldata-size guard, selector load, and `RD.dispatchTo`.

The bytecode-shape facts for the prefix are bundled in `solcDispatchPrefixWellFormed`; the selector
arms remain the existing `RD.dispatchTo` interface so single-arm and multi-arm dispatchers share the
same lemma. -/
theorem solcDispatchReachBody {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    {firstArmPc bodyPC : UInt256} {i : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code firstArmPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true)
    (hwf : ∀ j, j ≤ i → armWellFormed code (nthArmPc code firstArmPc j))
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat code (nthArmPc code firstArmPc j))
        (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat code (nthArmPc code firstArmPc i))
        (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains bodyPC = true)
    (hbody : armTgt code (nthArmPc code firstArmPc i) = bodyPC) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [solcSelectorWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h3'⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hsz hsize hprefix hguardJd
  exact RD.dispatchTo bodyPC i h3' hwf heq0 htake (by rw [hbody]; exact hjd) hbody (by simp)

/-! ### One-level binary selector dispatch

For larger contracts, solc may replace the single linear `EQ` chain with one `GT` pivot split whose
taken and fall-through branches are ordinary linear selector chains.  These two drivers share the
same prefix as `solcDispatchReachBody`, then perform the pivot split and finish with `RD.dispatchTo`
inside the selected half.
-/

/-- Reach a body through the **fall-through/high** half of a one-level binary selector dispatcher.
    The split pc has shape `DUP1; PUSH4 pivot; GT; PUSHk low; JUMPI`, the pivot `GT` is false, and
    the high half begins at the split fall-through pc. -/
theorem solcBinaryDispatchReachHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {splitPc bodyPC : UInt256} {i : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code splitPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true)
    (hsplit : selectorSplitWellFormed code splitPc)
    (hpivot : UInt256.gt (armSelNat code splitPc) (solcSelectorWord I) = ⟨0⟩)
    (hwf : ∀ j, j ≤ i →
      armWellFormed code (nthArmPc code (selArmNextPc splitPc (armTgtWidth code splitPc)) j))
    (heq0 : ∀ j, j < i →
      UInt256.eq
        (armSelNat code (nthArmPc code (selArmNextPc splitPc (armTgtWidth code splitPc)) j))
        (solcSelectorWord I) = ⟨0⟩)
    (htake : UInt256.eq
        (armSelNat code (nthArmPc code (selArmNextPc splitPc (armTgtWidth code splitPc)) i))
        (solcSelectorWord I) ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains bodyPC = true)
    (hbody : armTgt code (nthArmPc code (selArmNextPc splitPc (armTgtWidth code splitPc)) i)
        = bodyPC) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hsplitPc⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hsz hsize hprefix hguardJd
  have hfirst : RD code I g (initState cA gh bl σ σ₀ g A I)
      (selArmNextPc splitPc (armTgtWidth code splitPc)) [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ :=
    RD.selectorSplitNotTakenAuto hsplitPc hsplit hpivot (by simp)
  exact RD.dispatchTo bodyPC i hfirst hwf heq0 htake (by rw [hbody]; exact hjd) hbody
    (by simp)

/-- Reach a body through the **taken/low** half of a one-level binary selector dispatcher.  The
    split pc has shape `DUP1; PUSH4 pivot; GT; PUSHk lowJumpdest; JUMPI`; after the taken jump, the
    driver steps the low-half `JUMPDEST` and then runs the linear `EQ` chain beginning at
    `armTgt code splitPc + 1`. -/
theorem solcBinaryDispatchReachLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {splitPc bodyPC : UInt256} {i : ℕ}
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hprefix : solcDispatchPrefixWellFormed code splitPc)
    (hguardJd : (D_J code 0).contains (solcGuardTgt code) = true)
    (hsplit : selectorSplitWellFormed code splitPc)
    (hpivot : UInt256.gt (armSelNat code splitPc) (solcSelectorWord I) ≠ ⟨0⟩)
    (hsplitJd : (D_J code 0).contains (armTgt code splitPc) = true)
    (hlowJumpdest : decode code (armTgt code splitPc) = some (.JUMPDEST, .none))
    (hwf : ∀ j, j ≤ i →
      armWellFormed code (nthArmPc code (armTgt code splitPc + ⟨1⟩) j))
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat code (nthArmPc code (armTgt code splitPc + ⟨1⟩) j))
        (solcSelectorWord I) = ⟨0⟩)
    (htake : UInt256.eq (armSelNat code (nthArmPc code (armTgt code splitPc + ⟨1⟩) i))
        (solcSelectorWord I) ≠ ⟨0⟩)
    (hjd : (D_J code 0).contains bodyPC = true)
    (hbody : armTgt code (nthArmPc code (armTgt code splitPc + ⟨1⟩) i) = bodyPC) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) bodyPC
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hsplitPc⟩ := solcDispatchReachSelector (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hsz hsize hprefix hguardJd
  have hlowJd : RD code I g (initState cA gh bl σ σ₀ g A I) (armTgt code splitPc)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ :=
    RD.selectorSplitTakenAuto hsplitPc hsplit hpivot hsplitJd (by simp)
  have hfirst : RD code I g (initState cA gh bl σ σ₀ g A I)
      (armTgt code splitPc + ⟨1⟩) [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ :=
    hlowJd.jumpdest hlowJumpdest (by simp)
  exact RD.dispatchTo bodyPC i hfirst hwf heq0 htake (by rw [hbody]; exact hjd) hbody
    (by simp)

end Reasoning.Reach
