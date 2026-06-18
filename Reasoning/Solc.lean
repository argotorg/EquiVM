import Reasoning.Memory
import Reasoning.Stepping
import Reasoning.Reach

/-!
# Solc — reusable boilerplate shared by every solc-compiled contract

Solidity's compiler emits the same prologue for every external function: a free-memory-pointer
store, a non-payable guard, a `calldatasize` check, and a **4-byte selector dispatch**.  The
selector dispatch is identical across contracts apart from the four selector bytes, so it is proved
here once, generically, and instantiated per contract (`truthEvmSelector`, `powEvmSelector`).

Everything in this file is contract-agnostic; the only inputs are the four selector bytes and the
matching `UInt256` constant.
-/

namespace Reasoning.Theory

open Ethereum Ethereum.EVM Reasoning.Reach

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
theorem extract4_eq_iff (cd : ByteArray) (c0 c1 c2 c3 : UInt8) (hsz : 4 ≤ cd.size) :
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

/-! ## The free-memory-pointer memory

Every solc contract opens with `PUSH1 0x80; PUSH1 0x40; MSTORE`, storing the initial free pointer
`0x80` at `0x40`.  This is the resulting memory and the read-back lemma the epilogue's
`MLOAD 0x40` needs — contract-agnostic. -/

/-- Memory after solc stores the free pointer `0x80` at `0x40`. -/
noncomputable def solcFreePtrMem : ByteArray :=
  (UInt256.toByteArray ⟨128⟩).write 0 ByteArray.empty 64 32

theorem solcFreePtrMem_eq :
    solcFreePtrMem
      = (ByteArray.empty ++ ffi.ByteArray.zeroes (USize.ofNat 64)) ++ UInt256.toByteArray ⟨128⟩ := by
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
    (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)).size = 128 := by
  rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size _ (by norm_num)]

/-- Memory after solc stores a 32-byte return word `val` at `0x80`, over the free-pointer memory —
    the shape every solc ABI-encoder's epilogue produces (its `RETURN`s `mem[0x80 .. 0xa0] = val`). -/
noncomputable def solcReturnMem (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 solcFreePtrMem 128 32

theorem solcReturnMem_eq (val : UInt256) :
    solcReturnMem val = (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++ UInt256.toByteArray val := by
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
    simpa [UInt256.toNat] using s.machineState.activeWords.val.isLt
  have hof : UInt256.ofNat s.machineState.activeWords.toNat = s.machineState.activeWords :=
    u256_inj (by show (Fin.ofNat _ _).val = _
                 simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hlt)
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk,
    List.getElem!_cons_zero, List.getElem!_cons_succ,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, MachineState.M, hof, Nat.sub_self]

/-- `REVERT` (or `RETURN`) memory-expansion cost when the **offset is zero** and the length `len` is
    arbitrary (e.g. the post-call `RETURNDATACOPY`+`REVERT` failure tail copies/​reverts the whole
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

end Reasoning.Theory

namespace Reasoning.Reach
open Ethereum Ethereum.EVM Reasoning.Theory

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

/-! ## Solc dispatcher scaffold — small staged lemmas off the prologue

`solcGuardPrologueRD` lands at pc 8 with `[isZero(callvalue), callvalue]`.  These peel the standard
solc dispatcher: the callvalue guard (zero → continue, nonzero → revert), the calldatasize check
(`< 4` → revert), and the selector load (`PUSH0; CALLDATALOAD; PUSH1 0xe0; SHR` → `selWord`).  All
width-generic in the guard-target push (`pushConst`); concrete callers discharge the decode facts
with `by decide`.  Chain `selectorArmTaken`/`selectorArmNotTaken` after `solcSelectorLoad`. -/

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

end Reasoning.Reach
