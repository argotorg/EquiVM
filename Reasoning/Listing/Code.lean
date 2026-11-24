import Reasoning.Listing.Sound
import Reasoning.Immutables

/-!
# Listing — EquiVM's code is the listing's filled code

EquiVM's block theorems are stated over the runtime code written one of two ways:

* a contract without immutables: a `ByteArray` constant (`fooBytecode`);
* a contract with immutables: `layout.runtime template words`, the template with the 32-byte
  word `words key` written at the offset of every site `(offset, 32, key)` of the layout
  (`Reasoning/Immutables.lean`, a `writeCascade` of `writeWord`s).

The listing's theorems (`Reasoning/Listing/Sound.lean`) are about `filled bytes σ table`.  This
file shows the two are the same code, given a closed check per contract:

* `runtime_eq_filled`: if `codeCheck` holds, `layout.runtime template words` is
  `filled bytes (immσ names words) table` for every `words`, immutable number `i` of the listing
  being the key `names[i]`.
* `eq_filled`: if `plainCheck` holds, the constant is `filled bytes σ table` for every `σ`.

The proof is byte by byte.  Both sides are described by `patch`: a list of 32-byte windows
`(offset, word)`, the first window that holds byte `n` giving its value, the template giving the
bytes outside every window.

* The layout's writes are read in reverse order (the last write wins), in any order of the sites
  (`cascade_getElem?`).
* The filled code's windows are the immutable pushes' data, in offset order (`fill_getElem?`);
  they do not overlap (`immSites_unique`).

`codeCheck` then asks that every site be the data of an immutable push of the right name, that
every immutable push be a site, and that the template agree with `bytes` outside the sites (the
template may hold anything at the sites).  Two sites at the same offset are allowed; they must
then name the same key.

Both checks are structural list walks, proved per contract by `decide +kernel` after unfolding a
chunked `ByteArray` constant into one right-nested list of chunks:
`simp only [fooBytecode, ByteArray.data_append, Array.toList_append, List.append_assoc]`
(`List.append_assoc` matters: walking a left-nested append of many chunks is several times
slower in the kernel).
-/

open Ethereum Ethereum.EVM

set_option autoImplicit false

namespace Reasoning.Listing

/-- The words of `words` as the listing numbers them: immutable `i` is the key `names[i]`. -/
def immσ (names : List String) (words : String → UInt256) : Nat → UInt256 :=
  fun i => words (names.getD i "")

/-! ## Windows -/

/-- Is byte `n` one of the 32 bytes of the window at offset `o`? -/
def inWin (n o : Nat) : Bool := decide (o ≤ n) && decide (n < o + 32)

/-- Byte `n` of a code that is `d` outside the windows `S`: the first window holding `n` gives
its byte of the word. -/
def patch : List (Nat × UInt256) → Nat → Option UInt8 → Option UInt8
  | [], _, d => d
  | (o, w) :: rest, n, d => if inWin n o then (wordBytes w)[n - o]? else patch rest n d

theorem patch_append (n : Nat) (d : Option UInt8) :
    ∀ (A B : List (Nat × UInt256)), patch (A ++ B) n d = patch A n (patch B n d)
  | [], _ => rfl
  | (o, w) :: A, B => by
    simp only [List.cons_append, patch, patch_append n d A B]

/-- No window holds `n`: the default. -/
theorem patch_none {n : Nat} {d : Option UInt8} :
    ∀ {S : List (Nat × UInt256)}, (∀ q ∈ S, inWin n q.1 = false) → patch S n d = d
  | [], _ => rfl
  | (o, w) :: S, h => by
    have h1 : inWin n o = false := h (o, w) (by simp)
    simp only [patch, h1]
    exact patch_none (fun q hq => h q (by simp [hq]))

/-- Either no window holds `n` and the byte is the default, or some window holds `n` and gives
the byte. -/
theorem patch_cases (n : Nat) (d : Option UInt8) :
    ∀ (S : List (Nat × UInt256)),
      (patch S n d = d ∧ ∀ q ∈ S, inWin n q.1 = false) ∨
        ∃ q ∈ S, inWin n q.1 = true ∧ patch S n d = (wordBytes q.2)[n - q.1]?
  | [] => Or.inl ⟨rfl, by simp⟩
  | (o, w) :: S => by
    by_cases h : inWin n o = true
    · exact Or.inr ⟨(o, w), by simp, h, by simp [patch, h]⟩
    · have h' : inWin n o = false := by simpa using h
      rcases patch_cases n d S with ⟨he, hn⟩ | ⟨q, hq, hi, he⟩
      · refine Or.inl ⟨by simp [patch, h', he], ?_⟩
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact h'
        · exact hn q hq
      · exact Or.inr ⟨q, by simp [hq], hi, by simp [patch, h', he]⟩

/-! ## The immutables of a listing -/

/-- The instruction is an immutable push. -/
def Instr.isImm : Instr → Bool
  | .immutable _ => true
  | _ => false

/-- The data window of the instruction at `pc`, if it is an immutable push: the offset of its
data and its immutable number. -/
def Instr.site (pc : Nat) : Instr → List (Nat × Nat)
  | .immutable k => [(pc + 1, k)]
  | _ => []

/-- The data windows of the immutable pushes of a run starting at `pc`, in offset order. -/
def immSites : Nat → List Instr → List (Nat × Nat)
  | _, [] => []
  | pc, i :: rest => i.site pc ++ immSites (pc + i.width) rest

theorem width_pos' (i : Instr) : 1 ≤ i.width := by
  unfold Instr.width; omega

theorem immSites_ge : ∀ (J : List Instr) (pc : Nat), ∀ p ∈ immSites pc J, pc + 1 ≤ p.1
  | [], _, _, hp => by simp [immSites] at hp
  | i :: rest, pc, p, hp => by
    have hw := width_pos' i
    simp only [immSites, List.mem_append] at hp
    rcases hp with hp | hp
    · cases i <;> simp [Instr.site] at hp
      subst hp; simp
    · have := immSites_ge rest (pc + i.width) p hp
      omega

/-- The data windows of two immutable pushes never overlap. -/
theorem immSites_unique (n : Nat) : ∀ (J : List Instr) (pc : Nat) (a b : Nat × Nat),
    a ∈ immSites pc J → b ∈ immSites pc J → inWin n a.1 = true → inWin n b.1 = true → a = b
  | [], _, _, _, ha, _, _, _ => by simp [immSites] at ha
  | i :: rest, pc, a, b, ha, hb, hia, hib => by
    simp only [inWin, Bool.and_eq_true, decide_eq_true_eq] at hia hib
    cases i with
    | immutable k =>
      have hge := immSites_ge rest (pc + 33)
      have hw : (Instr.immutable k).width = 33 := rfl
      simp only [immSites, Instr.site, hw, List.singleton_append, List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · have := hge b hb; simp at hia; omega
      · have := hge a ha; simp at hib; omega
      · exact immSites_unique n rest (pc + 33) a b ha hb
          (by simp [inWin]; omega) (by simp [inWin]; omega)
    | op o =>
      simp only [immSites, Instr.site, List.nil_append] at ha hb
      exact immSites_unique n rest _ a b ha hb (by simp [inWin]; omega) (by simp [inWin]; omega)
    | push o v =>
      simp only [immSites, Instr.site, List.nil_append] at ha hb
      exact immSites_unique n rest _ a b ha hb (by simp [inWin]; omega) (by simp [inWin]; omega)

/-! ## The filled code, byte by byte -/

theorem immSites_of_fits_zero : ∀ (J : List Instr) (pc : Nat), fits J 0 = true → immSites pc J = []
  | [], _, _ => rfl
  | i :: rest, pc, h => by
    simp only [fits, Bool.and_eq_true] at h
    cases i with
    | immutable k => simp [Instr.fitsIn] at h
    | op o => simp only [immSites, Instr.site, List.nil_append]; exact immSites_of_fits_zero rest _ (by simpa using h.2)
    | push o v => simp only [immSites, Instr.site, List.nil_append]; exact immSites_of_fits_zero rest _ (by simpa using h.2)

theorem fill_nil_of_fits_zero (σ : Nat → UInt256) :
    ∀ (J : List Instr), fits J 0 = true → fill σ J [] = []
  | [], _ => rfl
  | i :: rest, h => by
    simp only [fits, Bool.and_eq_true] at h
    cases i with
    | immutable k => simp [Instr.fitsIn] at h
    | op o => simp only [fill, Instr.data]; simpa using fill_nil_of_fits_zero σ rest (by simpa using h.2)
    | push o v => simp only [fill, Instr.data]; simpa using fill_nil_of_fits_zero σ rest (by simpa using h.2)

/-- Every immutable push's data lies inside the code, `n` being its length from `pc` on. -/
theorem immSites_bound : ∀ (J : List Instr) (pc n : Nat), fits J n = true →
    ∀ p ∈ immSites pc J, p.1 + 32 ≤ pc + n
  | [], _, _, _, _, hp => by simp [immSites] at hp
  | i :: rest, pc, n, h, p, hp => by
    simp only [fits, Bool.and_eq_true] at h
    obtain ⟨hi, hrest⟩ := h
    simp only [immSites, List.mem_append] at hp
    by_cases hroom : i.width ≤ n
    · rcases hp with hp | hp
      · cases i <;> simp [Instr.site] at hp
        subst hp; simp [Instr.fitsIn] at hi; simp; omega
      · have := immSites_bound rest (pc + i.width) (n - i.width) hrest p hp
        omega
    · have h0 : n - i.width = 0 := by omega
      rw [h0] at hrest
      rw [immSites_of_fits_zero rest _ hrest] at hp
      rcases hp with hp | hp
      · cases i <;> simp [Instr.site] at hp
        subst hp; simp [Instr.fitsIn] at hi; omega
      · simp at hp

/-- Byte `n` of `fill σ J l`, the run `J` starting at `pc`: the immutables' words over the
template, where the template has room for each immutable (`fits`). -/
theorem fill_getElem? (σ : Nat → UInt256) : ∀ (J : List Instr) (pc : Nat) (l : List UInt8),
    fits J l.length = true → ∀ n,
      (fill σ J l)[n]? = patch ((immSites pc J).map (fun p => (p.1, σ p.2))) (pc + n) l[n]?
  | [], _, _, _, _ => rfl
  | i :: rest, pc, l, h, n => by
    simp only [fits, Bool.and_eq_true] at h
    obtain ⟨hi, hrest⟩ := h
    by_cases himm : ∃ k, i = .immutable k
    · obtain ⟨k, rfl⟩ := himm
      have hw : (Instr.immutable k).width = 33 := rfl
      have h33 : 33 ≤ l.length := by simpa [Instr.fitsIn] using hi
      have hfill : fill σ (.immutable k :: rest) l =
          l.take 1 ++ wordBytes (σ k) ++ fill σ rest (l.drop 33) := rfl
      have hsites : immSites pc (.immutable k :: rest) = (pc + 1, k) :: immSites (pc + 33) rest := rfl
      rw [hfill, hsites, List.map_cons]
      simp only [patch]
      have hwl := wordBytes_length (σ k)
      have htl : (l.take 1).length = 1 := by simp; omega
      by_cases hn0 : n = 0
      · subst hn0
        rw [if_neg (by simp [inWin]), patch_none]
        · rw [List.append_assoc, List.getElem?_append_left (by omega)]
          simp
        · intro q hq
          simp only [List.mem_map] at hq
          obtain ⟨p, hp, rfl⟩ := hq
          have := immSites_ge rest (pc + 33) p hp
          simp [inWin]; omega
      · by_cases hn33 : n < 33
        · have hyes : inWin (pc + n) (pc + 1) = true := by simp [inWin]; omega
          rw [if_pos hyes, List.append_assoc, List.getElem?_append_right (by omega), htl,
            List.getElem?_append_left (by omega)]
          congr 1; omega
        · have hno : inWin (pc + n) (pc + 1) = false := by simp [inWin]; omega
          rw [if_neg (by simp [hno]), List.getElem?_append_right (by simp; omega)]
          have hlen : (l.take 1 ++ wordBytes (σ k)).length = 33 := by simp [hwl]; omega
          rw [hlen, fill_getElem? σ rest (pc + 33) (l.drop 33) (by simpa [hw] using hrest) (n - 33),
            List.getElem?_drop]
          have e1 : pc + 33 + (n - 33) = pc + n := by omega
          have e2 : 33 + (n - 33) = n := by omega
          rw [e1, e2]
    · have hdata : i.data σ l = (l.drop 1).take (i.width - 1) := by
        cases i with
        | immutable k => exact absurd ⟨k, rfl⟩ himm
        | op o => rfl
        | push o v => rfl
      have hsite : i.site pc = [] := by
        cases i with
        | immutable k => exact absurd ⟨k, rfl⟩ himm
        | op o => rfl
        | push o v => rfl
      have hw := width_pos' i
      have htake : l.take 1 ++ (l.drop 1).take (i.width - 1) = l.take i.width := by
        rw [← List.take_add]; congr 1; omega
      have hfill : fill σ (i :: rest) l = l.take i.width ++ fill σ rest (l.drop i.width) := by
        rw [fill, hdata, htake]
      have hsites : immSites pc (i :: rest) = immSites (pc + i.width) rest := by
        rw [immSites, hsite, List.nil_append]
      rw [hfill, hsites]
      by_cases hroom : i.width ≤ l.length
      · have htl : (l.take i.width).length = i.width := by simp; omega
        by_cases hn : n < i.width
        · rw [List.getElem?_append_left (by omega), List.getElem?_take, if_pos hn, patch_none]
          intro q hq
          simp only [List.mem_map] at hq
          obtain ⟨p, hp, rfl⟩ := hq
          have := immSites_ge rest (pc + i.width) p hp
          simp [inWin]; omega
        · rw [List.getElem?_append_right (by omega), htl,
            fill_getElem? σ rest (pc + i.width) (l.drop i.width) (by simpa using hrest),
            List.getElem?_drop]
          have e1 : pc + i.width + (n - i.width) = pc + n := by omega
          have e2 : i.width + (n - i.width) = n := by omega
          rw [e1, e2]
      · have h0 : l.length - i.width = 0 := by omega
        rw [h0] at hrest
        have hd : l.drop i.width = [] := List.drop_eq_nil_of_le (by omega)
        rw [hd, fill_nil_of_fits_zero σ rest hrest, immSites_of_fits_zero rest _ hrest,
          List.append_nil, List.take_of_length_le (by omega)]
        rfl

/-- Over a run with no immutables, `fill` copies the template. -/
theorem fill_noImm (σ : Nat → UInt256) :
    ∀ (J : List Instr) (l : List UInt8), J.all (fun i => !i.isImm) = true → fill σ J l = l
  | [], _, _ => rfl
  | i :: rest, l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hdata : i.data σ l = (l.drop 1).take (i.width - 1) := by
      cases i with
      | immutable k => simp [Instr.isImm] at h
      | op o => rfl
      | push o v => rfl
    have hw := width_pos' i
    have htake : l.take 1 ++ (l.drop 1).take (i.width - 1) = l.take i.width := by
      rw [← List.take_add]; congr 1; omega
    rw [fill, hdata, htake, fill_noImm σ rest _ h.2, List.take_append_drop]

/-! ## EquiVM's code, byte by byte -/

theorem fromBytes'_inj : ∀ {a b : List UInt8}, a.length = b.length →
    fromBytes' a = fromBytes' b → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [fromBytes'] at h
    have hx : x.toFin.val < 256 := x.toFin.isLt
    have hy : y.toFin.val < 256 := y.toFin.isLt
    have h1 : x.toFin.val = y.toFin.val := by omega
    have h2 : fromBytes' a = fromBytes' b := by omega
    have hxy : x = y := UInt8.toNat_inj.mp h1
    rw [hxy, fromBytes'_inj (by simpa using hl) h2]

/-- A word's `toByteArray` is its 32 big-endian bytes `wordBytes`. -/
theorem toByteArray_toList (w : UInt256) :
    (UInt256.toByteArray w).data.toList = wordBytes w := by
  have hv : fromBytesBigEndian (UInt256.toByteArray w).data.toList =
      fromBytesBigEndian (wordBytes w) := by
    rw [fromBytesBigEndian_wordBytes, ← byteArray_toList]
    exact Reasoning.Theory.fromByteArrayBigEndian_toByteArray w
  have hl : (UInt256.toByteArray w).data.toList.length = (wordBytes w).length := by
    rw [wordBytes_length, Array.length_toList]; exact Reasoning.Theory.toByteArray_size w
  simp only [fromBytesBigEndian, Function.comp] at hv
  have hrev := fromBytes'_inj (by simpa using hl) hv
  simpa using hrev

/-- `writeWord` inside the code, as a list. -/
theorem writeWord_toList (m : ByteArray) (off : Nat) (w : UInt256) (h : off + 32 ≤ m.size) :
    (Reasoning.Theory.writeWord m off w).data.toList =
      m.data.toList.take off ++ wordBytes w ++ m.data.toList.drop (off + 32) := by
  unfold Reasoning.Theory.writeWord
  rw [Reasoning.Theory.write32_eq _ _ _ (by rw [Reasoning.Theory.toByteArray_size]) (by omega)]
  simp only [ByteArray.data_append, Array.toList_append, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
    toByteArray_toList]
  have hw : (wordBytes w).take 32 = wordBytes w :=
    List.take_of_length_le (by rw [wordBytes_length])
  have hd : (m.data.toList.drop (off + 32)).take (m.size - (off + 32)) =
      m.data.toList.drop (off + 32) :=
    List.take_of_length_le (by simp)
  rw [hw, hd]

/-- Byte `n` after one `writeWord` inside the code. -/
theorem writeWord_getElem? (m : ByteArray) (o : Nat) (w : UInt256) (h : o + 32 ≤ m.size)
    (n : Nat) :
    (Reasoning.Theory.writeWord m o w).data.toList[n]? = patch [(o, w)] n m.data.toList[n]? := by
  rw [writeWord_toList m o w h]
  have hL : m.data.toList.length = m.size := Array.length_toList
  have hwl := wordBytes_length w
  have htl : (m.data.toList.take o).length = o := by simp [hL]; omega
  simp only [patch, inWin, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h1 : n < o
  · rw [if_neg (by omega), List.append_assoc, List.getElem?_append_left (by omega),
      List.getElem?_take, if_pos h1]
  · by_cases h2 : n < o + 32
    · rw [if_pos (by omega), List.append_assoc, List.getElem?_append_right (by omega), htl,
        List.getElem?_append_left (by omega)]
    · rw [if_neg (by omega), List.getElem?_append_right (by simp [hwl]; omega)]
      simp only [List.length_append, htl, hwl, List.getElem?_drop]
      congr 1; omega

/-- Byte `n` after a cascade of `writeWord`s inside the code: the last write holding `n` gives
it, in whatever order the writes come. -/
theorem cascade_getElem? : ∀ (ws : List (Nat × UInt256)) (m : ByteArray),
    (∀ p ∈ ws, p.1 + 32 ≤ m.size) → ∀ n,
      (Reasoning.Theory.writeCascade m ws).data.toList[n]? = patch ws.reverse n m.data.toList[n]?
  | [], _, _, _ => rfl
  | (o, w) :: rest, m, h, n => by
    have ho : o + 32 ≤ m.size := h (o, w) (by simp)
    have hsz : (Reasoning.Theory.writeWord m o w).size = m.size := by
      rw [Reasoning.Theory.writeWord_size m o w
        (by rw [Nat.sub_eq_zero_of_le (by omega)]; exact USize.size_pos)]
      omega
    rw [Reasoning.Theory.writeCascade_cons,
      cascade_getElem? rest _ (fun p hp => hsz ▸ h p (by simp [hp])) n,
      writeWord_getElem? m o w ho n, List.reverse_cons, patch_append]

/-! ## The per-contract checks -/

/-- Is byte `n` inside one of the sites? -/
def inSites (sites : List (Nat × Nat × String)) (n : Nat) : Bool :=
  sites.any (fun s => inWin n s.1)

/-- The template and `bytes` have the same length and agree at every byte outside the sites,
the first byte being byte `n`. -/
def agree (sites : List (Nat × Nat × String)) : Nat → List UInt8 → List UInt8 → Bool
  | _, [], [] => true
  | n, x :: t, y :: b => (x == y || inSites sites n) && agree sites (n + 1) t b
  | _, _, _ => false

theorem agree_length (sites : List (Nat × Nat × String)) :
    ∀ (k : Nat) (t b : List UInt8), agree sites k t b = true → t.length = b.length
  | _, [], [], _ => rfl
  | k, _ :: t, _ :: b, h => by
    simp only [agree, Bool.and_eq_true] at h
    simp [agree_length sites (k + 1) t b h.2]
  | _, [], _ :: _, h => by simp [agree] at h
  | _, _ :: _, [], h => by simp [agree] at h

theorem agree_spec (sites : List (Nat × Nat × String)) :
    ∀ (k : Nat) (t b : List UInt8), agree sites k t b = true →
      ∀ n, inSites sites (k + n) = false → t[n]? = b[n]?
  | _, [], [], _, _, _ => rfl
  | k, x :: t, y :: b, h, n, hn => by
    simp only [agree, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    cases n with
    | zero =>
      rcases h.1 with h1 | h1
      · simp [h1]
      · rw [Nat.add_zero] at hn; rw [hn] at h1; exact absurd h1 (by simp)
    | succ n =>
      simp only [List.getElem?_cons_succ]
      exact agree_spec sites (k + 1) t b h.2 n (by rw [← hn]; congr 1; omega)
  | _, [], _ :: _, h, _, _ => by simp [agree] at h
  | _, _ :: _, [], h, _, _ => by simp [agree] at h

/-- Closed check that a layout's sites and a template agree with a listing:

* the template agrees with `bytes` outside the sites (`agree`);
* every immutable push has room in `bytes` (`fits`);
* every site is the data of an immutable push whose name, in `names`, is the site's key;
* the data of every immutable push is a site.

The site widths are not looked at: `Layout.runtime` writes 32 bytes at every site whatever
width it records. -/
def codeCheck (sites : List (Nat × Nat × String)) (template bytes : List UInt8) (table : Table)
    (names : List String) : Bool :=
  agree sites 0 template bytes &&
  fits (join table) bytes.length &&
  sites.all (fun s =>
    (immSites 0 (join table)).any (fun p => p.1 == s.1 && names.getD p.2 "" == s.2.2)) &&
  (immSites 0 (join table)).all (fun p => sites.any (fun s => s.1 == p.1))

/-- Closed check for a contract without immutables: the code is `bytes`, and the table has no
immutable push. -/
def plainCheck (code bytes : List UInt8) (table : Table) : Bool :=
  code == bytes && (join table).all (fun i => !i.isImm)

/-! ## The bridges -/

/-- The two codes byte by byte, under `codeCheck`. -/
theorem patch_eq_of_codeCheck {sites : List (Nat × Nat × String)} {t b : List UInt8}
    {table : Table} {names : List String} (h : codeCheck sites t b table names = true)
    (words : String → UInt256) (n : Nat) :
    patch (sites.map (fun s => (s.1, words s.2.2))).reverse n t[n]? =
      patch ((immSites 0 (join table)).map (fun p => (p.1, immσ names words p.2))) n b[n]? := by
  simp only [codeCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hag, -⟩, hsites⟩, himms⟩ := h
  rcases patch_cases n t[n]? (sites.map (fun s => (s.1, words s.2.2))).reverse with
    ⟨hW, hnone⟩ | ⟨q, hq, hin, hW⟩
  · -- No site holds `n`: both sides are the template's byte.
    have hsn : ∀ s ∈ sites, inWin n s.1 = false := fun s hs =>
      hnone (s.1, words s.2.2) (by simp only [List.mem_reverse, List.mem_map]; exact ⟨s, hs, rfl⟩)
    rw [hW, patch_none]
    · exact agree_spec sites 0 t b hag n (by
        simp only [inSites, Nat.zero_add, List.any_eq_false]
        intro s hs; simp [hsn s hs])
    · intro q hq
      simp only [List.mem_map] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      obtain ⟨s, hs, hse⟩ := himms p hp
      rw [← hse]; exact hsn s hs
  · -- Site `q` holds `n`: it is an immutable's data, and the only one holding `n`.
    simp only [List.mem_reverse, List.mem_map] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    obtain ⟨p, hp, hpo, hpk⟩ := hsites s hs
    rw [hW]
    rcases patch_cases n b[n]? ((immSites 0 (join table)).map (fun p => (p.1, immσ names words p.2)))
      with ⟨-, hnone'⟩ | ⟨q', hq', hin', hF⟩
    · exact absurd (hnone' (p.1, immσ names words p.2) (List.mem_map_of_mem hp))
        (by simp only at hin ⊢; rw [hpo, hin]; simp)
    · simp only [List.mem_map] at hq'
      obtain ⟨p', hp', rfl⟩ := hq'
      have he := immSites_unique n (join table) 0 p p' hp hp' (by rw [hpo]; exact hin) hin'
      subst he
      rw [hF]
      simp only [immσ, hpk, hpo]

/-- **EquiVM's runtime is the listing's filled code**: under `codeCheck`, the template with each
site's word written over it is `filled bytes σ table`, immutable `i` being the key `names[i]`. -/
theorem runtime_eq_filled {layout : Reasoning.Immutables.Layout} {template : ByteArray}
    {bytes : List UInt8} {table : Table} {names : List String}
    (h : codeCheck layout.sites template.data.toList bytes table names = true)
    (words : String → UInt256) :
    layout.runtime template words = filled bytes (immσ names words) table := by
  have hc := h
  simp only [codeCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hag, hfits⟩, hsites⟩, -⟩ := hc
  have hwrites : Reasoning.Immutables.Layout.writes layout words =
      layout.sites.map (fun s => (s.1, words s.2.2)) := by
    unfold Reasoning.Immutables.Layout.writes
    congr 1
  apply ByteArray.ext
  apply Array.ext'
  apply List.ext_getElem?
  intro n
  unfold Reasoning.Immutables.Layout.runtime
  rw [cascade_getElem? _ _ ?bound n]
  · show _ = (fill (immσ names words) (join table) bytes).toArray.toList[n]?
    rw [List.toList_toArray, fill_getElem? _ _ 0 _ hfits n, Nat.zero_add, hwrites]
    exact patch_eq_of_codeCheck h words n
  · intro p hp
    rw [hwrites] at hp
    simp only [List.mem_map] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨p, hp, hpo, -⟩ := hsites s hs
    have hb := immSites_bound _ 0 _ hfits p hp
    have hl := agree_length _ 0 _ _ hag
    rw [Array.length_toList] at hl
    show s.1 + 32 ≤ template.data.size
    omega

/-- **A code without immutables is the listing's filled code**, for every `σ`. -/
theorem eq_filled {code : ByteArray} {bytes : List UInt8} {table : Table}
    (h : plainCheck code.data.toList bytes table = true) (σ : Nat → UInt256) :
    code = filled bytes σ table := by
  simp only [plainCheck, Bool.and_eq_true, beq_iff_eq] at h
  apply ByteArray.ext
  apply Array.ext'
  show _ = (fill σ (join table) bytes).toArray.toList
  rw [List.toList_toArray, fill_noImm σ _ _ h.2, h.1]

end Reasoning.Listing
