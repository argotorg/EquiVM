import EVM.Disassembly.Sound
import Reasoning.Immutables
import Reasoning.Memory

/-!
# Immutables

Block theorems are stated over `layout.runtime template words` (`Reasoning/Immutables.lean`), or
over a plain `ByteArray` constant for a contract without immutables, while `EVM.Disassembly`
works with `filled bytes σ sections`. This file shows that these are the same code:

* `runtime_eq_filled` for a contract with immutables, given `codeCheck`;
* `eq_filled` for a contract without, given `plainCheck`.

Both checks are proved per contract by `decide +kernel`. `codeCheck` says that the sites of the
layout are exactly the immutable pushes of the sections. The proof compares the two codes byte
by byte: each of them is the template with some 32-byte windows written over it (`patch`).
-/

open Ethereum Ethereum.EVM EVM.Disassembly

set_option autoImplicit false

namespace Reasoning.Disassembly

/-- The value of the `i`-th immutable, which is `words` at the key `names[i]`. -/
def immσ (names : List String) (words : String → UInt256) : Nat → UInt256 :=
  fun i => words (names.getD i "")

/-! ## Windows -/

/-- Whether byte `n` is inside the 32-byte window at offset `o`. -/
def inWin (n o : Nat) : Bool := decide (o ≤ n) && decide (n < o + 32)

/-- Byte `n` of a code with the windows `S` written over it. It comes from the first window that
contains `n`, or is `d` if there is none. -/
def patch : List (Nat × UInt256) → Nat → Option UInt8 → Option UInt8
  | [], _, d => d
  | (o, w) :: rest, n, d => if inWin n o then (EVM.Word.toBytesBE w)[n - o]? else patch rest n d

theorem patch_append (n : Nat) (d : Option UInt8) :
    ∀ (A B : List (Nat × UInt256)), patch (A ++ B) n d = patch A n (patch B n d)
  | [], _ => rfl
  | (o, w) :: A, B => by
    simp only [List.cons_append, patch, patch_append n d A B]

/-- If no window contains `n`, the byte is `d`. -/
theorem patch_none {n : Nat} {d : Option UInt8} :
    ∀ {S : List (Nat × UInt256)}, (∀ q ∈ S, inWin n q.1 = false) → patch S n d = d
  | [], _ => rfl
  | (o, w) :: S, h => by
    have h1 : inWin n o = false := h (o, w) (by simp)
    simp only [patch, h1]
    exact patch_none (fun q hq => h q (by simp [hq]))

/-- The byte is either `d` or comes from a window that contains `n`. -/
theorem patch_cases (n : Nat) (d : Option UInt8) :
    ∀ (S : List (Nat × UInt256)),
      (patch S n d = d ∧ ∀ q ∈ S, inWin n q.1 = false) ∨
        ∃ q ∈ S, inWin n q.1 = true ∧ patch S n d = (EVM.Word.toBytesBE q.2)[n - q.1]?
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

/-! ## The immutables of the sections -/

def Instr.isImm : Instr → Bool
  | .immutable _ => true
  | _ => false

/-- The offset of the immediate and the index of the immutable, if the instruction at `pc` is an
immutable. -/
def Instr.site (pc : Nat) : Instr → List (Nat × Nat)
  | .immutable k => [(pc + 1, k)]
  | _ => []

/-- The sites of the immutables among the instructions, where the first instruction is at `pc`. -/
def immSites : Nat → List Instr → List (Nat × Nat)
  | _, [] => []
  | pc, i :: rest => Instr.site pc i ++ immSites (pc + i.width) rest

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

/-- Immutable sites do not overlap. -/
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

/-- Every immutable site is inside the code, where `n` is the number of bytes from `pc` on. -/
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

/-- `fill` does not change an instruction that is not an immutable. -/
theorem fill_cons_of_not_imm (σ : Nat → UInt256) {i : Instr} (hi : Instr.isImm i = false)
    (rest : List Instr) (l : List UInt8) :
    fill σ (i :: rest) l = l.take i.width ++ fill σ rest (l.drop i.width) := by
  have hdata : i.data σ l = (l.drop 1).take (i.width - 1) := by
    cases i with
    | immutable k => simp [Instr.isImm] at hi
    | op o => rfl
    | push o v => rfl
  have hw := width_pos' i
  have htake : l.take 1 ++ (l.drop 1).take (i.width - 1) = l.take i.width := by
    rw [← List.take_add]; congr 1; omega
  rw [fill, hdata, htake]

/-- Byte `n` of the filled template, as a `patch` of the immutable sites. -/
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
          l.take 1 ++ EVM.Word.toBytesBE (σ k) ++ fill σ rest (l.drop 33) := rfl
      have hsites : immSites pc (.immutable k :: rest) = (pc + 1, k) :: immSites (pc + 33) rest := rfl
      rw [hfill, hsites, List.map_cons]
      simp only [patch]
      have hwl := EVM.Word.toBytesBE_length (σ k)
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
          have hlen : (l.take 1 ++ EVM.Word.toBytesBE (σ k)).length = 33 := by simp [hwl]; omega
          rw [hlen, fill_getElem? σ rest (pc + 33) (l.drop 33) (by simpa [hw] using hrest) (n - 33),
            List.getElem?_drop]
          have e1 : pc + 33 + (n - 33) = pc + n := by omega
          have e2 : 33 + (n - 33) = n := by omega
          rw [e1, e2]
    · have hsite : Instr.site pc i = [] := by
        cases i with
        | immutable k => exact absurd ⟨k, rfl⟩ himm
        | op o => rfl
        | push o v => rfl
      have hfill := fill_cons_of_not_imm σ (i := i) (by
        cases i with
        | immutable k => exact absurd ⟨k, rfl⟩ himm
        | op o => rfl
        | push o v => rfl) rest l
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

/-- Without immutables, `fill` does nothing. -/
theorem fill_noImm (σ : Nat → UInt256) :
    ∀ (J : List Instr) (l : List UInt8), J.all (fun i => !Instr.isImm i) = true → fill σ J l = l
  | [], _, _ => rfl
  | i :: rest, l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [fill_cons_of_not_imm σ (by simpa using h.1), fill_noImm σ rest _ h.2,
      List.take_append_drop]

/-! ## The layout's code, byte by byte -/

/-- `writeWord` as a list operation, for a word inside the code. -/
theorem writeWord_toList (m : ByteArray) (off : Nat) (w : UInt256) (h : off + 32 ≤ m.size) :
    (Reasoning.Theory.writeWord m off w).data.toList =
      m.data.toList.take off ++ EVM.Word.toBytesBE w ++ m.data.toList.drop (off + 32) := by
  unfold Reasoning.Theory.writeWord
  rw [Reasoning.Theory.write32_eq _ _ _ (by rw [Reasoning.Theory.toByteArray_size]) (by omega)]
  simp only [ByteArray.data_append, Array.toList_append, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  rw [← Reasoning.Theory.byteArray_toList_eq (UInt256.toByteArray w),
    ← Reasoning.Theory.word_toBytesBE_eq_toByteArray_toList]
  have hw : (EVM.Word.toBytesBE w).take 32 = EVM.Word.toBytesBE w :=
    List.take_of_length_le (by rw [EVM.Word.toBytesBE_length])
  have hd : (m.data.toList.drop (off + 32)).take (m.size - (off + 32)) =
      m.data.toList.drop (off + 32) :=
    List.take_of_length_le (by simp)
  rw [hw, hd]

/-- Byte `n` after a `writeWord`. -/
theorem writeWord_getElem? (m : ByteArray) (o : Nat) (w : UInt256) (h : o + 32 ≤ m.size)
    (n : Nat) :
    (Reasoning.Theory.writeWord m o w).data.toList[n]? = patch [(o, w)] n m.data.toList[n]? := by
  rw [writeWord_toList m o w h]
  have hL : m.data.toList.length = m.size := Array.length_toList
  have hwl := EVM.Word.toBytesBE_length w
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

/-- Byte `n` after a series of `writeWord`s, as a `patch`. Later writes take precedence. -/
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

/-- The sites of the layout are exactly the immutables of the sections, and the key of each site is
the name of its immutable. Site widths are ignored because `Layout.runtime` always writes 32 bytes.
-/
def codeCheck (sites : List (Nat × Nat × String)) (table : List (Nat × List Instr)) (names : List String) : Bool :=
  sites.all (fun s =>
    (immSites 0 (join table)).any (fun p => p.1 == s.1 && names.getD p.2 "" == s.2.2)) &&
  (immSites 0 (join table)).all (fun p => sites.any (fun s => s.1 == p.1))

/-- The sections have no immutables. -/
def plainCheck (table : List (Nat × List Instr)) : Bool :=
  (join table).all (fun i => !Instr.isImm i)

/-! ## Main theorems -/

/-- Under `codeCheck`, the writes of the layout and the values of the immutables give the same
bytes. -/
theorem patch_eq_of_codeCheck {sites : List (Nat × Nat × String)} {b : List UInt8}
    {table : List (Nat × List Instr)} {names : List String} (h : codeCheck sites table names = true)
    (words : String → UInt256) (n : Nat) :
    patch (sites.map (fun s => (s.1, words s.2.2))).reverse n b[n]? =
      patch ((immSites 0 (join table)).map (fun p => (p.1, immσ names words p.2))) n b[n]? := by
  simp only [codeCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨hsites, himms⟩ := h
  rcases patch_cases n b[n]? (sites.map (fun s => (s.1, words s.2.2))).reverse with
    ⟨hW, hnone⟩ | ⟨q, hq, hin, hW⟩
  · -- No site holds `n`: both sides are the code's byte.
    have hsn : ∀ s ∈ sites, inWin n s.1 = false := fun s hs =>
      hnone (s.1, words s.2.2) (by simp only [List.mem_reverse, List.mem_map]; exact ⟨s, hs, rfl⟩)
    rw [hW, patch_none]
    intro q hq
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

/-- The runtime code of a contract with immutables is `filled`. -/
theorem runtime_eq_filled {layout : Reasoning.Immutables.Layout} {code : ByteArray}
    {table : List (Nat × List Instr)} {names : List String} (hc : Checked code.data.toList table)
    (h : codeCheck layout.sites table names = true) (words : String → UInt256) :
    layout.runtime code words = filled code.data.toList (immσ names words) table := by
  have hc' := h
  simp only [codeCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hc'
  obtain ⟨hsites, -⟩ := hc'
  have hfits := hc.fits_eq
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
  · show _ = (fill (immσ names words) (join table) code.data.toList).toArray.toList[n]?
    rw [List.toList_toArray, fill_getElem? _ _ 0 _ hfits n, Nat.zero_add, hwrites]
    exact patch_eq_of_codeCheck h words n
  · intro p hp
    rw [hwrites] at hp
    simp only [List.mem_map] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨p, hp, hpo, -⟩ := hsites s hs
    have hb := immSites_bound _ 0 _ hfits p hp
    have hl : code.data.toList.length = code.data.size := Array.length_toList
    show s.1 + 32 ≤ code.data.size
    omega

/-- A code without immutables is `filled`, for any `σ`. -/
theorem eq_filled {code : ByteArray} {table : List (Nat × List Instr)} (h : plainCheck table = true)
    (σ : Nat → UInt256) : code = filled code.data.toList σ table := by
  apply ByteArray.ext
  apply Array.ext'
  show _ = (fill σ (join table) code.data.toList).toArray.toList
  rw [List.toList_toArray, fill_noImm σ _ _ h]

/-! ## Numbering the immutables -/

/-- The keys of the layout in order of first appearance. This is the default numbering of the
immutables. -/
def keyOrder (sites : List (Nat × Nat × String)) : List String :=
  sites.foldl (fun out s => if out.contains s.2.2 then out else out ++ [s.2.2]) []

/-- The sites in the form `sectionsOf` takes: the offset of each site and the index of its key in
`names`. -/
def siteNumbers (sites : List (Nat × Nat × String)) (names : List String) : List (Nat × Nat) :=
  sites.map fun s => (s.1, names.idxOf s.2.2)

end Reasoning.Disassembly
