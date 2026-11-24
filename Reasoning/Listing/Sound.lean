import Reasoning.Listing.Basic

/-!
# Listing — what a checked table says about the deployed code

`Checked bytes table` (`Reasoning/Listing/Basic.lean`) is a closed fact about the *template*.  This file
turns it into facts about the code that is actually deployed, stated against evmlean's own
`decode` and `D_J`, for every assignment `σ : Nat → UInt256` of the immutables:

* `filled bytes σ table` is the deployed code: the template with the 32 big-endian bytes of
  `σ i` written over the data bytes of every `immutable i` push of the table.
* `Checked.decodes`: every section decodes on it, from its offset, as written (`Decodes`).
* `Checked.jumpdest_iff`: its valid jump destinations (`D_J`) are exactly the offsets of the
  sections that begin with `JUMPDEST`.
* `Checked.shape`, `Checked.ascending`, `Checked.first`: the sections are consecutive from 0,
  strictly ascending, non-empty, and cut exactly at the `JUMPDEST`s.

`D_J` is never evaluated: it is shown equal to a function of the decoded instructions by
induction (`D_J_aux_eq`), as `decode` is (`decodes_scan`).
-/

open Ethereum Ethereum.EVM

set_option autoImplicit false

namespace Reasoning.Listing

/-! ## What an instruction means, and what it means to decode as a section -/

/-- What `decode` returns for the instruction, under the assignment `σ`. -/
def Instr.sem (σ : Nat → UInt256) : Instr → Operation × Option (UInt256 × Nat)
  | .op o => (o, none)
  | .push o v => (o, some (UInt256.ofNat v, argOnNBytesOfInstr o))
  | .immutable i => (.PUSH32, some (σ i, 32))

/-- `code` decodes from `pc` as the instructions `is`, one after the other: the first is what
`decode` finds at `pc`, and the rest decode from just past it.  Consumed by `head`/`tail`. -/
def Decodes (code : ByteArray) (σ : Nat → UInt256) : Nat → List Instr → Prop
  | _, [] => True
  | pc, i :: rest =>
    decode code (UInt256.ofNat pc) = some (i.sem σ) ∧ Decodes code σ (pc + i.width) rest

theorem Decodes.head {code : ByteArray} {σ : Nat → UInt256} {pc : Nat} {i : Instr}
    {rest : List Instr} (h : Decodes code σ pc (i :: rest)) :
    decode code (UInt256.ofNat pc) = some (i.sem σ) := h.1

theorem Decodes.tail {code : ByteArray} {σ : Nat → UInt256} {pc : Nat} {i : Instr}
    {rest : List Instr} (h : Decodes code σ pc (i :: rest)) :
    Decodes code σ (pc + i.width) rest := h.2

/-! ## The deployed code -/

/-- `k` little-endian bytes of `n`. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: leBytes k (n / 256)

/-- A word as the 32 big-endian bytes a `PUSH32` holds. -/
def wordBytes (w : UInt256) : List UInt8 := (leBytes 32 w.toNat).reverse

/-- The data bytes the instruction has in the deployed code, `l` being the template from its
opcode on: an immutable's word, otherwise the template's own. -/
def Instr.data (σ : Nat → UInt256) (i : Instr) (l : List UInt8) : List UInt8 :=
  match i with
  | .immutable k => wordBytes (σ k)
  | _ => (l.drop 1).take (i.width - 1)

/-- Walk the template `l` along the instructions, writing each immutable's word over its data. -/
def fill (σ : Nat → UInt256) : List Instr → List UInt8 → List UInt8
  | [], l => l
  | i :: rest, l => l.take 1 ++ i.data σ l ++ fill σ rest (l.drop i.width)

/-- The deployed code: the template `bytes` with `σ i` written over every `immutable i`. -/
def filled (bytes : List UInt8) (σ : Nat → UInt256) (table : Table) : ByteArray :=
  ⟨(fill σ (join table) bytes).toArray⟩

/-! ## The shape of a table -/

/-- `table` is a run of sections from offset `pc`: each at the offset where the previous one
ends, non-empty, with no `JUMPDEST` after its first instruction, and followed (if at all) by a
section that begins with `JUMPDEST`. -/
def Shape : Nat → Table → Prop
  | _, [] => True
  | pc, p :: rest =>
    p.1 = pc ∧ p.2 ≠ [] ∧ (∀ i ∈ p.2.tail, i.isJumpdest = false) ∧
      (∀ q ∈ rest.head?, startsJD q.2 = true) ∧ Shape (pc + sectionWidth p.2) rest

/-! ## Bytes -/

theorem toList_loop (c : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop c i r = r.reverse ++ c.data.toList.drop i := by
  unfold ByteArray.toList.loop
  split
  · rename_i h
    rw [toList_loop c (i + 1)]
    have hd : c.data.toList.drop i = c.get! i :: c.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using h)]
      congr 1
      simp [ByteArray.get!, h]
      exact rfl
    rw [hd]; simp
  · rename_i h
    have : c.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp [this]
termination_by c.size - i

theorem byteArray_toList (c : ByteArray) : c.toList = c.data.toList := by
  simp [ByteArray.toList, toList_loop]

theorem get?_eq_getElem? (c : ByteArray) (i : Nat) : c.get? i = c.data.toList[i]? := by
  unfold ByteArray.get?
  split
  · rename_i h; simp [ByteArray.get, h]
  · rename_i h
    have hlen : c.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact Nat.le_of_not_lt h
    simp [List.getElem?_eq_none hlen]

theorem extract'_toList (c : ByteArray) (b e : Nat) :
    (ByteArray.extract' c b e).data.toList = (c.data.toList.drop b).take (e - b) := by
  unfold ByteArray.extract'
  split
  · rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  · simp [byteArray_toList]

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 256) : (UInt256.ofNat n).toNat = n := by
  show (Fin.ofNat _ n).val = n
  simp only [Fin.val_ofNat, UInt256.size]
  omega

theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  have hv : Fin.ofNat UInt256.size a.toNat = a.val := by
    apply Fin.ext
    rw [Fin.val_ofNat]
    exact Nat.mod_eq_of_lt a.val.isLt
  show (⟨Fin.ofNat UInt256.size a.toNat⟩ : UInt256) = a
  rw [hv]

theorem toNat_lt (a : UInt256) : a.toNat < 2 ^ 256 := a.val.isLt

theorem fromBytes'_leBytes : ∀ (k n : Nat), fromBytes' (leBytes k n) = n % 256 ^ k
  | 0, n => by simp [leBytes, fromBytes', Nat.mod_one]
  | k + 1, n => by
      rw [leBytes, fromBytes', fromBytes'_leBytes k (n / 256),
        show 256 ^ (k + 1) = 256 * 256 ^ k from Nat.pow_succ', Nat.mod_mul]
      have h : (UInt8.ofNat (n % 256)).toFin.val = n % 256 := by simp
      rw [h]; rfl

theorem fromBytesBigEndian_wordBytes (w : UInt256) :
    fromBytesBigEndian (wordBytes w) = w.toNat := by
  simp only [fromBytesBigEndian, wordBytes, Function.comp, List.reverse_reverse,
    fromBytes'_leBytes]
  exact Nat.mod_eq_of_lt (by have := toNat_lt w; norm_num at this ⊢; omega)

theorem leBytes_length : ∀ (k n : Nat), (leBytes k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [leBytes, leBytes_length k]

theorem wordBytes_length (w : UInt256) : (wordBytes w).length = 32 := by
  simp [wordBytes, leBytes_length]

/-! ## Decoding one instruction -/

theorem argOnNBytesOfInstr_le_32 (i : Operation) : argOnNBytesOfInstr i ≤ 32 := by
  cases i <;> first | decide | (rename_i p; cases p <;> decide)

theorem instrOf_opn (b : UInt8) (rest : List UInt8) :
    (instrOf b rest).opn = (parseInstr b).getD .INVALID := by
  dsimp only [instrOf]; split <;> rfl

theorem instrOf_width (b : UInt8) (rest : List UInt8) :
    (instrOf b rest).width = 1 + argOnNBytesOfInstr ((parseInstr b).getD .INVALID) := by
  rw [Instr.width, instrOf_opn]

/-- `instrOf` reads only the immediate's bytes. -/
theorem instrOf_congr (b : UInt8) {r r' : List UInt8}
    (h : r.take (argOnNBytesOfInstr ((parseInstr b).getD .INVALID))
      = r'.take (argOnNBytesOfInstr ((parseInstr b).getD .INVALID))) :
    instrOf b r = instrOf b r' := by
  dsimp only [instrOf]; rw [h]

theorem isJumpdest_op (o : Operation) : (Instr.op o).isJumpdest = decide (o = .JUMPDEST) := by
  cases o <;> (rename_i p; cases p <;> rfl)

theorem isJumpdest_instrOf (b : UInt8) (rest : List UInt8) :
    (instrOf b rest).isJumpdest = decide ((parseInstr b).getD .INVALID = .JUMPDEST) := by
  dsimp only [instrOf]
  split
  · exact isJumpdest_op _
  · rename_i h
    have : (parseInstr b).getD .INVALID ≠ .JUMPDEST := fun he => h (by rw [he]; rfl)
    simp [Instr.isJumpdest, this]

theorem parseInstr_isSome (b : UInt8) : (parseInstr b).isSome = true := by
  have h : ∀ n, n < 256 → (parseInstr (UInt8.ofNat n)).isSome = true := by decide +kernel
  simpa using h b.toNat b.toNat_lt

theorem drop_lt_size {c : ByteArray} {pc : Nat} {b : UInt8} {rest : List UInt8}
    (hd : c.data.toList.drop pc = b :: rest) : pc < c.size := by
  by_contra hc
  have hs : c.data.size = c.size := rfl
  have : c.data.toList.drop pc = [] :=
    List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)
  rw [this] at hd; exact absurd hd (by simp)

/-- What `decode` finds at an offset where the code continues `b :: rest`. -/
theorem decode_eq {c : ByteArray} {pc : Nat} {b : UInt8} {rest : List UInt8}
    (hsz : c.size < 2 ^ 256) (hd : c.data.toList.drop pc = b :: rest) (σ : Nat → UInt256) :
    decode c (UInt256.ofNat pc) = some ((instrOf b rest).sem σ) := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (parseInstr_isSome b)
  have hop : (parseInstr b).getD Operation.INVALID = o := by rw [ho]; rfl
  have hpclt : pc < c.size := drop_lt_size hd
  have hpcN : (UInt256.ofNat pc).toNat = pc := toNat_ofNat_of_lt (by omega)
  have hget : c.get? pc = some b := by
    rw [get?_eq_getElem?, ← List.head?_drop, hd]; rfl
  have htl : c.data.toList.drop (pc + 1) = rest := by rw [← List.tail_drop, hd]; rfl
  have himm : (ByteArray.extract' c (pc + 1) (pc + 1 + argOnNBytesOfInstr o)).data.toList
      = rest.take (argOnNBytesOfInstr o) := by
    rw [extract'_toList, htl]; congr 1; omega
  simp only [decode, hpcN, hget, Option.bind_eq_bind, Option.bind_some, ho,
    Nat.succ_eq_add_one, Option.some.injEq]
  unfold instrOf
  rw [hop]
  by_cases hz : argOnNBytesOfInstr o = 0
  · simp [hz, Instr.sem]
  · simp only [hz, if_false, Instr.sem, beq_iff_eq]
    congr 2
    unfold uInt256OfByteArray
    rw [himm]; rfl

/-! ## Decoding a whole byte list -/

theorem scan_skip : ∀ (k : Nat) (l : List UInt8), scan k l = scan 0 (l.drop k)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: rest => by simp only [scan, List.drop_succ_cons]; exact scan_skip k rest

theorem scan_cons (b : UInt8) (rest : List UInt8) :
    scan 0 (b :: rest) = instrOf b rest
      :: scan 0 (rest.drop (argOnNBytesOfInstr ((parseInstr b).getD .INVALID))) := by
  rw [scan, scan_skip]

theorem drop_next {c : ByteArray} {pc : Nat} {b : UInt8} {rest : List UInt8} (w : Nat)
    (hd : c.data.toList.drop pc = b :: rest) :
    c.data.toList.drop (pc + (1 + w)) = rest.drop w := by
  rw [← Nat.add_assoc, ← List.drop_drop, ← List.tail_drop, hd]; rfl

/-- Any code decodes, from any offset, as `scan` reads it from there. -/
theorem decodes_scan (c : ByteArray) (σ : Nat → UInt256) (hsz : c.size < 2 ^ 256) (pc : Nat) :
    Decodes c σ pc (scan 0 (c.data.toList.drop pc)) := by
  cases hd : c.data.toList.drop pc with
  | nil => rw [scan]; trivial
  | cons b rest =>
      have := drop_lt_size hd
      rw [scan_cons]
      refine ⟨decode_eq hsz hd σ, ?_⟩
      rw [instrOf_width, ← drop_next _ hd]
      exact decodes_scan c σ hsz _
termination_by c.size - pc
decreasing_by omega

/-! ## The jump destinations -/

/-- Offsets of the `JUMPDEST`s in a run of instructions starting at `pc`. -/
def jds (pc : Nat) : List Instr → List Nat
  | [] => []
  | i :: rest => if i.isJumpdest then pc :: jds (pc + i.width) rest else jds (pc + i.width) rest

theorem D_J_aux_eq (c : ByteArray) (pc : Nat) (acc : Array UInt256) :
    (D_J_aux c pc acc).toList
      = acc.toList ++ (jds pc (scan 0 (c.data.toList.drop pc))).map UInt256.ofNat := by
  cases hd : c.data.toList.drop pc with
  | nil =>
      have hget : c.get? pc = none := by rw [get?_eq_getElem?, ← List.head?_drop, hd]; rfl
      rw [D_J_aux]; split
      · simp [scan, jds]
      · rename_i hc; rw [hget] at hc; simp at hc
  | cons b rest =>
      have := drop_lt_size hd
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (parseInstr_isSome b)
      have hop : (parseInstr b).getD Operation.INVALID = o := by rw [ho]; rfl
      have hgp : c.get? pc >>= parseInstr = some o := by
        rw [get?_eq_getElem?, ← List.head?_drop, hd]; exact ho
      have ih := D_J_aux_eq c (pc + (1 + argOnNBytesOfInstr o))
        (if o = Operation.JUMPDEST then acc.push (UInt256.ofNat pc) else acc)
      rw [drop_next _ hd] at ih
      rw [D_J_aux]; split
      · rename_i hc; rw [hgp] at hc; simp at hc
      · rename_i ci hc
        rw [hgp] at hc
        simp only [Option.some.injEq] at hc
        subst hc
        rw [show N pc o = pc + (1 + argOnNBytesOfInstr o) by simp [N]; omega, ih,
          scan_cons, jds, instrOf_width, isJumpdest_instrOf, hop]
        by_cases hj : o = Operation.JUMPDEST
        all_goals simp [hj]
termination_by c.size - pc
decreasing_by omega

theorem D_J_toList (c : ByteArray) :
    (D_J c 0).toList = (jds 0 (scan 0 c.data.toList)).map UInt256.ofNat := by
  rw [D_J, D_J_aux_eq]; simp

/-- Every destination lies inside the code. -/
theorem jds_scan_lt : ∀ (l : List UInt8) (pc n : Nat), n ∈ jds pc (scan 0 l) →
    n < pc + l.length
  | [], _, _, h => by simp [scan, jds] at h
  | b :: rest, pc, n, h => by
      rw [scan_cons, jds] at h
      have ih := jds_scan_lt (rest.drop (argOnNBytesOfInstr ((parseInstr b).getD .INVALID)))
        (pc + (instrOf b rest).width) n
      rw [instrOf_width] at ih h
      simp only [List.length_drop, List.length_cons] at ih ⊢
      have ih' : n ∈ jds (pc + (1 + argOnNBytesOfInstr ((parseInstr b).getD .INVALID)))
          (scan 0 (rest.drop (argOnNBytesOfInstr ((parseInstr b).getD .INVALID))))
          → n < pc + (rest.length + 1) := by
        intro hn
        by_cases hr : argOnNBytesOfInstr ((parseInstr b).getD .INVALID) ≤ rest.length
        · have := ih hn; omega
        · rw [List.drop_eq_nil_of_le (by omega)] at hn; simp [scan, jds] at hn
      split at h
      · rcases List.mem_cons.mp h with h | h
        · omega
        · exact ih' h
      · exact ih' h
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-! ## Instructions that agree on width, meaning and `JUMPDEST` -/

/-- An immutable with its word filled in: the push that the deployed code holds there. -/
def Instr.inst (σ : Nat → UInt256) : Instr → Instr
  | .op o => .op o
  | .push o v => .push o v
  | .immutable k => .push .PUSH32 (σ k).toNat

theorem inst_sem (σ : Nat → UInt256) (i : Instr) : (i.inst σ).sem σ = i.sem σ := by
  cases i <;> simp [Instr.inst, Instr.sem, ofNat_toNat]; rfl

theorem inst_width (σ : Nat → UInt256) (i : Instr) : (i.inst σ).width = i.width := by
  cases i <;> rfl

theorem inst_isJumpdest (σ : Nat → UInt256) (i : Instr) :
    (i.inst σ).isJumpdest = i.isJumpdest := by
  cases i <;> rfl

theorem erase_width (i : Instr) : i.erase.width = i.width := by cases i <;> rfl

theorem erase_isJumpdest (i : Instr) : i.erase.isJumpdest = i.isJumpdest := by cases i <;> rfl

theorem decodes_inst {c : ByteArray} {σ : Nat → UInt256} :
    ∀ {pc : Nat} {J : List Instr}, Decodes c σ pc (J.map (Instr.inst σ)) → Decodes c σ pc J
  | _, [], _ => trivial
  | _, i :: J, h => by
      refine ⟨by rw [← inst_sem σ i]; exact h.1, ?_⟩
      have := h.2
      rw [inst_width] at this
      exact decodes_inst this

theorem jds_inst (σ : Nat → UInt256) : ∀ (pc : Nat) (J : List Instr),
    jds pc (J.map (Instr.inst σ)) = jds pc J
  | _, [] => rfl
  | pc, i :: J => by simp only [List.map_cons, jds, inst_width, inst_isJumpdest, jds_inst σ]

/-! ## Filling in the immutables -/

theorem take_append_drop_of {r X : List UInt8} {w : Nat} (h : w ≤ r.length ∨ X = []) :
    (r.take w ++ X).take w = r.take w ∧ (r.take w ++ X).drop w = X ∧
      (r.take w ++ X).length = min w r.length + X.length := by
  rcases h with h | rfl
  · simp [Nat.min_eq_left h, List.length_take]
  · simp

/-- Decoding the deployed code gives the table's instructions with the immutables' words
filled in, and filling in does not change the length. -/
theorem scan_fill (σ : Nat → UInt256) : ∀ (J : List Instr) (l : List UInt8),
    scan 0 l = J.map Instr.erase → fits J l.length = true →
      scan 0 (fill σ J l) = J.map (Instr.inst σ) ∧ (fill σ J l).length = l.length
  | [], l, h, _ => by
      cases l with
      | nil => simp [fill, scan]
      | cons b rest => rw [scan_cons] at h; simp at h
  | i :: J, l, h, hf => by
      cases l with
      | nil => simp [scan] at h
      | cons b rest =>
        rw [scan_cons, List.map_cons, List.cons.injEq] at h
        obtain ⟨hi, hJ⟩ := h
        simp only [fits, Bool.and_eq_true] at hf
        obtain ⟨hfi, hfJ⟩ := hf
        have hw : i.width = 1 + argOnNBytesOfInstr ((parseInstr b).getD .INVALID) := by
          rw [← erase_width, ← hi, instrOf_width]
        generalize hwdef : argOnNBytesOfInstr ((parseInstr b).getD .INVALID) = w at hw hJ
        have hlen : (b :: rest).length - i.width = (rest.drop w).length := by
          simp [hw]; omega
        rw [hlen] at hfJ
        obtain ⟨ihs, ihl⟩ := scan_fill σ J (rest.drop w) hJ hfJ
        have hX : w ≤ rest.length ∨ fill σ J (rest.drop w) = [] := by
          by_cases hr : w ≤ rest.length
          · exact Or.inl hr
          · right
            have hnil : rest.drop w = [] := List.drop_eq_nil_of_le (by omega)
            rw [hnil] at hJ ihl
            cases J with
            | nil => simp [fill]; omega
            | cons _ _ => simp [scan] at hJ
        have hdrop : (b :: rest).drop i.width = rest.drop w := by simp [hw, Nat.add_comm]
        cases i with
        | op o | push o v =>
          have hdata : ∀ i : Instr, i.width = 1 + w → (∀ k, i ≠ .immutable k) →
              Instr.data σ i (b :: rest) = rest.take w := by
            intro i hi hk
            cases i with
            | immutable k => exact absurd rfl (hk k)
            | _ => simp [Instr.data, hi]
          rw [fill, hdata _ hw (by simp), hdrop]
          simp only [ List.take_succ_cons, List.take_zero, List.nil_append,
            List.cons_append]
          obtain ⟨h1, h2, h3⟩ := take_append_drop_of hX
          rw [scan_cons, hwdef, h2, ihs, instrOf_congr b (r := rest.take w ++ fill σ J (rest.drop w)) (r' := rest) (by rw [hwdef, h1]), hi]
          refine ⟨rfl, ?_⟩
          simp only [List.length_cons, h3, ihl, List.length_drop]
          omega
        | immutable k =>
          have hpush : (parseInstr b).getD .INVALID = .PUSH32 := by
            dsimp only [instrOf] at hi
            split at hi
            · simp [Instr.erase] at hi
            · simp only [Instr.erase, Instr.push.injEq] at hi; exact hi.1
          rw [hpush] at hwdef
          have hw32 : w = 32 := by rw [← hwdef]; rfl
          subst hw32
          have hr : 32 ≤ rest.length := by simp [Instr.fitsIn] at hfi; omega
          have hdata : Instr.data σ (.immutable k) (b :: rest) = wordBytes (σ k) := rfl
          simp only [fill, hdata, hdrop, List.take_succ_cons, List.take_zero, List.nil_append,
            List.cons_append]
          have hwl := wordBytes_length (σ k)
          refine ⟨?_, ?_⟩
          · have hdrop2 : (wordBytes (σ k) ++ fill σ J (rest.drop 32)).drop 32
                = fill σ J (rest.drop 32) := List.drop_left' hwl
            have htake2 : (wordBytes (σ k) ++ fill σ J (rest.drop 32)).take 32
                = wordBytes (σ k) := List.take_left' hwl
            rw [scan_cons, hpush, show argOnNBytesOfInstr Operation.PUSH32 = 32 from rfl, hdrop2,
              ihs]
            dsimp only [instrOf]
            rw [hpush]
            simp [hwdef, htake2, fromBytesBigEndian_wordBytes, Instr.inst]
          · simp [hwl, ihl]; omega

/-! ## Tables -/

theorem join_cons (p : Nat × Section) (t : Table) : join (p :: t) = p.2 ++ join t := by
  simp [join]

theorem join_cut : ∀ (pc : Nat) (L : List Instr), join (cut pc L) = L
  | _, [] => rfl
  | pc, i :: rest => by
      have ih := join_cut (pc + i.width) rest
      simp only [cut]
      cases h : cut (pc + i.width) rest with
      | nil => rw [h] at ih; simp [join, ← ih]
      | cons p more =>
        rw [h, join_cons] at ih
        obtain ⟨q, s⟩ := p
        dsimp only
        split <;> simp [join_cons, ← ih]

theorem join_erase : ∀ t : Table, join t.erase = (join t).map Instr.erase
  | [] => rfl
  | p :: t => by
      rw [show Table.erase (p :: t) = (p.1, p.2.map Instr.erase) :: Table.erase t from rfl, join_cons,
        join_cons, join_erase t, List.map_append]

theorem sectionWidth_append : ∀ (A B : List Instr),
    sectionWidth (A ++ B) = sectionWidth A + sectionWidth B
  | [], _ => by simp [sectionWidth]
  | i :: A, B => by simp only [List.cons_append, sectionWidth, sectionWidth_append A B]; omega

theorem sectionWidth_erase : ∀ (s : List Instr), sectionWidth (s.map Instr.erase) = sectionWidth s
  | [] => rfl
  | i :: s => by simp only [List.map_cons, sectionWidth, erase_width, sectionWidth_erase s]

theorem sectionWidth_pos : ∀ {s : List Instr}, s ≠ [] → 0 < sectionWidth s
  | [], h => absurd rfl h
  | i :: _, _ => by simp only [sectionWidth, Instr.width]; omega

theorem startsJD_erase (s : List Instr) : startsJD (s.map Instr.erase) = startsJD s := by
  cases s with
  | nil => rfl
  | cons i _ => simp [startsJD, erase_isJumpdest]

theorem shape_cut : ∀ (pc : Nat) (L : List Instr), Shape pc (cut pc L)
  | _, [] => trivial
  | pc, i :: rest => by
      have ih := shape_cut (pc + i.width) rest
      simp only [cut]
      cases h : cut (pc + i.width) rest with
      | nil => exact ⟨rfl, by simp, by simp, by simp, trivial⟩
      | cons p more =>
        rw [h] at ih
        obtain ⟨q, s⟩ := p
        obtain ⟨hq, hs, htl, hhd, hrest⟩ := ih
        dsimp only at hq hs htl hrest ⊢
        split
        · rename_i hj
          refine ⟨rfl, by simp, by simp, by simpa using hj, ?_⟩
          simp only [sectionWidth, Nat.add_zero]
          exact ⟨hq, hs, htl, hhd, by rw [hq]; exact hrest⟩
        · rename_i hj
          refine ⟨rfl, by simp, ?_, hhd, ?_⟩
          · intro j hj'
            cases s with
            | nil => simp at hj'
            | cons s0 s' =>
              rcases List.mem_cons.mp hj' with rfl | hj'
              · simpa [startsJD] using hj
              · exact htl j hj'
          · simp only [sectionWidth]; rw [← Nat.add_assoc]; exact hrest

theorem shape_erase : ∀ (pc : Nat) (t : Table), Shape pc t.erase → Shape pc t
  | _, [], _ => trivial
  | pc, p :: t, h => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      dsimp only at h1 h2 h3 h5
      refine ⟨h1, fun he => h2 (by rw [he]; rfl), ?_, ?_, ?_⟩
      · intro i hi
        rw [← erase_isJumpdest]
        exact h3 _ (by rw [← List.map_tail]; exact List.mem_map_of_mem hi)
      · intro q hq
        cases t with
        | nil => simp at hq
        | cons q' t =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
          subst hq
          have := h4 (q'.1, q'.2.map Instr.erase) rfl
          rwa [startsJD_erase] at this
      · rw [← sectionWidth_erase]; exact shape_erase _ t h5

theorem decodes_append {c : ByteArray} {σ : Nat → UInt256} : ∀ {pc : Nat} {A B : List Instr},
    Decodes c σ pc (A ++ B) → Decodes c σ pc A ∧ Decodes c σ (pc + sectionWidth A) B
  | _, [], _, h => ⟨trivial, by simpa [sectionWidth] using h⟩
  | _, i :: _, _, h => by
      obtain ⟨h1, h2⟩ := decodes_append h.2
      exact ⟨⟨h.1, h1⟩, by rw [sectionWidth, ← Nat.add_assoc]; exact h2⟩

theorem decodes_table {c : ByteArray} {σ : Nat → UInt256} : ∀ {pc : Nat} {t : Table},
    Shape pc t → Decodes c σ pc (join t) → ∀ p ∈ t, Decodes c σ p.1 p.2
  | _, [], _, _, _, hp => absurd hp (by simp)
  | _, _ :: _, hs, hd, p, hp => by
      rw [join_cons] at hd
      obtain ⟨hA, hB⟩ := decodes_append hd
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [hs.1]; exact hA
      · exact decodes_table hs.2.2.2.2 hB p hp

theorem jds_append : ∀ (pc : Nat) (A B : List Instr),
    jds pc (A ++ B) = jds pc A ++ jds (pc + sectionWidth A) B
  | _, [], _ => by simp [jds, sectionWidth]
  | pc, i :: A, B => by
      simp only [List.cons_append, jds, jds_append (pc + i.width) A B, sectionWidth,
        Nat.add_assoc]
      split <;> rfl

theorem jds_none : ∀ (pc : Nat) (s : List Instr), (∀ i ∈ s, i.isJumpdest = false) → jds pc s = []
  | _, [], _ => rfl
  | pc, i :: s, h => by
      rw [jds, if_neg (by simp [h i (by simp)]), jds_none _ s (fun j hj => h j (by simp [hj]))]

theorem jds_section (pc : Nat) (s : List Instr) (h : ∀ i ∈ s.tail, i.isJumpdest = false) :
    jds pc s = if startsJD s then [pc] else [] := by
  cases s with
  | nil => rfl
  | cons i s =>
    simp only [jds, startsJD, jds_none _ s h]
    by_cases hi : i.isJumpdest <;> simp [hi]

theorem jds_table : ∀ {pc : Nat} {t : Table} (n : Nat), Shape pc t →
    (n ∈ jds pc (join t) ↔ ∃ s, (n, s) ∈ t ∧ startsJD s = true)
  | _, [], _, _ => by simp [join, jds]
  | _, (o, s) :: t, n, hs => by
      obtain ⟨h1, -, h3, -, h5⟩ := hs
      dsimp only at h1 h3 h5
      subst h1
      rw [join_cons, jds_append, jds_section _ _ h3, List.mem_append, jds_table n h5]
      by_cases hj : startsJD s = true
      · simp only [hj, if_true, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
        constructor
        · rintro (rfl | ⟨s', hm, hj'⟩)
          · exact ⟨s, Or.inl ⟨rfl, rfl⟩, hj⟩
          · exact ⟨s', Or.inr hm, hj'⟩
        · rintro ⟨s', (⟨rfl, rfl⟩ | hm), hj'⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨s', hm, hj'⟩
      · simp only [hj, Bool.false_eq_true, if_false, List.not_mem_nil, false_or, List.mem_cons,
          Prod.mk.injEq]
        constructor
        · rintro ⟨s', hm, hj'⟩; exact ⟨s', Or.inr hm, hj'⟩
        · rintro ⟨s', (⟨rfl, rfl⟩ | hm), hj'⟩
          · exact absurd hj' hj
          · exact ⟨s', hm, hj'⟩

theorem shape_ge : ∀ {pc : Nat} {t : Table}, Shape pc t → ∀ q ∈ t, pc ≤ q.1
  | _, [], _, _, hq => absurd hq (by simp)
  | _, _ :: _, hs, q, hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Nat.le_of_eq hs.1.symm
      · have := shape_ge hs.2.2.2.2 q hq; omega

theorem shape_ascending : ∀ {pc : Nat} {t : Table}, Shape pc t → t.Pairwise (fun a b => a.1 < b.1)
  | _, [], _ => List.Pairwise.nil
  | _, _ :: _, hs => by
      obtain ⟨h1, h2, -, -, h5⟩ := hs
      refine List.Pairwise.cons (fun q hq => ?_) (shape_ascending h5)
      have := shape_ge h5 q hq
      have := sectionWidth_pos h2
      omega

theorem cut_ne_nil (pc : Nat) (i : Instr) (rest : List Instr) : cut pc (i :: rest) ≠ [] := by
  simp only [cut]
  split
  · simp
  · split <;> simp

theorem mem_of_lookup : ∀ {t : Table} {n : Nat} {s : Section}, t.lookup n = some s → (n, s) ∈ t
  | [], _, _, h => by simp at h
  | (k, s') :: t, n, s, h => by
      rw [List.lookup_cons] at h
      split at h
      · rename_i hk
        cases h
        have : n = k := by simpa using hk
        subst this
        simp
      · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-! ## What the per-contract check gives -/

section Checked

variable {bytes : List UInt8} {table : Table}

/-- The template decodes to the table's instructions with the immutables erased. -/
theorem Checked.scan_eq (h : Checked bytes table) :
    scan 0 bytes = (join table).map Instr.erase := by
  have := congrArg join h.sections_eq
  rwa [sections, join_cut, join_erase] at this

/-- The deployed code decodes to the table's instructions with the immutables filled in, and
has the template's length. -/
theorem Checked.scan_filled (h : Checked bytes table) (σ : Nat → UInt256) :
    scan 0 (filled bytes σ table).data.toList = (join table).map (Instr.inst σ) ∧
      (filled bytes σ table).size = bytes.length := by
  have := scan_fill σ _ _ h.scan_eq h.fits_eq
  refine ⟨by simpa [filled] using this.1, ?_⟩
  show (fill σ (join table) bytes).toArray.size = _
  simpa using this.2

/-- **Shape**: the sections are consecutive from offset 0, non-empty, and cut exactly at the
`JUMPDEST`s. -/
theorem Checked.shape (h : Checked bytes table) : Shape 0 table := by
  have := shape_cut 0 (scan 0 bytes)
  rw [← sections, h.sections_eq] at this
  exact shape_erase 0 table this

/-- **Shape**: offsets strictly ascend. -/
theorem Checked.ascending (h : Checked bytes table) : table.Pairwise (fun a b => a.1 < b.1) :=
  shape_ascending h.shape

/-- **Shape**: the first section is at offset 0 (and there is none for empty code). -/
theorem Checked.first (h : Checked bytes table) :
    table.head?.map (·.1) = if bytes = [] then none else some 0 := by
  have he := h.sections_eq
  have hs := h.shape
  cases bytes with
  | nil =>
    cases table with
    | nil => rfl
    | cons _ _ => simp [sections, scan, cut, Table.erase] at he
  | cons b rest =>
    rw [sections, scan_cons] at he
    cases table with
    | nil => exact absurd he (cut_ne_nil _ _ _)
    | cons p t => simp [hs.1]

/-- **Decoding**: on the deployed code, every section decodes from its offset as written. -/
theorem Checked.decodes (h : Checked bytes table) (σ : Nat → UInt256) :
    ∀ p ∈ table, Decodes (filled bytes σ table) σ p.1 p.2 := by
  obtain ⟨hscan, hsize⟩ := h.scan_filled σ
  have hd := decodes_scan (filled bytes σ table) σ (by rw [hsize]; exact h.small) 0
  rw [List.drop_zero, hscan] at hd
  exact decodes_table h.shape (decodes_inst hd)

/-- **Decoding**, for the section a lookup returns. -/
theorem Checked.decodes_lookup (h : Checked bytes table) (σ : Nat → UInt256) {t : Nat}
    {s : Section} (hl : table.lookup t = some s) : Decodes (filled bytes σ table) σ t s :=
  h.decodes σ _ (mem_of_lookup hl)

/-- **Destinations**: a word is a valid jump destination of the deployed code exactly when the
table has a section at that offset beginning with `JUMPDEST`. -/
theorem Checked.jumpdest_iff (h : Checked bytes table) (σ : Nat → UInt256) (t : UInt256) :
    (D_J (filled bytes σ table) 0).contains t = true ↔
      ∃ s, (t.toNat, s) ∈ table ∧ startsJD s = true := by
  obtain ⟨hscan, hsize⟩ := h.scan_filled σ
  rw [Array.contains_iff_mem, Array.mem_def, D_J_toList, hscan, jds_inst, List.mem_map,
    ← jds_table _ h.shape]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hlt := jds_scan_lt _ 0 n (by rw [hscan, jds_inst]; exact hn)
    have hs : (filled bytes σ table).data.toList.length = (filled bytes σ table).size := by simp
    rw [toNat_ofNat_of_lt (by have := h.small; omega)]
    exact hn
  · intro hn; exact ⟨t.toNat, hn, ofNat_toNat t⟩

/-- **Destinations**, for an offset given as a number. -/
theorem Checked.jumpdest_iff_nat (h : Checked bytes table) (σ : Nat → UInt256) {t : Nat}
    (ht : t < 2 ^ 256) :
    (D_J (filled bytes σ table) 0).contains (UInt256.ofNat t) = true ↔
      ∃ s, (t, s) ∈ table ∧ startsJD s = true := by
  rw [h.jumpdest_iff σ, toNat_ofNat_of_lt ht]

end Checked

end Reasoning.Listing
