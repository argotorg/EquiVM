import EVM.Disassembly.Sound
import EVM.Disassembly.Tree

/-!
# The `JUMPDEST` set

Relates `D_J` to the sections, so that it never has to be evaluated.

* `Checked.contains_eq`: an offset is in `D_J` iff the section at that offset starts with a
  `JUMPDEST`. A bytecode file states this as its `@[valid_jumps]` theorem, which `jump_dest`
  rewrites with.
* `Checked.D_J_filled`: filling in the immutables does not change `D_J`.
* `Checked.D_J_of_agree`: neither does any other change that leaves the opcode bytes alone.
-/

open Ethereum Ethereum.EVM

set_option autoImplicit false

namespace EVM.Disassembly

/-- The offsets of the sections that start with a `JUMPDEST`. -/
def jumpdests (t : List (Nat × List Instr)) : List Nat :=
  t.flatMap fun p => if startsJD p.2 then [p.1] else []

/-- For consecutive sections, `jds` is `jumpdests`. -/
theorem jds_join : ∀ {pc : Nat} {t : List (Nat × List Instr)}, Shape pc t → jds pc (join t) = jumpdests t
  | _, [], _ => rfl
  | _, (o, s) :: t, hs => by
      obtain ⟨h1, -, h3, -, h5⟩ := hs
      dsimp only at h1 h3 h5
      subst h1
      rw [join_cons, jds_append, jds_section _ _ h3, jds_join h5]
      simp [jumpdests]

/-- With ascending offsets, `lookup` finds every pair of the list. -/
theorem lookup_of_mem : ∀ {t : List (Nat × List Instr)} {n : Nat} {s : List Instr},
    t.Pairwise (fun a b => a.1 < b.1) → (n, s) ∈ t → t.lookup n = some s
  | [], _, _, _, hm => by simp at hm
  | (k, s') :: t, n, s, hp, hm => by
      rw [List.pairwise_cons] at hp
      rw [List.lookup_cons]
      rcases List.mem_cons.mp hm with he | hm
      · cases he; simp
      · have hlt : k < n := hp.1 _ hm
        have hne : (n == k) = false := by simp [Nat.ne_of_gt hlt]
        simp only [hne]
        exact lookup_of_mem hp.2 hm

/-- The offsets of the instructions, where the first one is at `pc`. -/
def starts (pc : Nat) : List Instr → List Nat
  | [] => []
  | i :: rest => pc :: starts (pc + i.width) rest

/-- `starts` only depends on the widths. -/
theorem starts_map {f : Instr → Instr} (hw : ∀ i, (f i).width = i.width) :
    ∀ (pc : Nat) (J : List Instr), starts pc (J.map f) = starts pc J
  | _, [] => rfl
  | pc, i :: J => by simp only [List.map_cons, starts, hw, starts_map hw _ J]

theorem mem_starts_shift : ∀ (pc k : Nat) (J : List Instr) (n : Nat),
    n ∈ starts pc J → n + k ∈ starts (pc + k) J
  | _, _, [], _, h => by simp [starts] at h
  | pc, k, i :: J, n, h => by
      simp only [starts, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        have hs := mem_starts_shift (pc + i.width) k J n h
        rwa [show pc + k + i.width = pc + i.width + k by omega]

/-- Two codes that agree on their opcode bytes have the same `JUMPDEST` offsets. -/
theorem jds_scan_congr : ∀ (l l' : List UInt8) (pc : Nat), l'.length = l.length →
    (∀ n ∈ starts 0 (scan 0 l), l'[n]? = l[n]?) →
    jds pc (scan 0 l') = jds pc (scan 0 l)
  | [], l', _, hlen, _ => by
      rw [List.length_nil, List.length_eq_zero_iff] at hlen; subst hlen; rfl
  | b :: rest, l', pc, hlen, hag => by
      cases l' with
      | nil => simp at hlen
      | cons b' rest' =>
        have h0 : b' = b := by
          have h00 := hag 0 (by rw [scan_cons]; simp [starts])
          simpa using h00
        subst h0
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        rw [scan_cons, scan_cons]
        simp only [jds, isJumpdest_instrOf, instrOf_width]
        have ih := jds_scan_congr (rest.drop (argOnNBytesOfInstr ((parseInstr b').getD .INVALID)))
          (rest'.drop (argOnNBytesOfInstr ((parseInstr b').getD .INVALID)))
          (pc + (1 + argOnNBytesOfInstr ((parseInstr b').getD .INVALID)))
          (by simp [hlen])
          (by
            intro n hn
            have hm : n + (1 + argOnNBytesOfInstr ((parseInstr b').getD .INVALID))
                ∈ starts 0 (scan 0 (b' :: rest)) := by
              rw [scan_cons]
              simp only [starts, List.mem_cons, instrOf_width]
              right
              have hs := mem_starts_shift 0 (1 + argOnNBytesOfInstr ((parseInstr b').getD .INVALID)) _ n hn
              simpa using hs
            have hn' := hag _ hm
            simp only [List.getElem?_drop] at hn' ⊢
            rw [show n + (1 + argOnNBytesOfInstr ((parseInstr b').getD .INVALID))
                = (argOnNBytesOfInstr ((parseInstr b').getD .INVALID) + n) + 1 by omega] at hn'
            simpa using hn')
        rw [ih]
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

namespace Checked

variable {bytes : List UInt8} {table : List (Nat × List Instr)}

/-- `D_J` of the template. -/
theorem D_J_toList_bytes (h : Checked bytes table) :
    (D_J ⟨bytes.toArray⟩ 0).toList = (jumpdests table).map UInt256.ofNat := by
  rw [D_J_toList]
  show (jds 0 (scan 0 bytes.toArray.toList)).map UInt256.ofNat = _
  rw [List.toList_toArray, h.scan_eq, jds_map erase_width erase_isJumpdest, jds_join h.shape]

/-- `D_J` of the deployed code. -/
theorem D_J_toList_filled (h : Checked bytes table) (σ : Nat → UInt256) :
    (D_J (filled bytes σ table) 0).toList = (jumpdests table).map UInt256.ofNat := by
  rw [D_J_toList, (h.scan_filled σ).1, jds_map (inst_width σ) (inst_isJumpdest σ),
    jds_join h.shape]

/-- Filling in the immutables does not change `D_J`. -/
theorem D_J_filled (h : Checked bytes table) (σ : Nat → UInt256) :
    D_J (filled bytes σ table) 0 = D_J ⟨bytes.toArray⟩ 0 :=
  Array.toList_inj.mp (by rw [h.D_J_toList_filled, h.D_J_toList_bytes])

/-- An offset is in `D_J` iff the section at that offset starts with a `JUMPDEST`. -/
theorem contains_eq (h : Checked bytes table) {tree : Tree}
    (hget : ∀ n, tree.get? n = table.lookup n) (t : UInt256) :
    (D_J ⟨bytes.toArray⟩ 0).contains t = ((tree.get? t.toNat).map startsJD).getD false := by
  rw [← h.D_J_filled (fun _ => ⟨0⟩), hget]
  apply Bool.eq_iff_iff.mpr
  rw [h.jumpdest_iff]
  constructor
  · rintro ⟨s, hm, hs⟩
    rw [lookup_of_mem h.ascending hm]
    exact hs
  · intro hl
    cases hlk : table.lookup t.toNat with
    | none => rw [hlk] at hl; cases hl
    | some s =>
        rw [hlk] at hl
        exact ⟨s, mem_of_lookup hlk, hl⟩

/-- A code that agrees with the template on every opcode byte has the same `D_J`. This covers a
template with its immutables patched in by hand. -/
theorem D_J_of_agree (h : Checked bytes table) {code : ByteArray}
    (hsize : code.size = bytes.length)
    (hagree : ∀ n ∈ starts 0 (join table), code.get? n = bytes[n]?) :
    D_J code 0 = D_J ⟨bytes.toArray⟩ 0 := by
  apply Array.toList_inj.mp
  rw [D_J_toList, D_J_toList]
  show (jds 0 (scan 0 code.data.toList)).map UInt256.ofNat
    = (jds 0 (scan 0 bytes.toArray.toList)).map UInt256.ofNat
  rw [List.toList_toArray]
  congr 1
  apply jds_scan_congr
  · simpa using hsize
  · intro n hn
    rw [h.scan_eq, starts_map erase_width] at hn
    rw [← get?_eq_getElem?]
    exact hagree n hn

end Checked

end EVM.Disassembly
