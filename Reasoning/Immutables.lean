import Reasoning.MemCascade
import Reasoning.Reach

/-!
Immutable-aware runtime summaries execute the total runtime obtained by applying
fixed-width word writes to a concrete template.
-/

open Solm Ethereum Ethereum.EVM Reasoning.Reach

namespace Reasoning.Immutables

/-- A site's offset and width describe a fixed patch region. Keys may occur
    at several sites, so one valuation supplies every copy of an immutable. -/
structure Layout where
  sites : List (Nat × Nat × String)

def Layout.disjoint (layout : Layout) (lo hi : Nat) : Bool :=
  layout.sites.all (fun site => decide (hi ≤ site.1 ∨ site.1 + site.2.1 ≤ lo))

/-- Total runtime construction. Values are words, so every write has exactly
    32 bytes. `Layout.inBounds` checks that each recorded width agrees. -/
def Layout.writes (layout : Layout) (words : String → UInt256) : List (Nat × UInt256) :=
  layout.sites.map (fun (off, _, key) => (off, words key))

def Layout.runtime (layout : Layout) (template : ByteArray)
    (words : String → UInt256) : ByteArray :=
  Reasoning.Theory.writeCascade template (layout.writes words)

/-- Check that every recorded width is one word and every write fits. -/
def Layout.inBounds (layout : Layout) (template : ByteArray) : Bool :=
  layout.sites.all (fun site =>
    decide (site.2.1 = 32) && decide (site.1 + site.2.1 ≤ template.size))

theorem Layout.boundAt {layout : Layout} {template : ByteArray}
    (h : layout.inBounds template = true) (site : Nat × Nat × String)
    (hs : site ∈ layout.sites) : site.1 + 32 ≤ template.size := by
  unfold Layout.inBounds at h
  have hsite := List.all_eq_true.mp h site hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsite
  rw [← hsite.1]
  exact hsite.2

private theorem writes_gaps_of_bounds (sites : List (Nat × Nat × String))
    (words : String → UInt256) (size : Nat)
    (h : ∀ site ∈ sites, site.1 + 32 ≤ size) :
    Reasoning.Theory.WriteGapsOk size
      (sites.map (fun (off, _, key) => (off, words key))) := by
  induction sites with
  | nil => trivial
  | cons site rest ih =>
      rcases site with ⟨off, width, key⟩
      simp only [List.map_cons, Reasoning.Theory.WriteGapsOk]
      constructor
      · have hoff := h (off, width, key) (by simp)
        rw [Nat.sub_eq_zero_of_le (by omega : off ≤ size)]
        exact USize.size_pos
      · have hoff := h (off, width, key) (by simp)
        rw [max_eq_left hoff]
        exact ih (by intro s hs; exact h s (by simp [hs]))

private theorem writes_size_of_bounds (sites : List (Nat × Nat × String))
    (words : String → UInt256) (size : Nat)
    (h : ∀ site ∈ sites, site.1 + 32 ≤ size) :
    Reasoning.Theory.writeCascadeSize size
      (sites.map (fun (off, _, key) => (off, words key))) = size := by
  induction sites with
  | nil => rfl
  | cons site rest ih =>
      rcases site with ⟨off, width, key⟩
      simp only [List.map_cons, Reasoning.Theory.writeCascadeSize_cons]
      have hoff := h (off, width, key) (by simp)
      rw [max_eq_left hoff]
      exact ih (by intro s hs; exact h s (by simp [hs]))

theorem Layout.runtime_size_of_bounds {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (h : layout.inBounds template = true) :
    (layout.runtime template words).size = template.size := by
  rcases layout with ⟨sites⟩
  unfold Layout.runtime Layout.writes
  exact (Reasoning.Theory.writeCascade_size template _
    (writes_gaps_of_bounds sites words template.size
      (fun site hs => Layout.boundAt h site hs))).trans
    (writes_size_of_bounds sites words template.size
      (fun site hs => Layout.boundAt h site hs))

private theorem writes_window_of_disjoint (sites : List (Nat × Nat × String))
    (words : String → UInt256) (size lo hi : Nat)
    (hbound : ∀ site ∈ sites, site.1 + 32 ≤ size)
    (hdisj : ∀ site ∈ sites, hi ≤ site.1 ∨ site.1 + 32 ≤ lo)
    (hlo : lo ≤ hi) (hhi : hi ≤ size) :
    Reasoning.Theory.WindowDisjointFromWrites size lo (hi - lo)
      (sites.map (fun (off, _, key) => (off, words key))) := by
  induction sites with
  | nil => trivial
  | cons site rest ih =>
      rcases site with ⟨off, width, key⟩
      simp only [List.map_cons, Reasoning.Theory.WindowDisjointFromWrites]
      constructor
      · have hoff := hbound (off, width, key) (by simp)
        rw [Nat.sub_eq_zero_of_le (by omega : off ≤ size)]
        exact USize.size_pos
      constructor
      · have hd := hdisj (off, width, key) (by simp)
        rcases hd with hd | hd
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨hd, by omega⟩
      · have hoff := hbound (off, width, key) (by simp)
        rw [max_eq_left hoff]
        exact ih (by intro s hs; exact hbound s (by simp [hs]))
          (by intro s hs; exact hdisj s (by simp [hs]))

theorem Layout.windowDisjoint {layout : Layout} {template : ByteArray}
    {words : String → UInt256} {lo hi : Nat}
    (hbound : layout.inBounds template = true)
    (hdisj : layout.disjoint lo hi = true)
    (hlo : lo ≤ hi) (hhi : hi ≤ template.size) :
    Reasoning.Theory.WindowDisjointFromWrites template.size lo (hi - lo)
      (layout.writes words) := by
  rcases layout with ⟨sites⟩
  apply writes_window_of_disjoint sites words template.size lo hi
    (fun site hs => Layout.boundAt hbound site hs) ?_ hlo hhi
  intro site hs
  unfold Layout.disjoint at hdisj
  have hd : hi ≤ site.1 ∨ site.1 + site.2.1 ≤ lo := by
    simpa using (List.all_eq_true.mp hdisj site hs)
  have hw : site.2.1 = 32 := by
    unfold Layout.inBounds at hbound
    have hh := List.all_eq_true.mp hbound site hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1
  simpa [hw] using hd

private theorem get?_eq_of_extract_one (a b : ByteArray) (i : Nat)
    (ha : i < a.size) (hb : i < b.size)
    (h : a.extract i (i + 1) = b.extract i (i + 1)) :
    a.get? i = b.get? i := by
  unfold ByteArray.get?
  simp only [dif_pos ha, dif_pos hb]
  have h0 : (a.extract i (i + 1)).get? 0 = (b.extract i (i + 1)).get? 0 := by rw [h]
  unfold ByteArray.get? at h0
  have hsa : 0 < (a.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  have hsb : 0 < (b.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  simp only [dif_pos hsa, dif_pos hsb] at h0
  have hla : (a.extract i (i + 1)).get 0 hsa = a.get i ha := by
    change (a.extract i (i + 1))[0] = a[i]
    simpa using ByteArray.get_extract (a := a) (start := i) (stop := i + 1) (i := 0) hsa
  have hlb : (b.extract i (i + 1)).get 0 hsb = b.get i hb := by
    change (b.extract i (i + 1))[0] = b[i]
    simpa using ByteArray.get_extract (a := b) (start := i) (stop := i + 1) (i := 0) hsb
  rw [hla, hlb] at h0
  exact h0

private theorem decode_eq_of_get?_arg_eq (a b : ByteArray) (pc : UInt256)
    (hget : a.get? pc.toNat = b.get? pc.toNat)
    (harg : ∀ byte instr,
      b.get? pc.toNat = some byte → parseInstr byte = some instr →
      a.extract' (pc.toNat + 1) (pc.toNat + 1 + argOnNBytesOfInstr instr) =
        b.extract' (pc.toNat + 1) (pc.toNat + 1 + argOnNBytesOfInstr instr)) :
    decode a pc = decode b pc := by
  unfold decode
  rw [hget]
  cases hb : b.get? pc.toNat with
  | none => rfl
  | some byte =>
      cases hi : parseInstr byte with
      | none => simp [hi]
      | some instr =>
          simp [hi]
          by_cases hn : argOnNBytesOfInstr instr = 0
          · simp [hn]
          · simp [hn]
            rw [harg byte instr hb hi]

theorem Layout.getUnchanged {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (i : Nat)
    (hsize : (layout.runtime template words).size = template.size)
    (hwin : Reasoning.Theory.WindowDisjointFromWrites template.size i 1
      (layout.writes words))
    (hi : i + 1 ≤ template.size) :
    (layout.runtime template words).get? i = template.get? i := by
  apply get?_eq_of_extract_one
  · rw [hsize]; omega
  · omega
  · rw [← Reasoning.Theory.readWithPadding_eq_extract'
      (layout.runtime template words) i 1 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
    rw [← Reasoning.Theory.readWithPadding_eq_extract'
      template i 1 (by norm_num) (by norm_num) (by omega)]
    exact Reasoning.Theory.writeCascade_read_preserved_len template
      (layout.writes words) i 1 hwin (by norm_num) (by norm_num)

theorem Layout.decodeUnchanged {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (pc : UInt256) (byte : UInt8) (instr : Operation)
    (hsize : (layout.runtime template words).size = template.size)
    (hsize64 : template.size < 2 ^ 64)
    (hbyte : template.get? pc.toNat = some byte)
    (hinstr : parseInstr byte = some instr)
    (hgetwin : Reasoning.Theory.WindowDisjointFromWrites template.size pc.toNat 1
      (layout.writes words))
    (hgethi : pc.toNat + 1 ≤ template.size)
    (hargwin : Reasoning.Theory.WindowDisjointFromWrites template.size
      (pc.toNat + 1) (argOnNBytesOfInstr instr) (layout.writes words))
    (harghi : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ template.size) :
    decode (layout.runtime template words) pc = decode template pc := by
  apply decode_eq_of_get?_arg_eq
  · exact Layout.getUnchanged pc.toNat hsize hgetwin hgethi
  · intro byte' instr' hbyte' hinstr'
    rw [hbyte] at hbyte'
    cases hbyte'
    rw [hinstr] at hinstr'
    cases hinstr'
    let len := argOnNBytesOfInstr instr
    have hbound := harghi
    have hwindow := hargwin
    change pc.toNat + 1 + len ≤ template.size at hbound
    change Reasoning.Theory.WindowDisjointFromWrites template.size
      (pc.toNat + 1) len (layout.writes words) at hwindow
    change (layout.runtime template words).extract' (pc.toNat + 1)
      (pc.toNat + 1 + len) = template.extract' (pc.toNat + 1)
        (pc.toNat + 1 + len)
    by_cases hpos : 0 < len
    · unfold ByteArray.extract'
      have hguard : (decide (pc.toNat + 1 < 2 ^ 64) &&
          decide (pc.toNat + 1 + len < 2 ^ 64)) = true := by
        rw [decide_eq_true (by omega), decide_eq_true (by omega)]
        rfl
      rw [if_pos hguard, if_pos hguard]
      rw [← Reasoning.Theory.readWithPadding_eq_extract'
          (layout.runtime template words) (pc.toNat + 1) len hpos
          (by omega) (by rw [hsize]; exact hbound)]
      rw [← Reasoning.Theory.readWithPadding_eq_extract'
          template (pc.toNat + 1) len hpos (by omega) hbound]
      exact Reasoning.Theory.writeCascade_read_preserved_len template
        (layout.writes words) (pc.toNat + 1) len hwindow hpos (by omega)
    · have hz : len = 0 := by omega
      dsimp only [len] at hz ⊢
      simp [hz, ByteArray.extract']

/-- The two layout checks are concrete arithmetic, so generated summaries can
    discharge them with `native_decide` and then decode the template. -/
theorem Layout.decodeUnchangedOfLayout {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (pc : UInt256) (byte : UInt8) (instr : Operation)
    (hbound : layout.inBounds template = true)
    (hsize64 : template.size < 2 ^ 64)
    (hbyte : template.get? pc.toNat = some byte)
    (hinstr : parseInstr byte = some instr)
    (hopdisj : layout.disjoint pc.toNat (pc.toNat + 1) = true)
    (hophi : pc.toNat + 1 ≤ template.size)
    (hargdisj : layout.disjoint (pc.toNat + 1)
      (pc.toNat + 1 + argOnNBytesOfInstr instr) = true)
    (harghi : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ template.size) :
    decode (layout.runtime template words) pc = decode template pc := by
  apply Layout.decodeUnchanged pc byte instr (Layout.runtime_size_of_bounds hbound)
    hsize64 hbyte hinstr
  · simpa using (Layout.windowDisjoint (words := words) hbound hopdisj
      (by omega) hophi)
  · exact hophi
  · simpa using (Layout.windowDisjoint (words := words) hbound hargdisj
      (by omega) harghi)
  · exact harghi

/-- Lift one concrete template decode using one bundled check for the byte and windows. -/
theorem Layout.decodeConcreteOfChecks {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (pc : UInt256) (byte : UInt8) (instr : Operation)
    (arg : Option (UInt256 × Nat))
    (hbound : layout.inBounds template = true)
    (hsize64 : template.size < 2 ^ 64)
    (checks : template.get? pc.toNat = some byte ∧
      parseInstr byte = some instr ∧
      layout.disjoint pc.toNat (pc.toNat + 1) = true ∧
      pc.toNat + 1 ≤ template.size ∧
      layout.disjoint (pc.toNat + 1)
        (pc.toNat + 1 + argOnNBytesOfInstr instr) = true ∧
      pc.toNat + 1 + argOnNBytesOfInstr instr ≤ template.size ∧
      decode template pc = some (instr, arg)) :
    decode (layout.runtime template words) pc = some (instr, arg) := by
  rcases checks with ⟨hbyte, hinstr, hopdisj, hophi, hargdisj, harghi, hdecode⟩
  rw [Layout.decodeUnchangedOfLayout pc byte instr hbound hsize64
    hbyte hinstr hopdisj hophi hargdisj harghi]
  exact hdecode

/-- Decode with shared layout bounds and a single native check for a concrete instruction. -/
macro "immutable_decode" "(" layout:term "," template:term "," words:term ","
    pc:term "," byte:term "," instr:term "," arg:term ","
    hbound:term "," hsize64:term ")" : tactic =>
  `(tactic|
    (conv_lhs => arg 2; change $pc
     exact Reasoning.Immutables.Layout.decodeConcreteOfChecks
       (layout := $layout) (template := $template) (words := $words)
       (pc := $pc) (byte := $byte) (instr := $instr)
       (arg := $arg) $hbound $hsize64 (by native_decide)))

theorem Layout.readSiteWord {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (off : Nat) (key : String)
    (before after : List (Nat × UInt256))
    (hsplit : layout.writes words = before ++ (off, words key) :: after)
    (hbefore : (Reasoning.Theory.writeCascade template before).size = template.size)
    (hafter : Reasoning.Theory.WindowDisjointFromWrites template.size off 32 after)
    (hsize : (layout.runtime template words).size = template.size)
    (hsize64 : template.size < 2 ^ 64)
    (hbound : off + 32 ≤ template.size) :
    (layout.runtime template words).extract' off (off + 32) =
      (words key).toByteArray := by
  have hread : (layout.runtime template words).readWithPadding off 32 =
      (words key).toByteArray := by
    rw [Layout.runtime, hsplit, Reasoning.Theory.writeCascade_append]
    exact Reasoning.Theory.writeCascade_read_word_of_head
      (Reasoning.Theory.writeCascade template before) off (words key) after
      (by
        have hoff : off ≤ (Reasoning.Theory.writeCascade template before).size := by
          rw [hbefore]; omega
        rw [Nat.sub_eq_zero_of_le hoff]
        exact USize.size_pos)
      (by simpa [hbefore, max_eq_left hbound] using hafter)
  unfold ByteArray.extract'
  have hguard : (decide (off < 2 ^ 64) && decide (off + 32 < 2 ^ 64)) = true := by
    rw [decide_eq_true (by omega), decide_eq_true (by omega)]
    rfl
  rw [if_pos hguard]
  rw [← Reasoning.Theory.readWithPadding_eq_extract'
    (layout.runtime template words) off 32 (by norm_num) (by norm_num)
    (by rw [hsize]; exact hbound)]
  exact hread

private theorem word_from_bytes (w : UInt256) :
    uInt256OfByteArray (UInt256.toByteArray w) = w := by
  rw [Reasoning.Theory.uInt256OfByteArray_eq]
  rw [Reasoning.Theory.fromByteArrayBigEndian_toByteArray,
    Reasoning.Theory.u256_ofNat_toNat]

theorem Layout.decodeSite {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (pc : UInt256) (off : Nat) (key : String)
    (before after : List (Nat × UInt256))
    (hpc : pc.toNat + 1 = off)
    (hsize : (layout.runtime template words).size = template.size)
    (hsize64 : template.size < 2 ^ 64)
    (hbound : off + 32 ≤ template.size)
    (hgetwin : Reasoning.Theory.WindowDisjointFromWrites template.size pc.toNat 1
      (layout.writes words))
    (hopcode : template.get? pc.toNat = some 0x7f)
    (hsplit : layout.writes words = before ++ (off, words key) :: after)
    (hbefore : (Reasoning.Theory.writeCascade template before).size = template.size)
    (hafter : Reasoning.Theory.WindowDisjointFromWrites template.size off 32 after) :
    decode (layout.runtime template words) pc =
      some (.Push .PUSH32, some (words key, 32)) := by
  unfold decode
  rw [Layout.getUnchanged pc.toNat hsize hgetwin (by omega), hopcode]
  simp [parseInstr, argOnNBytesOfInstr]
  rw [hpc]
  rw [Layout.readSiteWord off key before after hsplit hbefore hafter hsize hsize64 hbound]
  rw [word_from_bytes]

end Reasoning.Immutables
