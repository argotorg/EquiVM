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

/-- A fixed-width suffix of a word, as used by PUSH20 and PUSH32 payloads. -/
def Layout.siteBytes (width : Nat) (word : UInt256) : ByteArray :=
  (UInt256.toByteArray word).extract (32 - width) 32

/-- The EVM stack value decoded from a patched PUSH argument. -/
def Layout.siteWord (width : Nat) (word : UInt256) : UInt256 :=
  uInt256OfByteArray (Layout.siteBytes width word)

/-- Write the low `width` bytes of a word at one immutable site. -/
def Layout.writeSite (mem : ByteArray) (site : Nat × Nat × String)
    (words : String → UInt256) : ByteArray :=
  let (off, width, key) := site
  (Layout.siteBytes width (words key)).write 0 mem off width

/-- Runtime construction for layouts that include narrower PUSH arguments. -/
def Layout.runtimeN (layout : Layout) (template : ByteArray)
    (words : String → UInt256) : ByteArray :=
  layout.sites.foldl (fun mem site => Layout.writeSite mem site words) template

/-- Width and bounds checks for variable-width PUSH arguments. -/
def Layout.inBoundsN (layout : Layout) (template : ByteArray) : Bool :=
  layout.sites.all (fun site =>
    decide (0 < site.2.1 ∧ site.2.1 ≤ 32 ∧ site.1 + site.2.1 ≤ template.size))

private theorem Layout.siteBytes_size (width : Nat) (word : UInt256)
    (hwidth : width ≤ 32) : (Layout.siteBytes width word).size = width := by
  unfold Layout.siteBytes
  rw [ByteArray.size_extract, Reasoning.Theory.toByteArray_size]
  omega

private theorem Layout.writeSite_size (mem : ByteArray) (site : Nat × Nat × String)
    (words : String → UInt256)
    (hwidth : 0 < site.2.1 ∧ site.2.1 ≤ 32)
    (hbound : site.1 + site.2.1 ≤ mem.size) :
    (Layout.writeSite mem site words).size = mem.size := by
  rcases site with ⟨off, width, key⟩
  change 0 < width ∧ width ≤ 32 at hwidth
  change off + width ≤ mem.size at hbound
  unfold Layout.writeSite
  simp only
  rw [Reasoning.Theory.write_eq_gen _ _ off width (by omega)
    (by rw [Layout.siteBytes_size width (words key) hwidth.2]) hbound]
  rw [ByteArray.size_append, ByteArray.size_append]
  simp only [ByteArray.size_extract]
  rw [Layout.siteBytes_size width (words key) hwidth.2]
  omega

private theorem Layout.runtimeN_size_aux (sites : List (Nat × Nat × String))
    (template : ByteArray) (words : String → UInt256)
    (hsites : ∀ site ∈ sites,
      0 < site.2.1 ∧ site.2.1 ≤ 32 ∧ site.1 + site.2.1 ≤ template.size) :
    (sites.foldl (fun mem site => Layout.writeSite mem site words) template).size =
      template.size := by
  induction sites generalizing template with
  | nil => rfl
  | cons site rest ih =>
      simp only [List.foldl_cons]
      have hs := hsites site (by simp)
      have hsize := Layout.writeSite_size template site words ⟨hs.1, hs.2.1⟩ hs.2.2
      rw [ih (Layout.writeSite template site words) (by
        intro s hmem
        rw [hsize]
        exact hsites s (by simp [hmem]))]
      exact hsize

theorem Layout.runtimeN_size_of_bounds {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (hbound : layout.inBoundsN template = true) :
    (layout.runtimeN template words).size = template.size := by
  unfold Layout.runtimeN
  apply Layout.runtimeN_size_aux
  intro site hs
  exact decide_eq_true_eq.mp (List.all_eq_true.mp hbound site hs)

open Reasoning.Theory in
private theorem writePatch_read_preserved (src mem : ByteArray)
    (off width read len : Nat)
    (hwidth : 0 < width ∧ width ≤ src.size)
    (hbound : off + width ≤ mem.size)
    (hread : read + len ≤ mem.size)
    (hdisj : read + len ≤ off ∨ off + width ≤ read)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write 0 mem off width).readWithPadding read len =
      mem.readWithPadding read len := by
  rw [write_eq_gen src mem off width (by omega) hwidth.2 hbound]
  rcases hdisj with hbelow | habove
  · have hbsz : (mem.extract 0 off).size = off := by
      rw [ByteArray.size_extract]; omega
    have hssz : (src.extract 0 width).size = width := by
      rw [ByteArray.size_extract]; omega
    rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbsz, hssz]
      rw [ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hbsz, hssz]; omega)]
    rw [extract_append_left _ _ _ _ (by rw [hbsz]; omega)]
    rw [extract_prefix _ _ _ _ hbelow]
    rw [← readWithPadding_eq_extract' mem read len hpos hlen64 hread]
  · have hbsz : (mem.extract 0 off).size = off := by
      rw [ByteArray.size_extract]; omega
    have hssz : (src.extract 0 width).size = width := by
      rw [ByteArray.size_extract]; omega
    have htsz : (mem.extract (off + width) mem.size).size = mem.size - (off + width) := by
      rw [ByteArray.size_extract]; omega
    have hleftsz : (mem.extract 0 off ++ src.extract 0 width).size = off + width := by
      rw [ByteArray.size_append, hbsz, hssz]
    rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
      rw [ByteArray.size_append, hleftsz, htsz]; omega)]
    rw [readWithPadding_eq_extract' mem read len hpos hlen64 hread]
    rw [extract_append_right_window _ _ _ _ (by rw [hleftsz]; omega), hleftsz]
    rw [extract_extract_BA]
    congr 1 <;> omega

open Reasoning.Theory in
private theorem writePatch_read_back (src mem : ByteArray)
    (off width : Nat) (hwidth : 0 < width ∧ width ≤ src.size)
    (hbound : off + width ≤ mem.size) (hwidth64 : width < 2 ^ 64) :
    (src.write 0 mem off width).readWithPadding off width = src.extract 0 width := by
  rw [write_eq_gen src mem off width (by omega) hwidth.2 hbound]
  have hbsz : (mem.extract 0 off).size = off := by
    rw [ByteArray.size_extract]; omega
  have hssz : (src.extract 0 width).size = width := by
    rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract' _ off width hwidth.1 hwidth64 (by
    rw [ByteArray.size_append, ByteArray.size_append, hbsz, hssz,
      ByteArray.size_extract]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, hbsz, hssz])]
  rw [extract_append_right_window _ _ _ _ (by rw [hbsz])]
  rw [hbsz]
  simp [extract_extract_BA]

private theorem Layout.writeSite_read_preserved (mem : ByteArray)
    (site : Nat × Nat × String) (words : String → UInt256)
    (read len : Nat)
    (hwidth : 0 < site.2.1 ∧ site.2.1 ≤ 32)
    (hbound : site.1 + site.2.1 ≤ mem.size)
    (hread : read + len ≤ mem.size)
    (hdisj : read + len ≤ site.1 ∨ site.1 + site.2.1 ≤ read)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (Layout.writeSite mem site words).readWithPadding read len =
      mem.readWithPadding read len := by
  rcases site with ⟨off, width, key⟩
  change 0 < width ∧ width ≤ 32 at hwidth
  change off + width ≤ mem.size at hbound
  change read + len ≤ off ∨ off + width ≤ read at hdisj
  exact writePatch_read_preserved (Layout.siteBytes width (words key)) mem
    off width read len
    ⟨hwidth.1, by rw [Layout.siteBytes_size width (words key) hwidth.2]⟩
    hbound hread hdisj hpos hlen64

private theorem Layout.writeSite_read_back (mem : ByteArray)
    (off width : Nat) (key : String) (words : String → UInt256)
    (hwidth : 0 < width ∧ width ≤ 32)
    (hbound : off + width ≤ mem.size) :
    (Layout.writeSite mem (off, width, key) words).readWithPadding off width =
      Layout.siteBytes width (words key) := by
  unfold Layout.writeSite
  rw [writePatch_read_back (Layout.siteBytes width (words key)) mem off width
    ⟨hwidth.1, by rw [Layout.siteBytes_size width (words key) hwidth.2]⟩
    hbound (by omega)]
  apply ByteArray.ext
  simp [ByteArray.data_extract, Layout.siteBytes_size width (words key) hwidth.2]

private theorem Layout.runtimeN_read_preserved_aux
    (sites : List (Nat × Nat × String)) (mem : ByteArray)
    (words : String → UInt256) (read len : Nat)
    (hsites : ∀ site ∈ sites,
      0 < site.2.1 ∧ site.2.1 ≤ 32 ∧ site.1 + site.2.1 ≤ mem.size)
    (hdisj : ∀ site ∈ sites,
      read + len ≤ site.1 ∨ site.1 + site.2.1 ≤ read)
    (hread : read + len ≤ mem.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (sites.foldl (fun acc site => Layout.writeSite acc site words) mem).readWithPadding
      read len = mem.readWithPadding read len := by
  induction sites generalizing mem with
  | nil => rfl
  | cons site rest ih =>
      simp only [List.foldl_cons]
      have hs := hsites site (by simp)
      have hsize := Layout.writeSite_size mem site words ⟨hs.1, hs.2.1⟩ hs.2.2
      rw [ih (Layout.writeSite mem site words) (by
        intro s hmem
        rw [hsize]
        exact hsites s (by simp [hmem])) (by
        intro s hmem
        exact hdisj s (by simp [hmem])) (by rw [hsize]; exact hread)]
      exact Layout.writeSite_read_preserved mem site words read len
        ⟨hs.1, hs.2.1⟩ hs.2.2 hread (hdisj site (by simp)) hpos hlen64

theorem Layout.runtimeN_read_preserved {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (read len : Nat)
    (hbound : layout.inBoundsN template = true)
    (hdisj : layout.disjoint read (read + len) = true)
    (hread : read + len ≤ template.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (layout.runtimeN template words).readWithPadding read len =
      template.readWithPadding read len := by
  unfold Layout.runtimeN
  apply Layout.runtimeN_read_preserved_aux layout.sites template words read len
  · intro site hs
    exact decide_eq_true_eq.mp (List.all_eq_true.mp hbound site hs)
  · intro site hs
    have hd := List.all_eq_true.mp hdisj site hs
    exact decide_eq_true_eq.mp hd
  · exact hread
  · exact hpos
  · exact hlen64

theorem Layout.runtimeN_read_site {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (off width : Nat) (key : String)
    (before after : List (Nat × Nat × String))
    (hsplit : layout.sites = before ++ (off, width, key) :: after)
    (hbound : layout.inBoundsN template = true)
    (hafter : ∀ site ∈ after,
      off + width ≤ site.1 ∨ site.1 + site.2.1 ≤ off)
    (hwidth64 : width < 2 ^ 64) :
    (layout.runtimeN template words).readWithPadding off width =
      Layout.siteBytes width (words key) := by
  have hsites : ∀ site ∈ layout.sites,
      0 < site.2.1 ∧ site.2.1 ≤ 32 ∧ site.1 + site.2.1 ≤ template.size := by
    intro site hs
    exact decide_eq_true_eq.mp (List.all_eq_true.mp hbound site hs)
  have hbefore : ∀ site ∈ before,
      0 < site.2.1 ∧ site.2.1 ≤ 32 ∧ site.1 + site.2.1 ≤ template.size := by
    intro site hs
    exact hsites site (by rw [hsplit]; simp [hs])
  have hsite := hsites (off, width, key) (by rw [hsplit]; simp)
  have hafterSites : ∀ site ∈ after,
      0 < site.2.1 ∧ site.2.1 ≤ 32 ∧ site.1 + site.2.1 ≤ template.size := by
    intro site hs
    exact hsites site (by rw [hsplit]; simp [hs])
  have hbeforeSize := Layout.runtimeN_size_aux before template words hbefore
  let mid := before.foldl (fun mem site => Layout.writeSite mem site words) template
  have hmidSize : mid.size = template.size := hbeforeSize
  have hheadSize := Layout.writeSite_size mid (off, width, key) words
    ⟨hsite.1, hsite.2.1⟩ (by rw [hmidSize]; exact hsite.2.2)
  unfold Layout.runtimeN
  rw [hsplit, List.foldl_append]
  simp only [List.foldl_cons]
  change (after.foldl (fun mem site => Layout.writeSite mem site words)
    (Layout.writeSite mid (off, width, key) words)).readWithPadding off width = _
  rw [Layout.runtimeN_read_preserved_aux after
    (Layout.writeSite mid (off, width, key) words) words off width
    (by intro site hs; rw [hheadSize, hmidSize]; exact hafterSites site hs)
    hafter (by rw [hheadSize, hmidSize]; exact hsite.2.2)
    hsite.1 hwidth64]
  exact Layout.writeSite_read_back mid off width key words
    ⟨hsite.1, hsite.2.1⟩ (by rw [hmidSize]; exact hsite.2.2)

theorem Layout.runtimeN_get_unchanged {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (i : Nat)
    (hbound : layout.inBoundsN template = true)
    (hdisj : layout.disjoint i (i + 1) = true)
    (hi : i + 1 ≤ template.size) :
    (layout.runtimeN template words).get? i = template.get? i := by
  apply get?_eq_of_extract_one
  · rw [Layout.runtimeN_size_of_bounds hbound]; omega
  · omega
  · rw [← Reasoning.Theory.readWithPadding_eq_extract'
      (layout.runtimeN template words) i 1 (by norm_num) (by norm_num)
      (by rw [Layout.runtimeN_size_of_bounds hbound]; omega)]
    rw [← Reasoning.Theory.readWithPadding_eq_extract'
      template i 1 (by norm_num) (by norm_num) hi]
    exact Layout.runtimeN_read_preserved i 1 hbound hdisj hi
      (by norm_num) (by norm_num)

/-- Decoding passes through the generic runtime away from its patch sites. -/
theorem Layout.decodeUnchangedNOfLayout {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (pc : UInt256) (byte : UInt8) (instr : Operation)
    (hbound : layout.inBoundsN template = true)
    (hsize64 : template.size < 2 ^ 64)
    (hbyte : template.get? pc.toNat = some byte)
    (hinstr : parseInstr byte = some instr)
    (hopdisj : layout.disjoint pc.toNat (pc.toNat + 1) = true)
    (hophi : pc.toNat + 1 ≤ template.size)
    (hargdisj : layout.disjoint (pc.toNat + 1)
      (pc.toNat + 1 + argOnNBytesOfInstr instr) = true)
    (harghi : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ template.size) :
    decode (layout.runtimeN template words) pc = decode template pc := by
  apply decode_eq_of_get?_arg_eq
  · exact Layout.runtimeN_get_unchanged pc.toNat hbound hopdisj hophi
  · intro byte' instr' hbyte' hinstr'
    rw [hbyte] at hbyte'
    cases hbyte'
    rw [hinstr] at hinstr'
    cases hinstr'
    let len := argOnNBytesOfInstr instr
    change (layout.runtimeN template words).extract' (pc.toNat + 1)
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
          (layout.runtimeN template words) (pc.toNat + 1) len hpos
          (by omega) (by rw [Layout.runtimeN_size_of_bounds hbound]; exact harghi)]
      rw [← Reasoning.Theory.readWithPadding_eq_extract'
          template (pc.toNat + 1) len hpos (by omega) harghi]
      exact Layout.runtimeN_read_preserved (pc.toNat + 1) len hbound
        hargdisj harghi hpos (by omega)
    · have hz : len = 0 := by omega
      dsimp only [len] at hz ⊢
      simp [hz, ByteArray.extract']

/-- Lift a concrete template decode when no patch intersects its opcode or argument. -/
theorem Layout.decodeConcreteNOfChecks {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (pc : UInt256) (byte : UInt8) (instr : Operation)
    (arg : Option (UInt256 × Nat))
    (hbound : layout.inBoundsN template = true)
    (hsize64 : template.size < 2 ^ 64)
    (checks : template.get? pc.toNat = some byte ∧
      parseInstr byte = some instr ∧
      layout.disjoint pc.toNat (pc.toNat + 1) = true ∧
      pc.toNat + 1 ≤ template.size ∧
      layout.disjoint (pc.toNat + 1)
        (pc.toNat + 1 + argOnNBytesOfInstr instr) = true ∧
      pc.toNat + 1 + argOnNBytesOfInstr instr ≤ template.size ∧
      decode template pc = some (instr, arg)) :
    decode (layout.runtimeN template words) pc = some (instr, arg) := by
  rcases checks with ⟨hbyte, hinstr, hopdisj, hophi, hargdisj, harghi, hdecode⟩
  rw [Layout.decodeUnchangedNOfLayout pc byte instr hbound hsize64
    hbyte hinstr hopdisj hophi hargdisj harghi]
  exact hdecode

macro "immutable_decode_n" "(" layout:term "," template:term "," words:term ","
    pc:term "," byte:term "," instr:term "," arg:term ","
    hbound:term "," hsize64:term ")" : tactic =>
  `(tactic|
    (conv_lhs => arg 2; change $pc
     exact Reasoning.Immutables.Layout.decodeConcreteNOfChecks
       (layout := $layout) (template := $template) (words := $words)
       (pc := $pc) (byte := $byte) (instr := $instr)
       (arg := $arg) $hbound $hsize64 (by native_decide)))

/-- Decode a PUSH20 whose 20-byte payload is supplied by a symbolic word. -/
theorem Layout.decodeSite20 {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (pc : UInt256) (off : Nat) (key : String)
    (before after : List (Nat × Nat × String))
    (hpc : pc.toNat + 1 = off)
    (hbound : layout.inBoundsN template = true)
    (hsize64 : template.size < 2 ^ 64)
    (hopdisj : layout.disjoint pc.toNat (pc.toNat + 1) = true)
    (hopcode : template.get? pc.toNat = some 0x73)
    (hsplit : layout.sites = before ++ (off, 20, key) :: after)
    (hafter : ∀ site ∈ after,
      off + 20 ≤ site.1 ∨ site.1 + site.2.1 ≤ off) :
    decode (layout.runtimeN template words) pc =
      some (.Push .PUSH20, some (Layout.siteWord 20 (words key), 20)) := by
  unfold decode
  rw [Layout.runtimeN_get_unchanged pc.toNat hbound hopdisj (by
    have hs : (off, 20, key) ∈ layout.sites := by rw [hsplit]; simp
    have hb := decide_eq_true_eq.mp (List.all_eq_true.mp hbound (off, 20, key) hs)
    omega), hopcode]
  simp [parseInstr, argOnNBytesOfInstr]
  rw [hpc]
  have hsite := Layout.runtimeN_read_site (words := words) off 20 key before after hsplit
    hbound hafter (by norm_num : 20 < 2 ^ 64)
  unfold ByteArray.extract'
  have hguard : (decide (off < 2 ^ 64) && decide (off + 20 < 2 ^ 64)) = true := by
    have hs : (off, 20, key) ∈ layout.sites := by rw [hsplit]; simp
    have hb := decide_eq_true_eq.mp (List.all_eq_true.mp hbound (off, 20, key) hs)
    have hb' : off + 20 ≤ template.size := by simpa using hb.2.2
    rw [decide_eq_true (by omega), decide_eq_true (by omega)]
    rfl
  rw [if_pos hguard]
  rw [← Reasoning.Theory.readWithPadding_eq_extract'
    (layout.runtimeN template words) off 20 (by norm_num) (by norm_num)
    (by rw [Layout.runtimeN_size_of_bounds hbound]
        have hs : (off, 20, key) ∈ layout.sites := by rw [hsplit]; simp
        have hb := decide_eq_true_eq.mp (List.all_eq_true.mp hbound (off, 20, key) hs)
        exact hb.2.2)]
  exact congrArg uInt256OfByteArray hsite

/-- Decode a PUSH32 in a layout that may also contain PUSH20 sites. -/
theorem Layout.decodeSite32N {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (pc : UInt256) (off : Nat) (key : String)
    (before after : List (Nat × Nat × String))
    (hpc : pc.toNat + 1 = off)
    (hbound : layout.inBoundsN template = true)
    (hsize64 : template.size < 2 ^ 64)
    (hopdisj : layout.disjoint pc.toNat (pc.toNat + 1) = true)
    (hopcode : template.get? pc.toNat = some 0x7f)
    (hsplit : layout.sites = before ++ (off, 32, key) :: after)
    (hafter : ∀ site ∈ after,
      off + 32 ≤ site.1 ∨ site.1 + site.2.1 ≤ off) :
    decode (layout.runtimeN template words) pc =
      some (.Push .PUSH32, some (Layout.siteWord 32 (words key), 32)) := by
  unfold decode
  rw [Layout.runtimeN_get_unchanged pc.toNat hbound hopdisj (by
    have hs : (off, 32, key) ∈ layout.sites := by rw [hsplit]; simp
    have hb := decide_eq_true_eq.mp (List.all_eq_true.mp hbound (off, 32, key) hs)
    omega), hopcode]
  simp [parseInstr, argOnNBytesOfInstr]
  rw [hpc]
  have hsite := Layout.runtimeN_read_site (words := words) off 32 key before after hsplit
    hbound hafter (by norm_num : 32 < 2 ^ 64)
  unfold ByteArray.extract'
  have hguard : (decide (off < 2 ^ 64) && decide (off + 32 < 2 ^ 64)) = true := by
    have hs : (off, 32, key) ∈ layout.sites := by rw [hsplit]; simp
    have hb := decide_eq_true_eq.mp (List.all_eq_true.mp hbound (off, 32, key) hs)
    have hb' : off + 32 ≤ template.size := by simpa using hb.2.2
    rw [decide_eq_true (by omega), decide_eq_true (by omega)]
    rfl
  rw [if_pos hguard]
  rw [← Reasoning.Theory.readWithPadding_eq_extract'
    (layout.runtimeN template words) off 32 (by norm_num) (by norm_num)
    (by rw [Layout.runtimeN_size_of_bounds hbound]
        have hs : (off, 32, key) ∈ layout.sites := by rw [hsplit]; simp
        have hb := decide_eq_true_eq.mp (List.all_eq_true.mp hbound (off, 32, key) hs)
        exact hb.2.2)]
  exact congrArg uInt256OfByteArray hsite

private theorem Layout.siteBytes32 (word : UInt256) :
    Layout.siteBytes 32 word = UInt256.toByteArray word := by
  simpa [Layout.siteBytes] using Reasoning.Theory.toByteArray_extract_all word

private theorem Layout.writeSite32 (mem : ByteArray) (off : Nat) (key : String)
    (words : String → UInt256) :
    Layout.writeSite mem (off, 32, key) words =
      Reasoning.Theory.writeWord mem off (words key) := by
  simp [Layout.writeSite, Layout.siteBytes32, Reasoning.Theory.writeWord]

private theorem Layout.runtimeN_eq_runtime_aux
    (sites : List (Nat × Nat × String)) (mem : ByteArray)
    (words : String → UInt256)
    (hwidth : ∀ site ∈ sites, site.2.1 = 32) :
    sites.foldl (fun acc site => Layout.writeSite acc site words) mem =
      Reasoning.Theory.writeCascade mem
        (sites.map fun (off, _, key) => (off, words key)) := by
  induction sites generalizing mem with
  | nil => rfl
  | cons site rest ih =>
      rcases site with ⟨off, width, key⟩
      have hw : width = 32 := by
        simpa using hwidth (off, width, key) (by simp)
      subst width
      simp only [List.foldl_cons, List.map_cons, Reasoning.Theory.writeCascade_cons]
      rw [Layout.writeSite32]
      exact ih (Reasoning.Theory.writeWord mem off (words key)) (by
        intro site hs
        exact hwidth site (by simp [hs]))

theorem Layout.runtimeN_eq_runtime {layout : Layout} {template : ByteArray}
    {words : String → UInt256}
    (hwidth : ∀ site ∈ layout.sites, site.2.1 = 32) :
    layout.runtimeN template words = layout.runtime template words := by
  unfold Layout.runtimeN Layout.runtime Layout.writes
  exact Layout.runtimeN_eq_runtime_aux layout.sites template words hwidth

theorem Layout.inBoundsN_of_inBounds {layout : Layout} {template : ByteArray}
    (hbound : layout.inBounds template = true) :
    layout.inBoundsN template = true := by
  unfold Layout.inBoundsN
  apply List.all_eq_true.mpr
  intro site hs
  have h := List.all_eq_true.mp hbound site hs
  unfold Layout.inBounds at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  apply decide_eq_true
  omega

theorem Layout.widths32_of_inBounds {layout : Layout} {template : ByteArray}
    (hbound : layout.inBounds template = true) :
    ∀ site ∈ layout.sites, site.2.1 = 32 := by
  intro site hs
  have hsite := List.all_eq_true.mp hbound site hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsite
  exact hsite.1

theorem Layout.siteWord32 (word : UInt256) : Layout.siteWord 32 word = word := by
  rw [Layout.siteWord, Layout.siteBytes32]
  rw [Reasoning.Theory.uInt256OfByteArray_eq]
  rw [Reasoning.Theory.fromByteArrayBigEndian_toByteArray,
    Reasoning.Theory.u256_ofNat_toNat]


theorem Layout.runtime_size_of_bounds {layout : Layout} {template : ByteArray}
    {words : String → UInt256} (h : layout.inBounds template = true) :
    (layout.runtime template words).size = template.size := by
  rw [← Layout.runtimeN_eq_runtime (words := words) (Layout.widths32_of_inBounds h)]
  exact Layout.runtimeN_size_of_bounds (Layout.inBoundsN_of_inBounds h)

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
  rw [← Layout.runtimeN_eq_runtime (words := words)
    (Layout.widths32_of_inBounds hbound)]
  exact Layout.decodeUnchangedNOfLayout pc byte instr
    (Layout.inBoundsN_of_inBounds hbound) hsize64
    hbyte hinstr hopdisj hophi hargdisj harghi

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

/-- The existing PUSH32 site interface splits the list of word writes. Keeping
    this form avoids new layout reductions in already-generated large summaries. -/
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
