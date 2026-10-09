import Benchmarks.Morpho.MorphoBlue.MarketParamsCommon
import Benchmarks.Morpho.MorphoBlue.ErrorRoutines
import Benchmarks.Morpho.MorphoBlue.WordBufferCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: word-load forms of the byte-window preservation lemmas.
theorem memLoad_writeWord_disjoint (mem : ByteArray) (off : Nat) (word addr : UInt256)
    (hgap : off - mem.size < USize.size)
    (hread : addr.toNat + 32 ≤ mem.size)
    (hdisj : addr.toNat + 32 ≤ off ∨ off + 32 ≤ addr.toNat) :
    memLoad addr (writeWord mem off word) = memLoad addr mem := by
  have hsize := writeWord_size mem off word hgap
  have hbytes := writeWord_read_preserved mem off addr.toNat word hgap
    (hdisj.elim (fun h ↦ Or.inl ⟨h, hread⟩) (fun h ↦ Or.inr ⟨h, hread⟩))
  simp only [memLoad, if_neg (show ¬ addr.toNat ≥ (writeWord mem off word).size by omega),
    if_neg (show ¬ addr.toNat ≥ mem.size by omega), hbytes]

theorem memLoad_writeWord_self (mem : ByteArray) (word addr : UInt256)
    (hgap : addr.toNat - mem.size < USize.size) :
    memLoad addr (writeWord mem addr.toNat word) = word := by
  have hsize := writeWord_size mem addr.toNat word hgap
  apply mloadWordValue_of_readWithPadding (by omega)
  exact writeWord_read_back mem addr.toNat word hgap

theorem memLoad_writeWord_self_of_offset (mem : ByteArray) (off : Nat) (word addr : UInt256)
    (hgap : off - mem.size < USize.size) (hoff : off = addr.toNat) :
    memLoad addr (writeWord mem off word) = word := by
  subst off
  exact memLoad_writeWord_self mem word addr hgap

def MarketParamsWords.word (p : MarketParamsWords) (i : Fin 5) : UInt256 :=
  match i.val with
  | 0 => p.loanToken
  | 1 => p.collateralToken
  | 2 => p.oracle
  | 3 => p.irm
  | _ => p.lltv

def MarketParamsWords.InMemory (p : MarketParamsWords) (ptr : UInt256) (mem : ByteArray) : Prop :=
  ∀ i : Fin 5, memLoad (ptr + UInt256.ofNat (32 * i.val)) mem = p.word i

theorem marketParamsMem_inMemory (p : MarketParamsWords) (ptr : UInt256) (mem : ByteArray)
    (hfit : ptr.toNat + 160 < UInt256.size)
    (hgap : ptr.toNat + 160 - mem.size < USize.size) :
    p.InMemory ptr (marketParamsMem p ptr mem) := by
  have hadd (n : Nat) (hn : n ≤ 160) : (ptr + UInt256.ofNat n).toNat = ptr.toNat + n :=
    uadd_word_ofNat_toNat ptr n (by omega)
  have hg (n : Nat) (hn : n ≤ 160) : ptr.toNat + n - mem.size < USize.size := by omega
  let m1 := writeWord mem ptr.toNat p.loanToken
  let m2 := writeWord m1 (ptr + UInt256.ofNat 32).toNat p.collateralToken
  let m3 := writeWord m2 (ptr + UInt256.ofNat 64).toNat p.oracle
  let m4 := writeWord m3 (ptr + UInt256.ofNat 96).toNat p.irm
  have hs1 : m1.size = max mem.size (ptr.toNat + 32) :=
    writeWord_size _ _ _ (by omega)
  have hs2 : m2.size = max m1.size ((ptr + UInt256.ofNat 32).toNat + 32) :=
    writeWord_size _ _ _ (by rw [hs1, hadd 32 (by omega)]; omega)
  have hs3 : m3.size = max m2.size ((ptr + UInt256.ofNat 64).toNat + 32) :=
    writeWord_size _ _ _ (by rw [hs2, hs1, hadd 32 (by omega), hadd 64 (by omega)]; omega)
  have hs4 : m4.size = max m3.size ((ptr + UInt256.ofNat 96).toNat + 32) :=
    writeWord_size _ _ _ (by
      rw [hs3, hs2, hs1, hadd 32 (by omega), hadd 64 (by omega), hadd 96 (by omega)]
      omega)
  dsimp only [m4, m3, m2, m1] at hs4 hs3 hs2 hs1
  have h32 := hadd 32 (by omega)
  have h64 := hadd 64 (by omega)
  have h96 := hadd 96 (by omega)
  have h128 := hadd 128 (by omega)
  intro i
  fin_cases i
  all_goals simp only [MarketParamsWords.word, marketParamsMem, writeCascade,
    Nat.reduceMul, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
  all_goals simp (disch := omega) only
    [memLoad_writeWord_self_of_offset, memLoad_writeWord_disjoint]

theorem marketParamsMem_size (p : MarketParamsWords) (ptr : UInt256) (mem : ByteArray)
    (hfit : ptr.toNat + 160 < UInt256.size)
    (hgap : ptr.toNat + 160 - mem.size < USize.size) :
    (marketParamsMem p ptr mem).size = max mem.size (ptr.toNat + 160) := by
  rw [marketParamsMem_asWordWrites p ptr mem hfit, writeCascade_size]
  · simp only [MarketParamsWords.toList, returnWordWrites, writeCascadeSize, Nat.add_assoc]
    omega
  · simp only [MarketParamsWords.toList, returnWordWrites, WriteGapsOk, Nat.add_assoc,
      and_true]
    omega

theorem MarketParamsWords.InMemory.writeWord {p : MarketParamsWords} {ptr : UInt256}
    {mem : ByteArray} (h : p.InMemory ptr mem) (off : Nat) (word : UInt256)
    (hfit : ptr.toNat + 160 < UInt256.size) (hsize : ptr.toNat + 160 ≤ mem.size)
    (hgap : off - mem.size < USize.size)
    (hdisj : ptr.toNat + 160 ≤ off ∨ off + 32 ≤ ptr.toNat) :
    p.InMemory ptr (Reasoning.Theory.writeWord mem off word) := by
  intro i
  have hi := i.isLt
  have hadd := uadd_word_ofNat_toNat ptr (32 * i.val) (by omega)
  rw [memLoad_writeWord_disjoint mem off word (ptr + UInt256.ofNat (32 * i.val))
    hgap (by omega) (by omega)]
  exact h i

theorem MarketParamsWords.InMemory.twoWordHashMem {p : MarketParamsWords} {ptr : UInt256}
    {mem : ByteArray} (h : p.InMemory ptr mem) (key slot : UInt256)
    (hfit : ptr.toNat + 160 < UInt256.size) (hsize : ptr.toNat + 160 ≤ mem.size)
    (hlo : 64 ≤ ptr.toNat) : p.InMemory ptr (Reasoning.Theory.twoWordHashMem key slot mem) := by
  intro i
  have hi := i.isLt
  have hadd := uadd_word_ofNat_toNat ptr (32 * i.val) (by omega)
  rw [twoWordHashMem_memLoad_above64 _ _ _ (by omega) (by omega)]
  exact h i

-- LIBRARY CANDIDATE: a contiguous word buffer preserves earlier, initialized word loads.
theorem memLoad_writeReturnWords_below (ws : List UInt256) (mem : ByteArray)
    (off : Nat) (addr : UInt256) (hgap : off - mem.size < USize.size)
    (hin : addr.toNat + 32 ≤ mem.size) (hbelow : addr.toNat + 32 ≤ off) :
    memLoad addr (writeCascade mem (returnWordWrites off ws)) = memLoad addr mem := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    have hs := writeReturnWords_size (w :: ws) mem off (by simp) hgap
    have hr := writeCascade_read_preserved mem (returnWordWrites off (w :: ws)) addr.toNat
      (returnWordWrites_preserveBelow _ _ _ _ _ hgap hin hbelow)
    simp only [memLoad, if_neg (show ¬ addr.toNat ≥ mem.size by omega),
      if_neg (show ¬ addr.toNat ≥ (writeCascade mem (returnWordWrites off (w :: ws))).size by omega), hr]

theorem MarketParamsWords.InMemory.copyAfter {p : MarketParamsWords} {src dest : UInt256}
    {mem : ByteArray} (h : p.InMemory src mem) (q : MarketParamsWords)
    (hsfit : src.toNat + 160 < UInt256.size) (hdfit : dest.toNat + 160 < UInt256.size)
    (hsize : src.toNat + 160 ≤ mem.size) (hsep : src.toNat + 160 ≤ dest.toNat)
    (hgap : dest.toNat - mem.size < USize.size) :
    p.InMemory src (marketParamsMem q dest mem) := by
  rw [marketParamsMem_asWordWrites q dest mem hdfit]
  intro i
  have hi := i.isLt
  have hadd := uadd_word_ofNat_toNat src (32 * i.val) (by omega)
  rw [memLoad_writeReturnWords_below _ _ _ _ hgap (by omega) (by omega)]
  exact h i

-- GENERALIZES Reasoning.Theory.wordAt32TwoWordHashMem_read0_64 to arbitrary initialized memory.
theorem twoWordHashMem_replaceSlot_hash (key oldSlot newSlot : UInt256) (mem : ByteArray)
    (hsize : 64 ≤ mem.size) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (writeWord (twoWordHashMem key oldSlot mem) 32 newSlot) = solcMappingSlot newSlot key := by
  have hs : (twoWordHashMem key oldSlot mem).size = mem.size :=
    twoWordHashMem_size_of_ge_64' _ _ hsize
  have hg : 32 - (twoWordHashMem key oldSlot mem).size < USize.size := by
    rw [hs]; have hpos := USize.size_pos; omega
  have hs' := writeWord_size (twoWordHashMem key oldSlot mem) 32 newSlot hg
  have hr : (writeWord (twoWordHashMem key oldSlot mem) 32 newSlot).readWithPadding 0 64 =
      key.toByteArray ++ newSlot.toByteArray := by
    rw [byteArray_readWithPadding_split _ 0 32 32 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [hs', hs]; omega)]
    rw [writeWord_read_preserved _ 32 0 newSlot hg (Or.inl ⟨by decide, by rw [hs]; omega⟩),
      writeWord_read_back _ _ _ hg, twoWordHashMem_read0_of_ge _ _ hsize]
  have hh := twoWordHashMem_solcMappingSlot_any newSlot key mem
  change UInt256.ofNat (fromByteArrayBigEndian (KEC
    ((writeWord (twoWordHashMem key oldSlot mem) 32 newSlot).readWithPadding 0 64))) = _
  rw [hr]
  simpa only [keccakWord, show (UInt256.ofNat 0).toNat = 0 from rfl,
    show (UInt256.ofNat 64).toNat = 64 from rfl, twoWordHashMem_read0_64_of_ge key newSlot hsize] using hh

end Benchmarks.Morpho.MorphoBlue
