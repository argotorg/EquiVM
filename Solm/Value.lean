import Std.Data.HashMap
import Solm.Value.Basic
import Solm.Value.DecEq

namespace Solm

def valueToWord : Value -> Option EVM.Word
  | .int i => pure $ EVM.wordOfInt i
  | .unit => .none
  | .bool b => b.toUInt256
  | .address a => pure $ .ofNat $ a.toNat
  | .array _ => .none
  | .tuple _ => .none
  | .struct _ _ => .none
  | .bytes _ => .none
  | .fixedBytes n bs =>
      if bs.length = n.val + 1 then
        some (.ofNat (Ethereum.fromBytesBigEndian bs))
      else
        none
  | .storageRef _ _ => .none

/-- Normalize an integer to the semantic value of a Solidity integer type.

Solm keeps local integers as unbounded `Int` values, while explicit Solidity
casts retain only the target width. Unsigned targets denote the nonnegative
residue; signed targets interpret that residue as two's complement. -/
def normalizeInt : ABI.IntType → Int → Int
  | .uint bits, i => i % Int.ofNat (EVM.twoPow bits.val)
  | .sint bits, i =>
      let modulus := Int.ofNat (EVM.twoPow bits.val)
      let residue := i % modulus
      if residue < Int.ofNat (EVM.twoPow (bits.val - 1)) then residue else residue - modulus

theorem normalizeInt_uint_eq_self (bits : ABI.BitWidth) (i : Int)
    (hnonneg : 0 ≤ i) (hbound : i < Int.ofNat (EVM.twoPow bits.val)) :
    normalizeInt (.uint bits) i = i := by
  exact Int.emod_eq_of_lt hnonneg hbound

theorem normalizeInt_uint256_word (w : EVM.Word) :
    normalizeInt (.uint ⟨256, by decide⟩) (Int.ofNat w.toNat) = Int.ofNat w.toNat := by
  apply normalizeInt_uint_eq_self
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    rw [show EVM.twoPow 256 = Ethereum.UInt256.size by rfl]
    exact w.val.isLt

theorem normalizeInt_sint256_word (w : EVM.Word) :
    normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat w.toNat) =
      if w.toNat < EVM.twoPow 255 then Int.ofNat w.toNat
      else Int.ofNat w.toNat - Int.ofNat EVM.wordModulus := by
  simp only [normalizeInt]
  rw [Int.emod_eq_of_lt]
  · rw [show 256 - 1 = 255 by omega]
    split
    · rename_i hsign
      rw [if_pos (Int.ofNat_lt.mp hsign)]
    · rename_i hsign
      rw [if_neg (fun h => hsign (Int.ofNat_lt.mpr h))]
      rw [show EVM.wordModulus = EVM.twoPow 256 by rfl]
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    rw [show EVM.twoPow 256 = Ethereum.UInt256.size by rfl]
    exact w.val.isLt

theorem normalizeInt_sint256_word_eq_signed (w : EVM.Word) :
    normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat w.toNat) = EVM.signed w := by
  rw [normalizeInt_sint256_word]
  simp only [EVM.signed, EVM.signBit, Ethereum.UInt256.toNat]
  rfl

theorem normalizeInt_sint256_bounds (i : Int) :
    -Int.ofNat (EVM.twoPow 255) ≤ normalizeInt (.sint ⟨256, by decide⟩) i ∧
      normalizeInt (.sint ⟨256, by decide⟩) i < Int.ofNat (EVM.twoPow 255) := by
  let modulus := Int.ofNat (EVM.twoPow 256)
  let half := Int.ofNat (EVM.twoPow 255)
  have hmodulusPos : 0 < modulus := by norm_num [modulus, EVM.twoPow]
  have hresidueNonneg : 0 ≤ i % modulus := Int.emod_nonneg i (ne_of_gt hmodulusPos)
  have hresidueLt : i % modulus < modulus := Int.emod_lt_of_pos i hmodulusPos
  have hmodulus : modulus = 2 * half := by
    dsimp [modulus, half, EVM.twoPow]
  change -half ≤ (if i % modulus < half then i % modulus else i % modulus - modulus) ∧
    (if i % modulus < half then i % modulus else i % modulus - modulus) < half
  split <;> omega

theorem normalizeInt_sint256_eq_self (i : Int)
    (hlo : -Int.ofNat (EVM.twoPow 255) ≤ i)
    (hhi : i < Int.ofNat (EVM.twoPow 255)) :
    normalizeInt (.sint ⟨256, by decide⟩) i = i := by
  let modulus := Int.ofNat (EVM.twoPow 256)
  let half := Int.ofNat (EVM.twoPow 255)
  have hhalfPos : 0 < half := by norm_num [half, EVM.twoPow]
  have hmodulus : modulus = 2 * half := by
    dsimp [modulus, half, EVM.twoPow]
  change (if i % modulus < half then i % modulus else i % modulus - modulus) = i
  by_cases hnonneg : 0 ≤ i
  · have hlt : i < modulus := by omega
    rw [Int.emod_eq_of_lt hnonneg hlt, if_pos (by simpa [half] using hhi)]
  · have hsumNonneg : 0 ≤ i + modulus := by
      have := hlo
      change -half ≤ i at this
      omega
    have hsumLt : i + modulus < modulus := by omega
    have hmod : i % modulus = i + modulus := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt hsumNonneg hsumLt]
    rw [hmod, if_neg (by
      intro hlt
      have := not_le.mpr hlt
      omega)]
    omega

theorem normalizeInt_sint256_word_of_lt (w : EVM.Word)
    (hbound : w.toNat < EVM.twoPow 255) :
    normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat w.toNat) = Int.ofNat w.toNat := by
  rw [normalizeInt_sint256_word, if_pos hbound]

/-- Negating a nonnegative word in the signed-256 range, including the signed
minimum boundary, agrees with EVM two's-complement negation. -/
theorem normalizeInt_sint256_neg_word_of_le (w : EVM.Word)
    (hbound : w.toNat ≤ EVM.twoPow 255) :
    normalizeInt (.sint ⟨256, by decide⟩)
        (-normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat w.toNat)) =
      -Int.ofNat w.toNat := by
  let n := Int.ofNat w.toNat
  let half := Int.ofNat (EVM.twoPow 255)
  let modulus := Int.ofNat (EVM.twoPow 256)
  have hnnonneg : 0 ≤ n := Int.natCast_nonneg _
  have hnltmod : n < modulus := by
    apply Int.ofNat_lt.mpr
    rw [show EVM.twoPow 256 = Ethereum.UInt256.size by rfl]
    exact w.val.isLt
  have hnle : n ≤ half := Int.ofNat_le.mpr hbound
  have hmodulusNat : EVM.twoPow 256 = 2 * EVM.twoPow 255 := by
    simp only [EVM.twoPow]
    rw [show 256 = 255 + 1 by omega, pow_succ]
    omega
  have hmodulus : modulus = 2 * half := by
    dsimp [modulus, half]
    exact_mod_cast hmodulusNat
  by_cases hnlt : n < half
  · have hinner : normalizeInt (.sint ⟨256, by decide⟩) n = n := by
      simp only [normalizeInt]
      rw [Int.emod_eq_of_lt hnnonneg hnltmod]
      rw [if_pos hnlt]
    change normalizeInt (.sint ⟨256, by decide⟩)
        (-normalizeInt (.sint ⟨256, by decide⟩) n) = -n
    rw [hinner]
    by_cases hnzero : n = 0
    · rw [hnzero]
      simp only [neg_zero, normalizeInt, Int.zero_emod]
      rw [if_pos]
      exact Int.natCast_pos.mpr (by simp [EVM.twoPow])
    · simp only [normalizeInt]
      rw [show 256 - 1 = 255 by omega]
      rw [Int.emod_eq_add_self_emod]
      rw [Int.emod_eq_of_lt]
      · rw [if_neg] <;> omega
      · omega
      · omega
  · have hne : n = half := by omega
    have hinner : normalizeInt (.sint ⟨256, by decide⟩) n = -half := by
      simp only [normalizeInt]
      rw [Int.emod_eq_of_lt hnnonneg hnltmod]
      rw [if_neg hnlt]
      omega
    change normalizeInt (.sint ⟨256, by decide⟩)
        (-normalizeInt (.sint ⟨256, by decide⟩) n) = -n
    rw [hinner]
    have hneg : - -half = half := by omega
    rw [hneg]
    simp only [normalizeInt]
    rw [show 256 - 1 = 255 by omega]
    rw [Int.emod_eq_of_lt]
    · rw [if_neg] <;> omega
    · omega
    · omega

#guard normalizeInt (ABI.IntType.uint ⟨8, by decide⟩) 511 = 255
#guard normalizeInt (ABI.IntType.uint ⟨8, by decide⟩) (-1) = 255
#guard normalizeInt (ABI.IntType.sint ⟨8, by decide⟩) 255 = -1
#guard normalizeInt (ABI.IntType.sint ⟨8, by decide⟩) 128 = -128
#guard normalizeInt (ABI.IntType.sint ⟨256, by decide⟩) (-1) = -1

def keyValueToWord : KeyValue -> EVM.Word
  | .int i => EVM.wordOfInt i
  | .bool b => b.toUInt256
  | .address a =>
    { val := (@Fin.castLE Ethereum.AccountAddress.size
                          Ethereum.UInt256.size
                            (by unfold Ethereum.AccountAddress.size Ethereum.UInt256.size; simp) a : Fin Ethereum.UInt256.size) }
  | .fixedBytes n bs =>
      -- `bytesN` keys are LEFT-aligned in the hashed word: `value * 2^(8·(31-n))` (solc 0.6.12 &
      -- 0.8.35 mask the key to its high bytes before `keccak256`).  `bytes32` (`n=31`) is `×1`.
      if bs.length = n.val + 1 then
        EVM.Word.ofNat (Ethereum.fromBytesBigEndian bs * 2 ^ (8 * (31 - n.val)))
      else
        -- Unreachable on the eval path (`valueToKey?` rejects length-mismatched keys); total fallback.
        ⟨0⟩
#guard keyValueToWord (.fixedBytes ⟨3, by decide⟩ [0xDE, 0xAD, 0xBE, 0xEF])
  = EVM.Word.ofNat (0xDEADBEEF * 2 ^ 224)
#guard keyValueToWord (.fixedBytes ⟨31, by decide⟩ (List.replicate 31 0 ++ [0x2A]))
  = EVM.Word.ofNat 0x2A

def wordToElem (t : ABI.ElemType) (w : EVM.Word) : Value :=
  match t with
  | .int intType => .int (normalizeInt intType (Int.ofNat w.toNat))
  | .bool => if w.val == 0 then .bool false else .bool true
  | .address => .address (.ofNat $ w.toNat)
  | .bytes n => .fixedBytes n (w.toBytesBE.drop (32 - (n.val + 1)))
  -- TODO: implement
  | .function => panic! "TODO: wordToElem: implement function"
  | .fixed _ => panic! "TODO: wordToElem: implement fixed"

-- Packed integer loads normalize at the declared width; at full width the signed arm agrees with
-- `EVM.signed` (here: `2^255 ↦ -2^255`).
#guard wordToElem (.int (.sint ⟨24, by decide⟩)) (EVM.Word.ofNat 0xFFFFFF) = .int (-1)
#guard wordToElem (.int (.sint ⟨24, by decide⟩)) (EVM.Word.ofNat 0x7FFFFF) = .int 8388607
#guard wordToElem (.int (.uint ⟨24, by decide⟩)) (EVM.Word.ofNat 0xFFFFFF) = .int 16777215
#guard wordToElem (.int (.uint ⟨8, by decide⟩)) (EVM.Word.ofNat 511) = .int 255
#guard wordToElem (.int (.sint ⟨256, by decide⟩)) (EVM.Word.ofNat (EVM.twoPow 255))
  = .int (EVM.signed (EVM.Word.ofNat (EVM.twoPow 255)))
#guard wordToElem (.int (.sint ⟨256, by decide⟩)) (EVM.Word.ofNat (EVM.twoPow 255))
  = .int (-(EVM.twoPow 255 : Int))

abbrev Store := Std.HashMap Ident Value
