import Benchmarks.Dss.Dog.BarkCheckedAddChecks

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem dogDecodePatchedEqTemplatePrecise {v : DogImmutables} {code : ByteArray}
    {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hwinOp : decide (pc.toNat + 1 ≤ dogBytecode.size) = true)
    (hoffsetsOp : dogPatchOffsets.all
      (fun off => decide (pc.toNat + 1 ≤ off ∨ off + 32 ≤ pc.toNat)) = true)
    (hwinArg : (match dogBytecode.get? pc.toNat >>= parseInstr with
      | none => true
      | some instr =>
          decide (pc.toNat.succ + argOnNBytesOfInstr instr ≤ dogBytecode.size)) = true)
    (hoffsetsArg : (match dogBytecode.get? pc.toNat >>= parseInstr with
      | none => true
      | some instr =>
          dogPatchOffsets.all (fun off =>
        decide (pc.toNat.succ + argOnNBytesOfInstr instr ≤ off ∨
          off + 32 ≤ pc.toNat.succ))) = true) :
    decode code pc = decode dogBytecode pc := by
  have hsize := dogPatchedSize hpatch
  have hsize64 : dogBytecode.size < 2 ^ 64 := by native_decide
  have hsize64' : dogBytecode.size + 32 < 2 ^ 64 := by native_decide
  have hwinOp' : pc.toNat + 1 ≤ dogBytecode.size := of_decide_eq_true hwinOp
  have hoffsetsOp' :
      ∀ off ∈ dogPatchOffsets, pc.toNat + 1 ≤ off ∨ off + 32 ≤ pc.toNat := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hoffsetsOp
  have hget : code.get? pc.toNat = dogBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · exact Nat.lt_of_succ_le hwinOp'
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (by omega) (by omega)
        (by
          intro p hp
          rcases hoffsetsOp' p.1 (dogPatchOffsetMem v p hp) with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  exact Reasoning.Theory.decode_eq_of_get?_arg_eq code dogBytecode pc hget hsize
    (by omega)
    (by
      intro instr
      have hlen := argOnNBytesOfInstr_le_32 instr
      omega)
    (by
      intro byte instr hgetTemplate hinstr
      have hwinArgBool :
          decide (pc.toNat.succ + argOnNBytesOfInstr instr ≤ dogBytecode.size) = true := by
        simpa [hgetTemplate, hinstr] using hwinArg
      have hwinArg' := of_decide_eq_true hwinArgBool
      have hoffsetsArgBool :
          dogPatchOffsets.all (fun off =>
            decide (pc.toNat.succ + argOnNBytesOfInstr instr ≤ off ∨
              off + 32 ≤ pc.toNat.succ)) = true := by
        simpa [hgetTemplate, hinstr] using hoffsetsArg
      have hoffsetsArg' :
          ∀ off ∈ dogPatchOffsets,
            pc.toNat.succ + argOnNBytesOfInstr instr ≤ off ∨
              off + 32 ≤ pc.toNat.succ := by
        simpa only [List.all_eq_true, decide_eq_true_eq] using hoffsetsArgBool
      have hExtract := patchRuntime_extract_eq (start := pc.toNat.succ)
        (stop := pc.toNat.succ + argOnNBytesOfInstr instr)
        (by omega) hwinArg'
        (by
          intro p hp
          rcases hoffsetsArg' p.1 (dogPatchOffsetMem v p hp) with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr (by omega))
        hpatch
      have hExtract' : code.extract' (pc.toNat + 1)
          (pc.toNat + 1 + argOnNBytesOfInstr instr) =
          dogBytecode.extract' (pc.toNat + 1)
            (pc.toNat + 1 + argOnNBytesOfInstr instr) := by
        unfold ByteArray.extract'
        have hb1 : decide (pc.toNat + 1 < 2 ^ 64) = true := by
          apply decide_eq_true_eq.mpr
          omega
        have hb2 : decide (pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64) = true := by
          apply decide_eq_true_eq.mpr
          omega
        have hb : (decide (pc.toNat + 1 < 2 ^ 64) &&
            decide (pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64)) = true := by
          simp only [Bool.and_eq_true]
          exact ⟨hb1, hb2⟩
        simp only [hb, if_true]
        exact hExtract
      exact hExtract')

theorem dogBarkVatPatchWord2890 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.extract 2890 2922 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
  let pre : List (Nat × ByteArray) := [(1405, value)]
  let post : List (Nat × ByteArray) := [(3170, value), (3965, value)]
  have hpatch' : patchRuntime dogBytecode (pre ++ (2890, value) :: post) = some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, Reasoning.Theory.wordBytes?, valueToWord,
      List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 2890 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 2890 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl <;> omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch (template := dogBytecode) (out := code)
    (value := value) (pre := pre) (post := post) (offset := 2890) hsize hpost hpatch'

end Benchmarks.Dss.Dog
