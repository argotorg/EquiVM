import Benchmarks.Dss.Dog.BarkDecodeConst2889

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem dogBarkVatPatchWord3170 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.extract 3170 3202 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
  let pre : List (Nat × ByteArray) := [(1405, value), (2890, value)]
  let post : List (Nat × ByteArray) := [(3965, value)]
  have hpatch' : patchRuntime dogBytecode (pre ++ (3170, value) :: post) = some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, Reasoning.Theory.wordBytes?, valueToWord,
      List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 3170 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 3170 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl
    omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch (template := dogBytecode) (out := code)
    (value := value) (pre := pre) (post := post) (offset := 3170) hsize hpost hpatch'

theorem dogBarkVatConstDecode3169 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨3169⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32)) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? ({ val := 3169 } : UInt256).toNat =
      dogBytecode.get? ({ val := 3169 } : UInt256).toNat := by
    change code.get? 3169 = dogBytecode.get? 3169
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 3169) (stop := 3170)
        (template := dogBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (by
          intro p hp
          have hm := dogPatchOffsetMem v p hp
          simp [dogPatchOffsets] at hm
          rcases hm with h | h | h | h

          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega)
        hpatch
  have hgetSome : code.get? ({ val := 3169 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.readWithPadding 3170 32), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32))
  rw [Reasoning.Theory.readWithPadding_eq_extract code 3170 (by rw [hsize]; native_decide),
    dogBarkVatPatchWord3170 hpatch,
    uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

end Benchmarks.Dss.Dog
