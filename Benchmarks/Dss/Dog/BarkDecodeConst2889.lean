import Benchmarks.Dss.Dog.BarkPatchPrecise

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem dogBarkVatConstDecode2889 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨2889⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32)) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? ({ val := 2889 } : UInt256).toNat =
      dogBytecode.get? ({ val := 2889 } : UInt256).toNat := by
    change code.get? 2889 = dogBytecode.get? 2889
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 2889) (stop := 2890)
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
  have hgetSome : code.get? ({ val := 2889 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.readWithPadding 2890 32), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32))
  rw [Reasoning.Theory.readWithPadding_eq_extract code 2890 (by rw [hsize]; native_decide),
    dogBarkVatPatchWord2890 hpatch,
    uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

end Benchmarks.Dss.Dog
