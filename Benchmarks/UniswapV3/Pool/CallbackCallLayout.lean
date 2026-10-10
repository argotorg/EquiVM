import Benchmarks.UniswapV3.Pool.CallbackBuildLayout

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: the padded input size and call bounds of a word-pair/bytes callback.
theorem callbackCallRange (p len : UInt256)
    (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200) :
    (UInt256.ofNat (132 + paddedSize len.toNat)).toNat = 132 + paddedSize len.toNat ∧
    UInt256.sub ((p + ⟨132⟩) + UInt256.ofNat (paddedSize len.toNat)) p =
      UInt256.ofNat (132 + paddedSize len.toNat) ∧
    p.toNat + (132 + paddedSize len.toNat) ≤ 2 ^ 200 := by
  have hpad : paddedSize len.toNat ≤ len.toNat + 31 := by unfold paddedSize; omega
  have h132 : (p + (⟨132⟩ : UInt256)).toNat = p.toNat + 132 :=
    uadd_word_ofNat_toNat p 132 (by change _ < 2 ^ 256; omega)
  have hsize : (UInt256.ofNat (132 + paddedSize len.toNat)).toNat =
      132 + paddedSize len.toNat := ulit_toNat' _ (by change _ < 2 ^ 256; omega)
  have hpn : (UInt256.ofNat (paddedSize len.toNat)).toNat = paddedSize len.toNat :=
    ulit_toNat' _ (by change _ < 2 ^ 256; omega)
  have hend : ((p + (⟨132⟩ : UInt256)) + UInt256.ofNat (paddedSize len.toNat)).toNat =
      p.toNat + 132 + paddedSize len.toNat := by
    change (UInt256.add _ _).toNat = _
    rw [addWord_toNat _ _ (by rw [h132, hpn]; change _ < 2 ^ 256; omega), h132, hpn]
  refine ⟨hsize, ?_, by omega⟩
  apply u256_inj
  rw [usub_toNat (by rw [hend]; omega), hend, hsize]
  omega

end Benchmarks.UniswapV3.Pool
