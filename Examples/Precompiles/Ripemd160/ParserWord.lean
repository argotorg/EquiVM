import Examples.Precompiles.Ripemd160.ParserArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Ripemd160

theorem hashParseWord_model {I : ExecutionEnv} {c : RuntimeMemCursor}
    {n block i : Nat} (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hi : i < 16) :
    hashParseWord c
        (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat i)) =
      UInt256.ofNat (Model.blockWord I.calldata block i) := by
  let p := block * 64 + i * 4
  obtain ⟨hb3, hb2, hb1, hb0⟩ := hashParseWord_bytes hc hsmall hblock hi
  unfold hashParseWord
  rw [hb3, hb2, hb1, hb0]
  rw [show (⟨24⟩ : UInt256) = UInt256.ofNat 24 from rfl,
    show (⟨16⟩ : UInt256) = UInt256.ofNat 16 from rfl,
    show (⟨8⟩ : UInt256) = UInt256.ofNat 8 from rfl]
  rw [assembleWordOfBytes
    (Model.paddedByte_lt I.calldata p)
    (Model.paddedByte_lt I.calldata (p + 1))
    (Model.paddedByte_lt I.calldata (p + 2))
    (Model.paddedByte_lt I.calldata (p + 3))]
  unfold Model.blockWord
  dsimp only [p]


end Ripemd160
