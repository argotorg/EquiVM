import Examples.Precompiles.Ripemd160.ParserWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem hashParseCursor_padded_next (I : ExecutionEnv)
    {c : RuntimeMemCursor} {block n : Nat}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hn : n < 16) :
    RuntimePaddedCursor I
      (hashParseStep I (UInt256.ofNat block) (UInt256.ofNat n) c) (n + 1) := by
  have hread :
      (hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat n)).toNat +
          66 < 32 * (2 ^ 64) := by
    rw [hashParseAddress_toNat I hsmall hblock hn,
      hashPadPtr_toNat I hsmall]
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    have hb : block * 64 < Model.paddedLength I.calldata.size := by omega
    unfold maxFallbackCalldataSize at hsmall
    omega
  have hwrite :
      (hashParseScratchAddress I (UInt256.ofNat n)).toNat + 63 <
          32 * (2 ^ 64) := by
    have hdst := hashParseScratchAddress_eq I hn
    have huint : (hashScratchPtr I).toNat + 512 < UInt256.size := by
      change (hashNewFreePtr I).toNat + 512 < UInt256.size
      rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall,
        show UInt256.size = 2 ^ 256 from by decide]
      have hp := (hashPaddedLength_bounds I.calldata.size).2
      unfold maxFallbackCalldataSize at hsmall
      omega
    rw [hdst, runtimeMessageAddress_toNat (Fin.mk n hn) huint]
    change (hashNewFreePtr I).toNat + 32 * n + 63 < 32 * (2 ^ 64)
    rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall]
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    unfold maxFallbackCalldataSize at hsmall
    omega
  exact hc.step hsmall hn hread hwrite

theorem hashParseCursor_padded_of_cursor (I : ExecutionEnv)
    {initial : RuntimeMemCursor} {block n : Nat}
    (hinitial : RuntimePaddedCursor I initial 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hn : n ≤ 16) :
    RuntimePaddedCursor I
      (hashParseCursor I (UInt256.ofNat block) initial n) n := by
  induction n with
  | zero =>
      change RuntimePaddedCursor I initial 0
      exact hinitial
  | succ n ih =>
      have hn16 : n < 16 := by omega
      have hprev : RuntimePaddedCursor I
          (hashParseCursor I (UInt256.ofNat block) initial n) n :=
        ih (by omega)
      change RuntimePaddedCursor I
        (hashParseStep I (UInt256.ofNat block) (UInt256.ofNat n)
          (hashParseCursor I (UInt256.ofNat block) initial n))
        (n + 1)
      exact hashParseCursor_padded_next I hprev hsmall hblock hn16

theorem hashParseCursor_padded (I : ExecutionEnv) {block n : Nat}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (hn : n ≤ 16) :
    RuntimePaddedCursor I
      (hashParseCursor I (UInt256.ofNat block)
        { mem := hashScratchMem I, aw := hashPaddedMessageAw I } n) n :=
  hashParseCursor_padded_of_cursor I (RuntimePaddedCursor.initial I hsmall)
    hsmall hblock hn

theorem runtimeParsedWords_model (I : ExecutionEnv) {block : Nat}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (i : Fin 16) :
    runtimeParsedWords I (UInt256.ofNat block)
        { mem := hashScratchMem I, aw := hashPaddedMessageAw I } i =
      UInt256.ofNat (Model.blockWord I.calldata block i.val) := by
  unfold runtimeParsedWords
  exact hashParseWord_model
    (hashParseCursor_padded I hsmall hblock i.isLt.le) hsmall hblock i.isLt

theorem runtimeParsedWords_model_of_cursor (I : ExecutionEnv)
    {cursor : RuntimeMemCursor} {block : Nat}
    (hcursor : RuntimePaddedCursor I cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (i : Fin 16) :
    runtimeParsedWords I (UInt256.ofNat block) cursor i =
      UInt256.ofNat (Model.blockWord I.calldata block i.val) := by
  unfold runtimeParsedWords
  exact hashParseWord_model
    (hashParseCursor_padded_of_cursor I hcursor hsmall hblock i.isLt.le)
    hsmall hblock i.isLt

end Ripemd160
