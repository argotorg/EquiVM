import Examples.Precompiles.Ripemd160.HashCursor

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem hashParseReadCursor_padded {I : ExecutionEnv} {c : RuntimeMemCursor}
    {n : Nat} {addr : UInt256}
    (hc : RuntimePaddedCursor I c n)
    (haddr : addr.toNat + 66 < 32 * (2 ^ 64)) :
    RuntimePaddedCursor I (hashParseReadCursor c addr) n := by
  have h1 : (addr + ⟨1⟩).toNat = addr.toNat + 1 :=
    uadd_ofNat_toNat 1 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h2 : (addr + ⟨2⟩).toNat = addr.toNat + 2 :=
    uadd_ofNat_toNat 2 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h3 : (addr + ⟨3⟩).toNat = addr.toNat + 3 :=
    uadd_ofNat_toNat 3 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  simp only [hashParseReadCursor]
  exact (((hc.afterLoad (by rw [h3]; omega)).afterLoad
    (by rw [h2]; omega)).afterLoad (by rw [h1]; omega)).afterLoad (by omega)

theorem RuntimeWordAt.afterParseReadsPadded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n : Nat} {read value addr : UInt256}
    (hword : RuntimeWordAt c read value)
    (hc : RuntimePaddedCursor I c n)
    (haddr : addr.toNat + 66 < 32 * (2 ^ 64)) :
    RuntimeWordAt (hashParseReadCursor c addr) read value := by
  have h1 : (addr + ⟨1⟩).toNat = addr.toNat + 1 :=
    uadd_ofNat_toNat 1 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h2 : (addr + ⟨2⟩).toNat = addr.toNat + 2 :=
    uadd_ofNat_toNat 2 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  have h3 : (addr + ⟨3⟩).toNat = addr.toNat + 3 :=
    uadd_ofNat_toNat 3 (by decide) (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega)
  let c1 := runtimeLoadCursor c (addr + ⟨3⟩)
  let c2 := runtimeLoadCursor c1 (addr + ⟨2⟩)
  let c3 := runtimeLoadCursor c2 (addr + ⟨1⟩)
  have hp1 := hc.afterLoad (by rw [h3]; omega)
  have hw1 := hword.afterLoadWide hc.awSmall (by rw [h3]; omega)
  have hp2 := hp1.afterLoad (by rw [h2]; omega)
  have hw2 := hw1.afterLoadWide hp1.awSmall (by rw [h2]; omega)
  have hp3 := hp2.afterLoad (by rw [h1]; omega)
  have hw3 := hw2.afterLoadWide hp2.awSmall (by rw [h1]; omega)
  have hw4 := hw3.afterLoadWide hp3.awSmall (addr := addr) (by omega)
  change RuntimeWordAt (runtimeLoadCursor c3 addr) read value
  exact hw4

theorem hashParseCursor_message_padded {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {block : Nat}
    (hinitial : RuntimePaddedCursor I initial 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64) :
    RuntimeMessageAt
      (hashParseCursor I (UInt256.ofNat block) initial 16)
      (hashScratchPtr I)
      (runtimeParsedWords I (UInt256.ofNat block) initial) := by
  have hprefix : ∀ n : Nat, n ≤ 16 →
      RuntimeMessagePrefix
        (hashParseCursor I (UInt256.ofNat block) initial n)
        (hashScratchPtr I)
        (runtimeParsedWords I (UInt256.ofNat block) initial) n := by
    intro n hn
    induction n with
    | zero => simp [RuntimeMessagePrefix]
    | succ n ih =>
        have hn16 : n < 16 := by omega
        have hprev := ih (by omega)
        let c := hashParseCursor I (UInt256.ofNat block) initial n
        let addr := hashParseAddress I (UInt256.ofNat block) (UInt256.ofNat n)
        let dst := hashParseScratchAddress I (UInt256.ofNat n)
        have hc : RuntimePaddedCursor I c n :=
          hashParseCursor_padded_of_cursor I hinitial hsmall hblock (by omega)
        have haddrNat : addr.toNat =
            (hashPadPtr I).toNat + block * 64 + n * 4 :=
          hashParseAddress_toNat I hsmall hblock hn16
        have hread : addr.toNat + 66 < 32 * (2 ^ 64) := by
          rw [haddrNat, hashPadPtr_toNat I hsmall]
          have hp := (hashPaddedLength_bounds I.calldata.size).2
          have hb : block * 64 < Model.paddedLength I.calldata.size := by omega
          unfold maxFallbackCalldataSize at hsmall
          omega
        have hdstEq : dst = runtimeMessageAddress (hashScratchPtr I) ⟨n, hn16⟩ := by
          dsimp only [dst]
          exact hashParseScratchAddress_eq I hn16
        have hdstNat : dst.toNat = (hashScratchPtr I).toNat + 32 * n := by
          rw [hdstEq, runtimeMessageAddress_toNat ⟨n, hn16⟩
              (lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
                (hashScratchPtr_add_uint I hsmall))]
        have hreads := hashParseReadCursor_padded hc hread
        intro j hj
        by_cases heq : j.val = n
        · have hjeq : j = ⟨n, hn16⟩ := Fin.ext heq
          subst j
          rw [hashParseCursor, hashParseStep_eq_store, ← hdstEq]
          simpa [runtimeParsedWords, c, addr] using
            hreads.storeWordAboveScratch
              (value := hashParseWord c addr) hsmall (by omega) hdstNat
        · have hjn : j.val < n := by omega
          have hold := hprev j hjn
          rw [hashParseCursor, hashParseStep_eq_store]
          apply (hold.afterParseReadsPadded hc hread).storeAboveScratch
            hreads hsmall (by omega) hdstNat
          rw [runtimeMessageAddress_toNat j
            (lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
              (hashScratchPtr_add_uint I hsmall)), hdstNat]
          omega
  intro i
  exact hprefix 16 (by omega) i i.isLt

end Ripemd160
