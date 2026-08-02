import Examples.Ripemd160.HashWideInvariant

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem RuntimeMessageAt.initLeftWide {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {X : Fin 16 → UInt256}
    {h : RuntimeChain}
    (hmessage : RuntimeMessageAt cursor (hashScratchPtr I) X)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLeftWideInvariant I
      (runtimeInitLineCursor cursor (hashScratchPtr I + ⟨512⟩)
        (runtimeLineOfChain h)) n X (runtimeLineOfChain h) := by
  have hbase : (hashScratchPtr I + ⟨512⟩).toNat =
      (hashScratchPtr I).toNat + 512 :=
    hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)
  have huint : (hashScratchPtr I).toNat + 512 < UInt256.size :=
    lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
      (hashScratchPtr_add_uint I hsmall)
  refine ⟨runtimeInitLineCursor_padded (baseOffset := 512) hpadded hsmall hbase (by omega),
    ?_, runtimeInitLineCursor_line_padded (baseOffset := 512)
      hpadded hsmall hbase (by omega)⟩
  intro i
  apply (hmessage i).runtimeInitLineCursor_below_padded
    (baseOffset := 512) hpadded hsmall hbase (by omega)
  rw [runtimeMessageAddress_toNat i huint, hbase]
  omega

theorem RuntimeLeftWideInvariant.initRightWide {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {X : Fin 16 → UInt256}
    {left : RuntimeLineState} {h : RuntimeChain}
    (hinv : RuntimeLeftWideInvariant I cursor n X left)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeRightWideInvariant I
      (runtimeInitLineCursor cursor (hashScratchPtr I + ⟨672⟩)
        (runtimeLineOfChain h)) n X left (runtimeLineOfChain h) := by
  rcases hinv with ⟨hp, hm, hl⟩
  have hbase : (hashScratchPtr I + ⟨672⟩).toNat =
      (hashScratchPtr I).toNat + 672 :=
    hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)
  have huint : (hashScratchPtr I).toNat + 512 < UInt256.size :=
    lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
      (hashScratchPtr_add_uint I hsmall)
  have preserve {addr value : UInt256} (hw : RuntimeWordAt cursor addr value)
      (hbelow : addr.toNat + 32 ≤ (hashScratchPtr I + ⟨672⟩).toNat) :
      RuntimeWordAt
        (runtimeInitLineCursor cursor (hashScratchPtr I + ⟨672⟩)
          (runtimeLineOfChain h)) addr value :=
    hw.runtimeInitLineCursor_below_padded (baseOffset := 672)
      hp hsmall hbase (by omega) hbelow
  have h512 : (hashScratchPtr I + ⟨512⟩).toNat =
      (hashScratchPtr I).toNat + 512 :=
    hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)
  have h32 : (hashScratchPtr I + ⟨512⟩ + ⟨32⟩).toNat =
      (hashScratchPtr I).toNat + 544 := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨32⟩ = ⟨544⟩ by native_decide] using
      hashScratchAdd_toNat I hsmall (by omega : 544 ≤ 895)
  have h64 : (hashScratchPtr I + ⟨512⟩ + ⟨64⟩).toNat =
      (hashScratchPtr I).toNat + 576 := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨64⟩ = ⟨576⟩ by native_decide] using
      hashScratchAdd_toNat I hsmall (by omega : 576 ≤ 895)
  have h96 : (hashScratchPtr I + ⟨512⟩ + ⟨96⟩).toNat =
      (hashScratchPtr I).toNat + 608 := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨96⟩ = ⟨608⟩ by native_decide] using
      hashScratchAdd_toNat I hsmall (by omega : 608 ≤ 895)
  have h128 : (hashScratchPtr I + ⟨512⟩ + ⟨128⟩).toNat =
      (hashScratchPtr I).toNat + 640 := by
    simpa [u256_add_assoc,
      show (⟨512⟩ : UInt256) + ⟨128⟩ = ⟨640⟩ by native_decide] using
      hashScratchAdd_toNat I hsmall (by omega : 640 ≤ 895)
  refine ⟨runtimeInitLineCursor_padded (baseOffset := 672) hp hsmall hbase (by omega),
    ?_, ?_, runtimeInitLineCursor_line_padded (baseOffset := 672)
      hp hsmall hbase (by omega)⟩
  · intro i
    apply preserve (hm i)
    rw [runtimeMessageAddress_toNat i huint, hbase]
    omega
  · exact ⟨preserve hl.1 (by rw [h512, hbase]; omega),
      preserve hl.2.1 (by rw [h32, hbase]; omega),
      preserve hl.2.2.1 (by rw [h64, hbase]; omega),
      preserve hl.2.2.2.1 (by rw [h96, hbase]; omega),
      preserve hl.2.2.2.2 (by rw [h128, hbase])⟩

theorem RuntimeMessageAt.hashLeftInitWide {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {X : Fin 16 → UInt256}
    {h : RuntimeChain}
    (hmessage : RuntimeMessageAt cursor (hashScratchPtr I) X)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLeftWideInvariant I (hashLeftInitCursor I h cursor) n X
      (runtimeLineOfChain h) := by
  rw [hashLeftInitCursor_eq]
  exact hmessage.initLeftWide hpadded hsmall

theorem RuntimeLeftWideInvariant.hashRightInitWide {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n : Nat} {X : Fin 16 → UInt256}
    {left : RuntimeLineState} {h : RuntimeChain}
    (hinv : RuntimeLeftWideInvariant I cursor n X left)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeRightWideInvariant I (hashRightInitCursor I h cursor) n X left
      (runtimeLineOfChain h) := by
  rw [hashRightInitCursor_eq]
  exact hinv.initRightWide hsmall

end Ripemd160
