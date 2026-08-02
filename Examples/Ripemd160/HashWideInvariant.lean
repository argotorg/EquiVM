import Examples.Ripemd160.HashWidePrelude

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem RuntimeWordAt.runtimeLeftRoundCursor_below_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat} {read value : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hbelow : read.toNat + 32 ≤ (hashScratchPtr I + ⟨512⟩).toNat) :
    RuntimeWordAt
      (runtimeLeftRoundCursor cursor (hashScratchPtr I) group round) read value := by
  have hp := Ripemd160.runtimeRoundPreludeCursor_padded hpadded hsmall
  have hw := hword.runtimeRoundPreludeCursor_padded hpadded hsmall
  unfold runtimeLeftRoundCursor
  exact hw.runtimeRoundCursor_below_padded (lineOffset := 512) hp hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)) (by omega) hbelow

theorem RuntimeWordAt.runtimeRightRoundCursor_below_padded {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat} {read value : UInt256}
    (hword : RuntimeWordAt cursor read value)
    (hpadded : RuntimePaddedCursor I cursor n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hbelow : read.toNat + 32 ≤ (hashScratchPtr I + ⟨672⟩).toNat) :
    RuntimeWordAt
      (runtimeRightRoundCursor cursor (hashScratchPtr I) group round) read value := by
  have hp := Ripemd160.runtimeRightPreludeCursor_padded hpadded hsmall
  have hw := hword.runtimeRightPreludeCursor_padded hpadded hsmall
  unfold runtimeRightRoundCursor
  exact hw.runtimeRoundCursor_below_padded (lineOffset := 672) hp hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)) (by omega) hbelow

structure RuntimeLeftWideInvariant (I : ExecutionEnv) (cursor : RuntimeMemCursor)
    (n : Nat) (X : Fin 16 → UInt256) (s : RuntimeLineState) : Prop where
  padded : RuntimePaddedCursor I cursor n
  message : RuntimeMessageAt cursor (hashScratchPtr I) X
  line : RuntimeLineAt cursor (hashScratchPtr I + ⟨512⟩) s

theorem RuntimeLeftWideInvariant.round {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hinv : RuntimeLeftWideInvariant I cursor n X s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLeftWideInvariant I
      (runtimeLeftRoundCursor cursor (hashScratchPtr I) group round) n X
      (runtimePureLeftRound X group round s) := by
  rcases hinv with ⟨hp, hm, hl⟩
  have huint : (hashScratchPtr I).toNat + 512 < UInt256.size :=
    lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
      (hashScratchPtr_add_uint I hsmall)
  refine ⟨runtimeLeftRoundCursor_padded hp hsmall, ?_,
    runtimeLeftRoundCursor_line_padded hp hm hl hsmall⟩
  intro i
  apply (hm i).runtimeLeftRoundCursor_below_padded hp hsmall
  rw [runtimeMessageAddress_toNat i huint]
  have h512 : (hashScratchPtr I + ⟨512⟩).toNat =
      (hashScratchPtr I).toNat + 512 :=
    hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)
  rw [h512]
  omega

theorem runtimeLeftGroupCursor_wideInvariant {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n group rounds : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hinv : RuntimeLeftWideInvariant I initial n X s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLeftWideInvariant I
      (runtimeLeftGroupCursor initial (hashScratchPtr I) group rounds) n X
      (runtimePureLeftGroup X group rounds s) := by
  induction rounds with
  | zero => simpa [runtimeLeftGroupCursor, runtimePureLeftGroup] using hinv
  | succ round ih =>
      simpa [runtimeLeftGroupCursor, runtimePureLeftGroup] using ih.round hsmall

theorem runtimeLeftLineCursor_wideInvariant {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n groups : Nat}
    {X : Fin 16 → UInt256} {s : RuntimeLineState}
    (hinv : RuntimeLeftWideInvariant I initial n X s)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeLeftWideInvariant I
      (runtimeLeftLineCursor initial (hashScratchPtr I) groups) n X
      (runtimePureLeftLine X groups s) := by
  induction groups with
  | zero => simpa [runtimeLeftLineCursor, runtimePureLeftLine] using hinv
  | succ group ih =>
      have hg := runtimeLeftGroupCursor_wideInvariant
        (group := group) (rounds := 16) ih hsmall
      simpa [runtimeLeftLineCursor, runtimePureLeftLine] using hg

structure RuntimeRightWideInvariant (I : ExecutionEnv) (cursor : RuntimeMemCursor)
    (n : Nat) (X : Fin 16 → UInt256)
    (left right : RuntimeLineState) : Prop where
  padded : RuntimePaddedCursor I cursor n
  message : RuntimeMessageAt cursor (hashScratchPtr I) X
  leftLine : RuntimeLineAt cursor (hashScratchPtr I + ⟨512⟩) left
  rightLine : RuntimeLineAt cursor (hashScratchPtr I + ⟨672⟩) right

theorem RuntimeRightWideInvariant.round {I : ExecutionEnv}
    {cursor : RuntimeMemCursor} {n group round : Nat}
    {X : Fin 16 → UInt256} {left right : RuntimeLineState}
    (hinv : RuntimeRightWideInvariant I cursor n X left right)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeRightWideInvariant I
      (runtimeRightRoundCursor cursor (hashScratchPtr I) group round) n X left
      (runtimePureRightRound X group round right) := by
  rcases hinv with ⟨hp, hm, hl, hr⟩
  have huint : (hashScratchPtr I).toNat + 512 < UInt256.size :=
    lt_of_le_of_lt (Nat.add_le_add_left (by omega : 512 ≤ 895) _)
      (hashScratchPtr_add_uint I hsmall)
  have h512 : (hashScratchPtr I + ⟨512⟩).toNat =
      (hashScratchPtr I).toNat + 512 :=
    hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)
  have h672 : (hashScratchPtr I + ⟨672⟩).toNat =
      (hashScratchPtr I).toNat + 672 :=
    hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)
  have preserve {addr value : UInt256} (hw : RuntimeWordAt cursor addr value)
      (hbelow : addr.toNat + 32 ≤ (hashScratchPtr I + ⟨672⟩).toNat) :
      RuntimeWordAt
        (runtimeRightRoundCursor cursor (hashScratchPtr I) group round)
        addr value :=
    hw.runtimeRightRoundCursor_below_padded (group := group) (round := round)
      hp hsmall hbelow
  refine ⟨runtimeRightRoundCursor_padded hp hsmall, ?_, ?_,
    runtimeRightRoundCursor_line_padded hp hm hr hsmall⟩
  · intro i
    apply preserve (hm i)
    rw [runtimeMessageAddress_toNat i huint, h672]
    omega
  · have h32 : (hashScratchPtr I + ⟨512⟩ + ⟨32⟩).toNat =
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
    exact ⟨preserve hl.1 (by rw [h512, h672]; omega),
      preserve hl.2.1 (by rw [h32, h672]; omega),
      preserve hl.2.2.1 (by rw [h64, h672]; omega),
      preserve hl.2.2.2.1 (by rw [h96, h672]; omega),
      preserve hl.2.2.2.2 (by rw [h128, h672])⟩

theorem runtimeRightGroupCursor_wideInvariant {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n group rounds : Nat}
    {X : Fin 16 → UInt256} {left right : RuntimeLineState}
    (hinv : RuntimeRightWideInvariant I initial n X left right)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeRightWideInvariant I
      (runtimeRightGroupCursor initial (hashScratchPtr I) group rounds) n X left
      (runtimePureRightGroup X group rounds right) := by
  induction rounds with
  | zero => simpa [runtimeRightGroupCursor, runtimePureRightGroup] using hinv
  | succ round ih =>
      simpa [runtimeRightGroupCursor, runtimePureRightGroup] using ih.round hsmall

theorem runtimeRightLineCursor_wideInvariant {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n groups : Nat}
    {X : Fin 16 → UInt256} {left right : RuntimeLineState}
    (hinv : RuntimeRightWideInvariant I initial n X left right)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeRightWideInvariant I
      (runtimeRightLineCursor initial (hashScratchPtr I) groups) n X left
      (runtimePureRightLine X groups right) := by
  induction groups with
  | zero => simpa [runtimeRightLineCursor, runtimePureRightLine] using hinv
  | succ group ih =>
      have hg := runtimeRightGroupCursor_wideInvariant
        (group := group) (rounds := 16) ih hsmall
      simpa [runtimeRightLineCursor, runtimePureRightLine] using hg

end Ripemd160
