import Examples.Precompiles.Modexp.BaseRange

/-!
# Exact base-zero/base-one arbitrary-width path

This proves the second trusted-parser fast path.  Once the exponent is known to be nonzero, the
runtime recognizes bases zero and one without entering either multi-precision exponentiation
backend.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def wideBaseSmallGas (I : ExecutionEnv) (baseSize : Nat) : Nat :=
  if baseSize = 0 then 82
  else if baseSize = 1 then 113
  else 163 + cdRangeGas I 96 (95 + baseSize)

def wideBaseGtOneGas (I : ExecutionEnv) (baseSize : Nat) : Nat :=
  if Model.bytesToNatPadded I.calldata (95 + baseSize) 1 < 2 then
    163 + cdRangeGas I 96 (95 + baseSize)
  else 74

private theorem baseSmallDecodes :
    [decode runtimeBytecode ⟨89⟩, decode runtimeBytecode ⟨90⟩,
      decode runtimeBytecode ⟨91⟩, decode runtimeBytecode ⟨92⟩,
      decode runtimeBytecode ⟨95⟩, decode runtimeBytecode ⟨96⟩,
      decode runtimeBytecode ⟨97⟩, decode runtimeBytecode ⟨99⟩,
      decode runtimeBytecode ⟨100⟩, decode runtimeBytecode ⟨101⟩,
      decode runtimeBytecode ⟨104⟩, decode runtimeBytecode ⟨181⟩,
      decode runtimeBytecode ⟨182⟩, decode runtimeBytecode ⟨183⟩,
      decode runtimeBytecode ⟨185⟩, decode runtimeBytecode ⟨186⟩,
      decode runtimeBytecode ⟨187⟩, decode runtimeBytecode ⟨190⟩,
      decode runtimeBytecode ⟨191⟩, decode runtimeBytecode ⟨192⟩,
      decode runtimeBytecode ⟨195⟩] =
    [some (.POP, .none), some (.PUSH0, .none), some (.DUP5, .none),
      some (.Push .PUSH2, some (⟨255⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨2⟩, 1)),
      some (.DUP2, .none), some (.LT, .none),
      some (.Push .PUSH2, some (⟨181⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.PUSH0, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP7, .none),
      some (.GT, .none), some (.Push .PUSH2, some (⟨237⟩, 2)),
      some (.JUMPI, .none), some (.JUMPDEST, .none),
      some (.Push .PUSH2, some (⟨105⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem baseLoadDecodes :
    [decode runtimeBytecode ⟨255⟩, decode runtimeBytecode ⟨256⟩,
      decode runtimeBytecode ⟨257⟩, decode runtimeBytecode ⟨259⟩,
      decode runtimeBytecode ⟨260⟩, decode runtimeBytecode ⟨261⟩,
      decode runtimeBytecode ⟨262⟩, decode runtimeBytecode ⟨263⟩,
      decode runtimeBytecode ⟨264⟩, decode runtimeBytecode ⟨267⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH1, some (⟨95⟩, 1)), some (.DUP5, .none),
      some (.ADD, .none), some (.CALLDATALOAD, .none), some (.PUSH0, .none),
      some (.BYTE, .none), some (.Push .PUSH2, some (⟨96⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem baseRangeCallDecodes :
    [decode runtimeBytecode ⟨237⟩, decode runtimeBytecode ⟨238⟩,
      decode runtimeBytecode ⟨239⟩, decode runtimeBytecode ⟨242⟩,
      decode runtimeBytecode ⟨244⟩, decode runtimeBytecode ⟨245⟩,
      decode runtimeBytecode ⟨246⟩, decode runtimeBytecode ⟨249⟩,
      decode runtimeBytecode ⟨250⟩, decode runtimeBytecode ⟨251⟩,
      decode runtimeBytecode ⟨254⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨250⟩, 2)),
      some (.Push .PUSH1, some (⟨95⟩, 1)), some (.DUP7, .none),
      some (.ADD, .none), some (.Push .PUSH2, some (⟨625⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none),
      some (.Push .PUSH2, some (⟨191⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_wide105 :
    (D_J runtimeBytecode 0).contains ⟨105⟩ = true := by
  native_decide

private theorem ofNat_add95 {n : Nat} (hn : 95 + n < UInt256.size) :
    UInt256.ofNat n + (⟨95⟩ : UInt256) = UInt256.ofNat (95 + n) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    show (⟨95⟩ : UInt256).toNat = 95 by decide,
    UInt256.toNat_ofNat_of_lt hn, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem base_last_eq (I : ExecutionEnv) {baseSize : Nat} (hpos : 0 < baseSize)
    (hsmall : Model.bytesToNatPadded I.calldata 96 baseSize ≤ 1) :
    Model.bytesToNatPadded I.calldata (95 + baseSize) 1 =
      Model.bytesToNatPadded I.calldata 96 baseSize := by
  have hsplit := model_bytesToNatPadded_split I.calldata 96 (baseSize - 1) 1
  rw [show baseSize - 1 + 1 = baseSize by omega,
    show 96 + (baseSize - 1) = 95 + baseSize by omega] at hsplit
  omega

private theorem base_prefix_zero (I : ExecutionEnv) {baseSize : Nat} (hpos : 0 < baseSize)
    (hsmall : Model.bytesToNatPadded I.calldata 96 baseSize ≤ 1) :
    Model.bytesToNatPadded I.calldata 96 (baseSize - 1) = 0 := by
  have hsplit := model_bytesToNatPadded_split I.calldata 96 (baseSize - 1) 1
  rw [show baseSize - 1 + 1 = baseSize by omega,
    show 96 + (baseSize - 1) = 95 + baseSize by omega] at hsplit
  omega

private theorem loadedBase_eq (I : ExecutionEnv) {baseSize : Nat}
    (hbound : 95 + baseSize < 2 ^ 64) (hpos : 0 < baseSize)
    (hsmall : Model.bytesToNatPadded I.calldata 96 baseSize ≤ 1) :
    UInt256.byteAt ⟨0⟩ (uInt256OfByteArray
        (I.calldata.readBytes (UInt256.ofNat (95 + baseSize)).toNat 32)) =
      UInt256.ofNat (Model.bytesToNatPadded I.calldata 96 baseSize) := by
  have hoff : 95 + baseSize < UInt256.size := lt_trans hbound (by decide)
  apply u256_inj
  rw [UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hsmall (by decide))]
  rw [UInt256.toNat_ofNat_of_lt hoff]
  rw [calldataByte0_toNat_eq_model I.calldata (95 + baseSize) hbound,
    base_last_eq I hpos hsmall]

private theorem loadedBaseLast_eq (I : ExecutionEnv) {baseSize : Nat}
    (hbound : 95 + baseSize < 2 ^ 64) :
    UInt256.byteAt ⟨0⟩ (uInt256OfByteArray
        (I.calldata.readBytes (UInt256.ofNat (95 + baseSize)).toNat 32)) =
      UInt256.ofNat (Model.bytesToNatPadded I.calldata (95 + baseSize) 1) := by
  have hoff : 95 + baseSize < UInt256.size := lt_trans hbound (by decide)
  have hbyte := model_bytesToNatPadded_lt_pow I.calldata (95 + baseSize) 1
  apply u256_inj
  rw [UInt256.toNat_ofNat_of_lt (by omega : 95 + baseSize < UInt256.size)]
  rw [calldataByte0_toNat_eq_model I.calldata (95 + baseSize) hbound]
  rw [UInt256.toNat_ofNat_of_lt (lt_trans hbyte (by decide))]

private theorem base_prefix_nonzero_of_gt_one_last_lt_two (I : ExecutionEnv)
    {baseSize : Nat} (hpos : 0 < baseSize)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hlast : Model.bytesToNatPadded I.calldata (95 + baseSize) 1 < 2) :
    Model.bytesToNatPadded I.calldata 96 (baseSize - 1) ≠ 0 := by
  intro hzero
  have hsplit := model_bytesToNatPadded_split I.calldata 96 (baseSize - 1) 1
  rw [show baseSize - 1 + 1 = baseSize by omega,
    show 96 + (baseSize - 1) = 95 + baseSize by omega] at hsplit
  rw [hzero] at hsplit
  omega

/-- Complement of `reachWideBaseSmall`: once the exponent is nonzero and the base is greater than
one, the wide prelude falls through to the operand-allocation block at PC 105. -/
theorem reachWideBaseGtOne {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : 96 + baseSize + exponentSize + 32 < 2 ^ 64)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨89⟩
      [UInt256.ofNat modulusSize, UInt256.ofNat (wideModulusOffset baseSize exponentSize),
        UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨105⟩
      [UInt256.ofNat (Model.bytesToNatPadded I.calldata (95 + baseSize) 1),
        UInt256.ofNat (wideModulusOffset baseSize exponentSize),
        UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k' (C + wideBaseGtOneGas I baseSize) := by
  have hd := baseSmallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19, hd20⟩
  have hl := baseLoadDecodes
  simp only [List.cons.injEq, and_true] at hl
  rcases hl with ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9⟩
  have hr := baseRangeCallDecodes
  simp only [List.cons.injEq, and_true] at hr
  rcases hr with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10⟩
  have hb0 : baseSize ≠ 0 := by
    intro h
    subst baseSize
    simp [model_bytesToNatPadded_zero_width] at hbase
  have hbpos : 0 < baseSize := Nat.pos_of_ne_zero hb0
  have hbaseSizeWord : baseSize < UInt256.size :=
    lt_trans (by omega : baseSize < 2 ^ 64) (by decide)
  have hlastBound := model_bytesToNatPadded_lt_pow I.calldata (95 + baseSize) 1
  have hlastWord :
      Model.bytesToNatPadded I.calldata (95 + baseSize) 1 < UInt256.size :=
    lt_trans hlastBound (by decide)
  have hadd := ofNat_add95 (lt_trans (by omega : 95 + baseSize < 2 ^ 64) (by decide))
  have hlastLoad := loadedBaseLast_eq I (by omega : 95 + baseSize < 2 ^ 64)
  have rdHead := evm_run rd0 with [
    known pop hd0, known push0 hd1, known dup5 hd2, known push2 hd3 ⟨255⟩ ]
  have rdLoad := rdHead.jumpiT hd4 (by
      intro hz
      have := congrArg UInt256.toNat hz
      rw [UInt256.toNat_ofNat_of_lt hbaseSizeWord] at this
      exact hb0 this) jumpDest_wide255 (by evm_ov)
  have rd96raw := evm_run rdLoad with [
    known jumpdest hl0, known pop hl1, known push1 hl2 ⟨95⟩,
    known dup5 hl3, known add hl4, known calldataload hl5,
    known push0 hl6, known byte hl7, known push2 hl8 ⟨96⟩,
    known jump hl9 jumpDest_wide96 ]
  have rd96 := rd96raw.withStack (by rw [hadd, hlastLoad])
  by_cases hlastLt : Model.bytesToNatPadded I.calldata (95 + baseSize) 1 < 2
  · have hlt : UInt256.lt
        (UInt256.ofNat (Model.bytesToNatPadded I.calldata (95 + baseSize) 1)) ⟨2⟩ = ⟨1⟩ := by
      apply ult_one
      rw [UInt256.toNat_ofNat_of_lt hlastWord,
        show (⟨2⟩ : UInt256).toNat = 2 by decide]
      exact hlastLt
    have hb1 : baseSize ≠ 1 := by
      intro h
      subst baseSize
      simp at hlastLt
      omega
    have hbgt : 1 < baseSize := by omega
    have hgt : UInt256.gt (UInt256.ofNat baseSize) ⟨1⟩ = ⟨1⟩ := by
      apply ugt_one
      rw [UInt256.toNat_ofNat_of_lt hbaseSizeWord,
        show (⟨1⟩ : UInt256).toNat = 1 by decide]
      exact hbgt
    have rd181 := evm_run rd96 with [
      known jumpdest hd5, known push1 hd6 ⟨2⟩, known dup2 hd7, known lt hd8,
      known push2 hd9 ⟨181⟩, known jumpiT hd10 (by rw [hlt]; decide) jumpDest_wide181,
      known jumpdest hd11, known push0 hd12, known push1 hd13 ⟨1⟩,
      known dup7 hd14, known gt hd15, known push2 hd16 ⟨237⟩ ]
    have rd237 := rd181.jumpiT hd17 (by rw [hgt]; decide) jumpDest_wide237 (by evm_ov)
    have rd625raw := evm_run rd237 with [
      known jumpdest hr0, known pop hr1, known push2 hr2 ⟨250⟩,
      known push1 hr3 ⟨95⟩, known dup7 hr4, known add hr5,
      known push2 hr6 ⟨625⟩, known jump hr7 jumpDest_625 ]
    have rd625 := rd625raw.withStack (by rw [hadd])
    obtain ⟨kScan, rd250raw⟩ := baseRangeExactTrusted (I := I)
      (tail := [UInt256.ofNat (Model.bytesToNatPadded I.calldata (95 + baseSize) 1),
        UInt256.ofNat (wideModulusOffset baseSize exponentSize),
        UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize])
      (htail := by simp) (hend64 := by omega) (hstart := by omega)
      jumpDest_wide250 rd625
    have hscan : cdRangeReference I 96 (95 + baseSize) = 1 := by
      unfold cdRangeReference
      have hpref := base_prefix_nonzero_of_gt_one_last_lt_two I hbpos hbase hlastLt
      simp [hpref, show 95 + baseSize - 96 = baseSize - 1 by omega]
    have hone : UInt256.ofNat 1 = (⟨1⟩ : UInt256) := by native_decide
    have rd250 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨250⟩
        ((⟨1⟩ : UInt256) ::
          UInt256.ofNat (Model.bytesToNatPadded I.calldata (95 + baseSize) 1) ::
          UInt256.ofNat (wideModulusOffset baseSize exponentSize) ::
          UInt256.ofNat exponentSize :: UInt256.ofNat (wideExponentOffset baseSize) ::
          UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: [])
        mem aw rdata acc kScan
        (C + 137 + cdRangeGas I 96 (95 + baseSize)) := by
      simpa [hscan, hone] using rd250raw.withIndices rfl (by omega)
    have rd105 := evm_run rd250 with [
      known jumpdest hr8, known push2 hr9 ⟨191⟩, known jump hr10 jumpDest_wide191,
      known jumpdest hd18, known push2 hd19 ⟨105⟩,
      known jumpiT hd20 (by native_decide) jumpDest_wide105 ]
    exact ⟨kScan + 6, by
      simpa [wideBaseGtOneGas, hlastLt] using rd105.withIndices rfl (by omega)⟩
  · have hlt : UInt256.lt
        (UInt256.ofNat (Model.bytesToNatPadded I.calldata (95 + baseSize) 1)) ⟨2⟩ = ⟨0⟩ := by
      apply ult_zero
      rw [UInt256.toNat_ofNat_of_lt hlastWord,
        show (⟨2⟩ : UInt256).toNat = 2 by decide]
      exact Nat.le_of_not_gt hlastLt
    have rd105 := evm_run rd96 with [
      known jumpdest hd5, known push1 hd6 ⟨2⟩, known dup2 hd7, known lt hd8,
      known push2 hd9 ⟨181⟩,
      known jumpiNT hd10 (by rw [hlt]) ]
    exact ⟨_, by
      simpa [wideBaseGtOneGas, hlastLt] using rd105⟩

/-- From the nonzero-exponent split to the shared base-zero/base-one return block. -/
theorem reachWideBaseSmall {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : 96 + baseSize + exponentSize + 32 < 2 ^ 64)
    (hsmall : Model.bytesToNatPadded I.calldata 96 baseSize ≤ 1)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨89⟩
      [UInt256.ofNat modulusSize, UInt256.ofNat (wideModulusOffset baseSize exponentSize),
        UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨196⟩
      [UInt256.ofNat (Model.bytesToNatPadded I.calldata 96 baseSize),
        UInt256.ofNat (wideModulusOffset baseSize exponentSize),
        UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k' (C + wideBaseSmallGas I baseSize) := by
  have hd := baseSmallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
    hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19, hd20⟩
  have hl := baseLoadDecodes
  simp only [List.cons.injEq, and_true] at hl
  rcases hl with ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9⟩
  have hr := baseRangeCallDecodes
  simp only [List.cons.injEq, and_true] at hr
  rcases hr with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10⟩
  have rdHead := evm_run rd0 with [
    known pop hd0, known push0 hd1, known dup5 hd2, known push2 hd3 ⟨255⟩ ]
  by_cases hb0 : baseSize = 0
  · subst baseSize
    have rd96 := rdHead.jumpiNT hd4 (by native_decide) (by evm_ov)
    have rd181 := evm_run rd96 with [
      known jumpdest hd5, known push1 hd6 ⟨2⟩, known dup2 hd7, known lt hd8,
      known push2 hd9 ⟨181⟩, known jumpiT hd10 (by native_decide) jumpDest_wide181,
      known jumpdest hd11, known push0 hd12, known push1 hd13 ⟨1⟩,
      known dup7 hd14, known gt hd15, known push2 hd16 ⟨237⟩,
      known jumpiNT hd17 (by native_decide), known jumpdest hd18,
      known push2 hd19 ⟨105⟩, known jumpiNT hd20 (by native_decide) ]
    refine ⟨k + 21, ?_⟩
    simpa [wideBaseSmallGas, model_bytesToNatPadded_zero_width] using
      rd181.withIndices rfl (by omega)
  · have hbpos : 0 < baseSize := Nat.pos_of_ne_zero hb0
    have hbase := loadedBase_eq I (by omega) hbpos hsmall
    have hbaseSizeWord : baseSize < UInt256.size :=
      lt_trans (by omega : baseSize < 2 ^ 64) (by decide)
    have hadd := ofNat_add95 (lt_trans (by omega : 95 + baseSize < 2 ^ 64) (by decide))
    have rdLoad := rdHead.jumpiT hd4 (by
      intro hz
      have := congrArg UInt256.toNat hz
      rw [UInt256.toNat_ofNat_of_lt hbaseSizeWord] at this
      exact hb0 this) jumpDest_wide255 (by evm_ov)
    have rd96raw := evm_run rdLoad with [
      known jumpdest hl0, known pop hl1, known push1 hl2 ⟨95⟩,
      known dup5 hl3, known add hl4, known calldataload hl5,
      known push0 hl6, known byte hl7, known push2 hl8 ⟨96⟩,
      known jump hl9 jumpDest_wide96 ]
    have rd96 := rd96raw.withStack (by rw [hadd, hbase])
    have hlt : UInt256.lt
        (UInt256.ofNat (Model.bytesToNatPadded I.calldata 96 baseSize)) ⟨2⟩ = ⟨1⟩ := by
      apply ult_one
      rw [UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hsmall (by decide))]
      rw [show (⟨2⟩ : UInt256).toNat = 2 by decide]
      omega
    have rd181 := evm_run rd96 with [
      known jumpdest hd5, known push1 hd6 ⟨2⟩, known dup2 hd7, known lt hd8,
      known push2 hd9 ⟨181⟩, known jumpiT hd10 (by rw [hlt]; decide) jumpDest_wide181,
      known jumpdest hd11, known push0 hd12, known push1 hd13 ⟨1⟩,
      known dup7 hd14, known gt hd15, known push2 hd16 ⟨237⟩ ]
    by_cases hb1 : baseSize = 1
    · subst baseSize
      have rd196 := evm_run rd181 with [
        known jumpiNT hd17 (by native_decide), known jumpdest hd18,
        known push2 hd19 ⟨105⟩, known jumpiNT hd20 (by native_decide) ]
      exact ⟨k + 31, by simpa [wideBaseSmallGas] using rd196.withIndices rfl (by omega)⟩
    · have hbgt : 1 < baseSize := by omega
      have hgt : UInt256.gt (UInt256.ofNat baseSize) ⟨1⟩ = ⟨1⟩ := by
        apply ugt_one
        rw [UInt256.toNat_ofNat_of_lt hbaseSizeWord]
        simpa using hbgt
      have rd237 := rd181.jumpiT hd17 (by rw [hgt]; decide) jumpDest_wide237 (by evm_ov)
      have rd625raw := evm_run rd237 with [
        known jumpdest hr0, known pop hr1, known push2 hr2 ⟨250⟩,
        known push1 hr3 ⟨95⟩, known dup7 hr4, known add hr5,
        known push2 hr6 ⟨625⟩, known jump hr7 jumpDest_625 ]
      have rd625 := rd625raw.withStack (by rw [hadd])
      obtain ⟨kScan, rd250raw⟩ := baseRangeExactTrusted (I := I)
        (tail := [UInt256.ofNat (Model.bytesToNatPadded I.calldata 96 baseSize),
          UInt256.ofNat (wideModulusOffset baseSize exponentSize),
          UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
          UInt256.ofNat baseSize, UInt256.ofNat modulusSize])
        (htail := by simp) (hend64 := by omega) (hstart := by omega)
        jumpDest_wide250 rd625
      have hpref := base_prefix_zero I hbpos hsmall
      have rd250 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨250⟩
          ((⟨0⟩ : UInt256) ::
            UInt256.ofNat (Model.bytesToNatPadded I.calldata 96 baseSize) ::
            UInt256.ofNat (wideModulusOffset baseSize exponentSize) ::
            UInt256.ofNat exponentSize :: UInt256.ofNat (wideExponentOffset baseSize) ::
            UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: [])
          mem aw rdata acc kScan
          (C + 137 + cdRangeGas I 96 (95 + baseSize)) := by
        have hscan : cdRangeReference I 96 (95 + baseSize) = 0 := by
          simp [cdRangeReference, hpref,
            show 95 + baseSize - 96 = baseSize - 1 by omega]
        have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by native_decide
        simpa [hscan, hzero] using rd250raw.withIndices rfl (by omega)
      have rd196 := evm_run rd250 with [
        known jumpdest hr8, known push2 hr9 ⟨191⟩, known jump hr10 jumpDest_wide191,
        known jumpdest hd18, known push2 hd19 ⟨105⟩,
        known jumpiNT hd20 (by native_decide) ]
      exact ⟨kScan + 6, by simpa [wideBaseSmallGas, hb0, hb1] using
        (rd196.withIndices rfl (by omega))⟩

end Modexp
