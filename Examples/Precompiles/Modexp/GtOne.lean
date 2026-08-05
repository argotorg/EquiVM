import Examples.Precompiles.Modexp.Range

/-!
# Exact `isGt1` helper

This helper supports the wide-input zero/one fast paths.  Its pure presentation is phrased only in
terms of the trusted padded parser; subsequent lemmas connect the two bytecode branches (prefix
scan and last-byte test) to this presentation and its exact gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def isGt1Prefix (I : ExecutionEnv) (off size : Nat) : Nat :=
  if 1 < size then cdRangeReference I off (off + size - 1) else 0

def isGt1Last (I : ExecutionEnv) (off size : Nat) : Nat :=
  if size = 0 then 0 else Model.bytesToNatPadded I.calldata (off + size - 1) 1

def isGt1Result (I : ExecutionEnv) (off size : Nat) : Nat :=
  if isGt1Prefix I off size = 0 ∧ 0 < size ∧ 1 < isGt1Last I off size then 1
  else isGt1Prefix I off size

/-- Source-level exact instruction gas for `isGt1`, excluding its caller. -/
def isGt1Gas (I : ExecutionEnv) (off size : Nat) : Nat :=
  let pfx := isGt1Prefix I off size
  let common :=
    if pfx ≠ 0 ∨ size = 0 then 44
    else if 1 < isGt1Last I off size then 91 else 83
  if 1 < size then 101 + cdRangeGas I off (off + size - 1) + common
  else 34 + common

/-- The source-shaped helper predicate is exactly comparison of the trusted padded integer with
one. -/
theorem isGt1Result_eq_model (I : ExecutionEnv) (off size : Nat) :
    isGt1Result I off size =
      if 1 < Model.bytesToNatPadded I.calldata off size then 1 else 0 := by
  by_cases hzero : size = 0
  · subst size
    have hread : Model.readPadded I.calldata off 0 = ByteArray.empty :=
      byteArray_eq_empty_of_size_eq_zero _ (model_readPadded_size _ _ _)
    simp [isGt1Result, isGt1Prefix, isGt1Last, Model.bytesToNatPadded,
      Model.bytesToBigEndianNat, hread, Reasoning.Theory.byteArray_toList_eq]
  · have hpos : 0 < size := Nat.pos_of_ne_zero hzero
    have hwidth : size = (size - 1) + 1 := by omega
    have hsplit := model_bytesToNatPadded_split I.calldata off (size - 1) 1
    rw [← hwidth] at hsplit
    have hlastBound : Model.bytesToNatPadded I.calldata (off + size - 1) 1 < 256 := by
      have := model_bytesToNatPadded_lt_pow I.calldata (off + size - 1) 1
      simpa using this
    by_cases hlarge : 1 < size
    · have hprefixOff : off + (size - 1) = off + size - 1 := by omega
      have hoffdiff : off + size - 1 - off = size - 1 := by omega
      rw [hprefixOff] at hsplit
      unfold isGt1Result isGt1Prefix isGt1Last cdRangeReference
      simp only [if_pos hlarge, if_neg hzero, hoffdiff]
      by_cases hpref : Model.bytesToNatPadded I.calldata off (size - 1) = 0
      · simp only [hpref, if_true, true_and]
        rw [hsplit, hpref]
        simp only [zero_mul, zero_add, pow_one]
        simp [hpos]
      · simp only [hpref, if_false, one_ne_zero, false_and]
        rw [hsplit]
        have hprefPos := Nat.pos_of_ne_zero hpref
        have : 1 < Model.bytesToNatPadded I.calldata off (size - 1) * 256 ^ 1 := by
          simp only [pow_one]
          omega
        rw [if_pos (lt_of_lt_of_le this (Nat.le_add_right _ _))]
    · have hone : size = 1 := by omega
      subst size
      simp [isGt1Result, isGt1Prefix, isGt1Last]

private theorem isGt1HeaderDecodes :
    [decode runtimeBytecode ⟨762⟩, decode runtimeBytecode ⟨763⟩,
      decode runtimeBytecode ⟨764⟩, decode runtimeBytecode ⟨765⟩,
      decode runtimeBytecode ⟨766⟩, decode runtimeBytecode ⟨767⟩,
      decode runtimeBytecode ⟨769⟩, decode runtimeBytecode ⟨770⟩,
      decode runtimeBytecode ⟨771⟩, decode runtimeBytecode ⟨774⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.PUSH0, .none),
      some (.SWAP3, .none), some (.SWAP2, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP3, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨813⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem isGt1CommonDecodes :
    [decode runtimeBytecode ⟨775⟩, decode runtimeBytecode ⟨776⟩,
      decode runtimeBytecode ⟨777⟩, decode runtimeBytecode ⟨778⟩,
      decode runtimeBytecode ⟨779⟩, decode runtimeBytecode ⟨780⟩,
      decode runtimeBytecode ⟨781⟩, decode runtimeBytecode ⟨782⟩,
      decode runtimeBytecode ⟨785⟩, decode runtimeBytecode ⟨786⟩,
      decode runtimeBytecode ⟨787⟩, decode runtimeBytecode ⟨788⟩] =
    [some (.JUMPDEST, .none), some (.DUP2, .none), some (.ISZERO, .none),
      some (.ISZERO, .none), some (.DUP5, .none), some (.ISZERO, .none),
      some (.AND, .none), some (.Push .PUSH2, some (⟨789⟩, 2)), some (.JUMPI, .none),
      some (.POP, .none), some (.POP, .none), some (.JUMP, .none)] := by
  native_decide

private theorem gtSizeSmall {size : Nat} (hsize : size ≤ 1)
    (hword : size < UInt256.size) :
    UInt256.gt (UInt256.ofNat size) ⟨1⟩ = ⟨0⟩ := by
  apply ugt_zero
  rw [UInt256.toNat_ofNat_of_lt hword]
  simpa using hsize

private theorem gtSizeLarge {size : Nat} (hsize : 1 < size)
    (hword : size < UInt256.size) :
    UInt256.gt (UInt256.ofNat size) ⟨1⟩ = ⟨1⟩ := by
  apply ugt_one
  rw [UInt256.toNat_ofNat_of_lt hword]
  simpa using hsize

/-- Header path when no prefix scan is required. -/
private theorem reachIsGt1Small {cA gh bl σ σ₀ A I} {g : Sat256}
    {off size ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1018) (hsizeWord : size < UInt256.size) (hsize : size ≤ 1)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨775⟩
      (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: ⟨0⟩ :: tail)
      mem aw rdata acc (k + 10) (C + 34) := by
  have hd := isGt1HeaderDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9⟩
  have hgt := gtSizeSmall hsize hsizeWord
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known swap1 hd1,
    known push0 hd2,
    known swap3 hd3,
    known swap2 hd4,
    known push1 hd5 ⟨1⟩,
    known dup3 hd6,
    known gt hd7,
    known push2 hd8 ⟨813⟩,
    known jumpiNT hd9 hgt ]
  exact (rd.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- Header path selecting the prefix scan. -/
private theorem reachIsGt1Large {cA gh bl σ σ₀ A I} {g : Sat256}
    {off size ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1018) (hsizeWord : size < UInt256.size) (hsize : 1 < size)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨813⟩
      (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: ⟨0⟩ :: tail)
      mem aw rdata acc (k + 10) (C + 34) := by
  have hd := isGt1HeaderDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9⟩
  have hgt := gtSizeLarge hsize hsizeWord
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known swap1 hd1,
    known push0 hd2,
    known swap3 hd3,
    known swap2 hd4,
    known push1 hd5 ⟨1⟩,
    known dup3 hd6,
    known gt hd7,
    known push2 hd8 ⟨813⟩,
    known jumpiT hd9 (by rw [hgt]; decide) jumpDest_813 ]
  exact rd.withIndices (by omega) (by omega)

/-- Exact zero-width helper call. -/
theorem isGt1ZeroExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {off ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1018)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat off :: ⟨0⟩ :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (⟨0⟩ :: tail) mem aw rdata acc (k + 22) (C + 78) := by
  have rdCommon := reachIsGt1Small (size := 0) (tail := tail)
    htail (by decide) (by omega) rd0
  have hd := isGt1CommonDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8,
    hd9, hd10, hd11⟩
  have rd := evm_run rdCommon with [
    known jumpdest hd0,
    known dup2 hd1,
    known iszero hd2,
    known iszero hd3,
    known dup5 hd4,
    known iszero hd5,
    known and hd6,
    known push2 hd7 ⟨789⟩,
    known jumpiNT hd8 (by native_decide),
    known pop hd9,
    known pop hd10,
    known jump hd11 hret ]
  exact rd.withIndices (by omega) (by omega)

private theorem isGt1LastDecodes :
    [decode runtimeBytecode ⟨789⟩, decode runtimeBytecode ⟨790⟩,
      decode runtimeBytecode ⟨792⟩, decode runtimeBytecode ⟨793⟩,
      decode runtimeBytecode ⟨794⟩, decode runtimeBytecode ⟨795⟩,
      decode runtimeBytecode ⟨796⟩, decode runtimeBytecode ⟨797⟩,
      decode runtimeBytecode ⟨798⟩, decode runtimeBytecode ⟨799⟩,
      decode runtimeBytecode ⟨800⟩, decode runtimeBytecode ⟨801⟩,
      decode runtimeBytecode ⟨804⟩, decode runtimeBytecode ⟨805⟩,
      decode runtimeBytecode ⟨806⟩, decode runtimeBytecode ⟨807⟩,
      decode runtimeBytecode ⟨808⟩, decode runtimeBytecode ⟨810⟩,
      decode runtimeBytecode ⟨811⟩, decode runtimeBytecode ⟨812⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.SWAP2, .none), some (.ADD, .none), some (.PUSH0, .none), some (.NOT, .none),
      some (.ADD, .none), some (.CALLDATALOAD, .none), some (.PUSH0, .none),
      some (.BYTE, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨807⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.SWAP2, .none), some (.POP, .none), some (.JUMP, .none)] := by
  native_decide

private theorem isGt1SizeOneAddr {off : Nat} (hoff : off < UInt256.size) :
    UInt256.lnot ⟨0⟩ + ((⟨1⟩ : UInt256) + UInt256.ofNat off) = UInt256.ofNat off := by
  rw [← u256_add_assoc]
  rw [show UInt256.lnot ⟨0⟩ + (⟨1⟩ : UInt256) = ⟨0⟩ by native_decide]
  apply u256_inj
  rw [uadd_toNat, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    UInt256.toNat_ofNat_of_lt hoff, zero_add, Nat.mod_eq_of_lt hoff]

/-- Exact one-byte helper call, including the last-byte comparison. -/
theorem isGt1OneExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {off ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1018) (hoff64 : off < 2 ^ 64)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat off :: ⟨1⟩ :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (isGt1Result I off 1) :: tail) mem aw rdata acc
      (if 1 < Model.bytesToNatPadded I.calldata off 1 then k + 37 else k + 34)
      (C + if 1 < Model.bytesToNatPadded I.calldata off 1 then 125 else 117) := by
  have rdCommon := reachIsGt1Small (size := 1) (tail := tail)
    htail (by decide) (by omega) rd0
  have hc := isGt1CommonDecodes
  simp only [List.cons.injEq, and_true] at hc
  rcases hc with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, _, _, _⟩
  have rdLast := evm_run rdCommon with [
    known jumpdest hc0,
    known dup2 hc1,
    known iszero hc2,
    known iszero hc3,
    known dup5 hc4,
    known iszero hc5,
    known and hc6,
    known push2 hc7 ⟨789⟩,
    known jumpiT hc8 (by native_decide) jumpDest_789 ]
  have hd := isGt1LastDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19⟩
  have rdTest := evm_run rdLast with [
    known jumpdest hd0,
    known push1 hd1 ⟨1⟩,
    known swap2 hd2,
    known add hd3,
    known push0 hd4,
    known not hd5,
    known add hd6 ]
  have hoffWord : off < UInt256.size := lt_trans hoff64 (by decide)
  have haddr := isGt1SizeOneAddr hoffWord
  have rdAddr := rdTest.withStack
    (congrArg (fun x : UInt256 => x :: (⟨1⟩ : UInt256) ::
      UInt256.ofNat ret :: (⟨0⟩ : UInt256) :: tail) haddr)
  have rdCmp := evm_run rdAddr with [
    known calldataload hd7,
    known push0 hd8,
    known byte hd9,
    known gt hd10,
    known push2 hd11 ⟨807⟩ ]
  have hbyte := calldataByte0_toNat_eq_model I.calldata off hoff64
  have hbyte' : (UInt256.byteAt ⟨0⟩
      (calldataWord I (UInt256.ofNat off))).toNat =
      Model.bytesToNatPadded I.calldata off 1 := by
    simpa [calldataWord, UInt256.toNat_ofNat_of_lt hoffWord] using hbyte
  have hlast : isGt1Last I off 1 = Model.bytesToNatPadded I.calldata off 1 := by
    simp [isGt1Last]
  by_cases hgt : 1 < Model.bytesToNatPadded I.calldata off 1
  · have hgtWord : UInt256.gt
        (UInt256.byteAt ⟨0⟩ (calldataWord I (UInt256.ofNat off))) ⟨1⟩ = ⟨1⟩ := by
      apply ugt_one
      rw [hbyte']
      simpa using hgt
    have hgtRaw : UInt256.gt
        (UInt256.byteAt ⟨0⟩
          (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat off).toNat 32))) ⟨1⟩ =
        ⟨1⟩ := by
      simpa [calldataWord] using hgtWord
    have rdFound := rdCmp.jumpiT hd12 (by rw [hgtRaw]; decide) jumpDest_807 (by evm_ov)
    have rd := evm_run rdFound with [
      known jumpdest hd15,
      known push1 hd16 ⟨1⟩,
      known swap2 hd17,
      known pop hd18,
      known jump hd19 hret ]
    have hres : isGt1Result I off 1 = 1 := by
      simp [isGt1Result, isGt1Prefix, isGt1Last, hgt]
    rw [hres]
    simp only [if_pos hgt]
    exact rd.withIndices (by omega) (by omega)
  · have hgtWord : UInt256.gt
        (UInt256.byteAt ⟨0⟩ (calldataWord I (UInt256.ofNat off))) ⟨1⟩ = ⟨0⟩ := by
      apply ugt_zero
      rw [hbyte']
      simpa using Nat.le_of_not_gt hgt
    have hgtRaw : UInt256.gt
        (UInt256.byteAt ⟨0⟩
          (uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat off).toNat 32))) ⟨1⟩ =
        ⟨0⟩ := by
      simpa [calldataWord] using hgtWord
    have rdNotFound := rdCmp.jumpiNT hd12 hgtRaw (by evm_ov)
    have rd := evm_run rdNotFound with [
      known jumpdest hd13,
      known jump hd14 hret ]
    have hres : isGt1Result I off 1 = 0 := by
      simp [isGt1Result, isGt1Prefix, isGt1Last, hgt]
    rw [hres]
    simp only [if_neg hgt]
    exact rd.withIndices (by omega) (by omega)

private theorem ofNat_add {a b : Nat} (hab : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    UInt256.toNat_ofNat_of_lt (by omega), UInt256.toNat_ofNat_of_lt hab,
    Nat.mod_eq_of_lt hab]

private theorem isGt1LastAddr {off size : Nat} (hsize : 0 < size)
    (hbound : off + size < UInt256.size) :
    UInt256.lnot ⟨0⟩ + (UInt256.ofNat size + UInt256.ofNat off) =
      UInt256.ofNat (off + size - 1) := by
  rw [ofNat_add (by simpa [Nat.add_comm] using hbound)]
  have hsum : size + off = 1 + (off + size - 1) := by omega
  rw [hsum, ← ofNat_add (by omega), ← u256_add_assoc]
  rw [show UInt256.lnot ⟨0⟩ + (UInt256.ofNat 1) = ⟨0⟩ by native_decide,
    u256_zero_add]

private theorem isGt1LargeSetupDecodes :
    [decode runtimeBytecode ⟨813⟩, decode runtimeBytecode ⟨814⟩,
      decode runtimeBytecode ⟨815⟩, decode runtimeBytecode ⟨816⟩,
      decode runtimeBytecode ⟨819⟩, decode runtimeBytecode ⟨820⟩,
      decode runtimeBytecode ⟨821⟩, decode runtimeBytecode ⟨822⟩,
      decode runtimeBytecode ⟨823⟩, decode runtimeBytecode ⟨824⟩,
      decode runtimeBytecode ⟨825⟩, decode runtimeBytecode ⟨826⟩,
      decode runtimeBytecode ⟨829⟩, decode runtimeBytecode ⟨830⟩,
      decode runtimeBytecode ⟨831⟩, decode runtimeBytecode ⟨832⟩,
      decode runtimeBytecode ⟨835⟩] =
    [some (.JUMPDEST, .none), some (.SWAP3, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨830⟩, 2)), some (.PUSH0, .none), some (.NOT, .none),
      some (.DUP3, .none), some (.DUP6, .none), some (.ADD, .none), some (.ADD, .none),
      some (.DUP5, .none), some (.Push .PUSH2, some (⟨694⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP3, .none),
      some (.Push .PUSH2, some (⟨775⟩, 2)), some (.JUMP, .none)] := by
  native_decide

/-- Exact arbitrary-width `isGt1` call.  Its result is stated through the trusted parser and its
gas is the source-level `isGt1Gas` expression. -/
theorem isGt1LargeExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {off size ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1013) (hsize : 1 < size)
    (hbound64 : off + size + 32 < 2 ^ 64)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (isGt1Result I off size) :: tail)
      mem aw rdata acc k' (C + isGt1Gas I off size) := by
  have hsizeWord : size < UInt256.size :=
    lt_trans (by omega : size < 2 ^ 64) (by decide)
  have rdSetup := reachIsGt1Large (tail := tail) (by omega) hsizeWord hsize rd0
  have hd := isGt1LargeSetupDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8,
    hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16⟩
  have rdRangeRaw := evm_run rdSetup with [
    known jumpdest hd0,
    known swap3 hd1,
    known pop hd2,
    known push2 hd3 ⟨830⟩,
    known push0 hd4,
    known not hd5,
    known dup3 hd6,
    known dup6 hd7,
    known add hd8,
    known add hd9,
    known dup5 hd10,
    known push2 hd11 ⟨694⟩,
    known jump hd12 jumpDest_694 ]
  have haddr := isGt1LastAddr (off := off) (size := size) (by omega)
    (lt_trans (by omega : off + size < 2 ^ 64) (by decide))
  have haddrRaw : UInt256.ofNat off + UInt256.ofNat size + UInt256.lnot ⟨0⟩ =
      UInt256.ofNat (off + size - 1) := by
    rw [u256_add_comm (UInt256.ofNat off + UInt256.ofNat size),
      u256_add_comm (UInt256.ofNat off) (UInt256.ofNat size), haddr]
  have hstack :
      (UInt256.ofNat off ::
        (UInt256.ofNat off + UInt256.ofNat size + UInt256.lnot ⟨0⟩) ::
        ⟨830⟩ :: UInt256.ofNat size :: UInt256.ofNat ret :: UInt256.ofNat off :: tail) =
      (UInt256.ofNat off :: UInt256.ofNat (off + size - 1) :: ⟨830⟩ ::
        UInt256.ofNat size :: UInt256.ofNat ret :: UInt256.ofNat off :: tail) := by
    rw [haddrRaw]
  have rdRange := rdRangeRaw.withStack hstack
  obtain ⟨kRange, rdScanned⟩ := cdRangeExactTrusted (I := I)
    (tail := UInt256.ofNat size :: UInt256.ofNat ret :: UInt256.ofNat off :: tail)
    (by simp; omega) (by omega) (by omega) jumpDest_830 rdRange
  have rdCommon := evm_run rdScanned with [
    known jumpdest hd13,
    known swap3 hd14,
    known push2 hd15 ⟨775⟩,
    known jump hd16 jumpDest_775 ]
  have hc := isGt1CommonDecodes
  simp only [List.cons.injEq, and_true] at hc
  rcases hc with ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11⟩
  have hpfx : isGt1Prefix I off size = cdRangeReference I off (off + size - 1) := by
    simp [isGt1Prefix, hsize]
  have hsizeNe : UInt256.ofNat size ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hsizeWord] at hzNat
    simp at hzNat
    omega
  have hsizeNZ := isZero_eq_zero_of_ne hsizeNe
  have hcondZero : UInt256.land (UInt256.isZero ⟨0⟩)
      (UInt256.isZero (UInt256.isZero (UInt256.ofNat size))) = ⟨1⟩ := by
    rw [hsizeNZ]
    native_decide
  have hcondOne : UInt256.land (UInt256.isZero ⟨1⟩)
      (UInt256.isZero (UInt256.isZero (UInt256.ofNat size))) = ⟨0⟩ := by
    rw [hsizeNZ]
    native_decide
  by_cases hpref : cdRangeReference I off (off + size - 1) = 0
  · have hstackZero :
        (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret ::
          UInt256.ofNat (cdRangeReference I off (off + size - 1)) :: tail) =
        (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: ⟨0⟩ :: tail) := by
      rw [hpref]
      rfl
    have rdCommonZero := rdCommon.withStack hstackZero
    have rdLast := evm_run rdCommonZero with [
      known jumpdest hc0,
      known dup2 hc1,
      known iszero hc2,
      known iszero hc3,
      known dup5 hc4,
      known iszero hc5,
      known and hc6,
      known push2 hc7 ⟨789⟩,
      known jumpiT hc8 (by rw [hcondZero]; decide) jumpDest_789 ]
    have hl := isGt1LastDecodes
    simp only [List.cons.injEq, and_true] at hl
    rcases hl with ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9,
      hl10, hl11, hl12, hl13, hl14, hl15, hl16, hl17, hl18, hl19⟩
    have rdTestRaw := evm_run rdLast with [
      known jumpdest hl0,
      known push1 hl1 ⟨1⟩,
      known swap2 hl2,
      known add hl3,
      known push0 hl4,
      known not hl5,
      known add hl6 ]
    have rdTest := rdTestRaw.withStack
      (congrArg (fun x : UInt256 => x :: (⟨1⟩ : UInt256) ::
        UInt256.ofNat ret :: (⟨0⟩ : UInt256) :: tail) haddr)
    have rdCmp := evm_run rdTest with [
      known calldataload hl7,
      known push0 hl8,
      known byte hl9,
      known gt hl10,
      known push2 hl11 ⟨807⟩ ]
    have hoffLast64 : off + size - 1 < 2 ^ 64 := by omega
    have hoffLastWord : off + size - 1 < UInt256.size :=
      lt_trans hoffLast64 (by decide)
    have hbyte := calldataByte0_toNat_eq_model I.calldata (off + size - 1) hoffLast64
    have hbyte' : (UInt256.byteAt ⟨0⟩
        (calldataWord I (UInt256.ofNat (off + size - 1)))).toNat =
        Model.bytesToNatPadded I.calldata (off + size - 1) 1 := by
      simpa [calldataWord, UInt256.toNat_ofNat_of_lt hoffLastWord] using hbyte
    have hlast : isGt1Last I off size =
        Model.bytesToNatPadded I.calldata (off + size - 1) 1 := by
      rw [isGt1Last, if_neg (by omega : size ≠ 0)]
    have hrawWord : uInt256OfByteArray
          (I.calldata.readBytes (UInt256.ofNat (off + size - 1)).toNat 32) =
        calldataWord I (UInt256.ofNat (off + size - 1)) := by
      simp [calldataWord, UInt256.toNat_ofNat_of_lt hoffLastWord]
    by_cases hgt : 1 < isGt1Last I off size
    · have hgtRaw : UInt256.gt
          (UInt256.byteAt ⟨0⟩ (uInt256OfByteArray
            (I.calldata.readBytes (UInt256.ofNat (off + size - 1)).toNat 32))) ⟨1⟩ =
          ⟨1⟩ := by
        apply ugt_one
        rw [hrawWord, hbyte', ← hlast]
        simpa using hgt
      have rdFound := rdCmp.jumpiT hl12 (by rw [hgtRaw]; decide) jumpDest_807 (by evm_ov)
      have rdFinal := evm_run rdFound with [
        known jumpdest hl15,
        known push1 hl16 ⟨1⟩,
        known swap2 hl17,
        known pop hl18,
        known jump hl19 hret ]
      have hres : isGt1Result I off size = 1 := by
        unfold isGt1Result
        rw [hpfx, hpref]
        rw [if_pos (And.intro rfl (And.intro (by omega) hgt))]
      rw [hres, isGt1Gas, hpfx, hpref, if_pos hsize, if_pos hgt]
      rw [if_neg (by simp; omega : ¬(0 ≠ 0 ∨ size = 0))]
      rw [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) by native_decide]
      exact ⟨kRange + 31, rdFinal.withIndices (by omega) (by omega)⟩
    · have hgtRaw : UInt256.gt
          (UInt256.byteAt ⟨0⟩ (uInt256OfByteArray
            (I.calldata.readBytes (UInt256.ofNat (off + size - 1)).toNat 32))) ⟨1⟩ =
          ⟨0⟩ := by
        apply ugt_zero
        rw [hrawWord, hbyte', ← hlast]
        simpa using Nat.le_of_not_gt hgt
      have rdNotFound := rdCmp.jumpiNT hl12 hgtRaw (by evm_ov)
      have rdFinal := evm_run rdNotFound with [
        known jumpdest hl13,
        known jump hl14 hret ]
      have hres : isGt1Result I off size = 0 := by
        unfold isGt1Result
        rw [hpfx, hpref]
        rw [if_neg (fun h => hgt h.2.2)]
      rw [hres, isGt1Gas, hpfx, hpref, if_pos hsize, if_neg hgt]
      rw [if_neg (by simp; omega : ¬(0 ≠ 0 ∨ size = 0))]
      rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by native_decide]
      exact ⟨kRange + 28, rdFinal.withIndices (by omega) (by omega)⟩
  · have hprefOne : cdRangeReference I off (off + size - 1) = 1 := by
      unfold cdRangeReference at hpref ⊢
      split <;> simp_all
    have hstackOne :
        (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret ::
          UInt256.ofNat (cdRangeReference I off (off + size - 1)) :: tail) =
        (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: ⟨1⟩ :: tail) := by
      rw [hprefOne]
      rfl
    have rdCommonOne := rdCommon.withStack hstackOne
    have rdFinal := evm_run rdCommonOne with [
      known jumpdest hc0,
      known dup2 hc1,
      known iszero hc2,
      known iszero hc3,
      known dup5 hc4,
      known iszero hc5,
      known and hc6,
      known push2 hc7 ⟨789⟩,
      known jumpiNT hc8 hcondOne,
      known pop hc9,
      known pop hc10,
      known jump hc11 hret ]
    have hres : isGt1Result I off size = 1 := by
      unfold isGt1Result
      rw [hpfx, hprefOne]
      simp
    rw [hres, isGt1Gas, hpfx, hprefOne, if_pos hsize]
    rw [if_pos (by simp : 1 ≠ 0 ∨ size = 0)]
    rw [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) by native_decide]
    exact ⟨kRange + 16, rdFinal.withIndices (by omega) (by omega)⟩

/-- Exact helper theorem for every input width. -/
theorem isGt1Exact {cA gh bl σ σ₀ A I} {g : Sat256}
    {off size ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1013) (hbound64 : off + size + 32 < 2 ^ 64)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (isGt1Result I off size) :: tail)
      mem aw rdata acc k' (C + isGt1Gas I off size) := by
  by_cases hzero : size = 0
  · subst size
    have rd := isGt1ZeroExact (tail := tail) (by omega) hret rd0
    have hres : isGt1Result I off 0 = 0 := by simp [isGt1Result, isGt1Prefix]
    have hgas : isGt1Gas I off 0 = 78 := by
      simp [isGt1Gas, isGt1Prefix]
    rw [hres, hgas]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by native_decide]
    exact ⟨k + 22, rd.withIndices rfl (by omega)⟩
  · by_cases hone : size = 1
    · subst size
      have rd := isGt1OneExact (tail := tail) (by omega) (by omega) hret rd0
      have hgas : isGt1Gas I off 1 =
          if 1 < Model.bytesToNatPadded I.calldata off 1 then 125 else 117 := by
        simp [isGt1Gas, isGt1Prefix, isGt1Last]
        split <;> omega
      rw [hgas]
      exact ⟨_, rd.withIndices rfl (by split <;> omega)⟩
    · exact isGt1LargeExact htail (by omega) hbound64 hret rd0

/-- Public helper theorem whose result is written solely with the unchanged trusted ModExp
parser. -/
theorem isGt1ExactTrusted {cA gh bl σ σ₀ A I} {g : Sat256}
    {off size ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1013) (hbound64 : off + size + 32 < 2 ^ 64)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat off :: UInt256.ofNat size :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret)
      (UInt256.ofNat (if 1 < Model.bytesToNatPadded I.calldata off size then 1 else 0) :: tail)
      mem aw rdata acc k' (C + isGt1Gas I off size) := by
  obtain ⟨k', rd⟩ := isGt1Exact htail hbound64 hret rd0
  rw [isGt1Result_eq_model] at rd
  exact ⟨k', rd⟩

end Modexp
