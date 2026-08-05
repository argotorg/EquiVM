import Examples.Precompiles.Modexp.Allocation

/-!
# Exact bounded calldata-segment copy

This is the compiler helper used to populate the three zero-initialized operand arrays.  It clamps
the requested copy to the available calldata and records every branch in its exact gas expression.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def calldataSegmentAvail (I : ExecutionEnv) (off size : Nat) : Nat :=
  min size (I.calldata.size - off)

def calldataSegmentSteps (I : ExecutionEnv) (off size : Nat) : Nat :=
  8 + (if off < I.calldata.size then 9 else 0) + 6 +
    (if size < I.calldata.size - off then 6 else 0) + 5 +
    (if calldataSegmentAvail I off size = 0 then 4 else 5)

def calldataSegmentGas (I : ExecutionEnv) (off size : Nat) : Nat :=
  27 + (if off < I.calldata.size then 28 else 0) + 23 +
    (if size < I.calldata.size - off then 19 else 0) + 19 +
    (if calldataSegmentAvail I off size = 0 then 14
     else 18 + 3 * ((calldataSegmentAvail I off size + 31) / 32))

private theorem copySegmentDecodes :
    [decode runtimeBytecode ⟨924⟩, decode runtimeBytecode ⟨925⟩,
      decode runtimeBytecode ⟨926⟩, decode runtimeBytecode ⟨927⟩,
      decode runtimeBytecode ⟨928⟩, decode runtimeBytecode ⟨929⟩,
      decode runtimeBytecode ⟨930⟩, decode runtimeBytecode ⟨933⟩,
      decode runtimeBytecode ⟨934⟩, decode runtimeBytecode ⟨935⟩,
      decode runtimeBytecode ⟨936⟩, decode runtimeBytecode ⟨937⟩,
      decode runtimeBytecode ⟨938⟩, decode runtimeBytecode ⟨941⟩,
      decode runtimeBytecode ⟨942⟩, decode runtimeBytecode ⟨943⟩,
      decode runtimeBytecode ⟨944⟩, decode runtimeBytecode ⟨945⟩,
      decode runtimeBytecode ⟨948⟩, decode runtimeBytecode ⟨949⟩,
      decode runtimeBytecode ⟨950⟩, decode runtimeBytecode ⟨951⟩,
      decode runtimeBytecode ⟨952⟩, decode runtimeBytecode ⟨953⟩,
      decode runtimeBytecode ⟨954⟩, decode runtimeBytecode ⟨956⟩,
      decode runtimeBytecode ⟨957⟩, decode runtimeBytecode ⟨958⟩,
      decode runtimeBytecode ⟨959⟩, decode runtimeBytecode ⟨960⟩,
      decode runtimeBytecode ⟨961⟩, decode runtimeBytecode ⟨962⟩,
      decode runtimeBytecode ⟨963⟩, decode runtimeBytecode ⟨966⟩,
      decode runtimeBytecode ⟨967⟩, decode runtimeBytecode ⟨968⟩,
      decode runtimeBytecode ⟨969⟩, decode runtimeBytecode ⟨970⟩,
      decode runtimeBytecode ⟨971⟩, decode runtimeBytecode ⟨972⟩,
      decode runtimeBytecode ⟨973⟩, decode runtimeBytecode ⟨974⟩,
      decode runtimeBytecode ⟨977⟩] =
    [some (.JUMPDEST, .none), some (.PUSH0, .none), some (.SWAP3, .none),
      some (.DUP3, .none), some (.CALLDATASIZE, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨967⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.DUP1, .none), some (.DUP5, .none),
      some (.GT, .none), some (.Push .PUSH2, some (⟨959⟩, 2)),
      some (.JUMPI, .none), some (.JUMPDEST, .none), some (.POP, .none),
      some (.DUP3, .none), some (.Push .PUSH2, some (⟨953⟩, 2)),
      some (.JUMPI, .none), some (.POP, .none), some (.POP, .none),
      some (.POP, .none), some (.JUMP, .none), some (.JUMPDEST, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.ADD, .none),
      some (.CALLDATACOPY, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP3, .none), some (.POP, .none),
      some (.PUSH0, .none), some (.Push .PUSH2, some (⟨942⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none), some (.SWAP3, .none),
      some (.POP, .none), some (.DUP2, .none), some (.CALLDATASIZE, .none),
      some (.SUB, .none), some (.SWAP3, .none),
      some (.Push .PUSH2, some (⟨934⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem gt_ofNat_one {a b : Nat} (ha : a < UInt256.size)
    (hb : b < UInt256.size) (h : b < a) :
    UInt256.gt (UInt256.ofNat a) (UInt256.ofNat b) = ⟨1⟩ := by
  apply ugt_one
  rw [UInt256.toNat_ofNat_of_lt ha, UInt256.toNat_ofNat_of_lt hb]
  exact h

private theorem gt_ofNat_zero {a b : Nat} (ha : a < UInt256.size)
    (hb : b < UInt256.size) (h : a ≤ b) :
    UInt256.gt (UInt256.ofNat a) (UInt256.ofNat b) = ⟨0⟩ := by
  apply ugt_zero
  rw [UInt256.toNat_ofNat_of_lt ha, UInt256.toNat_ofNat_of_lt hb]
  exact h

/-- Exact `cdCopySegment(dst, off, size)`.  The active-word premise states that the destination
array was already logically allocated by `new bytes(size)`; consequently the payload copy has no
additional memory-expansion charge. -/
theorem calldataSegmentCopyExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {dst off size ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcalldata : I.calldata.size < 2 ^ 64) (hoff : off < 2 ^ 64)
    (hsize : size ≤ 1024) (hdst : dst + 32 < 2 ^ 64)
    (hactive : UInt256.ofNat
        (MachineState.M aw.toNat (dst + 32) (calldataSegmentAvail I off size)) = aw)
    (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨924⟩
      (UInt256.ofNat dst :: UInt256.ofNat off :: UInt256.ofNat size ::
        UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      tail
      (I.calldata.write off mem (dst + 32) (calldataSegmentAvail I off size))
      aw rdata acc (k + calldataSegmentSteps I off size)
      (C + calldataSegmentGas I off size) := by
  have hd := copySegmentDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19,
    hd20, hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29,
    hd30, hd31, hd32, hd33, hd34, hd35, hd36, hd37, hd38, hd39,
    hd40, hd41, hd42⟩
  have hcdWord : I.calldata.size < UInt256.size := lt_trans hcalldata (by decide)
  have hoffWord : off < UInt256.size := lt_trans hoff (by decide)
  have hsizeWord : size < UInt256.size :=
    lt_trans (lt_of_le_of_lt hsize (by decide : 1024 < 2 ^ 64)) (by decide)
  have havailWord : calldataSegmentAvail I off size < UInt256.size := by
    unfold calldataSegmentAvail
    exact lt_of_le_of_lt (min_le_left _ _) hsizeWord
  have hdstWord : dst < UInt256.size := lt_trans (by omega : dst < 2 ^ 64) (by decide)
  have hdst32Word : dst + 32 < UInt256.size := lt_trans hdst (by decide)
  have hdst32 : UInt256.ofNat dst + ⟨32⟩ = UInt256.ofNat (dst + 32) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hdstWord,
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hdst32Word, Nat.mod_eq_of_lt hdst32Word]
  have hdst32' : (⟨32⟩ : UInt256) + UInt256.ofNat dst = UInt256.ofNat (dst + 32) := by
    rw [u256_add_comm, hdst32]
  have rd929 := evm_run rd0 with [known jumpdest hd0, known push0 hd1,
    known swap3 hd2, known dup3 hd3, known calldatasize hd4, known gt hd5,
    known push2 hd6 ⟨967⟩]
  by_cases hoffIn : off < I.calldata.size
  · have hgtOff := gt_ofNat_one hcdWord hoffWord hoffIn
    have rd967 := evm_run rd929 with [
      known jumpiT hd7 (by rw [hgtOff]; native_decide) (by native_decide)]
    have hsub : UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat off) =
        UInt256.ofNat (I.calldata.size - off) := by
      apply u256_inj
      rw [usub_ofNat_lit_toNat (Nat.le_of_lt hoffIn) hcdWord,
        UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hcdWord)]
    have rd934raw := evm_run rd967 with [known jumpdest hd34, known swap3 hd35,
      known pop hd36, known dup2 hd37, known calldatasize hd38, known sub hd39,
      known swap3 hd40, known push2 hd41 ⟨934⟩,
      known jump hd42 (by native_decide)]
    rw [hsub] at rd934raw
    have rd934 := rd934raw
    by_cases hclamp : size < I.calldata.size - off
    · have hgtSize := gt_ofNat_one
        (lt_of_le_of_lt (Nat.sub_le _ _) hcdWord) hsizeWord hclamp
      have rd959 := evm_run rd934 with [known jumpdest hd8, known dup1 hd9,
        known dup5 hd10, known gt hd11, known push2 hd12 ⟨959⟩,
        known jumpiT hd13 (by rw [hgtSize]; native_decide) (by native_decide)]
      have rd942 := evm_run rd959 with [known jumpdest hd28, known swap3 hd29,
        known pop hd30, known push0 hd31, known push2 hd32 ⟨942⟩,
        known jump hd33 (by native_decide)]
      have havail : calldataSegmentAvail I off size = size := by
        unfold calldataSegmentAvail; omega
      rw [havail] at hactive
      have rd943 := evm_run rd942 with [known jumpdest hd14, known pop hd15,
        known dup3 hd16, known push2 hd17 ⟨953⟩]
      by_cases hz : size = 0
      · subst size
        have rd949 := evm_run rd943 with [known jumpiNT hd18 (by native_decide)]
        have rd := evm_run rd949 with [known pop hd19, known pop hd20,
          known pop hd21, known jump hd22 hret]
        simpa [calldataSegmentAvail, calldataSegmentSteps, calldataSegmentGas,
          hoffIn, hclamp] using rd.withIndices (by omega) (by omega)
      · have hsizePos : 0 < size := Nat.pos_of_ne_zero hz
        have hsizeNZ : UInt256.ofNat size ≠ ⟨0⟩ := by
          intro heq
          have := congrArg UInt256.toNat heq
          rw [UInt256.toNat_ofNat_of_lt hsizeWord] at this
          simp at this
          omega
        have rd953 := evm_run rd943 with [known jumpiT hd18 hsizeNZ (by native_decide),
          known jumpdest hd23, known push1 hd24 ⟨32⟩, known add hd25]
        rw [hdst32'] at rd953
        have rd957 := RDx.calldatacopy 0
          (I.calldata.write off mem (dst + 32) size) aw rd953 hd26
          (by
            intro s hsaw hstk
            simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk,
              UInt256.toNat_ofNat_of_lt hdst32Word,
              UInt256.toNat_ofNat_of_lt hsizeWord, hactive])
          (by simp [UInt256.toNat_ofNat_of_lt hoffWord,
            UInt256.toNat_ofNat_of_lt hdst32Word,
            UInt256.toNat_ofNat_of_lt hsizeWord])
          (by simpa [UInt256.toNat_ofNat_of_lt hdst32Word,
            UInt256.toNat_ofNat_of_lt hsizeWord] using hactive)
          (by simp only [List.length_cons]; omega)
        have rd := evm_run rd957 with [known jump hd27 hret]
        have rd' := rd.withIndices (k' := k + 39)
          (C' := C + (134 + 3 * ((size + 31) / 32)))
          (by omega)
          (by
            simp [GasConstants.Gverylow, GasConstants.Gcopy,
              UInt256.toNat_ofNat_of_lt hsizeWord]
            omega)
        have hsteps : calldataSegmentSteps I off size = 39 := by
          simp only [calldataSegmentSteps, if_pos hoffIn, if_pos hclamp,
            havail, if_neg hz]
        have hgas : calldataSegmentGas I off size =
            134 + 3 * ((size + 31) / 32) := by
          simp only [calldataSegmentGas, if_pos hoffIn, if_pos hclamp,
            havail, if_neg hz]
          omega
        rw [hsteps, hgas, havail]
        exact rd'
    · have hrawWord : I.calldata.size - off < UInt256.size :=
        lt_of_le_of_lt (Nat.sub_le _ _) hcdWord
      have hgtSize := gt_ofNat_zero (a := I.calldata.size - off) (b := size)
        hrawWord hsizeWord (by omega)
      have rd942 := evm_run rd934 with [known jumpdest hd8, known dup1 hd9,
        known dup5 hd10, known gt hd11, known push2 hd12 ⟨959⟩,
        known jumpiNT hd13 hgtSize]
      have havail : calldataSegmentAvail I off size = I.calldata.size - off := by
        unfold calldataSegmentAvail; omega
      rw [havail] at hactive
      have rd943 := evm_run rd942 with [known jumpdest hd14, known pop hd15,
        known dup3 hd16, known push2 hd17 ⟨953⟩]
      by_cases hz : I.calldata.size - off = 0
      · have rd949 := evm_run rd943 with [known jumpiNT hd18 (by rw [hz]; native_decide)]
        have rd := evm_run rd949 with [known pop hd19, known pop hd20,
          known pop hd21, known jump hd22 hret]
        simpa [calldataSegmentAvail, calldataSegmentSteps, calldataSegmentGas,
          hoffIn, hclamp, hz] using rd.withIndices (by omega) (by omega)
      · have havailNZ : UInt256.ofNat (I.calldata.size - off) ≠ ⟨0⟩ := by
          intro heq
          have := congrArg UInt256.toNat heq
          rw [UInt256.toNat_ofNat_of_lt
            (lt_of_le_of_lt (Nat.sub_le _ _) hcdWord)] at this
          simp at this
          exact hz this
        have rd953 := evm_run rd943 with [known jumpiT hd18 havailNZ (by native_decide),
          known jumpdest hd23, known push1 hd24 ⟨32⟩, known add hd25]
        rw [hdst32'] at rd953
        have havailWord' : I.calldata.size - off < UInt256.size :=
          lt_of_le_of_lt (Nat.sub_le _ _) hcdWord
        have rd957 := RDx.calldatacopy 0
          (I.calldata.write off mem (dst + 32) (I.calldata.size - off)) aw rd953 hd26
          (by
            intro s hsaw hstk
            simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk,
              UInt256.toNat_ofNat_of_lt hdst32Word,
              UInt256.toNat_ofNat_of_lt havailWord', hactive])
          (by simp [UInt256.toNat_ofNat_of_lt hoffWord,
            UInt256.toNat_ofNat_of_lt hdst32Word,
            UInt256.toNat_ofNat_of_lt havailWord'])
          (by simpa [UInt256.toNat_ofNat_of_lt hdst32Word,
            UInt256.toNat_ofNat_of_lt havailWord'] using hactive)
          (by simp only [List.length_cons]; omega)
        have rd := evm_run rd957 with [known jump hd27 hret]
        have rd' := rd.withIndices (k' := k + 33)
          (C' := C + (115 + 3 * ((I.calldata.size - off + 31) / 32)))
          (by omega)
          (by
            simp [GasConstants.Gverylow, GasConstants.Gcopy,
              UInt256.toNat_ofNat_of_lt havailWord']
            omega)
        have hsteps : calldataSegmentSteps I off size = 33 := by
          simp only [calldataSegmentSteps, if_pos hoffIn, if_neg hclamp,
            havail, if_neg hz]
        have hgas : calldataSegmentGas I off size =
            115 + 3 * ((I.calldata.size - off + 31) / 32) := by
          simp only [calldataSegmentGas, if_pos hoffIn, if_neg hclamp,
            havail, if_neg hz]
          omega
        rw [hsteps, hgas, havail]
        exact rd'
  · have hgtOff := gt_ofNat_zero hcdWord hoffWord (by omega)
    have rd934 := evm_run rd929 with [known jumpiNT hd7 hgtOff]
    have hraw : I.calldata.size - off = 0 := by omega
    have hgtSize : UInt256.gt ⟨0⟩ (UInt256.ofNat size) = ⟨0⟩ := by
      apply ugt_zero
      simp
    have rd942 := evm_run rd934 with [known jumpdest hd8, known dup1 hd9,
      known dup5 hd10, known gt hd11, known push2 hd12 ⟨959⟩,
      known jumpiNT hd13 hgtSize]
    have rd943 := evm_run rd942 with [known jumpdest hd14, known pop hd15,
      known dup3 hd16, known push2 hd17 ⟨953⟩]
    have rd949 := evm_run rd943 with [known jumpiNT hd18 (by native_decide)]
    have rd := evm_run rd949 with [known pop hd19, known pop hd20,
      known pop hd21, known jump hd22 hret]
    simpa [calldataSegmentAvail, calldataSegmentSteps, calldataSegmentGas,
      hoffIn, hraw] using rd.withIndices (by omega) (by omega)

/-! ## Specialized base segment copier

The compiler constant-folds the base offset `96`, producing a smaller helper at PC 836 than the
generic exponent/modulus helper above. -/

def baseCalldataAvail (I : ExecutionEnv) (size : Nat) : Nat :=
  min size (I.calldata.size - 96)

def baseCalldataCopySteps (I : ExecutionEnv) (size : Nat) : Nat :=
  8 + (if 96 < I.calldata.size then 8 else 0) + 6 +
    (if size < I.calldata.size - 96 then 6 else 0) + 5 +
    (if baseCalldataAvail I size = 0 then 3 else 7)

def baseCalldataCopyGas (I : ExecutionEnv) (size : Nat) : Nat :=
  27 + (if 96 < I.calldata.size then 25 else 0) + 23 +
    (if size < I.calldata.size - 96 then 19 else 0) + 19 +
    (if baseCalldataAvail I size = 0 then 12
     else 24 + 3 * ((baseCalldataAvail I size + 31) / 32))

private theorem baseCopyFinishDecodes :
    [decode runtimeBytecode ⟨855⟩, decode runtimeBytecode ⟨856⟩,
      decode runtimeBytecode ⟨857⟩, decode runtimeBytecode ⟨858⟩,
      decode runtimeBytecode ⟨861⟩, decode runtimeBytecode ⟨862⟩,
      decode runtimeBytecode ⟨863⟩, decode runtimeBytecode ⟨864⟩,
      decode runtimeBytecode ⟨865⟩, decode runtimeBytecode ⟨866⟩,
      decode runtimeBytecode ⟨868⟩, decode runtimeBytecode ⟨870⟩,
      decode runtimeBytecode ⟨871⟩, decode runtimeBytecode ⟨872⟩,
      decode runtimeBytecode ⟨873⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none), some (.DUP2, .none),
      some (.Push .PUSH2, some (⟨865⟩, 2)), some (.JUMPI, .none),
      some (.POP, .none), some (.POP, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.Push .PUSH1, some (⟨96⟩, 1)), some (.SWAP2, .none),
      some (.ADD, .none), some (.CALLDATACOPY, .none), some (.JUMP, .none)] := by
  native_decide

private theorem baseCopyFinishExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {discard dst avail ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcalldata : I.calldata.size < 2 ^ 64) (havail : avail ≤ 1024)
    (hdst : dst + 32 < 2 ^ 64)
    (hactive : UInt256.ofNat (MachineState.M aw.toNat (dst + 32) avail) = aw)
    (htail : tail.length ≤ 1016)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨855⟩
      (UInt256.ofNat discard :: UInt256.ofNat dst :: UInt256.ofNat avail ::
        UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      tail (I.calldata.write 96 mem (dst + 32) avail) aw rdata acc
      (k + 5 + if avail = 0 then 3 else 7)
      (C + 19 + if avail = 0 then 12 else 24 + 3 * ((avail + 31) / 32)) := by
  have hd := baseCopyFinishDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14⟩
  have hcdWord : I.calldata.size < UInt256.size := lt_trans hcalldata (by decide)
  have havailWord : avail < UInt256.size :=
    lt_trans (lt_of_le_of_lt havail (by decide : 1024 < 2 ^ 64)) (by decide)
  have hdstWord : dst < UInt256.size := lt_trans (by omega : dst < 2 ^ 64) (by decide)
  have hdst32Word : dst + 32 < UInt256.size := lt_trans hdst (by decide)
  have hdst32 : UInt256.ofNat dst + (⟨32⟩ : UInt256) = UInt256.ofNat (dst + 32) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hdstWord,
      show (⟨32⟩ : UInt256).toNat = 32 by decide, UInt256.toNat_ofNat_of_lt hdst32Word,
      Nat.mod_eq_of_lt hdst32Word]
  have rd861 := evm_run rd0 with [known jumpdest hd0, known pop hd1,
    known dup2 hd2, known push2 hd3 ⟨865⟩]
  by_cases hz : avail = 0
  · subst avail
    have rd862 := evm_run rd861 with [known jumpiNT hd4 (by native_decide)]
    have rd := evm_run rd862 with [known pop hd5, known pop hd6, known jump hd7 hret]
    simpa using rd.withIndices (by omega) (by omega)
  · have havailNZ : UInt256.ofNat avail ≠ ⟨0⟩ := by
      intro heq
      have h := congrArg UInt256.toNat heq
      rw [UInt256.toNat_ofNat_of_lt havailWord] at h
      simp at h
      exact hz h
    have rd865 := evm_run rd861 with [known jumpiT hd4 havailNZ jumpDest_865,
      known jumpdest hd8, known push1 hd9 ⟨32⟩, known push1 hd10 ⟨96⟩,
      known swap2 hd11, known add hd12]
    rw [hdst32] at rd865
    have rd872 := RDx.calldatacopy 0
      (I.calldata.write 96 mem (dst + 32) avail) aw rd865 hd13
      (by
        intro s hsaw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk,
          UInt256.toNat_ofNat_of_lt hdst32Word,
          UInt256.toNat_ofNat_of_lt havailWord, hactive])
      (by simp [show (⟨96⟩ : UInt256).toNat = 96 by decide,
        UInt256.toNat_ofNat_of_lt hdst32Word,
        UInt256.toNat_ofNat_of_lt havailWord])
      (by simpa [UInt256.toNat_ofNat_of_lt hdst32Word,
        UInt256.toNat_ofNat_of_lt havailWord] using hactive)
      (by simp only [List.length_cons]; omega)
    have rd := evm_run rd872 with [known jump hd14 hret]
    have rd' := rd.withIndices
      (k' := k + 12) (C' := C + 43 + 3 * ((avail + 31) / 32))
      (by omega)
      (by
        simp [GasConstants.Gverylow, GasConstants.Gcopy,
          UInt256.toNat_ofNat_of_lt havailWord]
        omega)
    simp only [if_neg hz]
    exact rd'.withIndices (by omega) (by omega)

private theorem baseCopyClampDecodes :
    [decode runtimeBytecode ⟨847⟩, decode runtimeBytecode ⟨848⟩,
      decode runtimeBytecode ⟨849⟩, decode runtimeBytecode ⟨850⟩,
      decode runtimeBytecode ⟨851⟩, decode runtimeBytecode ⟨854⟩,
      decode runtimeBytecode ⟨874⟩, decode runtimeBytecode ⟨875⟩,
      decode runtimeBytecode ⟨876⟩, decode runtimeBytecode ⟨877⟩,
      decode runtimeBytecode ⟨878⟩, decode runtimeBytecode ⟨881⟩] =
    [some (.JUMPDEST, .none), some (.DUP1, .none), some (.DUP4, .none),
      some (.GT, .none), some (.Push .PUSH2, some (⟨874⟩, 2)),
      some (.JUMPI, .none), some (.JUMPDEST, .none), some (.SWAP2, .none),
      some (.POP, .none), some (.PUSH0, .none),
      some (.Push .PUSH2, some (⟨855⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem baseCopyClampExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {dst available size ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcalldata : I.calldata.size < 2 ^ 64)
    (havailable : available = I.calldata.size - 96)
    (hsize : size ≤ 1024) (hdst : dst + 32 < 2 ^ 64)
    (hactive : UInt256.ofNat
      (MachineState.M aw.toNat (dst + 32) (min size available)) = aw)
    (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨847⟩
      (UInt256.ofNat size :: UInt256.ofNat dst :: UInt256.ofNat available ::
        UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      tail (I.calldata.write 96 mem (dst + 32) (min size available)) aw rdata acc
      (k + 6 + (if size < available then 6 else 0) + 5 +
        (if min size available = 0 then 3 else 7))
      (C + 23 + (if size < available then 19 else 0) + 19 +
        (if min size available = 0 then 12 else 24 + 3 * ((min size available + 31) / 32))) := by
  have hd := baseCopyClampDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11⟩
  have hcdWord : I.calldata.size < UInt256.size := lt_trans hcalldata (by decide)
  have hsizeWord : size < UInt256.size :=
    lt_trans (lt_of_le_of_lt hsize (by decide : 1024 < 2 ^ 64)) (by decide)
  have havailableWord : available < UInt256.size := by
    rw [havailable]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hcdWord
  have rd851 := evm_run rd0 with [known jumpdest hd0, known dup1 hd1,
    known dup4 hd2, known gt hd3, known push2 hd4 ⟨874⟩]
  by_cases hclamp : size < available
  · have hgt := gt_ofNat_one havailableWord hsizeWord hclamp
    have rd874 := evm_run rd851 with [known jumpiT hd5
      (by rw [hgt]; native_decide) jumpDest_874]
    have rd855 := evm_run rd874 with [known jumpdest hd6, known swap2 hd7,
      known pop hd8, known push0 hd9, known push2 hd10 ⟨855⟩,
      known jump hd11 jumpDest_855]
    have havail : min size available = size := by omega
    rw [havail] at hactive
    have rd := baseCopyFinishExact hcalldata hsize hdst hactive
      (by omega) hret rd855
    simpa [hclamp, havail] using rd.withIndices (by omega) (by omega)
  · have hgt := gt_ofNat_zero havailableWord hsizeWord (by omega)
    have rd855 := evm_run rd851 with [known jumpiNT hd5 hgt]
    have havail : min size available = available := by omega
    rw [havail] at hactive
    have havailableBound : available ≤ 1024 := by omega
    have rd := baseCopyFinishExact hcalldata havailableBound hdst hactive
      (by omega) hret rd855
    simpa [hclamp, havail] using rd.withIndices (by omega) (by omega)

private theorem baseCopyPrefixDecodes :
    [decode runtimeBytecode ⟨836⟩, decode runtimeBytecode ⟨837⟩,
      decode runtimeBytecode ⟨838⟩, decode runtimeBytecode ⟨839⟩,
      decode runtimeBytecode ⟨841⟩, decode runtimeBytecode ⟨842⟩,
      decode runtimeBytecode ⟨843⟩, decode runtimeBytecode ⟨846⟩,
      decode runtimeBytecode ⟨882⟩, decode runtimeBytecode ⟨883⟩,
      decode runtimeBytecode ⟨884⟩, decode runtimeBytecode ⟨917⟩,
      decode runtimeBytecode ⟨918⟩, decode runtimeBytecode ⟨919⟩,
      decode runtimeBytecode ⟨920⟩, decode runtimeBytecode ⟨923⟩] =
    [some (.JUMPDEST, .none), some (.PUSH0, .none), some (.SWAP2, .none),
      some (.Push .PUSH1, some (⟨96⟩, 1)), some (.CALLDATASIZE, .none),
      some (.GT, .none), some (.Push .PUSH2, some (⟨882⟩, 2)),
      some (.JUMPI, .none), some (.JUMPDEST, .none), some (.CALLDATASIZE, .none),
      some (.Push .PUSH32,
        some (⟨115792089237316195423570985008687907853269984665640564039457584007913129639840⟩, 32)),
      some (.ADD, .none), some (.SWAP3, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨847⟩, 2)), some (.JUMP, .none)] := by
  native_decide

/-- Exact specialized `cdCopySegment(baseDst, 96, baseSize)`. -/
theorem baseCalldataCopyExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {dst size ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcalldata : I.calldata.size < 2 ^ 64) (hsize : size ≤ 1024)
    (hdst : dst + 32 < 2 ^ 64)
    (hactive : UInt256.ofNat
      (MachineState.M aw.toNat (dst + 32) (baseCalldataAvail I size)) = aw)
    (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨836⟩
      (UInt256.ofNat dst :: UInt256.ofNat size :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      tail (I.calldata.write 96 mem (dst + 32) (baseCalldataAvail I size))
      aw rdata acc (k + baseCalldataCopySteps I size)
      (C + baseCalldataCopyGas I size) := by
  have hd := baseCopyPrefixDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, hd15⟩
  have hcdWord : I.calldata.size < UInt256.size := lt_trans hcalldata (by decide)
  have h96Word : 96 < UInt256.size := by decide
  have rd843 := evm_run rd0 with [known jumpdest hd0, known push0 hd1,
    known swap2 hd2, known push1 hd3 ⟨96⟩, known calldatasize hd4,
    known gt hd5, known push2 hd6 ⟨882⟩]
  by_cases hin : 96 < I.calldata.size
  · have hgt := gt_ofNat_one hcdWord h96Word hin
    have hgt' : UInt256.gt (UInt256.ofNat I.calldata.size) (⟨96⟩ : UInt256) = ⟨1⟩ := by
      simpa using hgt
    have rd882 := evm_run rd843 with [known jumpiT hd7
      (by rw [hgt']; native_decide) jumpDest_882]
    have rd884 := evm_run rd882 with [known jumpdest hd8, known calldatasize hd9]
    have rd917 := RDx.pushConst rd884
      ⟨115792089237316195423570985008687907853269984665640564039457584007913129639840⟩
      (width := 32) (op := .PUSH32) (by decide) hd10 (by evm_ov)
    have hsub : UInt256.ofNat I.calldata.size +
        ⟨115792089237316195423570985008687907853269984665640564039457584007913129639840⟩ =
        UInt256.ofNat (I.calldata.size - 96) := by
      apply u256_inj
      rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hcdWord,
        show (⟨115792089237316195423570985008687907853269984665640564039457584007913129639840⟩ : UInt256).toNat =
          UInt256.size - 96 by native_decide,
        UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hcdWord)]
      have heq : I.calldata.size + (UInt256.size - 96) =
          UInt256.size + (I.calldata.size - 96) := by omega
      rw [heq, Nat.add_mod, Nat.mod_self, zero_add,
        Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hcdWord)]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hcdWord)
    have hsub' :
        ⟨115792089237316195423570985008687907853269984665640564039457584007913129639840⟩ +
          UInt256.ofNat I.calldata.size = UInt256.ofNat (I.calldata.size - 96) := by
      rw [u256_add_comm, hsub]
    have rd847raw := evm_run rd917 with [known add hd11, known swap3 hd12,
      known pop hd13, known push2 hd14 ⟨847⟩, known jump hd15 jumpDest_847]
    rw [hsub'] at rd847raw
    unfold baseCalldataAvail at hactive
    have rd := baseCopyClampExact hcalldata rfl hsize hdst hactive
      (by omega) hret rd847raw
    simp only [baseCalldataCopySteps, baseCalldataCopyGas, baseCalldataAvail,
      if_pos hin]
    exact rd.withIndices
      (by
        by_cases hc : size < I.calldata.size - 96 <;>
          by_cases hz : min size (I.calldata.size - 96) = 0 <;>
          simp [hc, hz] <;> omega)
      (by
        by_cases hc : size < I.calldata.size - 96 <;>
          by_cases hz : min size (I.calldata.size - 96) = 0 <;>
          simp [hc, hz] <;> omega)
  · have hgt := gt_ofNat_zero hcdWord h96Word (by omega)
    have hgt' : UInt256.gt (UInt256.ofNat I.calldata.size) (⟨96⟩ : UInt256) = ⟨0⟩ := by
      simpa using hgt
    have rd847 := evm_run rd843 with [known jumpiNT hd7 hgt']
    have hraw : I.calldata.size - 96 = 0 := by omega
    unfold baseCalldataAvail at hactive
    rw [hraw] at hactive
    have rd := baseCopyClampExact hcalldata hraw.symm hsize hdst hactive
      (by omega) hret rd847
    have rd' := rd.withIndices (k' := k + 22) (C' := C + 81)
      (by simp)
      (by simp)
    simpa [baseCalldataCopySteps, baseCalldataCopyGas, baseCalldataAvail, hin, hraw,
      Nat.not_lt_zero] using rd'

end Modexp
