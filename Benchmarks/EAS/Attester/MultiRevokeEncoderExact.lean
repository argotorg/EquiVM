import Benchmarks.EAS.Attester.MultiRevokePostLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

def attesterMultiRevokeEncoderInnerIter :
    Nat → AttesterMultiRevokeEncoderInnerState → AttesterMultiRevokeEncoderInnerState
  | 0, s => s
  | n + 1, s => attesterMultiRevokeEncoderInnerStepState
      (attesterMultiRevokeEncoderInnerIter n s)

def attesterMultiRevokeEncoderOuterStepState
    (dst : UInt256) (s : AttesterMultiRevokeEncoderOuterState) :
    AttesterMultiRevokeEncoderOuterState :=
  let inner0 := attesterMultiRevokeEncoderOuterInnerInitialState dst s
  let innerDone :=
    attesterMultiRevokeEncoderInnerIter
      (attesterMultiRevokeEncoderOuterInnerLen dst s).toNat inner0
  attesterMultiRevokeEncoderOuterBodyNextState s innerDone

def attesterMultiRevokeEncoderOuterIter
    (dst : UInt256) :
    Nat → AttesterMultiRevokeEncoderOuterState → AttesterMultiRevokeEncoderOuterState
  | 0, s => s
  | n + 1, s => attesterMultiRevokeEncoderOuterStepState dst
      (attesterMultiRevokeEncoderOuterIter dst n s)

theorem attester_nat_sub_succ_add_one {m n : Nat} (hle : n + 1 ≤ m) :
    m - n = m - (n + 1) + 1 := by
  omega

@[simp] theorem attesterMultiRevokeEncoderInnerIter_zero
    (s : AttesterMultiRevokeEncoderInnerState) :
    attesterMultiRevokeEncoderInnerIter 0 s = s := rfl

@[simp] theorem attesterMultiRevokeEncoderInnerIter_succ
    (n : Nat) (s : AttesterMultiRevokeEncoderInnerState) :
    attesterMultiRevokeEncoderInnerIter (n + 1) s =
      attesterMultiRevokeEncoderInnerStepState
        (attesterMultiRevokeEncoderInnerIter n s) := rfl

theorem attesterMultiRevokeEncoderInnerIter_idx_zero
    (n : Nat) (s : AttesterMultiRevokeEncoderInnerState)
    (hn : n < UInt256.size)
    (hidx : s.innerIdx = (⟨0⟩ : UInt256)) :
    (attesterMultiRevokeEncoderInnerIter n s).innerIdx = UInt256.ofNat n := by
  induction n with
  | zero =>
      change s.innerIdx = UInt256.ofNat 0
      rw [hidx]
      simpa using (u256_ofNat_toNat (⟨0⟩ : UInt256)).symm
  | succ n ih =>
      have hn' : n < UInt256.size := by omega
      have hstep :
          (attesterMultiRevokeEncoderInnerStepState
            (attesterMultiRevokeEncoderInnerIter n s)).innerIdx =
            (attesterMultiRevokeEncoderInnerIter n s).innerIdx + (⟨1⟩ : UInt256) := by
        rfl
      rw [attesterMultiRevokeEncoderInnerIter_succ, hstep, ih hn']
      exact attester_u256_ofNat_sub_succ_add_one
        (m := n + 1) (n := 0) (by omega) (by omega)

@[simp] theorem attesterMultiRevokeEncoderOuterIter_zero
    (dst : UInt256) (s : AttesterMultiRevokeEncoderOuterState) :
    attesterMultiRevokeEncoderOuterIter dst 0 s = s := rfl

@[simp] theorem attesterMultiRevokeEncoderOuterIter_succ
    (dst : UInt256) (n : Nat) (s : AttesterMultiRevokeEncoderOuterState) :
    attesterMultiRevokeEncoderOuterIter dst (n + 1) s =
      attesterMultiRevokeEncoderOuterStepState dst
        (attesterMultiRevokeEncoderOuterIter dst n s) := rfl

theorem attesterMultiRevokeEncoderOuterStepState_idx
    (dst : UInt256) (s : AttesterMultiRevokeEncoderOuterState) :
    (attesterMultiRevokeEncoderOuterStepState dst s).idx =
      (⟨1⟩ : UInt256) + s.idx := by
  rfl

theorem attesterMultiRevokeEncoderOuterIter_idx_zero
    (dst : UInt256) (n : Nat) (s : AttesterMultiRevokeEncoderOuterState)
    (hn : n < UInt256.size)
    (hidx : s.idx = (⟨0⟩ : UInt256)) :
    (attesterMultiRevokeEncoderOuterIter dst n s).idx = UInt256.ofNat n := by
  induction n with
  | zero =>
      change s.idx = UInt256.ofNat 0
      rw [hidx]
      simpa using (u256_ofNat_toNat (⟨0⟩ : UInt256)).symm
  | succ n ih =>
      have hn' : n < UInt256.size := by omega
      rw [attesterMultiRevokeEncoderOuterIter_succ,
        attesterMultiRevokeEncoderOuterStepState_idx, ih hn']
      exact attester_u256_one_add_ofNat_sub_succ
        (m := n + 1) (n := 0) (by omega) hn

theorem attesterEncodeABIValues_single_dynArray
    {elemTy : ABIType} {vs : List Value} :
    ABI.encodeABIValues? [.dynamicArray elemTy] [.array vs] =
      (ABI.encodeABIArrayElems? elemTy vs).bind
        (fun encoded =>
          some (ABI.natBytes 32 ++ (ABI.natBytes vs.length ++ encoded))) := by
  unfold ABI.encodeABIValues?
  cases h : ABI.encodeABIArrayElems? elemTy vs with
  | none =>
      simp [ABI.abiTupleHeadSize?, ABI.isDynamicABIType,
        ABI.encodeABIValuesFrom?, ABI.encodeABIValue?,
        h]
  | some encoded =>
      simp [ABI.abiTupleHeadSize?, ABI.isDynamicABIType,
        ABI.encodeABIValuesFrom?, ABI.encodeABIValue?,
        h]

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeEncoderLoopToReturnExactState
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {idx srcHead len dstHead endPtr scratch dst src : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (htail : tail.length ≤ 1000)
    (hinnerTail : tail.length + 9 ≤ 1000)
    (hidx0 : idx = (⟨0⟩ : UInt256))
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨2460⟩ : UInt256)
      (idx :: srcHead :: len :: dstHead :: endPtr :: scratch :: dst :: src ::
        (⟨775⟩ : UInt256) :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ s' : AttesterMultiRevokeEncoderOuterState, ∃ k' C',
      s' =
        attesterMultiRevokeEncoderOuterIter dst len.toNat
          { idx := idx,
            srcHead := srcHead,
            dstHead := dstHead,
            endPtr := endPtr,
            mem := mem,
            aw := aw } ∧
      s'.idx = len ∧
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨775⟩ : UInt256)
        (s'.endPtr :: tail)
        s'.mem s'.aw ByteArray.empty (cA, σ) k' C' := by
  let s0 : AttesterMultiRevokeEncoderOuterState :=
    { idx := idx,
      srcHead := srcHead,
      dstHead := dstHead,
      endPtr := endPtr,
      mem := mem,
      aw := aw }
  let OuterInv : Nat → AttesterMultiRevokeEncoderOuterState → Prop :=
    fun n s => s = attesterMultiRevokeEncoderOuterIter dst (len.toNat - n) s0 ∧
      n ≤ len.toNat
  have houterIdx :
      ∀ n s, OuterInv n s → s.idx = UInt256.ofNat (len.toNat - n) := by
    intro n s hInv
    rw [hInv.1]
    exact attesterMultiRevokeEncoderOuterIter_idx_zero dst (len.toNat - n) s0
      (lt_of_le_of_lt (Nat.sub_le _ _) len.val.isLt)
      (by simpa [s0] using hidx0)
  have houterLe : ∀ n s, OuterInv n s → n ≤ len.toNat := by
    intro n s hInv
    exact hInv.2
  have hbody :
      ∀ n s, OuterInv (n + 1) s → ∀ k C,
        RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
          (⟨2469⟩ : UInt256)
          (attesterMultiRevokeEncoderOuterStack len scratch dst src (⟨775⟩ : UInt256)
            tail s)
          s.mem s.aw ByteArray.empty (cA, σ) k C →
        ∃ s' k' C',
          OuterInv n s' ∧
          RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
            (⟨2460⟩ : UInt256)
            (attesterMultiRevokeEncoderOuterStack len scratch dst src (⟨775⟩ : UInt256)
              tail s')
            s'.mem s'.aw ByteArray.empty (cA, σ) k' C' := by
    intro n s hInv k C rdBody
    let innerLen := attesterMultiRevokeEncoderOuterInnerLen dst s
    let inner0 := attesterMultiRevokeEncoderOuterInnerInitialState dst s
    let InnerInv : Nat → AttesterMultiRevokeEncoderInnerState → Prop :=
      fun m inner => inner = attesterMultiRevokeEncoderInnerIter
        (innerLen.toNat - m) inner0 ∧ m ≤ innerLen.toNat
    have hinnerIdx :
        ∀ m inner, InnerInv m inner →
          inner.innerIdx =
            UInt256.ofNat
              ((attesterMultiRevokeEncoderOuterInnerLen dst s).toNat - m) := by
      intro m inner h
      rw [h.1]
      simpa [innerLen] using
        attesterMultiRevokeEncoderInnerIter_idx_zero
          (innerLen.toNat - m) inner0
          (lt_of_le_of_lt (Nat.sub_le _ _) innerLen.val.isLt)
          (by rfl)
    have hinnerLe :
        ∀ m inner, InnerInv m inner →
          m ≤ (attesterMultiRevokeEncoderOuterInnerLen dst s).toNat := by
      intro m inner h
      simpa [innerLen] using h.2
    have hinnerStep :
        ∀ m inner, InnerInv (m + 1) inner →
          InnerInv m (attesterMultiRevokeEncoderInnerStepState inner) := by
      intro m inner h
      constructor
      · rw [h.1, attester_nat_sub_succ_add_one h.2]
        rfl
      · omega
    have hinnerInit :
        InnerInv (attesterMultiRevokeEncoderOuterInnerLen dst s).toNat
          (attesterMultiRevokeEncoderOuterInnerInitialState dst s) := by
      constructor
      · simp [innerLen, inner0]
      · simp [innerLen]
    have houterNext :
        ∀ inner, InnerInv 0 inner →
          OuterInv n (attesterMultiRevokeEncoderOuterBodyNextState s inner) := by
      intro inner hinner
      constructor
      · rw [hinner.1]
        change attesterMultiRevokeEncoderOuterStepState dst s =
          attesterMultiRevokeEncoderOuterIter dst (len.toNat - n) s0
        rw [hInv.1, attester_nat_sub_succ_add_one hInv.2]
        rfl
      · omega
    exact
      attesterX_multiRevokeEncoderOuterLoopBodyWithStateInvariant
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) v
        (len := len) (scratch := scratch) (dst := dst) (src := src)
        (ret := (⟨775⟩ : UInt256)) (tail := tail) (outer := s)
        (k := k) (C := C) (n := n)
        htail hinnerTail OuterInv InnerInv hinnerIdx hinnerLe hinnerStep
        hinnerInit houterNext rdBody
  have hInv0 : OuterInv len.toNat s0 := by
    constructor
    · simp [s0]
    · omega
  obtain ⟨s', k1, C1, hInvFinal, rd2592⟩ :=
    attesterX_multiRevokeEncoderOuterLoopWithStateInvariant
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (srcHead := srcHead) (len := len) (dstHead := dstHead)
      (endPtr := endPtr) (scratch := scratch) (dst := dst) (src := src)
      (ret := (⟨775⟩ : UInt256)) (tail := tail) (mem := mem) (aw := aw)
      (k := k) (C := C) htail OuterInv houterIdx houterLe hbody hInv0 hidx0 rd
  obtain ⟨k2, C2, rd775⟩ :=
    attesterX_multiRevokeEncoderOuterLoopExitToReturn
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := s'.idx) (srcHead := s'.srcHead) (len := len)
      (dstHead := s'.dstHead) (endPtr := s'.endPtr) (scratch := scratch)
      (dst := dst) (src := src) (tail := tail) (mem := s'.mem) (aw := s'.aw)
      (k := k1) (C := C1) htail rd2592
  refine ⟨s', k2, C2, ?_, ?_, rd775⟩
  · simpa using hInvFinal.1
  · rw [hInvFinal.1]
    have hidxIter :=
      attesterMultiRevokeEncoderOuterIter_idx_zero dst len.toNat s0 len.val.isLt
        (by simpa [s0] using hidx0)
    simpa [s0] using hidxIter.trans (u256_ofNat_toNat len)

end Benchmarks.EAS.Attester
