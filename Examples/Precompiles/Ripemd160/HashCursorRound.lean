import Examples.Precompiles.Ripemd160.HashCursor

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem runtimeInitLineCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n baseOffset : Nat}
    {base : UInt256} {s : RuntimeLineState}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hbase : base.toNat = (hashScratchPtr I).toNat + baseOffset)
    (hoffset : baseOffset + 128 ≤ 832) :
    RuntimePaddedCursor I (runtimeInitLineCursor c base s) n := by
  have addNat (offset : Nat) (hoff : baseOffset + offset ≤ 832) :
      (base + UInt256.ofNat offset).toNat =
        (hashScratchPtr I).toNat + (baseOffset + offset) := by
    rw [uadd_ofNat_toNat offset (by
      rw [show UInt256.size = 2 ^ 256 from by decide]; omega) (by
        rw [hbase]
        have hu := hashScratchPtr_add_uint I hsmall
        omega)]
    omega
  simp only [runtimeInitLineCursor]
  exact ((((hc.storeAboveScratch hsmall (by omega) hbase).storeAboveScratch hsmall
    (by omega) (addNat 32 (by omega))).storeAboveScratch hsmall
    (by omega) (addNat 64 (by omega))).storeAboveScratch hsmall
    (by omega) (addNat 96 (by omega))).storeAboveScratch hsmall
    (by omega) (addNat 128 (by omega))

theorem hashLeftInitCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n : Nat} {h : RuntimeChain}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I (hashLeftInitCursor I h c) n := by
  rw [hashLeftInitCursor_eq]
  exact runtimeInitLineCursor_padded (baseOffset := 512) hc hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)) (by omega)

theorem hashRightInitCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n : Nat} {h : RuntimeChain}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I (hashRightInitCursor I h c) n := by
  rw [hashRightInitCursor_eq]
  exact runtimeInitLineCursor_padded (baseOffset := 672) hc hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)) (by omega)

theorem runtimeRoundPreludeCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n : Nat}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I (runtimeRoundPreludeCursor c (hashScratchPtr I)) n := by
  have h544 := hashScratchAdd_toNat I hsmall (by omega : 544 ≤ 895)
  have h576 := hashScratchAdd_toNat I hsmall (by omega : 576 ≤ 895)
  have h608 := hashScratchAdd_toNat I hsmall (by omega : 608 ≤ 895)
  rw [runtimeRoundPreludeCursor_eq_loads]
  exact ((hc.loadScratch hsmall (by omega) h544).loadScratch hsmall
    (by omega) h576).loadScratch hsmall (by omega) h608

theorem runtimeRightPreludeCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n : Nat}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I (runtimeRightPreludeCursor c (hashScratchPtr I)) n := by
  have h704 := hashScratchAdd_toNat I hsmall (by omega : 704 ≤ 895)
  have h736 := hashScratchAdd_toNat I hsmall (by omega : 736 ≤ 895)
  have h768 := hashScratchAdd_toNat I hsmall (by omega : 768 ≤ 895)
  rw [runtimeRightPreludeCursor_eq_loads]
  exact ((hc.loadScratch hsmall (by omega) h704).loadScratch hsmall
    (by omega) h736).loadScratch hsmall (by omega) h768

theorem runtimeLeftRoundCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n group round : Nat}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I
      (runtimeLeftRoundCursor c (hashScratchPtr I) group round) n := by
  unfold runtimeLeftRoundCursor
  exact runtimeRoundCursor_padded (lineOffset := 512)
    (runtimeRoundPreludeCursor_padded hc hsmall) hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 512 ≤ 895)) (by omega)

theorem runtimeRightRoundCursor_padded {I : ExecutionEnv}
    {c : RuntimeMemCursor} {n group round : Nat}
    (hc : RuntimePaddedCursor I c n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I
      (runtimeRightRoundCursor c (hashScratchPtr I) group round) n := by
  unfold runtimeRightRoundCursor
  exact runtimeRoundCursor_padded (lineOffset := 672)
    (runtimeRightPreludeCursor_padded hc hsmall) hsmall
    (hashScratchAdd_toNat I hsmall (by omega : 672 ≤ 895)) (by omega)

end Ripemd160
