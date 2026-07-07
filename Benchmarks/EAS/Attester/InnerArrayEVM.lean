import Benchmarks.EAS.Attester.InnerArray

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

private theorem attester_add_mul_zero_right (p : UInt256) :
    p + UInt256.mul (⟨32⟩ : UInt256) ⟨0⟩ = p := by
  apply u256_inj
  rw [uadd_toNat]
  have hmul : (UInt256.mul (⟨32⟩ : UInt256) ⟨0⟩).toNat = 0 := by decide
  rw [hmul, Nat.add_zero]
  exact Nat.mod_eq_of_lt p.val.isLt

private theorem attester_pc363_after_inner_setup :
    ((((((((((((⟨363⟩ : UInt256) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) +
                      UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) +
                  UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 3 =
      (⟨380⟩ : UInt256) := by
  native_decide

private theorem attester_pc1001_after_inner_setup :
    ((((((((((((⟨1001⟩ : UInt256) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) +
                      UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) +
                  UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 3 =
      (⟨1018⟩ : UInt256) := by
  native_decide

private theorem attester_first_inner_start_add32_comm (I : ExecutionEnv) :
    (⟨32⟩ : UInt256) + attesterFirstInnerArrayStartWord I =
      attesterFirstInnerArrayStartWord I + ⟨32⟩ := by
  exact u256_add_comm _ _

theorem attesterX_multiRevokeFirstInnerArrayDecoderSetup
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {l p sz base len fp ret sel : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
      [⟨0⟩, l, p, ⟨0⟩, sz, ⟨0⟩, base, len, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨380⟩ : UInt256)
      [⟨2353⟩, p, p, ⟨381⟩, ⟨0⟩, sz, ⟨0⟩, base, len, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa [attester_add_mul_zero_right, attester_pc363_after_inner_setup] using
      (evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨363⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨364⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨365⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨366⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨368⟩, 0x02, .MUL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨369⟩, 0x81, .DUP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨370⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨371⟩, 0x90, .SWAP1) (by evm_ov),
    raw push2 ⟨381⟩ (by attester_decode_at v, ⟨372⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨375⟩, 0x91, .SWAP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨376⟩, 0x90, .SWAP1) (by evm_ov),
    raw push2 ⟨2353⟩ (by attester_decode_at v, ⟨377⟩, 0x61, (.Push .PUSH2)) (by evm_ov)])⟩

theorem attesterX_multiRevokeFirstInnerArrayDecoderEntry
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {l p sz base len fp ret sel : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
      [⟨0⟩, l, p, ⟨0⟩, sz, ⟨0⟩, base, len, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      [p, p, ⟨381⟩, ⟨0⟩, sz, ⟨0⟩, base, len, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd0⟩ :=
    attesterX_multiRevokeFirstInnerArrayDecoderSetup
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (l := l) (p := p) (sz := sz) (base := base) (len := len)
      (fp := fp) (ret := ret) (sel := sel)
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  exact ⟨_, _, evm_run rd0 with [
    raw jump (by attester_decode_at v, ⟨380⟩, 0x56, .JUMP)
      (attesterInnerArrayDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeFirstInnerArrayDecoderEntryFromOuterSecond
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
      [⟨0⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      [(UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have hsetup : ∃ k0 C0, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨380⟩ : UInt256)
      [⟨2353⟩,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k0 C0 := by
    exact ⟨_, _, by
      simpa [attester_add_mul_zero_right, attester_pc363_after_inner_setup] using
        (evm_run hreach with [
      raw jumpdest (by attester_decode_at v, ⟨363⟩, 0x5b, .JUMPDEST) (by evm_ov),
      raw swap1 (by attester_decode_at v, ⟨364⟩, 0x90, .SWAP1) (by evm_ov),
      raw pop (by attester_decode_at v, ⟨365⟩, 0x50, .POP) (by evm_ov),
      raw push1 ⟨32⟩ (by attester_decode_at v, ⟨366⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
      raw mul (by attester_decode_at v, ⟨368⟩, 0x02, .MUL) (by evm_ov),
      raw dup2 (by attester_decode_at v, ⟨369⟩, 0x81, .DUP2) (by evm_ov),
      raw add (by attester_decode_at v, ⟨370⟩, 0x01, .ADD) (by evm_ov),
      raw swap1 (by attester_decode_at v, ⟨371⟩, 0x90, .SWAP1) (by evm_ov),
      raw push2 ⟨381⟩ (by attester_decode_at v, ⟨372⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
      raw swap2 (by attester_decode_at v, ⟨375⟩, 0x91, .SWAP2) (by evm_ov),
      raw swap1 (by attester_decode_at v, ⟨376⟩, 0x90, .SWAP1) (by evm_ov),
      raw push2 ⟨2353⟩ (by attester_decode_at v, ⟨377⟩, 0x61, (.Push .PUSH2)) (by evm_ov)])⟩
  obtain ⟨k0, C0, rd0⟩ := hsetup
  exact ⟨_, _, evm_run rd0 with [
    raw jump (by attester_decode_at v, ⟨380⟩, 0x56, .JUMP)
      (attesterInnerArrayDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeFirstInnerArrayOffsetOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hslt :
      UInt256.slt (attesterFirstInnerArrayOffsetWord I)
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (attesterSecondArrayPayloadStartWord I))
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      [attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2374⟩ : UInt256)
      [attesterFirstInnerArrayOffsetWord I, ⟨0⟩, ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2353⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2354⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2355⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2356⟩, 0x83, .DUP4) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2357⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨30⟩ (by attester_decode_at v, ⟨2358⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw not (by attester_decode_at v, ⟨2360⟩, 0x19, .NOT) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2361⟩, 0x84, .DUP5) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨2362⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2363⟩, 0x03, .SUB) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2364⟩, 0x01, .ADD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2365⟩, 0x81, .DUP2) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2366⟩, 0x12, .SLT) (by evm_ov),
    raw push2 ⟨2374⟩ (by attester_decode_at v, ⟨2367⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2370⟩, 0x57, .JUMPI)
      (by
        change UInt256.slt (attesterFirstInnerArrayOffsetWord I)
            (UInt256.add
              (UInt256.sub (UInt256.ofNat I.calldata.size)
                (attesterSecondArrayPayloadStartWord I))
              (UInt256.lnot (⟨30⟩ : UInt256))) ≠ ⟨0⟩
        rw [hslt]
        decide)
      (attesterInnerArrayOffsetOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeFirstInnerArrayLengthMaxOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hgt :
      UInt256.gt (attesterFirstInnerArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2374⟩ : UInt256)
      [attesterFirstInnerArrayOffsetWord I, ⟨0⟩, ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      [attesterFirstInnerArrayStartWord I,
        attesterFirstInnerArrayLengthWord I,
        ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2374⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2375⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2376⟩, 0x01, .ADD) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2377⟩, 0x80, .DUP1) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2378⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2379⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2380⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2381⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2383⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2385⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2387⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2388⟩, 0x03, .SUB) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2389⟩, 0x82, .DUP3) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2390⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2391⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2399⟩ (by attester_decode_at v, ⟨2392⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2395⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt (attesterFirstInnerArrayLengthWord I)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩
        rw [hgt]
        decide)
      (attesterInnerArrayLengthOkJumpdest v) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeFirstInnerArrayPayloadSetup
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      [attesterFirstInnerArrayStartWord I,
        attesterFirstInnerArrayLengthWord I,
        ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2405⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa [attester_first_inner_start_add32_comm] using
      (evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2399⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2400⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2402⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2403⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2404⟩, 0x50, .POP) (by evm_ov)])⟩

theorem attesterX_multiRevokeFirstInnerArrayPayloadGuardOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hsgt :
      UInt256.sgt (attesterFirstInnerArrayStartWord I + ⟨32⟩)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩)) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2405⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2405⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2407⟩, 0x81, .DUP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2408⟩, 0x90, .SWAP1) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2409⟩, 0x1b, .SHL) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨2410⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2411⟩, 0x03, .SUB) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2412⟩, 0x82, .DUP3) (by evm_ov),
    raw sgt (by attester_decode_at v, ⟨2413⟩, 0x13, .SGT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2414⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2102⟩ (by attester_decode_at v, ⟨2415⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2418⟩, 0x57, .JUMPI)
      (by
        rw [hsgt]
        decide)
      (attesterDynamicArrayPayloadOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeFirstInnerArrayReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2102⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2103⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2104⟩, 0x50, .POP) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2105⟩, 0x92, .SWAP3) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2106⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2107⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2108⟩, 0x56, .JUMP)
      (attesterMultiRevokeInnerArrayReturnJumpdest v) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeFirstInnerArrayPayloadOkToReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hsgt :
      UInt256.sgt (attesterFirstInnerArrayStartWord I + ⟨32⟩)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩)) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      [attesterFirstInnerArrayStartWord I,
        attesterFirstInnerArrayLengthWord I,
        ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨381⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd2405⟩ :=
    attesterX_multiRevokeFirstInnerArrayPayloadSetup
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  obtain ⟨k1, C1, rd2102⟩ :=
    attesterX_multiRevokeFirstInnerArrayPayloadGuardOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hsgt
      (mem := mem) (aw := aw) (k := k0) (C := C0) rd2405
  exact attesterX_multiRevokeFirstInnerArrayReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (mem := mem) (aw := aw) (k := k1) (C := C1) rd2102

theorem attesterX_multiRevokeFirstInnerArrayReturnCleanup
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨387⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨381⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨382⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨383⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨384⟩, 0x50, .POP) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨385⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨386⟩, 0x50, .POP) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeFirstInnerArrayLengthZeroReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenZero : attesterFirstInnerArrayLengthWord I = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, rd3870⟩ :=
    attesterX_multiRevokeFirstInnerArrayReturnCleanup
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  let len := attesterFirstInnerArrayLengthWord I
  let payload := attesterFirstInnerArrayStartWord I + ⟨32⟩
  let tail :=
    [attesterFirstArrayLengthWord I,
      attesterSecondArrayLengthWord I,
      attesterSecondArrayPayloadStartWord I,
      attesterFirstArrayLengthWord I,
      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
      ⟨97⟩, solcSelectorWord I]
  have rd387 : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨387⟩ : UInt256)
      (len :: payload :: ⟨0⟩ :: ⟨128⟩ :: tail)
      mem aw ByteArray.empty (cA, σ) k0 C0 := by
    simpa [len, payload, tail] using rd3870
  let free :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then
      (⟨0⟩ : UInt256)
    else
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let selector := UInt256.shiftLeft (⟨3036299187⟩ : UInt256) ⟨224⟩
  let mem1 := selector.toByteArray.write 0 mem free.toNat 32
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat free.toNat 32)
  let freeAfter :=
    if (⟨64⟩ : UInt256).toNat ≥ mem1.size ∨ (⟨64⟩ : UInt256) ≥ aw2 * ⟨32⟩ then
      (⟨0⟩ : UInt256)
    else
      UInt256.ofNat (fromByteArrayBigEndian (mem1.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let revLen := UInt256.sub ((⟨4⟩ : UInt256) + free) freeAfter
  let revAw := UInt256.ofNat (MachineState.M aw3.toNat freeAfter.toNat revLen.toNat)
  have hcostMload64 :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: len :: len :: payload :: ⟨0⟩ :: ⟨128⟩ :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMstoreSelector :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          free :: selector :: free :: len :: len :: payload :: ⟨0⟩ :: ⟨128⟩ :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMload64After :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: ((⟨4⟩ : UInt256) + free) :: len :: len ::
            payload :: ⟨0⟩ :: ⟨128⟩ :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostRevert :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          freeAfter :: revLen :: len :: len :: payload :: ⟨0⟩ :: ⟨128⟩ :: tail →
        memoryExpansionCost s .REVERT = Cₘ revAw - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    rfl
  exact evm_run rd387 with [
    raw dup1 (by attester_decode_at v, ⟨387⟩, 0x80, .DUP1) (by simp [tail]),
    raw push0 (by attester_decode_at v, ⟨388⟩, 0x5f, .PUSH0) (by simp [tail]),
    raw dup2 (by attester_decode_at v, ⟨389⟩, 0x81, .DUP2) (by simp [tail]),
    raw swap1 (by attester_decode_at v, ⟨390⟩, 0x90, .SWAP1) (by simp [tail]),
    raw sub (by attester_decode_at v, ⟨391⟩, 0x03, .SUB) (by simp [tail]),
    raw push2 ⟨420⟩ (by attester_decode_at v, ⟨392⟩, 0x61, (.Push .PUSH2))
      (by simp [tail]),
    raw jumpiNT (by attester_decode_at v, ⟨395⟩, 0x57, .JUMPI)
      (by
        rw [show len = (⟨0⟩ : UInt256) by simpa [len] using hlenZero]
        native_decide)
      (by simp [tail]),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨396⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨398⟩, 0x51, .MLOAD)
      hcostMload64 (by rfl) (by rfl) (by simp [tail]),
    raw push4 ⟨3036299187⟩ (by attester_decode_at v, ⟨399⟩, 0x63, (.Push .PUSH4))
      (by simp [tail]),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨404⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw shl (by attester_decode_at v, ⟨406⟩, 0x1b, .SHL) (by simp [tail]),
    raw dup2 (by attester_decode_at v, ⟨407⟩, 0x81, .DUP2) (by simp [tail]),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨408⟩, 0x52, .MSTORE)
      hcostMstoreSelector (by rfl) (by rfl) (by simp [tail]),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨409⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw add (by attester_decode_at v, ⟨411⟩, 0x01, .ADD) (by simp [tail]),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨412⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw mload (Cₘ aw3 - Cₘ aw2) freeAfter aw3
      (by attester_decode_at v, ⟨414⟩, 0x51, .MLOAD)
      hcostMload64After (by rfl) (by rfl) (by simp [tail]),
    raw dup1 (by attester_decode_at v, ⟨415⟩, 0x80, .DUP1) (by simp [tail]),
    raw swap2 (by attester_decode_at v, ⟨416⟩, 0x91, .SWAP2) (by simp [tail]),
    raw sub (by attester_decode_at v, ⟨417⟩, 0x03, .SUB) (by simp [tail]),
    raw swap1 (by attester_decode_at v, ⟨418⟩, 0x90, .SWAP1) (by simp [tail]),
    raw rev (Cₘ revAw - Cₘ aw3)
      (by attester_decode_at v, ⟨419⟩, 0xfd, .REVERT)
      hcostRevert (by simp [tail])]

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeFirstInnerArrayNonemptyGuardOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨387⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨420⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have rd388 := RD.dup1 hreach
    (by attester_decode_at v, ⟨387⟩, 0x80, .DUP1) (by evm_ov)
  have rd389 := RD.push0 rd388
    (by attester_decode_at v, ⟨388⟩, 0x5f, .PUSH0) (by evm_ov)
  have rd390 := RD.dup2 rd389
    (by attester_decode_at v, ⟨389⟩, 0x81, .DUP2) (by evm_ov)
  have rd391 := RD.swap1 rd390
    (by attester_decode_at v, ⟨390⟩, 0x90, .SWAP1) (by evm_ov)
  have rd392 := RD.sub rd391
    (by attester_decode_at v, ⟨391⟩, 0x03, .SUB) (by evm_ov)
  have rd395 := RD.push2 rd392 ⟨420⟩
    (by attester_decode_at v, ⟨392⟩, 0x61, (.Push .PUSH2)) (by evm_ov)
  have hcond :
      UInt256.sub (⟨0⟩ : UInt256) (attesterFirstInnerArrayLengthWord I) ≠ ⟨0⟩ :=
    u256_zero_sub_ne_zero hlenNe
  have rd420 := RD.jumpiT rd395
    (by attester_decode_at v, ⟨395⟩, 0x57, .JUMPI)
    hcond (attesterMultiRevokeInnerNonemptyOkJumpdest v) (by evm_ov)
  exact ⟨_, _, by simpa using rd420⟩

theorem attesterX_multiRevokeFirstInnerArrayNonemptyOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨381⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨420⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd387⟩ :=
    attesterX_multiRevokeFirstInnerArrayReturnCleanup
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  exact attesterX_multiRevokeFirstInnerArrayNonemptyGuardOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v hlenNe
    (mem := mem) (aw := aw) (k := k0) (C := C0) rd387

theorem attesterX_multiRevokeFirstInnerArrayLengthAllocMaxOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hgt :
      UInt256.gt (attesterFirstInnerArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨420⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨420⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨421⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨422⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨423⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨425⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨427⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨429⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨430⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨431⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨432⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨433⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨445⟩ (by attester_decode_at v, ⟨434⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨437⟩, 0x57, .JUMPI)
      (by
        rw [hgt]
        decide)
      (attesterMultiRevokeInnerLengthMaxOkJumpdest v) (by evm_ov)]⟩

abbrev attesterInnerArrayAllocFreeWord (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMloadWord mem aw ⟨64⟩

abbrev attesterInnerArrayAllocAwAfterMload (aw : UInt256) : UInt256 :=
  attesterMloadAw aw ⟨64⟩

abbrev attesterInnerArrayAllocLenMem
    (len : UInt256) (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray len).write 0 mem
    (attesterInnerArrayAllocFreeWord mem aw).toNat 32

abbrev attesterInnerArrayAllocLenAw
    (_len : UInt256) (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterInnerArrayAllocAwAfterMload aw).toNat
      (attesterInnerArrayAllocFreeWord mem aw).toNat 32)

abbrev attesterInnerArrayAllocEndWord
    (len : UInt256) (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterInnerArrayAllocFreeWord mem aw +
    ((⟨32⟩ : UInt256) + UInt256.mul (⟨32⟩ : UInt256) len)

abbrev attesterInnerArrayAllocMem
    (len : UInt256) (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (attesterInnerArrayAllocEndWord len mem aw)).write 0
    (attesterInnerArrayAllocLenMem len mem aw) 64 32

abbrev attesterInnerArrayAllocAw
    (len : UInt256) (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterInnerArrayAllocLenAw len mem aw).toNat 64 32)

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeFirstInnerArrayAllocToInitLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hlenNe : len ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
      (len :: ⟨0⟩ :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
      (((⟨32⟩ : UInt256) + attesterInnerArrayAllocFreeWord mem aw) ::
        len :: attesterInnerArrayAllocFreeWord mem aw :: ⟨0⟩ :: len :: len :: payload :: tail)
      (attesterInnerArrayAllocMem len mem aw)
      (attesterInnerArrayAllocAw len mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterInnerArrayAllocFreeWord mem aw
  let aw1 := attesterInnerArrayAllocAwAfterMload aw
  let mem1 := attesterInnerArrayAllocLenMem len mem aw
  let aw2 := attesterInnerArrayAllocLenAw len mem aw
  let endWord := attesterInnerArrayAllocEndWord len mem aw
  let mem2 := attesterInnerArrayAllocMem len mem aw
  let aw3 := attesterInnerArrayAllocAw len mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: len :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreLen :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          free :: len :: len :: free :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreFreePtr :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: endWord :: len :: free :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, endWord, mem2, aw3] using
      evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨445⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨446⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨448⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨449⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨450⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨451⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨452⟩, 0x52, .MSTORE)
      hcostStoreLen (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨453⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨454⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨456⟩, 0x02, .MUL) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨457⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨459⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨460⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨461⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨462⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨464⟩, 0x52, .MSTORE)
      hcostStoreFreePtr (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨465⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨466⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨513⟩ (by attester_decode_at v, ⟨467⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨470⟩, 0x57, .JUMPI)
      (isZero_eq_zero_of_ne hlenNe) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨471⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨472⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨474⟩, 0x01, .ADD) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiAttestFirstInnerArrayAllocToInitLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {len payload : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hlenNe : len ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1083⟩ : UInt256)
      (len :: ⟨0⟩ :: len :: len :: payload :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
      (((⟨32⟩ : UInt256) + attesterInnerArrayAllocFreeWord mem aw) ::
        len :: attesterInnerArrayAllocFreeWord mem aw :: ⟨0⟩ :: len :: len :: payload :: tail)
      (attesterInnerArrayAllocMem len mem aw)
      (attesterInnerArrayAllocAw len mem aw)
      ByteArray.empty (cA, σ) k' C' := by
  let free := attesterInnerArrayAllocFreeWord mem aw
  let aw1 := attesterInnerArrayAllocAwAfterMload aw
  let mem1 := attesterInnerArrayAllocLenMem len mem aw
  let aw2 := attesterInnerArrayAllocLenAw len mem aw
  let endWord := attesterInnerArrayAllocEndWord len mem aw
  let mem2 := attesterInnerArrayAllocMem len mem aw
  let aw3 := attesterInnerArrayAllocAw len mem aw
  have hcostMload :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: len :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreLen :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          free :: len :: len :: free :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreFreePtr :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: endWord :: len :: free :: ⟨0⟩ :: len :: len :: payload :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  exact ⟨_, _, by
    simpa [free, aw1, mem1, aw2, endWord, mem2, aw3] using
      evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨1083⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1084⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨1086⟩, 0x51, .MLOAD)
      hcostMload (by rfl) (by rfl) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1087⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1088⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1089⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨1090⟩, 0x52, .MSTORE)
      hcostStoreLen (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1091⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1092⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨1094⟩, 0x02, .MUL) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1095⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1097⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1098⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1099⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1100⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨1102⟩, 0x52, .MSTORE)
      hcostStoreFreePtr (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1103⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨1104⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨1176⟩ (by attester_decode_at v, ⟨1105⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨1108⟩, 0x57, .JUMPI)
      (isZero_eq_zero_of_ne hlenNe) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1109⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1110⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1112⟩, 0x01, .ADD) (by evm_ov)]⟩

set_option maxHeartbeats 3000000 in
theorem attesterX_multiRevokeFirstInnerArrayAllocProgress
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨445⟩ : UInt256)
          [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
            attesterFirstInnerArrayLengthWord I,
            attesterFirstInnerArrayLengthWord I,
            attesterFirstInnerArrayStartWord I + ⟨32⟩,
            ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I]
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨475⟩ : UInt256)
        (((⟨32⟩ : UInt256) +
            attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a')) ::
          attesterFirstInnerArrayLengthWord I ::
          attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a') ::
          ⟨0⟩ ::
          attesterFirstInnerArrayLengthWord I ::
          attesterFirstInnerArrayLengthWord I ::
          (attesterFirstInnerArrayStartWord I + ⟨32⟩) ::
          [⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨97⟩, solcSelectorWord I])
        (attesterInnerArrayAllocMem
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
        (attesterInnerArrayAllocAw
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, rd0⟩ := hprogress
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiRevokeFirstInnerArrayAllocToInitLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (len := attesterFirstInnerArrayLengthWord I)
      (payload := attesterFirstInnerArrayStartWord I + ⟨32⟩)
      (tail := [⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I])
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k0) (C := C0) (by simp) hlenNe rd0
  exact ⟨a', k1, C1, hrem, rd1⟩

set_option maxHeartbeats 3000000 in
theorem attesterX_multiAttestFirstInnerArrayAllocProgress
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hprogress :
      ∃ a' k C,
        a'.remaining = (⟨1⟩ : UInt256) ∧
        RD (patchedRuntime v) I g
          (initState cA gh bl σ σ₀ g A I) (⟨1083⟩ : UInt256)
          [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
            attesterFirstInnerArrayLengthWord I,
            attesterFirstInnerArrayLengthWord I,
            attesterFirstInnerArrayStartWord I + ⟨32⟩,
            ⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I]
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a')
          ByteArray.empty (cA, σ) k C) :
    ∃ a' k C,
      a'.remaining = (⟨1⟩ : UInt256) ∧
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨1113⟩ : UInt256)
        (((⟨32⟩ : UInt256) +
            attesterInnerArrayAllocFreeWord
              (attesterMultiOuterArrayInitFinalMem a')
              (attesterMultiOuterArrayInitFinalAw a')) ::
          attesterFirstInnerArrayLengthWord I ::
          attesterInnerArrayAllocFreeWord
            (attesterMultiOuterArrayInitFinalMem a')
            (attesterMultiOuterArrayInitFinalAw a') ::
          ⟨0⟩ ::
          attesterFirstInnerArrayLengthWord I ::
          attesterFirstInnerArrayLengthWord I ::
          (attesterFirstInnerArrayStartWord I + ⟨32⟩) ::
          [⟨0⟩, ⟨128⟩,
            attesterFirstArrayLengthWord I, ⟨96⟩,
            attesterSecondArrayLengthWord I,
            attesterSecondArrayPayloadStartWord I,
            attesterFirstArrayLengthWord I,
            (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
            ⟨118⟩, solcSelectorWord I])
        (attesterInnerArrayAllocMem
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
        (attesterInnerArrayAllocAw
          (attesterFirstInnerArrayLengthWord I)
          (attesterMultiOuterArrayInitFinalMem a')
          (attesterMultiOuterArrayInitFinalAw a'))
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨a', k0, C0, hrem, rd0⟩ := hprogress
  obtain ⟨k1, C1, rd1⟩ :=
    attesterX_multiAttestFirstInnerArrayAllocToInitLoop
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (len := attesterFirstInnerArrayLengthWord I)
      (payload := attesterFirstInnerArrayStartWord I + ⟨32⟩)
      (tail := [⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I])
      (mem := attesterMultiOuterArrayInitFinalMem a')
      (aw := attesterMultiOuterArrayInitFinalAw a')
      (k := k0) (C := C0) (by simp) hlenNe rd0
  exact ⟨a', k1, C1, hrem, rd1⟩

theorem attesterX_multiAttestFirstInnerArrayDecoderSetup
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {l p sz base len tag fp ret sel : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1001⟩ : UInt256)
      [⟨0⟩, l, p, ⟨0⟩, sz, ⟨0⟩, base, len, tag, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1018⟩ : UInt256)
      [⟨2353⟩, p, p, ⟨1019⟩, ⟨0⟩, sz, ⟨0⟩, base, len, tag, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa [attester_add_mul_zero_right, attester_pc1001_after_inner_setup] using
      (evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨1001⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1002⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1003⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1004⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨1006⟩, 0x02, .MUL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1007⟩, 0x81, .DUP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1008⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1009⟩, 0x90, .SWAP1) (by evm_ov),
    raw push2 ⟨1019⟩ (by attester_decode_at v, ⟨1010⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1013⟩, 0x91, .SWAP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1014⟩, 0x90, .SWAP1) (by evm_ov),
    raw push2 ⟨2353⟩ (by attester_decode_at v, ⟨1015⟩, 0x61, (.Push .PUSH2)) (by evm_ov)])⟩

theorem attesterX_multiAttestFirstInnerArrayDecoderEntry
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {l p sz base len tag fp ret sel : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1001⟩ : UInt256)
      [⟨0⟩, l, p, ⟨0⟩, sz, ⟨0⟩, base, len, tag, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      [p, p, ⟨1019⟩, ⟨0⟩, sz, ⟨0⟩, base, len, tag, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd0⟩ :=
    attesterX_multiAttestFirstInnerArrayDecoderSetup
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (l := l) (p := p) (sz := sz) (base := base) (len := len)
      (tag := tag) (fp := fp) (ret := ret) (sel := sel)
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  exact ⟨_, _, evm_run rd0 with [
    raw jump (by attester_decode_at v, ⟨1018⟩, 0x56, .JUMP)
      (attesterInnerArrayDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestFirstInnerArrayDecoderEntryFromOuterSecond
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1001⟩ : UInt256)
      [⟨0⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      [(UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have hsetup : ∃ k0 C0, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1018⟩ : UInt256)
      [⟨2353⟩,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k0 C0 := by
    exact ⟨_, _, by
      simpa [attester_add_mul_zero_right, attester_pc1001_after_inner_setup] using
        (evm_run hreach with [
      raw jumpdest (by attester_decode_at v, ⟨1001⟩, 0x5b, .JUMPDEST) (by evm_ov),
      raw swap1 (by attester_decode_at v, ⟨1002⟩, 0x90, .SWAP1) (by evm_ov),
      raw pop (by attester_decode_at v, ⟨1003⟩, 0x50, .POP) (by evm_ov),
      raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1004⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
      raw mul (by attester_decode_at v, ⟨1006⟩, 0x02, .MUL) (by evm_ov),
      raw dup2 (by attester_decode_at v, ⟨1007⟩, 0x81, .DUP2) (by evm_ov),
      raw add (by attester_decode_at v, ⟨1008⟩, 0x01, .ADD) (by evm_ov),
      raw swap1 (by attester_decode_at v, ⟨1009⟩, 0x90, .SWAP1) (by evm_ov),
      raw push2 ⟨1019⟩ (by attester_decode_at v, ⟨1010⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
      raw swap2 (by attester_decode_at v, ⟨1013⟩, 0x91, .SWAP2) (by evm_ov),
      raw swap1 (by attester_decode_at v, ⟨1014⟩, 0x90, .SWAP1) (by evm_ov),
      raw push2 ⟨2353⟩ (by attester_decode_at v, ⟨1015⟩, 0x61, (.Push .PUSH2)) (by evm_ov)])⟩
  obtain ⟨k0, C0, rd0⟩ := hsetup
  exact ⟨_, _, evm_run rd0 with [
    raw jump (by attester_decode_at v, ⟨1018⟩, 0x56, .JUMP)
      (attesterInnerArrayDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestFirstInnerArrayOffsetOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hslt :
      UInt256.slt (attesterFirstInnerArrayOffsetWord I)
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (attesterSecondArrayPayloadStartWord I))
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      [attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2374⟩ : UInt256)
      [attesterFirstInnerArrayOffsetWord I, ⟨0⟩, ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2353⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2354⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2355⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2356⟩, 0x83, .DUP4) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2357⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨30⟩ (by attester_decode_at v, ⟨2358⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw not (by attester_decode_at v, ⟨2360⟩, 0x19, .NOT) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2361⟩, 0x84, .DUP5) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨2362⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2363⟩, 0x03, .SUB) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2364⟩, 0x01, .ADD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2365⟩, 0x81, .DUP2) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2366⟩, 0x12, .SLT) (by evm_ov),
    raw push2 ⟨2374⟩ (by attester_decode_at v, ⟨2367⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2370⟩, 0x57, .JUMPI)
      (by
        change UInt256.slt (attesterFirstInnerArrayOffsetWord I)
            (UInt256.add
              (UInt256.sub (UInt256.ofNat I.calldata.size)
                (attesterSecondArrayPayloadStartWord I))
              (UInt256.lnot (⟨30⟩ : UInt256))) ≠ ⟨0⟩
        rw [hslt]
        decide)
      (attesterInnerArrayOffsetOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestFirstInnerArrayLengthMaxOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hgt :
      UInt256.gt (attesterFirstInnerArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2374⟩ : UInt256)
      [attesterFirstInnerArrayOffsetWord I, ⟨0⟩, ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      [attesterFirstInnerArrayStartWord I,
        attesterFirstInnerArrayLengthWord I,
        ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2374⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2375⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2376⟩, 0x01, .ADD) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2377⟩, 0x80, .DUP1) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2378⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2379⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2380⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2381⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2383⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2385⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2387⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2388⟩, 0x03, .SUB) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2389⟩, 0x82, .DUP3) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2390⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2391⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2399⟩ (by attester_decode_at v, ⟨2392⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2395⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt (attesterFirstInnerArrayLengthWord I)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩
        rw [hgt]
        decide)
      (attesterInnerArrayLengthOkJumpdest v) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiAttestFirstInnerArrayPayloadSetup
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      [attesterFirstInnerArrayStartWord I,
        attesterFirstInnerArrayLengthWord I,
        ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2405⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa [attester_first_inner_start_add32_comm] using
      (evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2399⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2400⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2402⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2403⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2404⟩, 0x50, .POP) (by evm_ov)])⟩

theorem attesterX_multiAttestFirstInnerArrayPayloadGuardOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hsgt :
      UInt256.sgt (attesterFirstInnerArrayStartWord I + ⟨32⟩)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩)) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2405⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2405⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2407⟩, 0x81, .DUP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2408⟩, 0x90, .SWAP1) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2409⟩, 0x1b, .SHL) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨2410⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2411⟩, 0x03, .SUB) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2412⟩, 0x82, .DUP3) (by evm_ov),
    raw sgt (by attester_decode_at v, ⟨2413⟩, 0x13, .SGT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2414⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2102⟩ (by attester_decode_at v, ⟨2415⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2418⟩, 0x57, .JUMPI)
      (by
        rw [hsgt]
        decide)
      (attesterDynamicArrayPayloadOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestFirstInnerArrayReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1019⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2102⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2103⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2104⟩, 0x50, .POP) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2105⟩, 0x92, .SWAP3) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2106⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2107⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2108⟩, 0x56, .JUMP)
      (attesterMultiAttestInnerArrayReturnJumpdest v) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiAttestFirstInnerArrayPayloadOkToReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hsgt :
      UInt256.sgt (attesterFirstInnerArrayStartWord I + ⟨32⟩)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩)) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      [attesterFirstInnerArrayStartWord I,
        attesterFirstInnerArrayLengthWord I,
        ⟨0⟩,
        attesterSecondArrayPayloadStartWord I,
        attesterSecondArrayPayloadStartWord I,
        ⟨1019⟩, ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1019⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd2405⟩ :=
    attesterX_multiAttestFirstInnerArrayPayloadSetup
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  obtain ⟨k1, C1, rd2102⟩ :=
    attesterX_multiAttestFirstInnerArrayPayloadGuardOk
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v hsgt
      (mem := mem) (aw := aw) (k := k0) (C := C0) rd2405
  exact attesterX_multiAttestFirstInnerArrayReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (mem := mem) (aw := aw) (k := k1) (C := C1) rd2102

theorem attesterX_multiAttestFirstInnerArrayReturnCleanup
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1019⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1025⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨1019⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1020⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨1021⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1022⟩, 0x50, .POP) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1023⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1024⟩, 0x50, .POP) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiAttestFirstInnerArrayLengthZeroReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenZero : attesterFirstInnerArrayLengthWord I = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1019⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, rd1025_0⟩ :=
    attesterX_multiAttestFirstInnerArrayReturnCleanup
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  let len := attesterFirstInnerArrayLengthWord I
  let payload := attesterFirstInnerArrayStartWord I + ⟨32⟩
  let tail :=
    [attesterFirstArrayLengthWord I, ⟨96⟩,
      attesterSecondArrayLengthWord I,
      attesterSecondArrayPayloadStartWord I,
      attesterFirstArrayLengthWord I,
      (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
      ⟨118⟩, solcSelectorWord I]
  have rd1025 : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1025⟩ : UInt256)
      (len :: payload :: ⟨0⟩ :: ⟨128⟩ :: tail)
      mem aw ByteArray.empty (cA, σ) k0 C0 := by
    simpa [len, payload, tail] using rd1025_0
  let free :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then
      (⟨0⟩ : UInt256)
    else
      UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let selector := UInt256.shiftLeft (⟨3036299187⟩ : UInt256) ⟨224⟩
  let mem1 := selector.toByteArray.write 0 mem free.toNat 32
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat free.toNat 32)
  let freeAfter :=
    if (⟨64⟩ : UInt256).toNat ≥ mem1.size ∨ (⟨64⟩ : UInt256) ≥ aw2 * ⟨32⟩ then
      (⟨0⟩ : UInt256)
    else
      UInt256.ofNat (fromByteArrayBigEndian (mem1.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
  let revLen := UInt256.sub ((⟨4⟩ : UInt256) + free) freeAfter
  let revAw := UInt256.ofNat (MachineState.M aw3.toNat freeAfter.toNat revLen.toNat)
  have hcostMload64 :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: len :: len :: payload :: ⟨0⟩ :: ⟨128⟩ :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMstoreSelector :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          free :: selector :: free :: len :: len :: payload :: ⟨0⟩ :: ⟨128⟩ :: tail →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMload64After :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: ((⟨4⟩ : UInt256) + free) :: len :: len ::
            payload :: ⟨0⟩ :: ⟨128⟩ :: tail →
        memoryExpansionCost s .MLOAD = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostRevert :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          freeAfter :: revLen :: len :: len :: payload :: ⟨0⟩ :: ⟨128⟩ :: tail →
        memoryExpansionCost s .REVERT = Cₘ revAw - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    rfl
  exact evm_run rd1025 with [
    raw dup1 (by attester_decode_at v, ⟨1025⟩, 0x80, .DUP1) (by simp [tail]),
    raw push0 (by attester_decode_at v, ⟨1026⟩, 0x5f, .PUSH0) (by simp [tail]),
    raw dup2 (by attester_decode_at v, ⟨1027⟩, 0x81, .DUP2) (by simp [tail]),
    raw swap1 (by attester_decode_at v, ⟨1028⟩, 0x90, .SWAP1) (by simp [tail]),
    raw sub (by attester_decode_at v, ⟨1029⟩, 0x03, .SUB) (by simp [tail]),
    raw push2 ⟨1058⟩ (by attester_decode_at v, ⟨1030⟩, 0x61, (.Push .PUSH2))
      (by simp [tail]),
    raw jumpiNT (by attester_decode_at v, ⟨1033⟩, 0x57, .JUMPI)
      (by
        rw [show len = (⟨0⟩ : UInt256) by simpa [len] using hlenZero]
        native_decide)
      (by simp [tail]),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1034⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨1036⟩, 0x51, .MLOAD)
      hcostMload64 (by rfl) (by rfl) (by simp [tail]),
    raw push4 ⟨3036299187⟩ (by attester_decode_at v, ⟨1037⟩, 0x63, (.Push .PUSH4))
      (by simp [tail]),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨1042⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw shl (by attester_decode_at v, ⟨1044⟩, 0x1b, .SHL) (by simp [tail]),
    raw dup2 (by attester_decode_at v, ⟨1045⟩, 0x81, .DUP2) (by simp [tail]),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨1046⟩, 0x52, .MSTORE)
      hcostMstoreSelector (by rfl) (by rfl) (by simp [tail]),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨1047⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw add (by attester_decode_at v, ⟨1049⟩, 0x01, .ADD) (by simp [tail]),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1050⟩, 0x60, (.Push .PUSH1))
      (by simp [tail]),
    raw mload (Cₘ aw3 - Cₘ aw2) freeAfter aw3
      (by attester_decode_at v, ⟨1052⟩, 0x51, .MLOAD)
      hcostMload64After (by rfl) (by rfl) (by simp [tail]),
    raw dup1 (by attester_decode_at v, ⟨1053⟩, 0x80, .DUP1) (by simp [tail]),
    raw swap2 (by attester_decode_at v, ⟨1054⟩, 0x91, .SWAP2) (by simp [tail]),
    raw sub (by attester_decode_at v, ⟨1055⟩, 0x03, .SUB) (by simp [tail]),
    raw swap1 (by attester_decode_at v, ⟨1056⟩, 0x90, .SWAP1) (by simp [tail]),
    raw rev (Cₘ revAw - Cₘ aw3)
      (by attester_decode_at v, ⟨1057⟩, 0xfd, .REVERT)
      hcostRevert (by simp [tail])]

set_option maxHeartbeats 1000000 in
theorem attesterX_multiAttestFirstInnerArrayNonemptyGuardOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1025⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1058⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  have rd1026 := RD.dup1 hreach
    (by attester_decode_at v, ⟨1025⟩, 0x80, .DUP1) (by evm_ov)
  have rd1027 := RD.push0 rd1026
    (by attester_decode_at v, ⟨1026⟩, 0x5f, .PUSH0) (by evm_ov)
  have rd1028 := RD.dup2 rd1027
    (by attester_decode_at v, ⟨1027⟩, 0x81, .DUP2) (by evm_ov)
  have rd1029 := RD.swap1 rd1028
    (by attester_decode_at v, ⟨1028⟩, 0x90, .SWAP1) (by evm_ov)
  have rd1030 := RD.sub rd1029
    (by attester_decode_at v, ⟨1029⟩, 0x03, .SUB) (by evm_ov)
  have rd1033 := RD.push2 rd1030 ⟨1058⟩
    (by attester_decode_at v, ⟨1030⟩, 0x61, (.Push .PUSH2)) (by evm_ov)
  have hcond :
      UInt256.sub (⟨0⟩ : UInt256) (attesterFirstInnerArrayLengthWord I) ≠ ⟨0⟩ :=
    u256_zero_sub_ne_zero hlenNe
  have rd1058 := RD.jumpiT rd1033
    (by attester_decode_at v, ⟨1033⟩, 0x57, .JUMPI)
    hcond (attesterMultiAttestInnerNonemptyOkJumpdest v) (by evm_ov)
  exact ⟨_, _, by simpa using rd1058⟩

theorem attesterX_multiAttestFirstInnerArrayNonemptyOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlenNe : attesterFirstInnerArrayLengthWord I ≠ ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1019⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1058⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd1025⟩ :=
    attesterX_multiAttestFirstInnerArrayReturnCleanup
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  exact attesterX_multiAttestFirstInnerArrayNonemptyGuardOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v hlenNe
    (mem := mem) (aw := aw) (k := k0) (C := C0) rd1025

theorem attesterX_multiAttestFirstInnerArrayLengthAllocMaxOk
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {mem : ByteArray} {aw : UInt256} {k C}
    (hgt :
      UInt256.gt (attesterFirstInnerArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1058⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1083⟩ : UInt256)
      [attesterFirstInnerArrayLengthWord I, ⟨0⟩,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayLengthWord I,
        attesterFirstInnerArrayStartWord I + ⟨32⟩,
        ⟨0⟩, ⟨128⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        attesterSecondArrayPayloadStartWord I,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨1058⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1059⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1060⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1061⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1063⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1065⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨1067⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1068⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1069⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨1070⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨1071⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨1083⟩ (by attester_decode_at v, ⟨1072⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨1075⟩, 0x57, .JUMPI)
      (by
        rw [hgt]
        decide)
      (attesterMultiAttestInnerLengthMaxOkJumpdest v) (by evm_ov)]⟩

end Benchmarks.EAS.Attester
