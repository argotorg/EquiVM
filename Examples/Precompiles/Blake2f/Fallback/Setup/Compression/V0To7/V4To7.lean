import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.V0To7.V0To3

/-!
# BLAKE2F fallback compression vector initialization, words 4 through loop exit
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validV4InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨5⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v4InitMem I) (UInt256.ofNat 51) ByteArray.empty (cA, σ) k 7123 := by
  obtain ⟨k0, rd1182⟩ := validV3InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload512 :
      (if (⟨512⟩ : UInt256).toNat ≥ (v3InitMem I).size
          ∨ (⟨512⟩ : UInt256) ≥ (UInt256.ofNat 50) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v3InitMem I).readWithPadding 512 32))) =
        v4LoadWord I := by
    unfold v4LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v3InitMem I) (aw := UInt256.ofNat 50) (off := (⟨512⟩ : UInt256))
      (memSize := 1600) (v3InitMem_size I hlen) (by decide) (by decide)
  have rd1182' := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup2,
    dup10,
    add,
    raw mload 0 (v4LoadWord I) (UInt256.ofNat 50)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload512
      (by native_decide) (by evm_ov),
    and,
    swap1,
    dup10,
    add,
    raw mstore 4 (v4InitMem I) (UInt256.ofNat 51)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v4InitMem v4StoredWord
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1182⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [v4StoredWord, GasConstants.Gverylow] using rd1182'⟩

/-- Sixth working-vector initialization iteration.

Source note: same bytecode loop body, now for `i = 5`; it copies the exact bytecode-loaded word
from `h + 160` into `v + 160`. -/
theorem validV5InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨6⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v5InitMem I) (UInt256.ofNat 52) ByteArray.empty (cA, σ) k 7209 := by
  obtain ⟨k0, rd1182⟩ := validV4InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload544 :
      (if (⟨544⟩ : UInt256).toNat ≥ (v4InitMem I).size
          ∨ (⟨544⟩ : UInt256) ≥ (UInt256.ofNat 51) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v4InitMem I).readWithPadding 544 32))) =
        v5LoadWord I := by
    unfold v5LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v4InitMem I) (aw := UInt256.ofNat 51) (off := (⟨544⟩ : UInt256))
      (memSize := 1632) (v4InitMem_size I hlen) (by decide) (by decide)
  have rd1182' := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup2,
    dup10,
    add,
    raw mload 0 (v5LoadWord I) (UInt256.ofNat 51)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload544
      (by native_decide) (by evm_ov),
    and,
    swap1,
    dup10,
    add,
    raw mstore 3 (v5InitMem I) (UInt256.ofNat 52)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v5InitMem v5StoredWord
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1182⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [v5StoredWord, GasConstants.Gverylow] using rd1182'⟩

/-- Seventh working-vector initialization iteration.

Source note: same bytecode loop body, now for `i = 6`; it copies the exact bytecode-loaded word
from `h + 192` into `v + 192`. -/
theorem validV6InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨7⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v6InitMem I) (UInt256.ofNat 53) ByteArray.empty (cA, σ) k 7295 := by
  obtain ⟨k0, rd1182⟩ := validV5InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload576 :
      (if (⟨576⟩ : UInt256).toNat ≥ (v5InitMem I).size
          ∨ (⟨576⟩ : UInt256) ≥ (UInt256.ofNat 52) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v5InitMem I).readWithPadding 576 32))) =
        v6LoadWord I := by
    unfold v6LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v5InitMem I) (aw := UInt256.ofNat 52) (off := (⟨576⟩ : UInt256))
      (memSize := 1664) (v5InitMem_size I hlen) (by decide) (by decide)
  have rd1182' := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup2,
    dup10,
    add,
    raw mload 0 (v6LoadWord I) (UInt256.ofNat 52)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload576
      (by native_decide) (by evm_ov),
    and,
    swap1,
    dup10,
    add,
    raw mstore 3 (v6InitMem I) (UInt256.ofNat 53)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v6InitMem v6StoredWord
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1182⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [v6StoredWord, GasConstants.Gverylow] using rd1182'⟩

/-- Eighth working-vector initialization iteration.

Source note: same bytecode loop body, now for `i = 7`; it copies the exact bytecode-loaded word
from `h + 224` into `v + 224`.  This completes the loop iterations that copy parsed `h` words
into the working vector. -/
theorem validV7InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨8⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v7InitMem I) (UInt256.ofNat 54) ByteArray.empty (cA, σ) k 7381 := by
  obtain ⟨k0, rd1182⟩ := validV6InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload608 :
      (if (⟨608⟩ : UInt256).toNat ≥ (v6InitMem I).size
          ∨ (⟨608⟩ : UInt256) ≥ (UInt256.ofNat 53) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v6InitMem I).readWithPadding 608 32))) =
        v7LoadWord I := by
    unfold v7LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v6InitMem I) (aw := UInt256.ofNat 53) (off := (⟨608⟩ : UInt256))
      (memSize := 1696) (v6InitMem_size I hlen) (by decide) (by decide)
  have rd1182' := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup2,
    dup10,
    add,
    raw mload 0 (v7LoadWord I) (UInt256.ofNat 53)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload608
      (by native_decide) (by evm_ov),
    and,
    swap1,
    dup10,
    add,
    raw mstore 3 (v7InitMem I) (UInt256.ofNat 54)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v7InitMem v7StoredWord
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1182⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [v7StoredWord, GasConstants.Gverylow] using rd1182'⟩

/-- Valid inputs exit the first working-vector initialization loop after copying `h[0..7]`.

Source note: at loop index `8`, the guard `8 < 8` is false, so the `JUMPI` at PC `1190` is not
taken.  The following `POP` removes the finished loop index, leaving a branch-independent cursor at
PC `1192`, immediately before the eight BLAKE2 IV constants are stored into `v[8..15]`. -/
theorem validVLoopExitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1192⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v7InitMem I) (UInt256.ofNat 54) ByteArray.empty (cA, σ) k 7406 := by
  obtain ⟨k0, rd1182⟩ := validV7InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd1192 := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiNT (by native_decide),
    pop ]
  exact ⟨_, by simpa using rd1192⟩

end Blake2f
