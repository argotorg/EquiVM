import Examples.Precompiles.Blake2f.Fallback.Setup

/-!
# BLAKE2F fallback positive-round traces: SIGMA selector

This module starts the positive-round compression-loop proof.  The current frontier from
`Fallback.Setup` is PC `1445`, the taken branch of the rounds-loop guard for loop index `0`.
The bytecode first computes `0 % 10`, dispatches through the compiled SIGMA selector at PC `946`,
and returns to PC `1466` with the round-0 SIGMA packing on the stack.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The compiled selector's packed SIGMA word for round `0`.

The Solidity/Via-IR selector encodes the sixteen 4-bit SIGMA indices as
`0x0123456789abcdef`. -/
abbrev sigmaRound0Word : UInt256 :=
  ⟨81985529216486895⟩

/-- The uint64 mask used by the compiled compression code. -/
abbrev u64MaskWord : UInt256 :=
  ⟨18446744073709551615⟩

/-- Round-0 SIGMA index `0` selects bytecode memory offset `640`, i.e. `m[0]`. -/
theorem sigmaRound0Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩)
    ⟨480⟩ = (⟨640⟩ : UInt256) := by
  native_decide

/-- Round-0 SIGMA index `1` selects bytecode memory offset `672`, i.e. `m[1]`. -/
theorem sigmaRound0Offset1 : UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨672⟩ : UInt256) := by
  native_decide

/-- First round's first message load, selected by SIGMA index `0`. -/
abbrev firstRoundM0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 640 32))

/-- First round's second message load, selected by SIGMA index `1`. -/
abbrev firstRoundM1Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 672 32))

/-- First round's first message argument, selected by SIGMA index `0`. -/
abbrev firstRoundM0Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM0Load mem) u64MaskWord

/-- First round's second message argument, selected by SIGMA index `1`. -/
abbrev firstRoundM1Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (firstRoundM1Load mem) u64MaskWord

/-- Valid final-flag-`0` inputs with positive rounds have selected the round-0 SIGMA word.

Source note: this executes PC `1445..1465`, jumps into the SIGMA selector at PC `946`, takes the
zero-case branch to PC `1141`, and returns to PC `1466`.  Exact cumulative gas is `7735`. -/
theorem validPositiveRoundSigmaZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1466⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7735 := by
  obtain ⟨k0, rd1445⟩ := validRoundsGuardPositiveRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1466 := evm_run rd1445 with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound0Word,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound0Word] using rd1466⟩

/-- Valid final-flag-`1` inputs with positive rounds have selected the round-0 SIGMA word.

This is the same bytecode path as the flag-`0` case, preserving the final-flag memory overwrite.
Exact cumulative gas is `7762`. -/
theorem validPositiveRoundSigmaOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1466⟩
      [sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7762 := by
  obtain ⟨k0, rd1445⟩ := validRoundsGuardPositiveRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1466 := evm_run rd1445 with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound0Word,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound0Word] using rd1466⟩

/-- Valid final-flag-`0` inputs with positive rounds have prepared the first `mixG` call.

Source note: this executes PC `1466..1511`, extracting round-0 SIGMA indices `0` and `1` from
`0x0123456789abcdef`, loading `m[0]` and `m[1]`, and jumping to the shared `mixG` body at
PC `1512`.  Exact cumulative gas is `7828`. -/
theorem validPositiveRoundMix0ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [firstRoundM1Arg (v13MixedMem I), firstRoundM0Arg (v13MixedMem I), ⟨1693⟩,
        sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7828 := by
  obtain ⟨k0, rd1466⟩ := validPositiveRoundSigmaZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have hmloadM0 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩).toNat ≥
            (v13MixedMem I).size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian ((v13MixedMem I).readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        firstRoundM0Load (v13MixedMem I) := by
    rw [sigmaRound0Offset0]
    unfold firstRoundM0Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v13MixedMem I) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
      (memSize := 1984) (v13MixedMem_size I hlen) (by decide) (by decide)
  have hmloadM1 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            (v13MixedMem I).size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian ((v13MixedMem I).readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        firstRoundM1Load (v13MixedMem I) := by
    rw [sigmaRound0Offset1]
    unfold firstRoundM1Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v13MixedMem I) (aw := UInt256.ofNat 62) (off := (⟨672⟩ : UInt256))
      (memSize := 1984) (v13MixedMem_size I hlen) (by decide) (by decide)
  have rd1512 := evm_run rd1466 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
    dup3,
    dup9,
    push8 ⟨18446744073709551615⟩,
    swap1,
    swap3,
    swap2,
    swap3,
    push2 ⟨480⟩,
    dup3,
    dup2,
    dup7,
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (firstRoundM0Load (v13MixedMem I)) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (firstRoundM1Load (v13MixedMem I)) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM1
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound0Word, u64MaskWord, firstRoundM0Arg, firstRoundM1Arg] using rd1512⟩

/-- Valid final-flag-`1` inputs with positive rounds have prepared the first `mixG` call.

This is the same bytecode path as the flag-`0` case, preserving the final-flag memory overwrite.
Exact cumulative gas is `7855`. -/
theorem validPositiveRoundMix0ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [firstRoundM1Arg (v14FinalFlagMem I), firstRoundM0Arg (v14FinalFlagMem I), ⟨1693⟩,
        sigmaRound0Word, ⟨3109⟩, ⟨3292⟩, ⟨0⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7855 := by
  obtain ⟨k0, rd1466⟩ := validPositiveRoundSigmaOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have hmloadM0 :
      (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩).toNat ≥
            (v14FinalFlagMem I).size
          ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian ((v14FinalFlagMem I).readWithPadding
          (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨55⟩) ⟨480⟩).toNat 32))) =
        firstRoundM0Load (v14FinalFlagMem I) := by
    rw [sigmaRound0Offset0]
    unfold firstRoundM0Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v14FinalFlagMem I) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
      (memSize := 1984) (v14FinalFlagMem_size I hlen) (by decide) (by decide)
  have hmloadM1 :
      (if (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
            (v14FinalFlagMem I).size
          ∨ (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
            (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian ((v14FinalFlagMem I).readWithPadding
          (UInt256.land (UInt256.shiftRight sigmaRound0Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
        firstRoundM1Load (v14FinalFlagMem I) := by
    rw [sigmaRound0Offset1]
    unfold firstRoundM1Load
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v14FinalFlagMem I) (aw := UInt256.ofNat 62) (off := (⟨672⟩ : UInt256))
      (memSize := 1984) (v14FinalFlagMem_size I hlen) (by decide) (by decide)
  have rd1512 := evm_run rd1466 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
    dup3,
    dup9,
    push8 ⟨18446744073709551615⟩,
    swap1,
    swap3,
    swap2,
    swap3,
    push2 ⟨480⟩,
    dup3,
    dup2,
    dup7,
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (firstRoundM0Load (v14FinalFlagMem I)) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (firstRoundM1Load (v14FinalFlagMem I)) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM1
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound0Word, u64MaskWord, firstRoundM0Arg, firstRoundM1Arg] using rd1512⟩

end Blake2f
