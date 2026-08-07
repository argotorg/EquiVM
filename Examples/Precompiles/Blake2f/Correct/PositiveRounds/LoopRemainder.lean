import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopResidues
import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopUpdate

/-!
# BLAKE2F positive-round shared mix remainder

This file composes the residue-independent part of one positive round after the SIGMA selector has
reached the first shared `mixG` body at PC `1512`.

The theorem here starts at `positiveRoundMix0Pc`, executes all eight `mixG` calls, performs the
loop-index increment, and returns to the rounds-loop guard at PC `1370`.  It is parametric in the
loop index `i`; residue-specific selector proofs can combine with this theorem through
`PositiveRoundResidueBodyStep.of_selector_remainder_and_invariant`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Bytecode memory after the eight shared `mixG` calls for positive loop index `i`. -/
def positiveRoundBodyMem (i : Nat) (mem : ByteArray) : ByteArray :=
  positiveRoundMix7Mem3 i
    (positiveRoundMix6Mem3 i
      (positiveRoundMix5Mem3 i
        (positiveRoundMix4Mem3 i
          (positiveRoundMix3Mem3 i
            (positiveRoundMix2Mem3 i
              (positiveRoundMix1Mem3 i
                (positiveRoundMix0Mem3 i mem)))))))

theorem positiveRoundBodyMem_size {i : Nat} {mem : ByteArray} (hmem : mem.size = 1984) :
    (positiveRoundBodyMem i mem).size = 1984 := by
  unfold positiveRoundBodyMem
  exact positiveRoundMix7Mem3_size
    (positiveRoundMix6Mem3_size
      (positiveRoundMix5Mem3_size
        (positiveRoundMix4Mem3_size
          (positiveRoundMix3Mem3_size
            (positiveRoundMix2Mem3_size
              (positiveRoundMix1Mem3_size
                (positiveRoundMix0Mem3_size hmem)))))))

/-- Generic exact trace for the residue-independent remainder after the SIGMA selector, from PC
`1512` to the next loop header at PC `1370`. -/
theorem positiveRoundSharedMixRemainderRaw
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {i C k : Nat}
    (hmem : mem.size = 1984)
    (hi : i + 1 < UInt256.size)
    (hprefix : RDx runtimeBytecode I g s0
      positiveRoundMix0Pc
      (positiveRoundMix0EntryStack I i mem)
      mem (UInt256.ofNat 62) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g s0
      positiveRoundHeaderPc
      (positiveRoundHeaderStack I (i + 1))
      (positiveRoundBodyMem i mem) (UInt256.ofNat 62) ByteArray.empty acc k'
      (C + positiveRoundAfterMix0EntryGas) := by
  obtain ⟨k0, hmix0⟩ :=
    positiveRoundMix0BodyFromEntryStackRaw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := mem) (i := i) (C := C) (k := k)
      hmem hprefix
  have hmem0 : (positiveRoundMix0Mem3 i mem).size = 1984 :=
    positiveRoundMix0Mem3_size hmem
  obtain ⟨k1a, hmix1a⟩ :=
    positiveRoundMix1ArgsFromMix0Raw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix0Mem3 i mem) (i := i)
      (C := C + 315) (k := k0)
      hmem0 hmix0
  obtain ⟨k1, hmix1⟩ :=
    positiveRoundMix1BodyFromEntryStackRaw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix0Mem3 i mem) (i := i)
      (C := C + 315 + 93) (k := k1a)
      hmem0 hmix1a
  have hmem1 :
      (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)).size = 1984 :=
    positiveRoundMix1Mem3_size hmem0
  obtain ⟨k2a, hmix2a⟩ :=
    positiveRoundMix2ArgsFromMix1Raw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) (i := i)
      (C := C + 315 + 93 + 321) (k := k1)
      hmem1 hmix1
  obtain ⟨k2, hmix2⟩ :=
    positiveRoundMix2BodyFromEntryStackRaw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)) (i := i)
      (C := C + 315 + 93 + 321 + 93) (k := k2a)
      hmem1 hmix2a
  have hmem2 :
      (positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))).size = 1984 :=
    positiveRoundMix2Mem3_size hmem1
  obtain ⟨k3a, hmix3a⟩ :=
    positiveRoundMix3ArgsFromMix2Raw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321) (k := k2)
      hmem2 hmix2
  obtain ⟨k3, hmix3⟩ :=
    positiveRoundMix3BodyFromEntryStackRaw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix2Mem3 i
        (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93) (k := k3a)
      hmem2 hmix3a
  have hmem3 :
      (positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))).size = 1984 :=
    positiveRoundMix3Mem3_size hmem2
  obtain ⟨k4a, hmix4a⟩ :=
    positiveRoundMix4ArgsFromMix3Raw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321) (k := k3)
      hmem3 hmix3
  obtain ⟨k4, hmix4⟩ :=
    positiveRoundMix4BodyFromEntryStackRaw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix3Mem3 i
        (positiveRoundMix2Mem3 i
          (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93) (k := k4a)
      hmem3 hmix4a
  have hmem4 :
      (positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))).size = 1984 :=
    positiveRoundMix4Mem3_size hmem3
  obtain ⟨k5a, hmix5a⟩ :=
    positiveRoundMix5ArgsFromMix4Raw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93 + 315) (k := k4)
      hmem4 hmix4
  obtain ⟨k5, hmix5⟩ :=
    positiveRoundMix5BodyFromEntryStackRaw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix4Mem3 i
        (positiveRoundMix3Mem3 i
          (positiveRoundMix2Mem3 i
            (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93 + 315 + 93) (k := k5a)
      hmem4 hmix5a
  have hmem5 :
      (positiveRoundMix5Mem3 i
        (positiveRoundMix4Mem3 i
          (positiveRoundMix3Mem3 i
            (positiveRoundMix2Mem3 i
              (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))))).size = 1984 :=
    positiveRoundMix5Mem3_size hmem4
  obtain ⟨k6a, hmix6a⟩ :=
    positiveRoundMix6ArgsFromMix5Raw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix5Mem3 i
        (positiveRoundMix4Mem3 i
          (positiveRoundMix3Mem3 i
            (positiveRoundMix2Mem3 i
              (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93 + 315 + 93 + 321) (k := k5)
      hmem5 hmix5
  obtain ⟨k6, hmix6⟩ :=
    positiveRoundMix6BodyFromEntryStackRaw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix5Mem3 i
        (positiveRoundMix4Mem3 i
          (positiveRoundMix3Mem3 i
            (positiveRoundMix2Mem3 i
              (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem)))))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93 + 315 + 93 + 321 + 93)
      (k := k6a)
      hmem5 hmix6a
  have hmem6 :
      (positiveRoundMix6Mem3 i
        (positiveRoundMix5Mem3 i
          (positiveRoundMix4Mem3 i
            (positiveRoundMix3Mem3 i
              (positiveRoundMix2Mem3 i
                (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))))).size = 1984 :=
    positiveRoundMix6Mem3_size hmem5
  obtain ⟨k7a, hmix7a⟩ :=
    positiveRoundMix7ArgsFromMix6Raw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix6Mem3 i
        (positiveRoundMix5Mem3 i
          (positiveRoundMix4Mem3 i
            (positiveRoundMix3Mem3 i
              (positiveRoundMix2Mem3 i
                (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93 + 315 + 93 + 321 + 93 + 321)
      (k := k6)
      hmem6 hmix6
  obtain ⟨k7, hmix7⟩ :=
    positiveRoundMix7BodyFromEntryStackRaw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundMix6Mem3 i
        (positiveRoundMix5Mem3 i
          (positiveRoundMix4Mem3 i
            (positiveRoundMix3Mem3 i
              (positiveRoundMix2Mem3 i
                (positiveRoundMix1Mem3 i (positiveRoundMix0Mem3 i mem))))))) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93 + 315 + 93 + 321 + 93 + 321 + 84)
      (k := k7a)
      hmem6 hmix7a
  obtain ⟨k8, hupdate⟩ :=
    positiveRoundUpdateFromMix7Raw
      (I := I) (g := g) (s0 := s0) (acc := acc)
      (mem := positiveRoundBodyMem i mem) (i := i)
      (C := C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93 + 315 + 93 + 321 + 93 + 321 + 84 + 318)
      (k := k7)
      hi
      (by simpa [positiveRoundBodyMem] using hmix7)
  refine ⟨k8, ?_⟩
  have hcost :
      C + 315 + 93 + 321 + 93 + 321 + 93 + 321 + 93 + 315 + 93 + 321 + 93 + 321 + 84 +
          318 + 15 =
        C + positiveRoundAfterMix0EntryGas := by
    unfold positiveRoundAfterMix0EntryGas
    omega
  exact RDx.withIndices
    (by
      simpa [positiveRoundHeaderPc, positiveRoundHeaderStack, positiveRoundAfterUpdateStack]
        using hupdate)
    rfl hcost

/-- Context-level shared-mix remainder theorem in the residue interface expected by
`LoopResidues`. -/
theorem positiveRoundSharedMixRemainderTrace
    (ctx : BytecodeContext) (residue : Nat) :
    PositiveRoundResidueMixRemainderTrace ctx residue
      (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem)
      positiveRoundBodyMem := by
  intro i mem _hresidue hinv hrounds k C hrdx
  have hmem := positiveRoundHeaderInvariant.mem_size
    (positiveRoundInvariantContext.model hinv)
  have hi : i + 1 < UInt256.size := by
    have hmodel : Model.rounds ctx.executionEnv.calldata < 2 ^ 32 :=
      modelRounds_lt_uint32 ctx.executionEnv.calldata
    have hsize : 2 ^ 32 < UInt256.size := by
      native_decide
    omega
  exact positiveRoundSharedMixRemainderRaw
    (I := ctx.executionEnv)
    (g := ctx.gas)
    (s0 := ctx.initialState)
    (acc := (ctx.createdAccounts, ctx.accountMap))
    (mem := mem)
    (i := i)
    (C := C)
    (k := k)
    hmem hi hrdx

/-- For one residue, the generic selector plus the shared mix remainder reduce the body proof to
the pure/model memory-invariant preservation obligation for `positiveRoundBodyMem`. -/
theorem positiveRoundResidueBodyStep_of_shared_invariant
    (ctx : BytecodeContext) {residue : Nat}
    (hlt : residue < 10)
    (hinvStep : PositiveRoundResidueInvariantStep ctx residue positiveRoundBodyMem) :
    PositiveRoundResidueBodyStep ctx residue := by
  exact PositiveRoundResidueBodyStep.of_selector_remainder_and_invariant
    ctx residue
    (fun i mem => positiveRoundMix0EntryStack ctx.executionEnv i mem)
    positiveRoundBodyMem
    (positiveRoundResidueSelectorTrace ctx hlt)
    (positiveRoundSharedMixRemainderTrace ctx residue)
    hinvStep

/-- A complete residue-indexed invariant-preservation family gives the global arbitrary body step.

At this point all bytecode execution obligations for the round body are discharged by generic
selector/mix/update traces; only the model-memory relation remains residue-specific. -/
theorem positiveRoundBodyStep_of_shared_invariant_family
    (ctx : BytecodeContext)
    (hinvStep :
      ∀ residue, residue < 10 →
        PositiveRoundResidueInvariantStep ctx residue positiveRoundBodyMem) :
    PositiveRoundBodyStep ctx := by
  apply positiveRoundBodyStep_of_residue_family ctx
  intro residue hlt
  exact positiveRoundResidueBodyStep_of_shared_invariant ctx hlt (hinvStep residue hlt)

end Blake2f
