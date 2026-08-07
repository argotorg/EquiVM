import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopRemainder
import Reasoning.MemCascade

/-!
# BLAKE2F positive-round invariant preservation interface

The bytecode-side arbitrary round body is already assembled in `LoopRemainder`.  The remaining
proof obligation is semantic: show that the resulting memory `positiveRoundBodyMem i mem`
preserves the parsed `h`, `m`, and `t` regions and stores the pure model's next working vector.

This file packages that obligation into small predicates and proves that they are exactly enough
to discharge `PositiveRoundResidueInvariantStep`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Static parsed-memory regions that should be unchanged by the positive-round body. -/
def PositiveRoundBodyStaticRegions
    (I : ExecutionEnv) (i : Nat) (mem : ByteArray) : Prop :=
  memoryRepresentsH (positiveRoundBodyMem i mem) (Model.parsedH I.calldata) ∧
  memoryRepresentsM (positiveRoundBodyMem i mem) (Model.parsedM I.calldata) ∧
  memoryRepresentsT (positiveRoundBodyMem i mem)
    (Model.parsedT0 I.calldata) (Model.parsedT1 I.calldata)

/-- Dynamic working-vector region after one bytecode round. -/
def PositiveRoundBodyVectorRegion
    (I : ExecutionEnv) (i : Nat) (mem : ByteArray) : Prop :=
  memoryRepresentsVector (positiveRoundBodyMem i mem)
    (positiveRoundModelState I.calldata (i + 1))

/-- Chronological 32-byte writes performed by the eight `mixG` calls in one positive round.

The words are intentionally written in terms of the same intermediate memories used by
`positiveRoundBodyMem`, so this list is definitionally equal to the body memory transformer when
interpreted by `writeCascade`. -/
def positiveRoundBodyWrites (i : Nat) (mem : ByteArray) : List (Nat × UInt256) :=
  let mem0 := positiveRoundMix0Mem3 i mem
  let mem1 := positiveRoundMix1Mem3 i mem0
  let mem2 := positiveRoundMix2Mem3 i mem1
  let mem3 := positiveRoundMix3Mem3 i mem2
  let mem4 := positiveRoundMix4Mem3 i mem3
  let mem5 := positiveRoundMix5Mem3 i mem4
  let mem6 := positiveRoundMix6Mem3 i mem5
  [(1472, positiveRoundMix0A1 mem i),
    (1600, positiveRoundMix0B1 mem i),
    (1728, positiveRoundMix0C1 mem i),
    (1856, positiveRoundMix0D1 mem i),
    (1504, positiveRoundMix1A1 mem0 i),
    (1632, positiveRoundMix1B1 mem0 i),
    (1760, positiveRoundMix1C1 mem0 i),
    (1888, positiveRoundMix1D1 mem0 i),
    (1536, positiveRoundMix2A1 mem1 i),
    (1664, positiveRoundMix2B1 mem1 i),
    (1792, positiveRoundMix2C1 mem1 i),
    (1920, positiveRoundMix2D1 mem1 i),
    (1568, positiveRoundMix3A1 mem2 i),
    (1696, positiveRoundMix3B1 mem2 i),
    (1824, positiveRoundMix3C1 mem2 i),
    (1952, positiveRoundMix3D1 mem2 i),
    (1472, positiveRoundMix4A1 mem3 i),
    (1632, positiveRoundMix4B1 mem3 i),
    (1792, positiveRoundMix4C1 mem3 i),
    (1952, positiveRoundMix4D1 mem3 i),
    (1504, positiveRoundMix5A1 mem4 i),
    (1664, positiveRoundMix5B1 mem4 i),
    (1824, positiveRoundMix5C1 mem4 i),
    (1856, positiveRoundMix5D1 mem4 i),
    (1536, positiveRoundMix6A1 mem5 i),
    (1696, positiveRoundMix6B1 mem5 i),
    (1728, positiveRoundMix6C1 mem5 i),
    (1888, positiveRoundMix6D1 mem5 i),
    (1568, positiveRoundMix7A1 mem6 i),
    (1600, positiveRoundMix7B1 mem6 i),
    (1760, positiveRoundMix7C1 mem6 i),
    (1920, positiveRoundMix7D1 mem6 i)]

theorem positiveRoundBodyMem_eq_writeCascade (i : Nat) (mem : ByteArray) :
    positiveRoundBodyMem i mem =
      writeCascade mem (positiveRoundBodyWrites i mem) := by
  rfl

private theorem WindowDisjointFromWrites_below_vBase
    {writes : List (Nat × UInt256)} {read : Nat}
    (hlo : ∀ p ∈ writes, vBaseOffset ≤ p.1)
    (hhi : ∀ p ∈ writes, p.1 + 32 ≤ 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    WindowDisjointFromWrites 1984 read 32 writes := by
  induction writes with
  | nil =>
      trivial
  | cons p rest ih =>
      rcases p with ⟨off, word⟩
      have hoffLo : vBaseOffset ≤ off := hlo (off, word) (by simp)
      have hoffHi : off + 32 ≤ 1984 := hhi (off, word) (by simp)
      constructor
      · have hsub : off - 1984 = 0 := by
          omega
        rw [hsub]
        native_decide
      constructor
      · left
        constructor
        · unfold vBaseOffset at hbelow hoffLo
          omega
        · unfold vBaseOffset at hbelow
          omega
      · have hmax : max 1984 (off + 32) = 1984 := by
          omega
        simpa [hmax] using ih
          (fun p hp => hlo p (by simp [hp]))
          (fun p hp => hhi p (by simp [hp]))

private theorem positiveRoundBodyWrites_offsets_ge_vBase
    (i : Nat) (mem : ByteArray) :
    ∀ p ∈ positiveRoundBodyWrites i mem, vBaseOffset ≤ p.1 := by
  intro p hp
  simp [positiveRoundBodyWrites] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [vBaseOffset]

private theorem positiveRoundBodyWrites_offsets_le_end
    (i : Nat) (mem : ByteArray) :
    ∀ p ∈ positiveRoundBodyWrites i mem, p.1 + 32 ≤ 1984 := by
  intro p hp
  simp [positiveRoundBodyWrites] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

/-- The full body memory transformer preserves any 32-byte read below `vBaseOffset`. -/
theorem positiveRoundBodyMem_read_below_vBase
    {i : Nat} {mem : ByteArray} {read : Nat}
    (hmem : mem.size = 1984)
    (hbelow : read + 32 ≤ vBaseOffset) :
    (positiveRoundBodyMem i mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [positiveRoundBodyMem_eq_writeCascade]
  exact writeCascade_read_preserved_of_base mem (positiveRoundBodyWrites i mem)
    (hbase := hmem)
    (WindowDisjointFromWrites_below_vBase
      (positiveRoundBodyWrites_offsets_ge_vBase i mem)
      (positiveRoundBodyWrites_offsets_le_end i mem)
      hbelow)

private theorem memorySlotStoresU64_positiveRoundBodyMem_of_below_vBase
    {i : Nat} {mem : ByteArray} {off : Nat} {w : UInt64}
    (hmem : mem.size = 1984)
    (hbelow : off + 32 ≤ vBaseOffset)
    (hslot : memorySlotStoresU64 mem off w) :
    memorySlotStoresU64 (positiveRoundBodyMem i mem) off w := by
  unfold memorySlotStoresU64 memoryWord at *
  rw [positiveRoundBodyMem_read_below_vBase hmem hbelow]
  exact hslot

/-- `positiveRoundBodyMem` preserves the parsed `h`, `m`, and `t` regions from the loop-header
invariant. -/
theorem positiveRoundBodyStaticRegions_of_headerInvariant
    {I : ExecutionEnv} {i : Nat} {mem : ByteArray}
    (hinv : positiveRoundHeaderInvariant I i mem) :
    PositiveRoundBodyStaticRegions I i mem := by
  have hmem := positiveRoundHeaderInvariant.mem_size hinv
  constructor
  · obtain ⟨hsize, hslots⟩ := positiveRoundHeaderInvariant.representsH hinv
    constructor
    · exact hsize
    · intro j hj
      exact memorySlotStoresU64_positiveRoundBodyMem_of_below_vBase hmem
        (by unfold hSlotOffset hBaseOffset wordBytes vBaseOffset; omega)
        (hslots j hj)
  constructor
  · obtain ⟨msize, mslots⟩ := positiveRoundHeaderInvariant.representsM hinv
    constructor
    · exact msize
    · intro j hj
      exact memorySlotStoresU64_positiveRoundBodyMem_of_below_vBase hmem
        (by unfold mSlotOffset mBaseOffset wordBytes vBaseOffset; omega)
        (mslots j hj)
  · obtain ⟨ht0, ht1⟩ := positiveRoundHeaderInvariant.representsT hinv
    constructor
    · exact memorySlotStoresU64_positiveRoundBodyMem_of_below_vBase hmem
        (by unfold tSlotOffset tBaseOffset wordBytes vBaseOffset; omega)
        ht0
    · exact memorySlotStoresU64_positiveRoundBodyMem_of_below_vBase hmem
        (by unfold tSlotOffset tBaseOffset wordBytes vBaseOffset; omega)
        ht1

/-- Context-level static-region preservation. -/
theorem positiveRoundBodyStaticRegions_of_invariantContext
    {ctx : BytecodeContext} {i : Nat} {mem : ByteArray}
    (hinv : positiveRoundInvariantContext ctx i mem) :
    PositiveRoundBodyStaticRegions ctx.executionEnv i mem :=
  positiveRoundBodyStaticRegions_of_headerInvariant
    (positiveRoundInvariantContext.model hinv)

/-- Canonical RDx header fact required by `positiveRoundInvariantContext` after one body step. -/
def PositiveRoundBodyHeaderRDx
    (ctx : BytecodeContext) (i : Nat) (mem : ByteArray) : Prop :=
  positiveRoundHeaderRDxContext ctx (i + 1) (positiveRoundBodyMem i mem)
    (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) (i + 1))

/-- The bytecode traces already prove the canonical next-header RDx fact needed by
`positiveRoundInvariantContext`. -/
theorem positiveRoundBodyHeaderRDx_of_trace
    (ctx : BytecodeContext)
    (hvalid : valid ctx) :
    ∀ {i : Nat} {mem : ByteArray},
      positiveRoundInvariantContext ctx i mem →
      i < Model.rounds ctx.executionEnv.calldata →
      PositiveRoundBodyHeaderRDx ctx i mem := by
  intro i mem hinv hrounds
  obtain ⟨kg, hguard⟩ :=
    positiveRoundInvariantGuardContinue ctx hvalid hinv hrounds
  obtain ⟨ks, hselector⟩ :=
    positiveRoundSelectorTrace ctx hinv hrounds hguard
  obtain ⟨kr, hremainder⟩ :=
    positiveRoundSharedMixRemainderTrace ctx (i % 10) rfl hinv hrounds hselector
  refine ⟨kr, ?_⟩
  have hcost :
      (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) i + 23 +
          sigmaSelectorToMix0Gas i) + positiveRoundAfterMix0EntryGas =
        positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) (i + 1) := by
    rw [positiveRoundHeaderGas_succ_decompose]
    unfold positiveRoundGuardGas positiveRoundBodyDelta
    omega
  exact RDx.withIndices hremainder rfl hcost

/-- Static-region preservation plus vector-region correctness are sufficient for the residue
invariant step expected by the arbitrary-round loop driver. -/
theorem positiveRoundResidueInvariantStep_of_body_memory_regions
    (ctx : BytecodeContext) (residue : Nat)
    (hrdx :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyHeaderRDx ctx i mem)
    (hstatic :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyStaticRegions ctx.executionEnv i mem)
    (hvector :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyVectorRegion ctx.executionEnv i mem) :
    PositiveRoundResidueInvariantStep ctx residue positiveRoundBodyMem := by
  intro i mem hresidue hinv hrounds
  have hmodel := positiveRoundInvariantContext.model hinv
  have hmem : mem.size = 1984 := positiveRoundHeaderInvariant.mem_size hmodel
  have hr := hrdx hresidue hinv hrounds
  have hs := hstatic hresidue hinv hrounds
  have hv := hvector hresidue hinv hrounds
  constructor
  · simpa [PositiveRoundBodyHeaderRDx] using hr
  · constructor
    · exact Nat.succ_le_of_lt hrounds
    constructor
    · exact positiveRoundBodyMem_size hmem
    constructor
    · exact hs.1
    constructor
    · exact hs.2.1
    constructor
    · exact hs.2.2
    · simpa [PositiveRoundBodyVectorRegion] using hv

/-- Variant of `positiveRoundResidueInvariantStep_of_body_memory_regions` that derives the
canonical RDx component from the already-proven bytecode traces.  Users of this theorem only need
to prove the semantic memory facts. -/
theorem positiveRoundResidueInvariantStep_of_body_memory_regions_from_trace
    (ctx : BytecodeContext) (hvalid : valid ctx) (residue : Nat)
    (hstatic :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyStaticRegions ctx.executionEnv i mem)
    (hvector :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyVectorRegion ctx.executionEnv i mem) :
    PositiveRoundResidueInvariantStep ctx residue positiveRoundBodyMem := by
  exact positiveRoundResidueInvariantStep_of_body_memory_regions ctx residue
    (fun _hresidue hinv hrounds =>
      positiveRoundBodyHeaderRDx_of_trace ctx hvalid hinv hrounds)
    hstatic hvector

/-- A residue body step can now be produced from the two model-memory region facts. -/
theorem positiveRoundResidueBodyStep_of_body_memory_regions
    (ctx : BytecodeContext) {residue : Nat}
    (hlt : residue < 10)
    (hrdx :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyHeaderRDx ctx i mem)
    (hstatic :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyStaticRegions ctx.executionEnv i mem)
    (hvector :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyVectorRegion ctx.executionEnv i mem) :
    PositiveRoundResidueBodyStep ctx residue := by
  exact positiveRoundResidueBodyStep_of_shared_invariant ctx hlt
    (positiveRoundResidueInvariantStep_of_body_memory_regions ctx residue hrdx hstatic hvector)

/-- Residue body step from semantic memory facts; the canonical RDx part is supplied by the
generic bytecode trace composition. -/
theorem positiveRoundResidueBodyStep_of_body_memory_regions_from_trace
    (ctx : BytecodeContext) (hvalid : valid ctx) {residue : Nat}
    (hlt : residue < 10)
    (hstatic :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyStaticRegions ctx.executionEnv i mem)
    (hvector :
      ∀ {i : Nat} {mem : ByteArray},
        i % 10 = residue →
        positiveRoundInvariantContext ctx i mem →
        i < Model.rounds ctx.executionEnv.calldata →
        PositiveRoundBodyVectorRegion ctx.executionEnv i mem) :
    PositiveRoundResidueBodyStep ctx residue := by
  exact positiveRoundResidueBodyStep_of_shared_invariant ctx hlt
    (positiveRoundResidueInvariantStep_of_body_memory_regions_from_trace
      ctx hvalid residue hstatic hvector)

/-- Global arbitrary-round body step from residue-indexed static/vector memory facts. -/
theorem positiveRoundBodyStep_of_body_memory_regions
    (ctx : BytecodeContext)
    (hrdx :
      ∀ residue, residue < 10 →
        ∀ {i : Nat} {mem : ByteArray},
          i % 10 = residue →
          positiveRoundInvariantContext ctx i mem →
          i < Model.rounds ctx.executionEnv.calldata →
          PositiveRoundBodyHeaderRDx ctx i mem)
    (hstatic :
      ∀ residue, residue < 10 →
        ∀ {i : Nat} {mem : ByteArray},
          i % 10 = residue →
          positiveRoundInvariantContext ctx i mem →
          i < Model.rounds ctx.executionEnv.calldata →
          PositiveRoundBodyStaticRegions ctx.executionEnv i mem)
    (hvector :
      ∀ residue, residue < 10 →
        ∀ {i : Nat} {mem : ByteArray},
          i % 10 = residue →
          positiveRoundInvariantContext ctx i mem →
          i < Model.rounds ctx.executionEnv.calldata →
          PositiveRoundBodyVectorRegion ctx.executionEnv i mem) :
    PositiveRoundBodyStep ctx := by
  exact positiveRoundBodyStep_of_shared_invariant_family ctx
    (fun residue hlt =>
      positiveRoundResidueInvariantStep_of_body_memory_regions ctx residue
        (hrdx residue hlt)
        (hstatic residue hlt)
        (hvector residue hlt))

/-- Global arbitrary-round body step from residue-indexed semantic memory facts; all bytecode
trace and gas obligations are discharged by the generic trace composition. -/
theorem positiveRoundBodyStep_of_body_memory_regions_from_trace
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    (hstatic :
      ∀ residue, residue < 10 →
        ∀ {i : Nat} {mem : ByteArray},
          i % 10 = residue →
          positiveRoundInvariantContext ctx i mem →
          i < Model.rounds ctx.executionEnv.calldata →
          PositiveRoundBodyStaticRegions ctx.executionEnv i mem)
    (hvector :
      ∀ residue, residue < 10 →
        ∀ {i : Nat} {mem : ByteArray},
          i % 10 = residue →
          positiveRoundInvariantContext ctx i mem →
          i < Model.rounds ctx.executionEnv.calldata →
          PositiveRoundBodyVectorRegion ctx.executionEnv i mem) :
    PositiveRoundBodyStep ctx := by
  exact positiveRoundBodyStep_of_shared_invariant_family ctx
    (fun residue hlt =>
      positiveRoundResidueInvariantStep_of_body_memory_regions_from_trace ctx hvalid residue
        (hstatic residue hlt)
        (hvector residue hlt))

/-- Global arbitrary-round body step from residue-indexed vector-region correctness only.

The static parsed-memory regions and the exact RDx/gas component are discharged generically. -/
theorem positiveRoundBodyStep_of_vector_regions_from_trace
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    (hvector :
      ∀ residue, residue < 10 →
        ∀ {i : Nat} {mem : ByteArray},
          i % 10 = residue →
          positiveRoundInvariantContext ctx i mem →
          i < Model.rounds ctx.executionEnv.calldata →
          PositiveRoundBodyVectorRegion ctx.executionEnv i mem) :
    PositiveRoundBodyStep ctx := by
  exact positiveRoundBodyStep_of_body_memory_regions_from_trace ctx hvalid
    (fun _residue _hlt => by
      intro _i _mem _hresidue hinv _hrounds
      exact positiveRoundBodyStaticRegions_of_invariantContext hinv)
    hvector

end Blake2f
