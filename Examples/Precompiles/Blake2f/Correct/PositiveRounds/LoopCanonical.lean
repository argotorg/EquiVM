import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopVectorMix7

/-!
# BLAKE2F positive-round canonical body step

The existing `PositiveRoundBodyStep` interface existentially packages the next memory.  For carrying
extra bytecode-memory facts, such as the free-memory pointer at offset `64`, it is useful to expose
the concrete next memory transformer `positiveRoundBodyMem i mem`.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Canonical arbitrary-round body step: from the body PC, the next loop-header memory is exactly
`positiveRoundBodyMem i mem`. -/
theorem positiveRoundCanonicalBodyStep_from_trace
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {i : Nat} {mem : ByteArray}
    (hinv : positiveRoundInvariantContext ctx i mem)
    (hrounds : i < Model.rounds ctx.executionEnv.calldata)
    {k C : Nat}
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundBodyPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k',
      positiveRoundInvariantContext ctx (i + 1) (positiveRoundBodyMem i mem) ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundHeaderPc
        (positiveRoundHeaderStack ctx.executionEnv (i + 1))
        (positiveRoundBodyMem i mem) (UInt256.ofNat 62) ByteArray.empty
        (ctx.createdAccounts, ctx.accountMap) k' (C + positiveRoundBodyDelta i) := by
  obtain ⟨ks, hselector⟩ :=
    positiveRoundSelectorTrace ctx hinv hrounds hrdx
  obtain ⟨kr, hremainder⟩ :=
    positiveRoundSharedMixRemainderTrace ctx (i % 10) rfl hinv hrounds hselector
  have hstatic : PositiveRoundBodyStaticRegions ctx.executionEnv i mem :=
    positiveRoundBodyStaticRegions_of_invariantContext hinv
  have hvector : PositiveRoundBodyVectorRegion ctx.executionEnv i mem :=
    positiveRoundBodyVectorRegion_of_invariantContext hinv
  have hinvNext :
      positiveRoundInvariantContext ctx (i + 1) (positiveRoundBodyMem i mem) := by
    have hmodel := positiveRoundInvariantContext.model hinv
    constructor
    · exact positiveRoundBodyHeaderRDx_of_trace ctx hvalid hinv hrounds
    · constructor
      · exact Nat.succ_le_of_lt hrounds
      constructor
      · exact positiveRoundBodyMem_size (positiveRoundHeaderInvariant.mem_size hmodel)
      constructor
      · exact hstatic.1
      constructor
      · exact hstatic.2.1
      constructor
      · exact hstatic.2.2
      · simpa [PositiveRoundBodyVectorRegion] using hvector
  refine ⟨kr, hinvNext, ?_⟩
  have hcost :
      C + sigmaSelectorToMix0Gas i + positiveRoundAfterMix0EntryGas =
        C + positiveRoundBodyDelta i := by
    unfold positiveRoundBodyDelta
    omega
  exact RDx.withIndices hremainder rfl hcost

/-- The canonical body transformer preserves the free-memory pointer read at offset `64`. -/
theorem positiveRoundBodyMem_read64
    {i : Nat} {mem : ByteArray}
    (hmem : mem.size = 1984) :
    (positiveRoundBodyMem i mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  exact positiveRoundBodyMem_read_below_vBase
    (i := i) (mem := mem) (read := 64) hmem (by decide)

end Blake2f
