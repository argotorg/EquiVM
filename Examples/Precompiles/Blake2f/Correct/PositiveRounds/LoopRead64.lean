import Examples.Precompiles.Blake2f.Correct.PositiveRounds.LoopCanonical
import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Compression.Read64

/-!
# BLAKE2F positive-round loop with free-memory-pointer preservation

The main arbitrary-round loop invariant tracks the model regions and exact gas.  The return
allocator additionally needs the Solidity free-memory pointer at offset `64`.  This file proves a
small strengthened wrapper that carries that read through the same arbitrary-round loop, without
changing the established loop invariant.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

def positiveRoundInvariantContextRead64
    (ctx : BytecodeContext) (i : Nat) (mem : ByteArray) : Prop :=
  positiveRoundInvariantContext ctx i mem ∧
    mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984)

theorem positiveRoundInvariantContextRead64.invariant
    {ctx : BytecodeContext} {i : Nat} {mem : ByteArray}
    (h : positiveRoundInvariantContextRead64 ctx i mem) :
    positiveRoundInvariantContext ctx i mem :=
  h.1

theorem positiveRoundInvariantContextRead64.read64
    {ctx : BytecodeContext} {i : Nat} {mem : ByteArray}
    (h : positiveRoundInvariantContextRead64 ctx i mem) :
    mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984) :=
  h.2

/-- Header-to-header canonical round step preserving the offset-`64` free-memory-pointer read. -/
theorem positiveRoundRead64HeaderStep
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {i : Nat} {mem : ByteArray}
    (hinv : positiveRoundInvariantContextRead64 ctx i mem)
    (hrounds : i < Model.rounds ctx.executionEnv.calldata)
    {k C : Nat}
    (hrdx : RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
      positiveRoundHeaderPc
      (positiveRoundHeaderStack ctx.executionEnv i)
      mem (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C) :
    ∃ k',
      positiveRoundInvariantContextRead64 ctx (i + 1) (positiveRoundBodyMem i mem) ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundHeaderPc
        (positiveRoundHeaderStack ctx.executionEnv (i + 1))
        (positiveRoundBodyMem i mem) (UInt256.ofNat 62) ByteArray.empty
        (ctx.createdAccounts, ctx.accountMap) k' (C + positiveRoundDelta i) := by
  obtain ⟨kg, hguard⟩ :=
    positiveRoundGuardContinueOfModelRoundsGt ctx hvalid hrounds
      (by exact ⟨k, hrdx⟩)
  obtain ⟨kb, hinvNext, hnext⟩ :=
    positiveRoundCanonicalBodyStep_from_trace ctx hvalid
      (positiveRoundInvariantContextRead64.invariant hinv) hrounds hguard
  have hmem : mem.size = 1984 :=
    positiveRoundHeaderInvariant.mem_size
      (positiveRoundInvariantContext.model
        (positiveRoundInvariantContextRead64.invariant hinv))
  refine ⟨kb, ?_, ?_⟩
  · constructor
    · exact hinvNext
    · rw [positiveRoundBodyMem_read64 hmem]
      exact positiveRoundInvariantContextRead64.read64 hinv
  · have hcost : C + 23 + positiveRoundBodyDelta i = C + positiveRoundDelta i := by
      rw [positiveRoundDelta_decompose]
      omega
    exact RDx.withIndices hnext rfl hcost

def positiveRoundRead64LoopInv (ctx : BytecodeContext)
    (remaining : Nat) (st : PositiveRoundLoopState) : Prop :=
  st.index + remaining = Model.rounds ctx.executionEnv.calldata ∧
    positiveRoundInvariantContextRead64 ctx st.index st.mem

/-- Arbitrary-round positive-loop theorem carrying the offset-`64` free-memory-pointer read. -/
theorem positiveRoundLoopRead64FromInvariant
    (ctx : BytecodeContext)
    (hvalid : valid ctx)
    {mem0 : ByteArray}
    (hinv0 : positiveRoundInvariantContextRead64 ctx 0 mem0) :
    ∃ memFinal k,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundExitPc
        (positiveRoundHeaderStack ctx.executionEnv (Model.rounds ctx.executionEnv.calldata))
        memFinal (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23) := by
  let rounds := Model.rounds ctx.executionEnv.calldata
  let st0 : PositiveRoundLoopState := { index := 0, mem := mem0 }
  have hInv0 : positiveRoundRead64LoopInv ctx rounds st0 := by
    simp [positiveRoundRead64LoopInv, st0, rounds, hinv0]
  obtain ⟨k0, hrdx0⟩ :=
    positiveRoundInvariantContext.rdx
      (positiveRoundInvariantContextRead64.invariant hinv0)
  have hexit :
      ∀ st, positiveRoundRead64LoopInv ctx 0 st → ∀ k C,
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundHeaderPc (positiveRoundLoopStack ctx st) st.mem (UInt256.ofNat 62)
          ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ k',
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            positiveRoundExitPc (positiveRoundLoopExitStack ctx st) st.mem (UInt256.ofNat 62)
            ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k'
            (C + positiveRoundRemainingGas st.index 0) := by
    intro st hInv k C hrdx
    have hrel : st.index + 0 = Model.rounds ctx.executionEnv.calldata := hInv.1
    have hrounds : Model.rounds ctx.executionEnv.calldata = st.index := by
      omega
    have hprefix : positiveRoundHeaderRDxContext ctx st.index st.mem C := by
      exact ⟨k, by simpa [positiveRoundLoopStack] using hrdx⟩
    simpa [positiveRoundLoopExitStack, positiveRoundRemainingGas] using
      positiveRoundGuardExitOfModelRoundsEq
        ctx hvalid hrounds hprefix
  have hstep :
      ∀ v st, positiveRoundRead64LoopInv ctx (v + 1) st → ∀ k C,
        RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
          positiveRoundHeaderPc (positiveRoundLoopStack ctx st) st.mem (UInt256.ofNat 62)
          ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k C →
        ∃ st' k' dC,
          positiveRoundRead64LoopInv ctx v st' ∧
          positiveRoundRemainingGas st.index (v + 1) =
            dC + positiveRoundRemainingGas st'.index v ∧
          RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
            positiveRoundHeaderPc (positiveRoundLoopStack ctx st') st'.mem (UInt256.ofNat 62)
            ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k' (C + dC) := by
    intro v st hInv k C hrdx
    have hrel : st.index + (v + 1) = Model.rounds ctx.executionEnv.calldata := hInv.1
    have hlt : st.index < Model.rounds ctx.executionEnv.calldata := by
      omega
    obtain ⟨k', hinv', hnext⟩ :=
      positiveRoundRead64HeaderStep
        ctx hvalid hInv.2 hlt (by simpa [positiveRoundLoopStack] using hrdx)
    let st' : PositiveRoundLoopState := { index := st.index + 1, mem := positiveRoundBodyMem st.index st.mem }
    refine ⟨st', k', positiveRoundDelta st.index, ?_, ?_, ?_⟩
    · constructor
      · simp [st']
        omega
      · simpa [st'] using hinv'
    · simp [st']
    · simpa [positiveRoundLoopStack, st'] using hnext
  obtain ⟨stFinal, kFinal, hInvFinal, hrdxFinal⟩ :=
    RDx.whileLoopCarryGas
      (code := runtimeBytecode)
      (ee := ctx.executionEnv)
      (g := ctx.gas)
      (s0 := ctx.initialState)
      (rdata := ByteArray.empty)
      (acc := (ctx.createdAccounts, ctx.accountMap))
      positiveRoundHeaderPc
      positiveRoundExitPc
      (positiveRoundRead64LoopInv ctx)
      (positiveRoundLoopStack ctx)
      (fun st => st.mem)
      (fun _ => UInt256.ofNat 62)
      (positiveRoundLoopExitStack ctx)
      (fun remaining st => positiveRoundRemainingGas st.index remaining)
      hexit hstep
      rounds st0 hInv0 k0
      (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) 0)
      (by simpa [positiveRoundLoopStack, st0] using hrdx0)
  have hidx : stFinal.index = Model.rounds ctx.executionEnv.calldata := by
    have hrel : stFinal.index + 0 = Model.rounds ctx.executionEnv.calldata := hInvFinal.1
    omega
  have hcost :
      positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx) 0 +
          positiveRoundRemainingGas 0 rounds =
        positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23 := by
    simpa [rounds] using
      positiveRoundHeaderGas_add_remaining
        (positiveRoundFinalFlagSet ctx) 0 rounds
  refine ⟨stFinal.mem, kFinal, ?_, ?_⟩
  · simpa [hidx] using hInvFinal.2
  · have hrdxCost := RDx.withIndices hrdxFinal rfl hcost
    simpa [positiveRoundLoopExitStack, hidx] using hrdxCost

theorem positiveRoundInitialInvariantZeroRead64
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    positiveRoundInvariantContextRead64 ctx 0 (v13MixedMem ctx.executionEnv) := by
  have hvalidAll : valid ctx := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  constructor
  · exact positiveRoundInitialInvariantZero ctx hcode haccepts hvalidAll hbyte
  · exact v13MixedMem_read64 ctx.executionEnv (by simpa [Model.inputLength] using hlen)

theorem positiveRoundInitialInvariantOneRead64
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    positiveRoundInvariantContextRead64 ctx 0 (v14FinalFlagMem ctx.executionEnv) := by
  have hvalidAll : valid ctx := hvalid
  obtain ⟨hlen, _hflag⟩ := hvalid
  constructor
  · exact positiveRoundInitialInvariantOne ctx hcode haccepts hvalidAll hbyte
  · exact v14FinalFlagMem_read64 ctx.executionEnv (by simpa [Model.inputLength] using hlen)

theorem positiveRoundLoopZeroRead64_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 0) :
    ∃ memFinal k,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundExitPc
        (positiveRoundHeaderStack ctx.executionEnv (Model.rounds ctx.executionEnv.calldata))
        memFinal (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23) := by
  exact positiveRoundLoopRead64FromInvariant ctx hvalid
    (positiveRoundInitialInvariantZeroRead64 ctx hcode haccepts hvalid hbyte)

theorem positiveRoundLoopOneRead64_from_trace
    (ctx : BytecodeContext)
    (hcode : ctx.executionEnv.code = runtimeBytecode)
    (haccepts : accepts ctx)
    (hvalid : valid ctx)
    (hbyte : ctx.executionEnv.calldata[212]! = 1) :
    ∃ memFinal k,
      positiveRoundInvariantContextRead64 ctx
        (Model.rounds ctx.executionEnv.calldata) memFinal ∧
      RDx runtimeBytecode ctx.executionEnv ctx.gas ctx.initialState
        positiveRoundExitPc
        (positiveRoundHeaderStack ctx.executionEnv (Model.rounds ctx.executionEnv.calldata))
        memFinal (UInt256.ofNat 62) ByteArray.empty (ctx.createdAccounts, ctx.accountMap) k
        (positiveRoundHeaderGas (positiveRoundFinalFlagSet ctx)
          (Model.rounds ctx.executionEnv.calldata) + 23) := by
  exact positiveRoundLoopRead64FromInvariant ctx hvalid
    (positiveRoundInitialInvariantOneRead64 ctx hcode haccepts hvalid hbyte)

end Blake2f
