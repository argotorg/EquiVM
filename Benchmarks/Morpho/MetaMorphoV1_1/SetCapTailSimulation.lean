import Benchmarks.Morpho.MetaMorphoV1_1.SetCapTailRuntime

/-! Source states and bytecode returns for the cap setter's final stores. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapFinalState_source {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id cap : UInt256) :
    SourceState s0 I (setCapFinalState evm id cap).accountMap (setCapFinalState evm id cap) := by
  refine ⟨?_, ?_, rfl⟩
  · simp only [setCapFinalState, setCapValueState, storageStore_σ₀]
    exact hs.world
  · simp only [setCapFinalState, setCapValueState, storageStore_executionEnv]
    exact hs.env

theorem setCapTailSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {junk cap id ret ptr : UInt256} {R : List UInt256} {p : MarketParamsData}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hready : SetCapReady frame p id cap ptr) (hs : SourceState s0 I σ evm)
    (hcap : cap.toNat < 2 ^ 184) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13479⟩
      ([junk, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw out σ k C) :
    ∃ final mem',
      SourceState s0 I (setCapFinalState evm id cap).accountMap (setCapFinalState evm id cap) ∧
      ExecBlock config frame evm setCapTail
        (.returned final (setCapFinalState evm id cap) (some [uint256Value ptr])) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out
        (setCapFinalState evm id cap).accountMap k' C' := by
  obtain ⟨mem', aw', k', C', h⟩ := setCapTailRuntime v hstack hcap hperm hret rd
  have ha : setCapTailAccounts I σ id cap = (setCapFinalState evm id cap).accountMap := by
    rw [setCapFinalState_accounts, hs.env, ← hs.accounts]
  rw [ha] at h
  obtain ⟨final, hsource⟩ := setCapTailReturns (evm := evm) hready
  exact ⟨final, mem', setCapFinalState_source hs id cap, hsource, aw', k', C', h⟩

theorem setCapClearTimeState_source {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id : UInt256) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨13⟩ id)
        (UInt256.land (UInt256.ofNat (2 ^ 192 - 1))
          (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ id))))
      (setCapClearTimeState evm id) :=
  hs.readModifyWrite (solcMappingSlot ⟨13⟩ id)
    (fun word ↦ UInt256.land (UInt256.ofNat (2 ^ 192 - 1)) word)

theorem setCapClearAndTailSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {junk cap id ret ptr : UInt256} {R : List UInt256} {p : MarketParamsData}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hready : SetCapReady frame p id cap ptr) (hs : SourceState s0 I σ evm)
    (hcap : cap.toNat < 2 ^ 184) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13576⟩
      ([junk, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw out σ k C) :
    ∃ final mem',
      SourceState s0 I (setCapFinalState (setCapClearTimeState evm id) id cap).accountMap
        (setCapFinalState (setCapClearTimeState evm id) id cap) ∧
      ExecBlock config frame (setCapClearTimeState evm id) setCapTail
        (.returned final (setCapFinalState (setCapClearTimeState evm id) id cap)
          (some [uint256Value ptr])) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out
        (setCapFinalState (setCapClearTimeState evm id) id cap).accountMap k' C' := by
  obtain ⟨k1, C1, h1⟩ := setCapClearTimeRuntime v hstack hperm rd
  exact setCapTailSimulation v hstack hready (setCapClearTimeState_source hs id)
    hcap hperm hret h1

end Benchmarks.Morpho.MetaMorphoV1_1
