import Reasoning.Reach

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.sdiv_xstep to the SMOD binary opcode.
theorem smod_xstep {s : State} {code : ByteArray} {pc a b : UInt256} {R : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.SMOD, .none))
    (hstack : s.machineState.stack = a :: b :: R) (hov : R.length+1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
      else .ok (stBinop5 s (UInt256.smod a b) R, .none) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SMOD, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_smod s hd, hstack]
  have hov' : ¬ (a :: b :: R).length - 2 + 1 > 1024 := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Glow, stBinop5]

-- LIBRARY CANDIDATE: the generic reachability step for signed remainder.
theorem rdSmod {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {a b : UInt256} {R : List UInt256}
    (h : RD code I g s0 pc (a :: b :: R) mem aw rdata σ k C)
    (hdec : decode code pc = some (.SMOD, .none)) (hov : R.length+1 ≤ 1024) :
    RD code I g s0 (pc+⟨1⟩) (UInt256.smod a b :: R) mem aw rdata σ (k+1) (C+5) :=
  h.stepBinop5 (fun _ hc hp hs => smod_xstep hc hp hdec hs hov)

end Benchmarks.UniswapV4PoolManager
