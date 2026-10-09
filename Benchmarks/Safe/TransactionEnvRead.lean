import Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: transaction environment fields pushed by ORIGIN and GASPRICE.
inductive TransactionEnvField where
  | origin
  | gasPrice

def TransactionEnvField.op : TransactionEnvField → Operation
  | .origin => .ORIGIN
  | .gasPrice => .GASPRICE

def TransactionEnvField.word (field : TransactionEnvField) (I : ExecutionEnv) : UInt256 :=
  match field with
  | .origin => UInt256.ofNat I.sender.val
  | .gasPrice => UInt256.ofNat I.gasPrice

def transactionEnvReadState (field : TransactionEnvField) (s : State) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := field.word s.executionEnv :: s.machineState.stack,
      execLength := s.machineState.execLength + 1,
      gasAvailable := s.machineState.gasAvailable.subNat 2 } }

theorem transactionEnvReadStep (field : TransactionEnvField)
    {s : State} {code : ByteArray} {pc : UInt256} {stk : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (field.op, .none))
    (hstk : s.machineState.stack = stk) (hov : stk.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 2 then .error .OutOfGass
      else .ok (transactionEnvReadState field s, .none) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (field.op, .none) := by
    rw [hcode, hpc]; exact hdec
  have ho : ¬ (s.machineState.stack.length - 0 + 1 > 1024) := by rw [hstk]; omega
  cases field with
  | origin =>
    rw [← hcode, step_origin s hd]
    simp only [ho, if_false, GasConstants.Gbase, transactionEnvReadState,
      TransactionEnvField.word]
  | gasPrice =>
    rw [← hcode, step_gasprice s hd]
    simp only [ho, if_false, GasConstants.Gbase, transactionEnvReadState,
      TransactionEnvField.word]

-- GENERALIZES RD.caller to the other transaction environment words with the same gas cost.
theorem transactionEnvRead (field : TransactionEnvField)
    {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : AccountMap} {k C : Nat}
    (h : RD code I g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (field.op, .none)) (hov : stk.length + 1 ≤ 1024) :
    RD code I g s0 (pc + ⟨1⟩) (field.word I :: stk) mem aw rdata acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog |
    ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := transactionEnvReadStep field hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨transactionEnvReadState field s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcode
      · simp only [transactionEnvReadState, hpc]
      · simp only [transactionEnvReadState, hstk, hee]
      · simp only [transactionEnvReadState, hgas, Sat256.subNat_sub_add_of_sub_sub]
      · exact hmem
      · exact haw
      · exact hrdata
      · exact hacc
      · exact hee
      · exact hworld

end Benchmarks.Safe
