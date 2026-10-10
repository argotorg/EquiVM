import Benchmarks.UniswapV4PoolManager.MemoryFootprint

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: each live stack word accounts for at least two operation gas.
noncomputable def operationPotential (s : State) : Nat :=
  2*s.machineState.stack.length+memoryFootprint s.machineState.memory

theorem pop_length {stack rest : Stack UInt256} {a : UInt256}
    (h : stack.pop = some (rest, a)) : stack.length = rest.length+1 := by
  cases stack <;> simp_all [Stack.pop]

theorem pop2_length {stack rest : Stack UInt256} {a b : UInt256}
    (h : stack.pop2 = some (rest, a, b)) : stack.length = rest.length+2 := by
  rcases stack with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp_all [Stack.pop2]

theorem pop3_length {stack rest : Stack UInt256} {a b c : UInt256}
    (h : stack.pop3 = some (rest, a, b, c)) : stack.length = rest.length+3 := by
  rcases stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [Stack.pop3]

theorem pop4_length {stack rest : Stack UInt256} {a b c d : UInt256}
    (h : stack.pop4 = some (rest, a, b, c, d)) : stack.length = rest.length+4 := by
  rcases stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp_all [Stack.pop4]

theorem pop5_length {stack rest : Stack UInt256} {a b c d e : UInt256}
    (h : stack.pop5 = some (rest, a, b, c, d, e)) : stack.length = rest.length+5 := by
  rcases stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩ <;> simp_all [Stack.pop5]

theorem pop6_length {stack rest : Stack UInt256} {a b c d e f : UInt256}
    (h : stack.pop6 = some (rest, a, b, c, d, e, f)) : stack.length = rest.length+6 := by
  rcases stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, rest⟩⟩⟩⟩⟩⟩ <;>
    simp_all [Stack.pop6]

theorem pop7_length {stack rest : Stack UInt256} {a b c d e f g : UInt256}
    (h : stack.pop7 = some (rest, a, b, c, d, e, f, g)) : stack.length = rest.length+7 := by
  rcases stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all [Stack.pop7]

theorem execUnOp_potential {f : Primop.Unary} {s s' : State}
    (h : execUnOp f s = .ok s') : operationPotential s' = operationPotential s := by
  unfold execUnOp at h
  split at h
  · rename_i rest a hp
    have hs := pop_length hp
    simp only [Id.run] at h
    injection h with he
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Stack.push, List.length_cons, hs]
  · contradiction

theorem execBinOp_potential {f : Primop.Binary} {s s' : State}
    (h : execBinOp f s = .ok s') : operationPotential s' ≤ operationPotential s := by
  unfold execBinOp at h
  split at h
  · rename_i rest a b hp
    have hs := pop2_length hp
    simp only [Id.run] at h
    injection h with he
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Stack.push, List.length_cons, hs]
    omega
  · contradiction

theorem execTriOp_potential {f : Primop.Ternary} {s s' : State}
    (h : execTriOp f s = .ok s') : operationPotential s' ≤ operationPotential s := by
  unfold execTriOp at h
  split at h
  · rename_i rest a b c hp
    have hs := pop3_length hp
    simp only [Id.run] at h
    injection h with he
    subst s'
    simp only [operationPotential, Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC,
      Stack.push, List.length_cons, hs]
    omega
  · contradiction

theorem step_stoparith_potential {gasCost : Nat} {op : Operation.SAOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.StopArith op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s := by
  cases op <;> rw [step.eq_1] at h
  all_goals first
  | simpa only [operationPotential] using execBinOp_potential h
  | simpa only [operationPotential] using execTriOp_potential h
  | simp only [Except.ok.injEq] at h; subst s'; exact Nat.le_refl _

theorem step_compbit_potential {gasCost : Nat} {op : Operation.CBLOp}
    {arg : Option (UInt256 × Nat)} {s s' : State}
    (h : step gasCost (.CompBit op, arg) s = .ok s') :
    operationPotential s' ≤ operationPotential s := by
  cases op <;> rw [step.eq_1] at h
  all_goals first
  | simpa only [operationPotential] using execBinOp_potential h
  | simpa only [operationPotential] using Nat.le_of_eq (execUnOp_potential h)

end Benchmarks.UniswapV4PoolManager
