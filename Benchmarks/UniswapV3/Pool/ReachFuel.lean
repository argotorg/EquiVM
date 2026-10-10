import Reasoning.Reach
import Ethereum.Theory.NoOutOfFuel

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a terminating fuelled run is unchanged by extra fuel.
theorem evmRun_moreFuel {n m : Nat} {jumps : Array UInt256} {s : EVM.State}
    (hle : n ≤ m) (hrun : X n jumps s ≠ .error .OutOfFuel) : X n jumps s = X m jumps s := by
  induction n generalizing m s with
  | zero => exact False.elim (hrun (by rw [X]))
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      unfold X at hrun ⊢
      cases hs : Xstep jumps s with
      | error err => simp only [hs, bind, Except.bind]
      | ok pair =>
        rcases pair with ⟨next, result⟩
        cases result with
        | none =>
          simp only [hs, bind, Except.bind] at hrun ⊢
          exact ih (by omega) hrun
        | some result =>
          rcases result with ⟨kind, output⟩
          cases kind <;> simp only [hs, bind, Except.bind]

-- LIBRARY CANDIDATE: gas bounds make the iterator's fuel parameter irrelevant.
theorem evmRun_fuel_eq {n m : Nat} {jumps : Array UInt256} {s : EVM.State}
    (hn : s.machineState.gasAvailable.toNat < n)
    (hm : s.machineState.gasAvailable.toNat < m) : X n jumps s = X m jumps s := by
  rcases Nat.le_total n m with h | h
  · exact evmRun_moreFuel h (X_no_OufOfFuel_of_gas_lt_fuel jumps hn)
  · exact (evmRun_moreFuel h (X_no_OufOfFuel_of_gas_lt_fuel jumps hm)).symm

end Benchmarks.UniswapV3.Pool
