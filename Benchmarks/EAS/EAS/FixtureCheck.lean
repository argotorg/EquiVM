import Benchmarks.EAS.EAS.DiffTarget

/-- Successful stateful cases supplement the randomized suite's guard coverage. -/
def main : IO UInt32 := do
  match Benchmarks.EAS.EAS.fixtureSequence with
  | .ok names =>
    IO.println s!"EAS deterministic coverage: {String.intercalate ", " names}"
    return 0
  | .error message =>
    IO.eprintln message
    return 1
