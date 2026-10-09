import Benchmarks.Safe.Correct

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.safeExectransactionBodyCore,
      ``Benchmarks.Safe.safeConstructorCorrect, ``Benchmarks.Safe.safeCorrect,
      ``Benchmarks.Safe.safeContractCorrect] do
    let axioms ← Lean.collectAxioms name
    let standard := axioms.filter fun x ↦
      x == ``propext || x == ``Classical.choice || x == ``Quot.sound
    let native := axioms.filter fun x ↦ (x.toString.splitOn "native_decide.ax_").length > 1
    let unexpected := axioms.filter fun x ↦ !standard.contains x && !native.contains x
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; standard: {standard}; native: {native.size}; \
      unexpected: {unexpected}"
