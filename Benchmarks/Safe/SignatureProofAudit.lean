import Benchmarks.Safe.CheckNSignatures
import Benchmarks.Safe.CheckSignatures
import Benchmarks.Safe.CheckNSignaturesAddress
import Benchmarks.Safe.CheckSignaturesAddress

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.safeChecknsignaturesBodyCore,
      ``Benchmarks.Safe.safeChecksignaturesBodyCore,
      ``Benchmarks.Safe.safeChecknsignaturesAddressBytes32BytesUint256BodyCore,
      ``Benchmarks.Safe.safeChecksignaturesAddressBytes32BytesBodyCore] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
