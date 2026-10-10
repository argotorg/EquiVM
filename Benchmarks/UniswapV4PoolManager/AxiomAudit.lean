import Benchmarks.UniswapV4PoolManager.Correct

/-! Check the trusted dependencies of the public runtime and deployment refinements. -/

open Lean in
run_cmd do
  for name in [``Benchmarks.UniswapV4PoolManager.poolManagerDonateBody,
      ``Benchmarks.UniswapV4PoolManager.poolManagerCorrect,
      ``Benchmarks.UniswapV4PoolManager.poolManagerRuntimeCorrect,
      ``Benchmarks.UniswapV4PoolManager.poolManagerConstructorCorrect,
      ``Benchmarks.UniswapV4PoolManager.poolManagerContractCorrect] do
    let axioms ← collectAxioms name
    let standard := axioms.filter fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax
    let native := axioms.filter fun ax => (ax.toString.splitOn ".native_decide.ax_").length > 1
    let unexpected := axioms.filter fun ax => !standard.contains ax && !native.contains ax
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms: {unexpected}"
    logInfo m!"{name}: {standard.size} standard axioms, {native.size} native_decide axioms, 0 unexpected axioms"
