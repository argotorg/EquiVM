import Tests.DiffTest.Targets

/-!
# `solm-difftest`

Runs the differential suite over every registered target.

```
lake exe solm-difftest [--seed N] [--count N] [--only NAME[,NAME…]]
```

Exit status is nonzero when any case disagrees or the specification got stuck.
-/

open Solm.DiffTest Tests.DiffTest

def parseArgs (args : List String) : Nat × Nat × Option (List String) := Id.run do
  let mut seed := 2026
  let mut count := 20
  let mut only : Option (List String) := none
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--seed" :: v :: tail => seed := v.toNat?.getD seed; rest := tail
    | "--count" :: v :: tail => count := v.toNat?.getD count; rest := tail
    | "--only" :: v :: tail => only := some (v.splitOn ","); rest := tail
    | _ :: tail => rest := tail
    | [] => pure ()
  return (seed, count, only)

def main (args : List String) : IO UInt32 := do
  let (seed, count, only) := parseArgs args
  let targets := match only with
    | some names => allTargets.filter fun t => names.contains t.name
    | none => allTargets
  IO.println s!"solm-difftest: {targets.length} target(s), seed {seed}, {count} cases per transition"
  let ok ← runTargets targets seed count
  pure (if ok then 0 else 1)
