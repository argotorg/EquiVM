# Pipeline validation runs

Complete runs of the scaffold automation (`Misc/scaffold-prompt.md`) on contracts written for it.
Every file but `<Name>.sol`, `SpecSyntax.lean` and `HANDOFF.md` is generated; regenerate with the
commands recorded in each `HANDOFF.md`. The directories build (`lake build Tests.Pipeline.<Name>.Correct`)
with exactly the generated `sorry` stubs, and their targets run in `lake exe solm-difftest`.

- `Vault/`: immutables set by a constructor with arguments, modifiers, a transient reentrancy
  lock (EVM version cancun), a mapping, a dynamic array with push and pop, typed external calls
  with return values, events.
