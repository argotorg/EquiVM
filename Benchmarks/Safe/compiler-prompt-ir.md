  # Safe proof repair: legacy pipeline -> via-IR

  Layout. Every version of the Safe proof is a directory `Benchmarks/Safe/<NAME>/`
  with Lean module path `Benchmarks.Safe.<NAME>`; the same name appears in its
  `namespace` lines and path strings. `Benchmarks/Safe/Main/` is the live proof
  and is never modified: a complete, axiom-clean refinement proof
  (`safeContractCorrect` in `Correct.lean`) of Safe at upstream commit
  77901a5a1ad835b74ad3b72f73a8412cfe491c57 of safe-fndn/safe-smart-account, compiled
  with the command in `Benchmarks/Safe/Main/README.md` (solc 0.8.35+commit.47b9dedd,
  legacy pipeline, `--optimize-runs 200`). `Benchmarks/Safe/ViaIR/` does not exist yet;
  it will hold the proof of the same sources compiled through the IR pipeline (`--via-ir`),
  with the other settings unchanged.

  Goal: carry the proof over to the new bytecode with the smallest sound change to the proof.
  Most of the bytecode is structurally new (the constructor prelude, the dispatcher with the
  external function bodies inlined into it, the internal functions); expect to reprove most
  block-level lemmas while keeping the spec, the file structure and every theorem statement.

  Input: the compiler flag `--via-ir`. The sources do not change. The pinned compiler
  0.8.35+commit.47b9dedd is the only compiler to use; `<solc>` below is the path of that binary.
  Do not consult any other version of this proof: no directory under `Benchmarks/Safe/` other
  than `Main` and your copy, no other EquiVM checkout, branch, remote or fork.

    0. Copy `Benchmarks/Safe/Main/` to `Benchmarks/Safe/ViaIR/`. In the copy only, replace every
       occurrence of the token `Benchmarks.Safe.Main` by `Benchmarks.Safe.ViaIR` and of
       `Benchmarks/Safe/Main` by `Benchmarks/Safe/ViaIR`. Build `Benchmarks.Safe.ViaIR.Correct`
       to confirm the copy. Commit: "Benchmarks: Safe copy Main to ViaIR".
       From here on work only in `Benchmarks/Safe/ViaIR/`; never touch `Main`.
    1. Recompile with the command in the copy's README, adding `--via-ir` and changing nothing
       else. Replace `runtime.hex`, `creation.hex`, `Safe.abi.json`; regenerate `Bytecode.lean` and
       `CreationBytecode.lean` (`scripts/gen_listing.py --dir Benchmarks/Safe/ViaIR --force`, then
       again with `--creation`); `contracts/` and `sources.sha256` stay as they are. Then run
       `python3 scripts/audit_safe.py --dir Benchmarks/Safe/ViaIR --via-ir --solc <solc> --write`,
       which regenerates the block summaries (`Blocks/`, `Blocks.lean`), `ArtifactChecks.lean` and
       `AuditManifest.json`. If it reports stale block shards, delete those files in `Blocks/` and
       rerun it. Update the README's provenance: the compile command, byte sizes, hashes.
       Commit: "Benchmarks: Safe regenerate artifacts".
    2. The source is unchanged, so `Spec.lean` and `SpecSyntax.lean` stay as they are. Update the
       `Audit.lean` cases whose expected outcome changes (only gas-dependent outcomes can move).
       In `Tests/DiffTest/Targets.lean` add `def safe_ViaIR : Target` with `name := "Safe_ViaIR"`,
       mirroring `safe`, and add it to the same list; this is the one permitted edit outside the
       directory. Then run the differential tests on the spec and the new bytecode:
       `lake build Benchmarks.Safe.ViaIR.Audit` must print `failures 0`, and
       `lake exe stele-difftest --only Safe_ViaIR --count 50` must print `0 disagree`, before you
       touch any proof. Do not change the statement of `safeContractCorrect`, `safeCorrect`,
       `safeConstructorCorrect` or any of the 33 `safe…Refines` entrypoint theorems.
       Commit: "Benchmarks: Safe spec and audit".
    3. Repair the proofs. Keep file structure, names and lemma statements wherever the code they
       describe is unchanged; edit in place rather than rewrite; add files only for new code
       paths and delete files only for removed ones. Commit: "Benchmarks: Safe proof repaired".
    4. Done means: `lake build Benchmarks.Safe.ViaIR.Correct
       Benchmarks.Safe.ViaIR.CorrectProofAudit Benchmarks.Safe.ViaIR.ArtifactChecks
       Benchmarks.Safe.ViaIR.Audit` succeeds; `python3 scripts/audit_safe.py --dir
       Benchmarks/Safe/ViaIR --via-ir --solc <solc>` (no `--write`) passes; there is no `sorry`,
       `admit` or new axiom; and `#print axioms Benchmarks.Safe.ViaIR.safeContractCorrect` shows
       only `propext`, `Classical.choice`, `Quot.sound` and native_decide certificates.
    5. Write `Benchmarks/Safe/ViaIR/REPAIR.md`, briefly: what the IR pipeline changed in the
       bytecode as seen in the block summaries; the difftest summary line; which lemma statements
       changed and why; what could not be repaired in place and was reproved; blockers. Do not
       list files: the commits record them. Commit: "Benchmarks: Safe repair report".

  Rules: work only inside `Benchmarks/Safe/ViaIR/`, plus the registry entry of step 2. No
  other edits to `Tests/`, and none to `Stele/`, `Reasoning/`, `EVM/`, `scripts/`,
  `Benchmarks.lean`, CI or the lakefile; if one seems unavoidable, stop and report. Never
  bypass a problem; if something looks unprovable, investigate, report and wait.
