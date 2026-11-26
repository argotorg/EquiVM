# Safe proof repair: <FROM_COMMIT> -> <TO_COMMIT>

Layout. Every version of the Safe proof is a directory `Benchmarks/Safe/<NAME>/`
with Lean module path `Benchmarks.Safe.<NAME>`; the same name appears in its
`namespace` lines and path strings. `Benchmarks/Safe/Main/` is the live proof
and is never modified. `Benchmarks/Safe/<START>/` holds a complete,
axiom-clean refinement proof (`safeContractCorrect` in `Correct.lean`) of Safe
at upstream commit <FROM_COMMIT> of safe-fndn/safe-smart-account (formerly
safe-global/safe-smart-account). `Benchmarks/Safe/<TARGET>/` does not exist yet;
it will hold the proof for upstream commit <TO_COMMIT>.

Goal: carry the proof over to <TO_COMMIT> with the smallest sound change to the proof.
Input: the commit hash <TO_COMMIT>. Fetch the upstream `contracts/` directory at that commit,
byte-exact, and the pinned compiler 0.8.35+commit.47b9dedd, the only compiler to use; `<solc>`
below is the path of that binary. The compile command is in `Benchmarks/Safe/<START>/README.md`.
Do not consult any other version of this proof: no other EquiVM checkout, branch, remote or fork.

0. Copy `Benchmarks/Safe/<START>/` to `Benchmarks/Safe/<TARGET>/`. In the copy only, replace
   every occurrence of the token `Benchmarks.Safe.<START>` by `Benchmarks.Safe.<TARGET>` and of
   `Benchmarks/Safe/<START>` by `Benchmarks/Safe/<TARGET>`. Build
   `Benchmarks.Safe.<TARGET>.Correct` to confirm the copy. Commit: "Benchmarks: Safe copy <START> to <TARGET>".
   From here on work only in `Benchmarks/Safe/<TARGET>/`; never touch `<START>` or `Main`.

1. Replace `Benchmarks/Safe/<TARGET>/contracts/` with the fetched sources. Recompile with the
   command in the copy's README. Replace `runtime.hex`, `creation.hex`, `Safe.abi.json`;
   regenerate `sources.sha256`, `Bytecode.lean` and `CreationBytecode.lean`
   (`scripts/gen_bytecode.py --dir Benchmarks/Safe/<TARGET> --force`, then again with
   `--creation`); then run
   `python3 scripts/audit_safe.py --dir Benchmarks/Safe/<TARGET> --solc <solc> --write`, which
   regenerates the block summaries (`Blocks/`, `Blocks.lean`), `ArtifactChecks.lean` and
   `AuditManifest.json`. If it reports stale block shards, delete those files in `Blocks/` and
   rerun it. Update the README's provenance: upstream commit, byte sizes, hashes.
   Commit: "Benchmarks: Safe regenerate artifacts".

2. Update `SpecSyntax.lean` and `Spec.lean` to the new source, following the bytecode as the
   README's audit tables do, and keep `contractSyntax_eq` in `SpecSyntax.lean` proved. Update the
   `Audit.lean` cases whose expected outcome changes. In `Tests/DiffTest/Targets.lean` add
   `def safe_<TARGET> : Target` with `name := "Safe_<TARGET>"`, mirroring `safe`, and add it to
   the same list; this is the one permitted edit outside the directory. Then run the differential
   tests on the new spec and bytecode: `lake build Benchmarks.Safe.<TARGET>.Audit` must print
   `failures 0`, and `lake exe stele-difftest --only Safe_<TARGET> --count 50` must print
   `0 disagree`, before you touch any proof. Do not change the statement of
   `safeContractCorrect`, `safeCorrect`, `safeConstructorCorrect` or any of the 33
   `safe…Refines` entrypoint theorems. Commit: "Benchmarks: Safe spec and audit".

3. Repair the proofs. Keep file structure, names and lemma statements wherever the code they
   describe is unchanged; edit in place rather than rewrite; add files only for new code
   paths and delete files only for removed ones. Commit: "Benchmarks: Safe proof repaired".

4. Done means: `lake build Benchmarks.Safe.<TARGET>.Correct
   Benchmarks.Safe.<TARGET>.CorrectProofAudit Benchmarks.Safe.<TARGET>.ArtifactChecks
   Benchmarks.Safe.<TARGET>.Audit` succeeds; `python3 scripts/audit_safe.py --dir
   Benchmarks/Safe/<TARGET> --solc <solc>` (no `--write`) passes; there is no `sorry`, `admit`
   or new axiom; and `#print axioms Benchmarks.Safe.<TARGET>.safeContractCorrect` shows only
   `propext`, `Classical.choice`, `Quot.sound` and native_decide certificates.

5. Write `Benchmarks/Safe/<TARGET>/REPAIR.md`, briefly: the spec change and the bytecode
   evidence for it; the difftest summary line; which lemma statements changed and why; what
   could not be repaired in place and was reproved; blockers. Do not list files: the commits
   record them. Commit: "Benchmarks: Safe repair report".

Rules: work only inside `Benchmarks/Safe/<TARGET>/`, plus the registry entry of step 2. No
other edits to `Tests/`, and none to `Stele/`, `Reasoning/`, `EVM/`, `scripts/`,
`Benchmarks.lean`, CI or the lakefile; if one seems unavoidable, stop and report. Never
bypass a problem; if something looks unprovable, investigate, report and wait.