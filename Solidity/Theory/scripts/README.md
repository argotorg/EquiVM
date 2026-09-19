# Generator for `Solidity/Theory/Complete.lean`

Run from the repo root after changing the rules in `Solidity/Semantics/Exec.lean`:

    python3 Solidity/Theory/scripts/rules.py        # extracts the rules into rules.json
    python3 Solidity/Theory/scripts/gen_complete.py # writes Solidity/Theory/Complete.lean

`complete_header.lean` is the hand-written prefix of the generated file; `manual.json` holds the
completeness cases whose proofs are written by hand (keyed `Family.rule`).
