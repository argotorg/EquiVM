# ModExp precompile bytecode proof status

`CoveredSpec.lean` is the current proved union of branch-local bytecode specs.  It proves exact-gas
functional correctness against `Model.output` for:

- the all-single-word path;
- wide fast exits: exponent zero and base ≤ 1;
- zero declared modulus-length exits;
- positive one-word small-modulus-value exits: modulus value zero or one;
- one-word odd-modulus Montgomery;
- one-word even-modulus Barrett, both direct and normalized.

`Spec.lean` states the intended general ModExp proof interface:

- `modexpAccepts`: the ModExp-level input predicate (`weiValue = 0` and Osaka operand-length
  validity);
- `modexpSomeExactGasEnsures`: functional correctness against `Model.output`, with some exact
  bytecode gas threshold;
- `modexpSomeExactGasSpec_of_coverage`: the formal reduction showing that full coverage of
  `coveredAccepts` over `modexpAccepts` is sufficient for a general ModExp bytecode spec.

The remaining proof obligation is `missingModexpCases`: accepted ModExp inputs not yet covered by
the completed branch predicates.  `Spec.lean` proves that bounded-calldata missing cases are in the
wide, nontrivial backend region: not all-single-word, exponent nonzero, and base > 1.

It also factors the one-word nontrivial backend shape:

- `wideOneWordBackendInputs`;
- `wideModulusNat`;
- `wideModulusParity`;
- `wideBarrettDirectSelector`.

For that shape, `Spec.lean` proves that an odd modulus is already covered by Montgomery, and that
the two completed even-modulus Barrett selectors are already covered.  Thus a bounded missing
one-word case is reduced to the branch-selection gap around the Barrett normalization predicate.
The scanner-control part of that gap is now also explicit:
`wideOneWordBarrett_not_direct_hnorm` proves that a nontrivial one-word Barrett input not selected
by the direct path must enter the normalization branch.  The remaining one-word normalization
obligations are now factored as `WideBarrettNormalizedWordMemoryFacts`, with
`wideBarrettNormalizedWordFacts_of_hnorm_memory` reconstructing the backend predicate and
`wideOneWordBarrettNormalizedMemory_coveredAccepts` giving the coverage theorem once those memory
facts are proved.

The raw normalized-memory facts are also connected to pure payload facts:
`WideBarrettNormalizedWordModelFacts` states that the normalized payload is neither zero nor one and
has an accepted first-byte shape, while `wideBarrettNormalizedWordMemoryFacts_of_model` uses the
existing `memoryZeroResult_eq_reference`/`memoryOneResult_eq_reference` lemmas to derive the
operational scanner facts from those pure predicates plus `wideBarrettNormalizedMemoryBounds`.
`wideBarrettNormalizedMemoryBounds_of_oneWordBackendInputs` proves those bounds automatically for
the one-word backend shape, and `wideOneWordBarrettNormalizedModelAuto_coveredAccepts` is the
corresponding coverage theorem.  The one-word direct-false residual is now only
`WideBarrettNormalizedWordModelFacts`.

This has been reduced one step further: `WideBarrettNormalizedWordPayloadFacts` packages payload
equality with the original modulus plus the normalized first-byte shape.
`wideBarrettNormalizedWordModelFacts_of_oneWordPayload` derives the previous model facts from these
payload facts and the already-known `wideModulusNat > 1`, and
`wideOneWordBarrettNormalizedPayload_coveredAccepts` is the coverage theorem in that form.

The generic parity fact is now discharged by `wideModulusParityCoverage_of_landOne`: because the
bytecode computes parity by `land x 1`, the result is always either `0` or `1`.

The full nontrivial one-word backend is now packaged by
`wideOneWordBackend_coveredAccepts_of_payload`.  It needs only `wideOneWordPayloadCoverage`: in the
even/direct-false Barrett case, the normalized payload facts hold.
The arithmetic part of that payload proof is factored out by
`wideBarrettNormalizedPayloadNat_eq_wideModulusNat_of_read_prefix`: once the normalized result
payload read is shown to be the significant suffix of the original modulus and the skipped prefix
is shown to decode to zero, the normalized payload Nat is exactly `wideModulusNat`.
Those lower-level facts are now packaged as `WideBarrettNormalizedWordReadFacts`, and
`wideOneWordBackend_coveredAccepts_of_readFacts` is the corresponding one-word coverage theorem.
The `k + normalizedLen = modulusSize` read-facts field is now discharged for the canonical skipped
prefix by `wideBarrettNormalizedSkippedPrefix_add_len`, backed by the generic scanner theorem
`barrettNormalizedSkippedPrefix_add_len`.
The skipped-prefix-zero field is discharged by `wideBarrettNormalizedSkippedPrefix_zero`, and the
canonical normalized payload read-preservation field is discharged by
`wideBarrettNormalizedResultMem_read_canonical_payload`.  Consequently
`wideBarrettNormalizedWordReadFacts_of_canonical` builds read facts from only the normalized
first-byte shape, and `wideBarrettNormalizedWordFirstByteShape_of_notDirect` discharges that shape
from the scanner stop theorem plus the canonical payload-read bridge.

`missing_bounded_oneWord_impossible_of_payload` is the no-missing-cases form of that same one-word
result; `missing_bounded_oneWord_impossible_of_readFacts` is the lower-level read-facts form, and
`missing_bounded_oneWord_impossible` closes the bounded nontrivial one-word backend.

The positive one-word small-modulus-value path is now proved directly by
`wideSmallModulusValueBytecodeSpec`; it composes the operand-copy prelude, the zero/one
dispatcher exits, and the Solidity bytes return suffix with exact gas.

The zero declared modulus-length path is also proved directly by
`wideZeroModulusLengthBytecodeSpec`; it composes the operand-copy prelude, the dispatcher
empty-bytes return path, and the Solidity bytes return suffix with exact gas.

The formal residual after this closure is `wideBackendResidualInputs`, proved by
`missing_bounded_backendResidualInputs`: any bounded missing case is now a multi-limb nontrivial
backend (`wideMultiLimbBackendInputs`).  `modexpSomeExactGasSpec_of_bounded_residualCoverage`
packages the remaining route to the intended general theorem: provide the calldata-size bound
required by the current wide proofs and prove coverage for `wideBackendResidualInputs`.

`Spec.lean` also splits this residual along the bytecode's actual odd/even dispatcher:
`wideMultiLimbOddMontgomeryInputs` and `wideMultiLimbEvenBarrettInputs`, with
`modexpSomeExactGasSpec_of_bounded_multiLimbBranchCoverage` packaging the corresponding route to
the general theorem.  `MultiLimbPrefix.lean` proves the exact-gas prefix from the normal precompile
entry to those backend entry PCs:

- `wideMultiLimbOddDispatcherPrefixExact`: reaches PC 1925, the Montgomery backend entry;
- `wideMultiLimbEvenDispatcherPrefixExact`: reaches PC 1549, the Barrett backend entry.

`MultiLimbPrefix.lean` also defines the final backend-suffix interface:
`WideMultiLimbOddBackendSuffixExact` and `WideMultiLimbEvenBackendSuffixExact`.  These start from
the exact backend cursor, assume a backend-local gas expression, and return `RDxRet` against
`Model.output`.  The theorem `modexpSomeExactGasSpec_of_bounded_multiLimbBackendSuffix` composes
those two suffix proofs with all existing covered branches into the intended general
`BytecodeSpec`.

The shared result-allocation blocks for both residual branches are now proved as well:

- `wideMultiLimbOddAllocationPrefixExact`: reaches PC 1946 after Montgomery result allocation;
- `wideMultiLimbEvenAllocationPrefixExact`: reaches PC 1570 after Barrett result allocation.

The shared result-array allocation interface is:
`WideMultiLimbOddPostAllocationSuffixExact` and
`WideMultiLimbEvenPostAllocationSuffixExact`.  The theorem
`modexpSomeExactGasSpec_of_bounded_multiLimbPostAllocationSuffix` composes those narrower suffix
proofs with the checked dispatcher/allocation prefixes and all previously covered branches.

The odd Montgomery residual has now been pushed through the first temporary word-array allocation,
the first loop-entry test, the first copy-loop call-frame setup, the concrete checked-add helper for
the first index increment, the jump into the read-offset helper, and the checked
`modulusSize - 32` subtraction, the first full-word copy store, the subsequent loop guard, the
taken guard branch's call-frame setup for the second copy iteration, and that iteration's
checked-add helper, jump back to the read-offset helper, and checked `modulusSize - 64`
subtraction, the second full-word copy store, the subsequent loop guard, and the call-frame setup
for the third copy iteration, that iteration's checked-add helper, the jump back into the
read-offset helper, the checked `modulusSize - 96` subtraction, the third full-word copy store, and
the subsequent loop guard, and the taken guard branch's call-frame setup for the fourth copy
iteration, its checked-add helper, and the jump back into the read-offset helper.
The preferred current full-spec reduction is
`modexpSomeExactGasSpec_of_bounded_multiLimbFourthCopyReadSuffixes`; its remaining backend
obligations start at:

- odd Montgomery, if `3 < modulusSize / 32`: PC 1903, at the read-offset helper for the fourth
  copy iteration, with `i = 4` and three copied words committed to memory;
- odd Montgomery, if `2 < modulusSize / 32` and not `3 < modulusSize / 32`: PC 2865, the
  fall-through path after the third full-word copy;
- odd Montgomery, if `1 < modulusSize / 32` and not `2 < modulusSize / 32`: PC 2865, the
  fall-through path after the second full-word copy;
- odd Montgomery, otherwise: PC 2865, the fall-through path after the first full-word copy;
- even Barrett: PC 1603, at the leading-zero scan loop cursor.

The next substantial work is proving the residual multi-limb backend paths with their exact gas
expressions, and finally replacing the existential gas postcondition with a total bytecode gas
selector.
