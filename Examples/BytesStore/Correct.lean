import Examples.BytesStore.Bytecode
import Examples.BytesStore.Dispatch
import Examples.BytesStore.Constructor
import Examples.BytesStore.FullPacketTag
import Examples.BytesStore.FullSetByte
import Examples.BytesStore.FullSetPacketByte
import Examples.BytesStore.FullPushChunkLongTail
import Examples.BytesStore.FullPushChunkCalldataWords
import Examples.BytesStore.FullPushChunkLongStorage
import Examples.BytesStore.FullPushChunkLongRuntime
import Examples.BytesStore.FullSetLongOldLongReturn
import Examples.BytesStore.FullSetLongOldLongRuntime
import Examples.BytesStore.FullSetPacketRuntime
import Examples.BytesStore.FullSetChunkOldLongReturn
import Examples.BytesStore.FullSetChunkByteSuccess
import Examples.BytesStore.FullSetMapped
import Examples.BytesStore.FullSetMappedByteSuccess
import Examples.BytesStore.FullClearCurrentLong
import Examples.BytesStore.Tests

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-!
# BytesStore — top-level example module

This module keeps the bytes-focused Solidity/spec/test example available from `Examples.lean`.
`Bytecode.lean` pins the optimized full-contract bytecode for `BytesStore.sol`; `Constructor.lean`
proves the optimized Solidity creation code matches the Solm constructor, including the non-payable
guard.  `FullPacketTag.lean` proves optimized full-runtime no-dispatch reverts for short calldata
and selector no-match, the dispatch/body slice for the scalar `packetTag()` getter, and the complete
`currentLength()`, `packetLength()`, `mappedLength(uint256)`, and `chunkLength(uint256)` getters
including malformed bytes-header reverts, mapped/chunk ABI decode failures, and chunk array-bounds
reverts.  It also proves the optimized full-runtime `clearCurrent()` selector arm across malformed
current-header reverts, decoded zero-length current values, short packed nonzero values, and valid
long current values, including the long copy/delete loops and final state/return equivalence, plus
the `pushChunk(bytes)` ABI head-short, huge calldata,
offset-too-large, length-short, length-too-large, and payload-short decode-failure reverts, along
with the valid `pushChunk(bytes)` decoder reach/decode facts up to the body entry and the first
body scaffold that increments the chunks array length, enters the bytes-write helper using the
documented `keccak256(1)` storage-base literal, and reaches the shared bytes-header decoder; a
generic short-header branch also reaches the write-helper cleanup subroutine and, when the old
stored bytes value is short, the new-value write branch, with the empty appended-value case reaching
the empty-header storage write and encoded `RDret` return; the non-empty short appended-value case
now has the bytecode-shaped packed-header storage write helper, encoded `RDret` return endpoint,
an algebraic bridge from the optimized `SHL/SHR/AND/OR` word shape to the shared
`setShortPackedHeader` helper, and matching Solm short-value `pushArray?` storage
update/body-return/account-map scaffolding.  The dispatcher scaffold now also reaches the optimized
setter selector arms (`set`, `setByte`, `setChunk`, `setChunkByte`, `setPacket`, `setPacketByte`,
`setMapped`, and `setMappedByte`), preparing the full-contract setter proofs to reuse the existing
bytes-write and byte-write helpers; `set(bytes)` now has concrete selector-entry/decoder-entry
reach facts, the short/huge dynamic-head revert branches, valid dynamic decoding to the optimized
body entry, the body reach into the shared storage-write helper, and the nonempty helper bridge to
the old-value header decoder for slot `0`, now extending through the valid old-short cleanup
handoff into the new-value write branch and the nonempty short packed-header storage write back to
the set body, plus the encoded return from that set body and reusable Solm-side write/body/runtime
bridges for the full-contract `set(bytes)` transition, with a named full-contract set ABI decode
fact, current-slot short-write post-state account-map bridge, and composed bytecode endpoint for
the valid old-short/nonempty-new-short path, including the selector/ABI decode handoff into that
endpoint, plus the Solm decoded-value short-write helper for `current`, the matching stored-word
equality for helper payload words, the decoded short return-equivalence fact, and created-account
preservation for the short current-slot write, now composed into the full runtime theorem for the
valid old-short/new-short `set(bytes)` branch; the malformed old-current nonempty-short path now
has full-bytecode panic/header-decoder endpoints plus full-contract Solm malformed-write and
set-body revert helpers, including PC-522 current-header bridges for both old-short and old-long
malformed headers now composed into runtime theorems from supplied PC-522 reach/dispatch/decode
facts, plus reusable account-map-to-Solm malformed current-write facts, a generic set-body
write-revert-to-runtime bridge and named pure ABI source-bound/max-length facts for later branch
composition; ABI-decoded variants of both malformed `set(bytes)` branches now derive
dispatch/decode, decoded length bounds, payload source bounds, and decoded-value locals while still
taking the optimized body-entry reach as an input, with raw decoder-stack variants that compose
the full selector/ABI decoder reach into runtime equivalence for both malformed old-current
nonempty branches, and the Solm side now also has a decoded new-short write helper for valid
old-long current storage after clearing old data words.  The split `FullSetByte.lean` module now
pins the optimized `setByte(uint256,uint8)` selector/decoder reach, ABI short/huge/noncanonical
decode-failure runtime wrappers, and the Solm body-return scaffold for the byte write.  It also pins the Solm-side
`chunks` dynamic-array resolution/base-slot facts and the account-map equivalence bridge for append
storage shapes, using a trusted keccak disjointness fact for `chunks` element slots versus the
length slot.  The
executable checks in `Tests.lean` cover whole-value `bytes` writes, specific byte writes with bounds
checking, and layout reachability for nested `bytes` under dynamic-array and mapping refs.

The full `BytesStore` constructor, no-dispatch cases, five full-runtime getter branches, and
the complete full-runtime `clearCurrent()` selector arm are pinned/proved here as scaffolding for
the remaining runtime equivalence work, plus the malformed `pushChunk(bytes)` decoder failure branches
through the payload-bounds check and the valid decoder handoff to the `pushChunk(bytes)` body, now
extended through the chunks-length increment, bytes-write helper entry, header-decoder handoff, and
short-header cleanup handoff into the new-value write branch, empty-header storage write, and
encoded `RDret` return.  The empty decoded payload branch is also bridged into full runtime
equivalence theorems when the length increment fits and the appended chunk slot is either initially
zero or already holds a valid short packed bytes header, using the matching Solm `chunks` layout,
empty `pushArray?` storage update, body return, post-state account-map equivalence, and
keccak-disjointness-backed header preservation.  For any valid decoded `pushChunk(bytes)` payload,
the malformed old append-slot bytes-header branches (long and short encodings) are now bridged to
full runtime revert equivalence theorems as well.  The valid non-empty short appended-value branch
now has a full runtime equivalence theorem for valid old short packed append slots, using the
masked direct-calldata payload bridge to align the optimized stored word with Solm's short bytes
storage word.
-/

namespace BytesStore

set_option maxHeartbeats 1200000 in
theorem bytesStoreCorrect :
    runtimeEquivalence!?! bytesStoreConfig bytesStoreBytecode
      bytesStoreContract := by
    refine runtimeEquivalence!?!.intro ?_
    intro cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts
    by_cases hwv : I.weiValue = ⟨0⟩
    · by_cases hsz : 4 ≤ I.calldata.size
      · by_cases hselSet : selIs I ⟨#[0x03, 0x99, 0x32, 0x1e]⟩
        · exact bytesStoreSetRuntime hcode hsize hperm hwv hselSet hAccounts
        · by_cases hselSetByte : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩
          · exact bytesStoreSetByteRuntime hcode hsize hperm hwv hselSetByte hAccounts
          · by_cases hselClear : selIs I ⟨#[0xa6, 0xdf, 0xa2, 0x62]⟩
            · exact bytesStoreClearCurrentRuntime hcode hsize hperm hwv hselClear hAccounts
            · by_cases hselCurrent : selIs I ⟨#[0xa3, 0xd3, 0x5f, 0x36]⟩
              · exact bytesStoreCurrentLengthRuntime hcode hsize hperm hwv hselCurrent hAccounts
              · by_cases hselPush : selIs I ⟨#[0xb5, 0x0c, 0xc8, 0xac]⟩
                · exact bytesStorePushChunkRuntime hcode hsize hperm hwv hselPush hAccounts
                · by_cases hselSetChunk : selIs I ⟨#[0x39, 0x3d, 0x9c, 0xd7]⟩
                  · exact bytesStoreSetChunkRuntime hcode hsize hperm hwv
                      hselSetChunk hAccounts
                  · by_cases hselSetChunkByte : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩
                    · exact bytesStoreSetChunkByteRuntime hcode hsize hperm hwv
                        hselSetChunkByte hAccounts
                    · by_cases hselChunkLength : selIs I ⟨#[0xe8, 0xbd, 0x9a, 0xf5]⟩
                      · exact bytesStoreChunkLengthRuntime hcode hsize hperm hwv
                          hselChunkLength hAccounts
                      · by_cases hselSetPacket : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩
                        · exact bytesStoreSetPacketRuntime hcode hsize hperm hwv
                            hselSetPacket hAccounts
                        · by_cases hselSetPacketByte : selIs I ⟨#[0x0a, 0xb2, 0x59, 0x00]⟩
                          · exact bytesStoreSetPacketByteRuntime hcode hsize hperm hwv
                              hselSetPacketByte hAccounts
                          · by_cases hselPacketLength : selIs I ⟨#[0xb5, 0x18, 0xd2, 0xc4]⟩
                            · exact bytesStorePacketLengthRuntime hcode hsize hperm hwv
                                hselPacketLength hAccounts
                            · by_cases hselPacketTag : selIs I ⟨#[0x99, 0x3e, 0x0a, 0x90]⟩
                              · exact bytesStorePacketTagRuntime hcode hsize hperm hwv
                                  hselPacketTag hAccounts
                              · by_cases hselSetMapped : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩
                                · exact bytesStoreSetMappedRuntime hcode hsize hperm hwv
                                    hselSetMapped hAccounts
                                · by_cases hselSetMappedByte :
                                    selIs I ⟨#[0x13, 0x2f, 0xa3, 0x46]⟩
                                  · exact bytesStoreSetMappedByteRuntime hcode hsize hperm hwv
                                      hselSetMappedByte hAccounts
                                  · by_cases hselMappedLength :
                                      selIs I ⟨#[0x39, 0x1d, 0x72, 0x80]⟩
                                    · exact bytesStoreMappedLengthRuntime hcode hsize hperm hwv
                                        hselMappedLength hAccounts
                                    · refine bytesStoreNoDispatch hcode hsize ?_
                                      intro i hi
                                      interval_cases i
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselSet)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselSetByte)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselClear)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselCurrent)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselPush)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselSetChunk)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselSetChunkByte)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselChunkLength)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselSetPacket)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselSetPacketByte)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselPacketLength)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselPacketTag)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselSetMapped)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselSetMappedByte)
                                      · exact Bool.eq_false_of_not_eq_true
                                          (by simpa [selIs, bytesStoreSelBytes] using hselMappedLength)
      · have hshort : I.calldata.size < 4 := by omega
        exact bytesStoreShortRevert hcode hshort
    · exact bytesStoreNonPayable hcode hwv

end BytesStore
