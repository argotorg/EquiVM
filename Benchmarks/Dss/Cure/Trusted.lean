import Benchmarks.Dss.Cure.Bytecode
import Solm.Dispatch
import Reasoning.Solc

/-!
# MakerDAO/Sky DSS Cure trusted bytecode facts

Lean does not reduce the FFI-backed Keccak computation used by `selectorOf`. These facts are the
contract-local selector bytes used to connect Solm dispatch to the runtime dispatcher constants.
The jump-destination tables are computed from the concrete byte arrays in `Bytecode.lean`; this
file gives them proof-local names.
-/

open Solm Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Dss.Cure

/-! ## Trusted Keccak values -/

/-- `keccak256(bytes32(2))` — the dynamic-array data base slot for storage slot 2 (`srcs`). -/
axiom cureSrcsDataSlot_trusted :
    (⟨29102676481673041902632991033461445430619272659676223336789171408008386403022⟩ :
      UInt256) = srcsDataSlot

/-! ## Trusted storage disjointness -/

/--
The two writes in `drop`'s swap branch, `srcs[pos - 1] = move` and `pos[move] = pos_`,
do not alias the dynamic-array length slot `2` that is read by the following `srcs.pop()`.
-/
axiom cureDropSwapWritesPreserveSrcsLength_trusted
    (evm : EVM.State) (idx moveWord pos val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (srcElemSlot (.int (Int.ofNat idx.toNat))) val)
          evm.executionEnv.codeOwner (solcMappingSlot ⟨5⟩ moveWord) pos)
        evm.executionEnv.codeOwner ⟨2⟩ =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

/-! ## Trusted selector bytes -/

/-- `keccak("amt(address)")[0:4] = 0x09615662`. -/
axiom cureAmtSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr amtTransition))).extract 0 4 =
      ⟨#[0x09, 0x61, 0x56, 0x62]⟩

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom cureCageSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr cageTransition))).extract 0 4 =
      ⟨#[0x69, 0x24, 0x50, 0x09]⟩

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom cureDenySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr denyTransition))).extract 0 4 =
      ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩

/-- `keccak("drop(address)")[0:4] = 0x91f2700a`. -/
axiom cureDropSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr dropTransition))).extract 0 4 =
      ⟨#[0x91, 0xf2, 0x70, 0x0a]⟩

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom cureFileSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileTransition))).extract 0 4 =
      ⟨#[0x29, 0xae, 0x81, 0x14]⟩

/-- `keccak("lCount()")[0:4] = 0x493aa4c7`. -/
axiom cureLCountSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr lCountTransition))).extract 0 4 =
      ⟨#[0x49, 0x3a, 0xa4, 0xc7]⟩

/-- `keccak("lift(address)")[0:4] = 0x3c278bd5`. -/
axiom cureLiftSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr liftTransition))).extract 0 4 =
      ⟨#[0x3c, 0x27, 0x8b, 0xd5]⟩

/-- `keccak("list()")[0:4] = 0x0f560cd7`. -/
axiom cureListSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr listTransition))).extract 0 4 =
      ⟨#[0x0f, 0x56, 0x0c, 0xd7]⟩

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom cureLiveSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr liveTransition))).extract 0 4 =
      ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩

/-- `keccak("load(address)")[0:4] = 0x2f40e734`. -/
axiom cureLoadSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr loadTransition))).extract 0 4 =
      ⟨#[0x2f, 0x40, 0xe7, 0x34]⟩

/-- `keccak("loaded(address)")[0:4] = 0xffa9ca9f`. -/
axiom cureLoadedSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr loadedTransition))).extract 0 4 =
      ⟨#[0xff, 0xa9, 0xca, 0x9f]⟩

/-- `keccak("pos(address)")[0:4] = 0x93d0281c`. -/
axiom curePosSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr posTransition))).extract 0 4 =
      ⟨#[0x93, 0xd0, 0x28, 0x1c]⟩

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom cureRelySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr relyTransition))).extract 0 4 =
      ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩

/-- `keccak("say()")[0:4] = 0x954ab4b2`. -/
axiom cureSaySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr sayTransition))).extract 0 4 =
      ⟨#[0x95, 0x4a, 0xb4, 0xb2]⟩

/-- `keccak("srcs(uint256)")[0:4] = 0xf381273f`. -/
axiom cureSrcsSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr srcsTransition))).extract 0 4 =
      ⟨#[0xf3, 0x81, 0x27, 0x3f]⟩

/-- `keccak("tCount()")[0:4] = 0x53f9a873`. -/
axiom cureTCountSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr tCountTransition))).extract 0 4 =
      ⟨#[0x53, 0xf9, 0xa8, 0x73]⟩

/-- `keccak("tell()")[0:4] = 0x53d700e5`. -/
axiom cureTellSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr tellTransition))).extract 0 4 =
      ⟨#[0x53, 0xd7, 0x00, 0xe5]⟩

/-- `keccak("wait()")[0:4] = 0x64bd7013`. -/
axiom cureWaitSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr waitTransition))).extract 0 4 =
      ⟨#[0x64, 0xbd, 0x70, 0x13]⟩

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom cureWardsSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr wardsTransition))).extract 0 4 =
      ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩

/-- `keccak("when()")[0:4] = 0xe2b0caef`. -/
axiom cureWhenSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr whenTransition))).extract 0 4 =
      ⟨#[0xe2, 0xb0, 0xca, 0xef]⟩

/-- The `JUMPDEST` set of `cureBytecode`, named for the Cure proof. -/
@[valid_jumps] theorem cureValidJumps :
    Ethereum.EVM.D_J cureBytecode 0
      = #[
      ⟨16⟩, ⟨113⟩, ⟨173⟩, ⟨244⟩, ⟨300⟩, ⟨305⟩, ⟨327⟩, ⟨343⟩, ⟨361⟩, ⟨369⟩,
      ⟨405⟩, ⟨429⟩, ⟨449⟩, ⟨471⟩, ⟨484⟩, ⟨486⟩, ⟨508⟩, ⟨524⟩, ⟨546⟩, ⟨562⟩,
      ⟨570⟩, ⟨578⟩, ⟨586⟩, ⟨594⟩, ⟨616⟩, ⟨632⟩, ⟨640⟩, ⟨662⟩, ⟨678⟩, ⟨700⟩,
      ⟨716⟩, ⟨724⟩, ⟨732⟩, ⟨754⟩, ⟨770⟩, ⟨792⟩, ⟨808⟩, ⟨816⟩, ⟨838⟩, ⟨845⟩,
      ⟨873⟩, ⟨895⟩, ⟨911⟩, ⟨929⟩, ⟨987⟩, ⟨1017⟩, ⟨1027⟩, ⟨1117⟩, ⟨1188⟩, ⟨1213⟩,
      ⟨1290⟩, ⟨1348⟩, ⟨1419⟩, ⟨1520⟩, ⟨1598⟩, ⟨1618⟩, ⟨1640⟩, ⟨1689⟩, ⟨1695⟩, ⟨1767⟩,
      ⟨1824⟩, ⟨1914⟩, ⟨1985⟩, ⟨2092⟩, ⟨2226⟩, ⟨2232⟩, ⟨2267⟩, ⟨2326⟩, ⟨2333⟩, ⟨2339⟩,
      ⟨2345⟩, ⟨2435⟩, ⟨2506⟩, ⟨2575⟩, ⟨2665⟩, ⟨2736⟩, ⟨2755⟩, ⟨2801⟩, ⟨2891⟩, ⟨2962⟩,
      ⟨3064⟩, ⟨3093⟩, ⟨3138⟩, ⟨3197⟩, ⟨3208⟩, ⟨3326⟩, ⟨3344⟩, ⟨3350⟩, ⟨3356⟩, ⟨3446⟩,
      ⟨3517⟩, ⟨3585⟩, ⟨3603⟩, ⟨3609⟩, ⟨3622⟩, ⟨3648⟩, ⟨3666⟩, ⟨3743⟩, ⟨3749⟩
      ] := by
  simpa using validJumps

/-- The `JUMPDEST` set of `cureCreationBytecode`, named for the Cure proof. -/
@[valid_jumps] theorem cureCreationValidJumps :
    Ethereum.EVM.D_J cureCreationBytecode 0
      = #[
      ⟨16⟩, ⟨112⟩, ⟨209⟩, ⟨269⟩, ⟨340⟩, ⟨396⟩, ⟨401⟩, ⟨423⟩, ⟨439⟩, ⟨457⟩,
      ⟨465⟩, ⟨501⟩, ⟨525⟩, ⟨545⟩, ⟨567⟩, ⟨580⟩, ⟨582⟩, ⟨604⟩, ⟨620⟩, ⟨642⟩,
      ⟨658⟩, ⟨666⟩, ⟨674⟩, ⟨682⟩, ⟨690⟩, ⟨712⟩, ⟨728⟩, ⟨736⟩, ⟨758⟩, ⟨774⟩,
      ⟨796⟩, ⟨812⟩, ⟨820⟩, ⟨828⟩, ⟨850⟩, ⟨866⟩, ⟨888⟩, ⟨904⟩, ⟨912⟩, ⟨934⟩,
      ⟨941⟩, ⟨969⟩, ⟨991⟩, ⟨1007⟩, ⟨1025⟩, ⟨1083⟩, ⟨1113⟩, ⟨1123⟩, ⟨1213⟩, ⟨1284⟩,
      ⟨1309⟩, ⟨1386⟩, ⟨1444⟩, ⟨1515⟩, ⟨1616⟩, ⟨1694⟩, ⟨1714⟩, ⟨1736⟩, ⟨1785⟩, ⟨1791⟩,
      ⟨1863⟩, ⟨1920⟩, ⟨2010⟩, ⟨2081⟩, ⟨2188⟩, ⟨2322⟩, ⟨2328⟩, ⟨2363⟩, ⟨2422⟩, ⟨2429⟩,
      ⟨2435⟩, ⟨2441⟩, ⟨2531⟩, ⟨2602⟩, ⟨2671⟩, ⟨2761⟩, ⟨2832⟩, ⟨2851⟩, ⟨2897⟩, ⟨2987⟩,
      ⟨3058⟩, ⟨3160⟩, ⟨3189⟩, ⟨3234⟩, ⟨3293⟩, ⟨3304⟩, ⟨3422⟩, ⟨3440⟩, ⟨3446⟩, ⟨3452⟩,
      ⟨3542⟩, ⟨3613⟩, ⟨3681⟩, ⟨3699⟩, ⟨3705⟩, ⟨3718⟩, ⟨3744⟩, ⟨3762⟩, ⟨3839⟩, ⟨3845⟩
      ] := by
  simpa using creationValidJumps

end Benchmarks.Dss.Cure
