import Benchmarks.Dss.Cat.Bytecode
import Solm.Semantics

/-!
# MakerDAO/Sky DSS Cat trusted bytecode facts

The selector facts are trusted because `ffi.KEC` is opaque to Lean. The `JUMPDEST` tables are already
proved (via `native_decide`) and tagged `@[valid_jumps]` in `Bytecode.lean` (`validJumps`,
`creationValidJumps`), so the `jump_dest` tactic sees them directly; no re-export is needed here.
-/

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Cat

/-- `keccak("bite(bytes32,address)")[0:4] = 0x45cf2230`. -/
axiom biteSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr biteTransition))).extract 0 4 =
      ⟨#[0x45, 0xcf, 0x22, 0x30]⟩

/-- `keccak("box()")[0:4] = 0x754215a1`. -/
axiom boxSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr boxTransition))).extract 0 4 =
      ⟨#[0x75, 0x42, 0x15, 0xa1]⟩

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr cageTransition))).extract 0 4 =
      ⟨#[0x69, 0x24, 0x50, 0x09]⟩

/-- `keccak("claw(uint256)")[0:4] = 0xe66d279b`. -/
axiom clawSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr clawTransition))).extract 0 4 =
      ⟨#[0xe6, 0x6d, 0x27, 0x9b]⟩

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr denyTransition))).extract 0 4 =
      ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom fileAddressSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileAddressTransition))).extract 0 4 =
      ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩

/-- `keccak("file(bytes32,bytes32,address)")[0:4] = 0xebecb39d`. -/
axiom fileIlkFlipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileIlkFlipTransition))).extract 0 4 =
      ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩

/-- `keccak("file(bytes32,bytes32,uint256)")[0:4] = 0x1a0b287e`. -/
axiom fileIlkUintSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileIlkUintTransition))).extract 0 4 =
      ⟨#[0x1a, 0x0b, 0x28, 0x7e]⟩

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileUintSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileUintTransition))).extract 0 4 =
      ⟨#[0x29, 0xae, 0x81, 0x14]⟩

/-- `keccak("ilks(bytes32)")[0:4] = 0xd9638d36`. -/
axiom ilksSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr ilksTransition))).extract 0 4 =
      ⟨#[0xd9, 0x63, 0x8d, 0x36]⟩

/-- `keccak("litter()")[0:4] = 0xa4fe8caf`. -/
axiom litterSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr litterTransition))).extract 0 4 =
      ⟨#[0xa4, 0xfe, 0x8c, 0xaf]⟩

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr liveTransition))).extract 0 4 =
      ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr relyTransition))).extract 0 4 =
      ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr vatTransition))).extract 0 4 =
      ⟨#[0x36, 0x56, 0x9e, 0x77]⟩

/-- `keccak("vow()")[0:4] = 0x626cb3c5`. -/
axiom vowSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr vowTransition))).extract 0 4 =
      ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr wardsTransition))).extract 0 4 =
      ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩

end Benchmarks.Dss.Cat
