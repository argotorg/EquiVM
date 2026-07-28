import Benchmarks.Dss.Cat.Common
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-!
# Cat `bite(bytes32,address)` — EVM-side foundation

Dispatcher navigation (`catDispatch_bite`), calldata decode (`catDecode_bite`), and dispatcher
reach to the `bite` arm body at pc `⟨375⟩` (`catReachBiteEntry`).

`bite` is low-low arm 3 (selector `0x45cf2230`, selNat `1171202608`); its arm body at pc `375`
sets return pc `419` (the shared uint256 return encoder), decodes the two args and jumps into the
`bite` routine at pc `1163`.
-/

/-- The two decoded `bite` locals: `ilk : bytes32`, `urn : address`. -/
def biteLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk"
      (.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))).insert "urn"
    (.address (Ethereum.AccountAddress.ofNat (calldataWord I.calldata 36).toNat))

theorem catDispatch_bite {I : ExecutionEnv} (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩) :
    dispatchMsg contract I.calldata = some biteTransition := by
  have hcd : I.calldata.extract 0 4 = (⟨#[0x45, 0xcf, 0x22, 0x30]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [])
    (post := [boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition,
      ilksTransition, litterTransition, liveTransition, relyTransition, vatTransition,
      vowTransition, wardsTransition])
    (ti := biteTransition) (htr := by rfl)
  · intro t ht
    simp at ht
  · rw [selectorOf, biteSelectorBytes]; exact hsel

theorem catReachBiteEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x45, 0xcf, 0x22, 0x30]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨375⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : catSelWord I = ⟨1171202608⟩ :=
    catSelWord_eq_of_beq I hsz 0x45 0xcf 0x22 0x30 ⟨1171202608⟩ (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj; interval_cases j <;> (rw [hword]; native_decide)
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc 3))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  exact catReachLowLowBody 3 (by omega) ⟨375⟩ hcode hwv hsz hsize hroot hlow heq0 htake
    (by jump_dest) (by native_decide)

/-- `decodeABIValues?` for the `(bytes32, address)` head tuple under `legacySolc05`.
The legacy solc-0.5 decoder does not enforce the address canonical-form check, so `_hcanon` is
retained only for interface parity with the `modern` lemma. -/
theorem decodeABIValues_bytes32_address_legacy {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (_hcanon : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeABIValues? [abiBytes32, .elem .address] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32, UInt256.toNat]

theorem catDecode_bite {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (biteTransition.params.map Param.name)
      (transitionSignature biteTransition).paramTypes I.calldata = some (biteLocals I) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "urn"]
    [bytes32, addr] I.calldata = some (biteLocals I)
  rw [decodeCalldataWithMode]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) = calldataWord I.calldata 36 :=
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  show decodeCalldata ["ilk", "urn"] [abiBytes32, .elem .address] I.calldata DecodeMode.legacySolc05
    = some (biteLocals I)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, .elem .address] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_legacy (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          calldataWord I.calldata 36 from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanon)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (I.calldata.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues, biteLocals, hword36]

end Benchmarks.Dss.Cat
