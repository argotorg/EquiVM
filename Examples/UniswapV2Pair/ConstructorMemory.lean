import Examples.UniswapV2Pair.ConstructorCode
import Examples.UniswapV2Pair.CodeCopyRevertSteps
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

def constructorTypeInputMem : ByteArray :=
  uniswapV2PairInitcode.write 9094 solcFreePtrMem 128 82

noncomputable abbrev constructorTypeHashWord : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC eip712DomainTypehashBytes))

def constructorLiteralMem : ByteArray :=
  let m0 := (⟨192⟩ : UInt256).toByteArray.write 0 constructorTypeInputMem 64 32
  let m1 := (⟨10⟩ : UInt256).toByteArray.write 0 m0 128 32
  let nameWord : UInt256 :=
    ⟨38641673103035791393623033292975719447393963951753298749149485052705600700416⟩
  let m2 := nameWord.toByteArray.write 0 m1 160 32
  let m3 := (⟨256⟩ : UInt256).toByteArray.write 0 m2 64 32
  let m4 := (⟨1⟩ : UInt256).toByteArray.write 0 m3 192 32
  let versionWord : UInt256 :=
    ⟨22163329580580053030292883849319169862539958002407764210677428189014622470144⟩
  versionWord.toByteArray.write 0 m4 224 32

theorem constructorTypeInputMem_read :
    constructorTypeInputMem.readWithPadding 128 82 = eip712DomainTypehashBytes := by
  native_decide

theorem constructorTypeInputMem_mload64 :
    memoryWordLoad constructorTypeInputMem ⟨7⟩ ⟨64⟩ = ⟨128⟩ := by
  unfold memoryWordLoad
  native_decide

theorem constructorLiteralMem_size : constructorLiteralMem.size = 256 := by native_decide

theorem constructorLiteralMem_read64 :
    constructorLiteralMem.readWithPadding 64 32 = (⟨256⟩ : UInt256).toByteArray := by native_decide

end UniswapV2Pair
