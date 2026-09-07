import Examples.UniswapV2Pair.ConstructorCode
import Examples.UniswapV2Pair.Permit
import Examples.UniswapV2Pair.CodeCopyRevertSteps
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000

abbrev constructorNameHashWord : UInt256 :=
  ⟨86753177656789946143617852270382413483605072673293953774383968070347263481656⟩
abbrev constructorVersionHashWord : UInt256 :=
  ⟨90743482286830539503240959006302832933333810038750515972785732718729991261126⟩

theorem constructorNameHash :
    ffi.KEC nameBytes = constructorNameHashWord.toByteArray := by native_decide

theorem constructorVersionHash :
    ffi.KEC versionBytes = constructorVersionHashWord.toByteArray := by native_decide

end UniswapV2Pair
