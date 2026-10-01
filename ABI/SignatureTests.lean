import ABI.Signature

namespace ABI.SignatureTests

-- Check signature formatting without the Format pretty-printer.
example : intTypeToSigStr (.uint ⟨256, by decide⟩) = "uint256" := by rfl
example : intTypeToSigStr (.sint ⟨8, by decide⟩) = "int8" := by rfl
example : fixedTypeToSigStr (.ufixed ⟨128, by decide⟩ ⟨18, by decide⟩) =
    "ufixed128x18" := by rfl
example : fixedTypeToSigStr (.fixed ⟨256, by decide⟩ ⟨80, by decide⟩) =
    "fixed256x80" := by rfl
example : elemToSigStr (.bytes ⟨0, by decide⟩) = "bytes1" := by rfl
example : elemToSigStr (.bytes ⟨31, by decide⟩) = "bytes32" := by rfl
example : abiToSigStr (.array (.elem .address) 1000) = "address[1000]" := by
  simp only [abiToSigStr, elemToSigStr] <;> rfl
example : abiToSigStr (.array (.elem .bool) 0) = "bool[0]" := by
  simp only [abiToSigStr, elemToSigStr] <;> rfl
example : printSignature ⟨"transfer", [.elem .address, .elem (.int (.uint ⟨256, by decide⟩))]⟩ =
    "transfer(address,uint256)" := by
  simp [printSignature, abiToSigStr, elemToSigStr, intTypeToSigStr] <;> rfl
example : printSignature ⟨"nested", [.tuple [.array (.dynamicArray (.elem .bool)) 12, .string]]⟩ =
    "nested((bool[][12],string))" := by
  simp [printSignature, abiToSigStr, elemToSigStr] <;> rfl

end ABI.SignatureTests
