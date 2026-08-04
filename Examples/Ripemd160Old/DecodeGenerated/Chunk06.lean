import Examples.Ripemd160Old.DecodeGenerated.Chunk05

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes6 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨1045⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1298⟩, 2))),
  (⟨1048⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1049⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1050⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨1052⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1053⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1279⟩, 2))),
  (⟨1056⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1057⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1058⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨1060⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1061⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1260⟩, 2))),
  (⟨1064⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1065⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1066⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨1068⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1069⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1241⟩, 2))),
  (⟨1072⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1073⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1074⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨1075⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1076⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1222⟩, 2))),
  (⟨1079⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1080⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1081⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨1083⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1084⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1203⟩, 2))),
  (⟨1087⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1088⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1089⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨1091⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1092⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1184⟩, 2))),
  (⟨1095⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1096⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1097⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨1099⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1100⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1165⟩, 2))),
  (⟨1103⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1104⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨1105⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨1107⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1108⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1146⟩, 2))),
  (⟨1111⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1112⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨1114⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨1115⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1128⟩, 2))),
  (⟨1118⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨1119⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1120⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1121⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1122⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1123⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨1124⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2))),
  (⟨1127⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1128⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1129⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1130⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1131⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1132⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1133⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1134⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1135⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨1137⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1138⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1139⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1140⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1141⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1142⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1145⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1146⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1147⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1148⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1149⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1150⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1151⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1152⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1153⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1154⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨1156⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1157⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1158⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1159⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1160⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1161⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1164⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1165⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1166⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1167⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1168⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1169⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1170⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1171⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1172⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1173⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨1175⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1176⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1177⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1178⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1179⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1180⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1183⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none))
]

private theorem generatedDecodes6_correct : ∀ i : Fin generatedDecodes6.size,
    decode runtimeBytecode generatedDecodes6[i].1 = generatedDecodes6[i].2 := by
  native_decide

theorem decode_1045 : decode runtimeBytecode ⟨1045⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1298⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨0, by decide⟩
theorem decode_1048 : decode runtimeBytecode ⟨1048⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨1, by decide⟩
theorem decode_1049 : decode runtimeBytecode ⟨1049⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨2, by decide⟩
theorem decode_1050 : decode runtimeBytecode ⟨1050⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨3, by decide⟩
theorem decode_1052 : decode runtimeBytecode ⟨1052⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨4, by decide⟩
theorem decode_1053 : decode runtimeBytecode ⟨1053⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1279⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨5, by decide⟩
theorem decode_1056 : decode runtimeBytecode ⟨1056⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨6, by decide⟩
theorem decode_1057 : decode runtimeBytecode ⟨1057⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨7, by decide⟩
theorem decode_1058 : decode runtimeBytecode ⟨1058⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨8, by decide⟩
theorem decode_1060 : decode runtimeBytecode ⟨1060⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨9, by decide⟩
theorem decode_1061 : decode runtimeBytecode ⟨1061⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1260⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨10, by decide⟩
theorem decode_1064 : decode runtimeBytecode ⟨1064⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨11, by decide⟩
theorem decode_1065 : decode runtimeBytecode ⟨1065⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨12, by decide⟩
theorem decode_1066 : decode runtimeBytecode ⟨1066⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨13, by decide⟩
theorem decode_1068 : decode runtimeBytecode ⟨1068⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨14, by decide⟩
theorem decode_1069 : decode runtimeBytecode ⟨1069⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1241⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨15, by decide⟩
theorem decode_1072 : decode runtimeBytecode ⟨1072⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨16, by decide⟩
theorem decode_1073 : decode runtimeBytecode ⟨1073⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨17, by decide⟩
theorem decode_1074 : decode runtimeBytecode ⟨1074⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨18, by decide⟩
theorem decode_1075 : decode runtimeBytecode ⟨1075⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨19, by decide⟩
theorem decode_1076 : decode runtimeBytecode ⟨1076⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1222⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨20, by decide⟩
theorem decode_1079 : decode runtimeBytecode ⟨1079⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨21, by decide⟩
theorem decode_1080 : decode runtimeBytecode ⟨1080⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨22, by decide⟩
theorem decode_1081 : decode runtimeBytecode ⟨1081⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨23, by decide⟩
theorem decode_1083 : decode runtimeBytecode ⟨1083⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨24, by decide⟩
theorem decode_1084 : decode runtimeBytecode ⟨1084⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1203⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨25, by decide⟩
theorem decode_1087 : decode runtimeBytecode ⟨1087⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨26, by decide⟩
theorem decode_1088 : decode runtimeBytecode ⟨1088⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨27, by decide⟩
theorem decode_1089 : decode runtimeBytecode ⟨1089⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨28, by decide⟩
theorem decode_1091 : decode runtimeBytecode ⟨1091⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨29, by decide⟩
theorem decode_1092 : decode runtimeBytecode ⟨1092⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1184⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨30, by decide⟩
theorem decode_1095 : decode runtimeBytecode ⟨1095⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨31, by decide⟩
theorem decode_1096 : decode runtimeBytecode ⟨1096⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨32, by decide⟩
theorem decode_1097 : decode runtimeBytecode ⟨1097⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨33, by decide⟩
theorem decode_1099 : decode runtimeBytecode ⟨1099⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨34, by decide⟩
theorem decode_1100 : decode runtimeBytecode ⟨1100⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1165⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨35, by decide⟩
theorem decode_1103 : decode runtimeBytecode ⟨1103⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨36, by decide⟩
theorem decode_1104 : decode runtimeBytecode ⟨1104⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨37, by decide⟩
theorem decode_1105 : decode runtimeBytecode ⟨1105⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨38, by decide⟩
theorem decode_1107 : decode runtimeBytecode ⟨1107⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨39, by decide⟩
theorem decode_1108 : decode runtimeBytecode ⟨1108⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1146⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨40, by decide⟩
theorem decode_1111 : decode runtimeBytecode ⟨1111⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨41, by decide⟩
theorem decode_1112 : decode runtimeBytecode ⟨1112⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨42, by decide⟩
theorem decode_1114 : decode runtimeBytecode ⟨1114⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨43, by decide⟩
theorem decode_1115 : decode runtimeBytecode ⟨1115⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1128⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨44, by decide⟩
theorem decode_1118 : decode runtimeBytecode ⟨1118⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨45, by decide⟩
theorem decode_1119 : decode runtimeBytecode ⟨1119⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨46, by decide⟩
theorem decode_1120 : decode runtimeBytecode ⟨1120⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨47, by decide⟩
theorem decode_1121 : decode runtimeBytecode ⟨1121⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨48, by decide⟩
theorem decode_1122 : decode runtimeBytecode ⟨1122⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨49, by decide⟩
theorem decode_1123 : decode runtimeBytecode ⟨1123⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨50, by decide⟩
theorem decode_1124 : decode runtimeBytecode ⟨1124⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨51, by decide⟩
theorem decode_1127 : decode runtimeBytecode ⟨1127⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨52, by decide⟩
theorem decode_1128 : decode runtimeBytecode ⟨1128⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨53, by decide⟩
theorem decode_1129 : decode runtimeBytecode ⟨1129⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨54, by decide⟩
theorem decode_1130 : decode runtimeBytecode ⟨1130⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨55, by decide⟩
theorem decode_1131 : decode runtimeBytecode ⟨1131⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨56, by decide⟩
theorem decode_1132 : decode runtimeBytecode ⟨1132⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨57, by decide⟩
theorem decode_1133 : decode runtimeBytecode ⟨1133⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨58, by decide⟩
theorem decode_1134 : decode runtimeBytecode ⟨1134⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨59, by decide⟩
theorem decode_1135 : decode runtimeBytecode ⟨1135⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨60, by decide⟩
theorem decode_1137 : decode runtimeBytecode ⟨1137⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨61, by decide⟩
theorem decode_1138 : decode runtimeBytecode ⟨1138⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨62, by decide⟩
theorem decode_1139 : decode runtimeBytecode ⟨1139⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨63, by decide⟩
theorem decode_1140 : decode runtimeBytecode ⟨1140⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨64, by decide⟩
theorem decode_1141 : decode runtimeBytecode ⟨1141⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨65, by decide⟩
theorem decode_1142 : decode runtimeBytecode ⟨1142⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨66, by decide⟩
theorem decode_1145 : decode runtimeBytecode ⟨1145⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨67, by decide⟩
theorem decode_1146 : decode runtimeBytecode ⟨1146⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨68, by decide⟩
theorem decode_1147 : decode runtimeBytecode ⟨1147⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨69, by decide⟩
theorem decode_1148 : decode runtimeBytecode ⟨1148⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨70, by decide⟩
theorem decode_1149 : decode runtimeBytecode ⟨1149⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨71, by decide⟩
theorem decode_1150 : decode runtimeBytecode ⟨1150⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨72, by decide⟩
theorem decode_1151 : decode runtimeBytecode ⟨1151⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨73, by decide⟩
theorem decode_1152 : decode runtimeBytecode ⟨1152⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨74, by decide⟩
theorem decode_1153 : decode runtimeBytecode ⟨1153⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨75, by decide⟩
theorem decode_1154 : decode runtimeBytecode ⟨1154⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨76, by decide⟩
theorem decode_1156 : decode runtimeBytecode ⟨1156⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨77, by decide⟩
theorem decode_1157 : decode runtimeBytecode ⟨1157⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨78, by decide⟩
theorem decode_1158 : decode runtimeBytecode ⟨1158⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨79, by decide⟩
theorem decode_1159 : decode runtimeBytecode ⟨1159⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨80, by decide⟩
theorem decode_1160 : decode runtimeBytecode ⟨1160⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨81, by decide⟩
theorem decode_1161 : decode runtimeBytecode ⟨1161⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨82, by decide⟩
theorem decode_1164 : decode runtimeBytecode ⟨1164⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨83, by decide⟩
theorem decode_1165 : decode runtimeBytecode ⟨1165⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨84, by decide⟩
theorem decode_1166 : decode runtimeBytecode ⟨1166⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨85, by decide⟩
theorem decode_1167 : decode runtimeBytecode ⟨1167⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨86, by decide⟩
theorem decode_1168 : decode runtimeBytecode ⟨1168⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨87, by decide⟩
theorem decode_1169 : decode runtimeBytecode ⟨1169⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨88, by decide⟩
theorem decode_1170 : decode runtimeBytecode ⟨1170⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨89, by decide⟩
theorem decode_1171 : decode runtimeBytecode ⟨1171⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨90, by decide⟩
theorem decode_1172 : decode runtimeBytecode ⟨1172⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨91, by decide⟩
theorem decode_1173 : decode runtimeBytecode ⟨1173⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨92, by decide⟩
theorem decode_1175 : decode runtimeBytecode ⟨1175⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨93, by decide⟩
theorem decode_1176 : decode runtimeBytecode ⟨1176⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨94, by decide⟩
theorem decode_1177 : decode runtimeBytecode ⟨1177⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨95, by decide⟩
theorem decode_1178 : decode runtimeBytecode ⟨1178⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨96, by decide⟩
theorem decode_1179 : decode runtimeBytecode ⟨1179⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨97, by decide⟩
theorem decode_1180 : decode runtimeBytecode ⟨1180⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨98, by decide⟩
theorem decode_1183 : decode runtimeBytecode ⟨1183⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes6] using generatedDecodes6_correct ⟨99, by decide⟩

end Ripemd160Old
