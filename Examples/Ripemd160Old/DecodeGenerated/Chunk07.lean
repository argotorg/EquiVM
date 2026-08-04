import Examples.Ripemd160Old.DecodeGenerated.Chunk06

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes7 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨1184⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1185⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1186⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1187⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1188⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1189⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1190⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1191⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1192⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨1194⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1195⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1196⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1197⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1198⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1199⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1202⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1203⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1204⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1205⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1206⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1207⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1208⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1209⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1210⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1211⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨1213⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1214⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1215⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1216⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1217⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1218⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1221⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1222⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1223⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1224⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1225⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1226⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1227⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1228⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1229⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1230⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨1232⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1233⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1234⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1235⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1236⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1237⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1240⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1241⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1242⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1243⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1244⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1245⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1246⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1247⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1248⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1249⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨1251⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1252⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1253⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1254⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1255⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1256⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1259⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1260⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1261⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1262⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1263⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1264⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1265⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1266⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1267⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1268⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨1270⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1271⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1272⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1273⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1274⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1275⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1278⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1279⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1280⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1281⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1282⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1283⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1284⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1285⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1286⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1287⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨1289⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1290⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1291⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1292⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1293⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1294⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1297⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1298⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1299⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1300⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1301⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none))
]

private theorem generatedDecodes7_correct : ∀ i : Fin generatedDecodes7.size,
    decode runtimeBytecode generatedDecodes7[i].1 = generatedDecodes7[i].2 := by
  native_decide

theorem decode_1184 : decode runtimeBytecode ⟨1184⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨0, by decide⟩
theorem decode_1185 : decode runtimeBytecode ⟨1185⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨1, by decide⟩
theorem decode_1186 : decode runtimeBytecode ⟨1186⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨2, by decide⟩
theorem decode_1187 : decode runtimeBytecode ⟨1187⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨3, by decide⟩
theorem decode_1188 : decode runtimeBytecode ⟨1188⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨4, by decide⟩
theorem decode_1189 : decode runtimeBytecode ⟨1189⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨5, by decide⟩
theorem decode_1190 : decode runtimeBytecode ⟨1190⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨6, by decide⟩
theorem decode_1191 : decode runtimeBytecode ⟨1191⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨7, by decide⟩
theorem decode_1192 : decode runtimeBytecode ⟨1192⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨8, by decide⟩
theorem decode_1194 : decode runtimeBytecode ⟨1194⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨9, by decide⟩
theorem decode_1195 : decode runtimeBytecode ⟨1195⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨10, by decide⟩
theorem decode_1196 : decode runtimeBytecode ⟨1196⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨11, by decide⟩
theorem decode_1197 : decode runtimeBytecode ⟨1197⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨12, by decide⟩
theorem decode_1198 : decode runtimeBytecode ⟨1198⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨13, by decide⟩
theorem decode_1199 : decode runtimeBytecode ⟨1199⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨14, by decide⟩
theorem decode_1202 : decode runtimeBytecode ⟨1202⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨15, by decide⟩
theorem decode_1203 : decode runtimeBytecode ⟨1203⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨16, by decide⟩
theorem decode_1204 : decode runtimeBytecode ⟨1204⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨17, by decide⟩
theorem decode_1205 : decode runtimeBytecode ⟨1205⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨18, by decide⟩
theorem decode_1206 : decode runtimeBytecode ⟨1206⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨19, by decide⟩
theorem decode_1207 : decode runtimeBytecode ⟨1207⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨20, by decide⟩
theorem decode_1208 : decode runtimeBytecode ⟨1208⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨21, by decide⟩
theorem decode_1209 : decode runtimeBytecode ⟨1209⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨22, by decide⟩
theorem decode_1210 : decode runtimeBytecode ⟨1210⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨23, by decide⟩
theorem decode_1211 : decode runtimeBytecode ⟨1211⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨24, by decide⟩
theorem decode_1213 : decode runtimeBytecode ⟨1213⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨25, by decide⟩
theorem decode_1214 : decode runtimeBytecode ⟨1214⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨26, by decide⟩
theorem decode_1215 : decode runtimeBytecode ⟨1215⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨27, by decide⟩
theorem decode_1216 : decode runtimeBytecode ⟨1216⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨28, by decide⟩
theorem decode_1217 : decode runtimeBytecode ⟨1217⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨29, by decide⟩
theorem decode_1218 : decode runtimeBytecode ⟨1218⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨30, by decide⟩
theorem decode_1221 : decode runtimeBytecode ⟨1221⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨31, by decide⟩
theorem decode_1222 : decode runtimeBytecode ⟨1222⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨32, by decide⟩
theorem decode_1223 : decode runtimeBytecode ⟨1223⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨33, by decide⟩
theorem decode_1224 : decode runtimeBytecode ⟨1224⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨34, by decide⟩
theorem decode_1225 : decode runtimeBytecode ⟨1225⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨35, by decide⟩
theorem decode_1226 : decode runtimeBytecode ⟨1226⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨36, by decide⟩
theorem decode_1227 : decode runtimeBytecode ⟨1227⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨37, by decide⟩
theorem decode_1228 : decode runtimeBytecode ⟨1228⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨38, by decide⟩
theorem decode_1229 : decode runtimeBytecode ⟨1229⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨39, by decide⟩
theorem decode_1230 : decode runtimeBytecode ⟨1230⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨40, by decide⟩
theorem decode_1232 : decode runtimeBytecode ⟨1232⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨41, by decide⟩
theorem decode_1233 : decode runtimeBytecode ⟨1233⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨42, by decide⟩
theorem decode_1234 : decode runtimeBytecode ⟨1234⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨43, by decide⟩
theorem decode_1235 : decode runtimeBytecode ⟨1235⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨44, by decide⟩
theorem decode_1236 : decode runtimeBytecode ⟨1236⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨45, by decide⟩
theorem decode_1237 : decode runtimeBytecode ⟨1237⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨46, by decide⟩
theorem decode_1240 : decode runtimeBytecode ⟨1240⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨47, by decide⟩
theorem decode_1241 : decode runtimeBytecode ⟨1241⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨48, by decide⟩
theorem decode_1242 : decode runtimeBytecode ⟨1242⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨49, by decide⟩
theorem decode_1243 : decode runtimeBytecode ⟨1243⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨50, by decide⟩
theorem decode_1244 : decode runtimeBytecode ⟨1244⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨51, by decide⟩
theorem decode_1245 : decode runtimeBytecode ⟨1245⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨52, by decide⟩
theorem decode_1246 : decode runtimeBytecode ⟨1246⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨53, by decide⟩
theorem decode_1247 : decode runtimeBytecode ⟨1247⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨54, by decide⟩
theorem decode_1248 : decode runtimeBytecode ⟨1248⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨55, by decide⟩
theorem decode_1249 : decode runtimeBytecode ⟨1249⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨56, by decide⟩
theorem decode_1251 : decode runtimeBytecode ⟨1251⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨57, by decide⟩
theorem decode_1252 : decode runtimeBytecode ⟨1252⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨58, by decide⟩
theorem decode_1253 : decode runtimeBytecode ⟨1253⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨59, by decide⟩
theorem decode_1254 : decode runtimeBytecode ⟨1254⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨60, by decide⟩
theorem decode_1255 : decode runtimeBytecode ⟨1255⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨61, by decide⟩
theorem decode_1256 : decode runtimeBytecode ⟨1256⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨62, by decide⟩
theorem decode_1259 : decode runtimeBytecode ⟨1259⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨63, by decide⟩
theorem decode_1260 : decode runtimeBytecode ⟨1260⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨64, by decide⟩
theorem decode_1261 : decode runtimeBytecode ⟨1261⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨65, by decide⟩
theorem decode_1262 : decode runtimeBytecode ⟨1262⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨66, by decide⟩
theorem decode_1263 : decode runtimeBytecode ⟨1263⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨67, by decide⟩
theorem decode_1264 : decode runtimeBytecode ⟨1264⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨68, by decide⟩
theorem decode_1265 : decode runtimeBytecode ⟨1265⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨69, by decide⟩
theorem decode_1266 : decode runtimeBytecode ⟨1266⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨70, by decide⟩
theorem decode_1267 : decode runtimeBytecode ⟨1267⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨71, by decide⟩
theorem decode_1268 : decode runtimeBytecode ⟨1268⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨72, by decide⟩
theorem decode_1270 : decode runtimeBytecode ⟨1270⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨73, by decide⟩
theorem decode_1271 : decode runtimeBytecode ⟨1271⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨74, by decide⟩
theorem decode_1272 : decode runtimeBytecode ⟨1272⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨75, by decide⟩
theorem decode_1273 : decode runtimeBytecode ⟨1273⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨76, by decide⟩
theorem decode_1274 : decode runtimeBytecode ⟨1274⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨77, by decide⟩
theorem decode_1275 : decode runtimeBytecode ⟨1275⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨78, by decide⟩
theorem decode_1278 : decode runtimeBytecode ⟨1278⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨79, by decide⟩
theorem decode_1279 : decode runtimeBytecode ⟨1279⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨80, by decide⟩
theorem decode_1280 : decode runtimeBytecode ⟨1280⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨81, by decide⟩
theorem decode_1281 : decode runtimeBytecode ⟨1281⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨82, by decide⟩
theorem decode_1282 : decode runtimeBytecode ⟨1282⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨83, by decide⟩
theorem decode_1283 : decode runtimeBytecode ⟨1283⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨84, by decide⟩
theorem decode_1284 : decode runtimeBytecode ⟨1284⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨85, by decide⟩
theorem decode_1285 : decode runtimeBytecode ⟨1285⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨86, by decide⟩
theorem decode_1286 : decode runtimeBytecode ⟨1286⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨87, by decide⟩
theorem decode_1287 : decode runtimeBytecode ⟨1287⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨88, by decide⟩
theorem decode_1289 : decode runtimeBytecode ⟨1289⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨89, by decide⟩
theorem decode_1290 : decode runtimeBytecode ⟨1290⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨90, by decide⟩
theorem decode_1291 : decode runtimeBytecode ⟨1291⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨91, by decide⟩
theorem decode_1292 : decode runtimeBytecode ⟨1292⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨92, by decide⟩
theorem decode_1293 : decode runtimeBytecode ⟨1293⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨93, by decide⟩
theorem decode_1294 : decode runtimeBytecode ⟨1294⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨94, by decide⟩
theorem decode_1297 : decode runtimeBytecode ⟨1297⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨95, by decide⟩
theorem decode_1298 : decode runtimeBytecode ⟨1298⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨96, by decide⟩
theorem decode_1299 : decode runtimeBytecode ⟨1299⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨97, by decide⟩
theorem decode_1300 : decode runtimeBytecode ⟨1300⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨98, by decide⟩
theorem decode_1301 : decode runtimeBytecode ⟨1301⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes7] using generatedDecodes7_correct ⟨99, by decide⟩

end Ripemd160Old
