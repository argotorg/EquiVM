import Benchmarks.UniswapV4PoolManager.WordArrayLoop

namespace Benchmarks.UniswapV4PoolManager
abbrev exttloadArrayCond := wordArrayCond
abbrev exttloadArrayLoopBody := wordArrayLoopBody true
abbrev exttloadArrayValue := wordArrayValue true
abbrev ExttloadArrayLocals := WordArrayLocals
abbrev exttloadArrayLoopStep := wordArrayLoopStep true
abbrev exttloadArraySourceLoop := wordArraySourceLoop true
end Benchmarks.UniswapV4PoolManager
