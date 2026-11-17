import SquareData
namespace SquareProgram.Emit
open CircuitTransport SquareProgram SquareProgram.Data

private def textOp : Op→String
  | .var n => "v|"++toString n
  | .int n => "i|"++toString n
  | .add i j => "a|"++toString i++"|"++toString j
  | .mul i j => "m|"++toString i++"|"++toString j
private def ref : Word→String
  | .ref i => toString i
  | _ => "missing"
def emitAll : IO Unit := do
  let ops:=source
  let b:=Book.make targetSeed
  let t:=bank ops
  let w:=table b ops
  let p:=compile targetSeed ops shape
  IO.println s!"SOURCE {ops.length}"
  for op in ops do IO.println (textOp op)
  IO.println s!"TARGET {p.nodes.length} {p.ordinary} {p.marked}"
  for op in p.nodes do IO.println (textOp op)
  for r in peaks++others do
    let v:=result b ops.length t w r
    let word:=ref (v.num b)
    match r with
    | .replace492 => IO.println s!"REPLACED 492 {v.exponent} {word}"
    | .inherit f i high =>
      let j:=guardedIndex ops.length t f i high
      let e:=(getA empty w j).im.isNone
      IO.println s!"SIGNED {i} {j} {v.exponent} {word} {e} {high}"
end SquareProgram.Emit

def main : IO Unit := SquareProgram.Emit.emitAll
