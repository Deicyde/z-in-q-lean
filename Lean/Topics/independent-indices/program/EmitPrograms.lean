import IndexData
open CircuitTransport IndependentIndices IndependentIndices.Data

private def textOp : Op→String
  | .var n => "v|"++toString n
  | .int n => "i|"++toString n
  | .add i j => "a|"++toString i++"|"++toString j
  | .mul i j => "m|"++toString i++"|"++toString j

private def dump (name : String) (seed : Array Op) (fs : Families) (rs : Routes) (s : Shape) : IO Unit := do
  let c:=build seed fs rs s
  IO.println s!"PROGRAM {name} {c.ordinary} {c.marked} {c.nodes.length}"
  for op in c.nodes do IO.println (textOp op)
  let b:=Book.make seed
  let ws:=tables b fs rs
  for r in s.high.refs++s.low.refs do
    match fromTables b fs rs ws r with
    | .ref i => IO.println s!"ROW {r.cell} {r.node} {r.origin} {i}"
    | _ => IO.println "UNBOUND ROW"
  IO.println "END"

def main : IO Unit := do
  for gate in [false,true] do
    let n:=if gate then "67830" else "510"
    let fs:=families gate
    for (ops,i) in fs.toList.zipIdx do
      IO.println s!"FAMILY {n} {i} {ops.length}"
      for op in ops do IO.println (textOp op)
    dump (n++"-74") (oldSeed gate) fs oldRoutes oldShape
    dump (n++"-134") (newSeed gate) fs newRoutes newShape
