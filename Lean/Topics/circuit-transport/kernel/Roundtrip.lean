import Certificates
namespace CircuitTransport
open ZeroInput.Sparse
open Triangular.Data (ps top rest code back)

private def showNode : Op→String
  | .var i => "v|"++toString i
  | .int n => "i|"++toString n
  | .add a b => "a|"++toString a++"|"++toString b
  | .mul a b => "m|"++toString a++"|"++toString b

private def reference : Word→String
  | .ref i => toString i
  | _ => "fallback"

private def dump (g : Bool) : IO Unit := do
  let seed := Seeds.nodes g
  IO.println s!"SEED {seed.size}"
  for op in seed do IO.println (showNode op)
  let p := published g
  IO.println s!"PROGRAM {p.nodes.length} {p.ordinary} {p.marked}"
  for op in p.nodes do IO.println (showNode op)
  for i in List.range 153 do IO.println s!"SLOT {back (i+1)} {Triangular.Data.w (back (i+1))}"
  for r in source g do
    IO.println s!"SOURCE {r.1}"
    for t in r.2 do IO.println (toString t.coefficient ++ "|" ++ String.intercalate "," (t.monomial.map toString))
  let b := Book.make seed
  let base := initial b code
  let stored := cells b (ps g) base
  let env := select base stored
  for pivot in ps g do
    let c := env pivot.slot
    IO.println s!"PIVOT {pivot.id} {pivot.slot} {reference c.num} {c.den}"
  for row in top::rest g do
    let c := clearRow b env row.2
    IO.println s!"ROW {row.1} {reference c.num} {c.den}"
  IO.println s!"MARK {p.eval true (finiteLift designated)}"
  IO.println "END"

#eval dump false
#eval dump true
end CircuitTransport
namespace CircuitTransport
private def badHint (forward : Bool) : Program :=
  let ops : Array Op := if forward then #[.add 1 1,.var 1] else #[.var 1,.mul 0 0]
  let i := if forward then 1 else 0
  let wrong := if forward then 0 else 1
  let index : Std.HashMap Op Nat := ({} : Std.HashMap Op Nat).insert (.add i i) wrong
  let b : Book := ⟨ops,index⟩
  finish b (plus b (.ref i) (.ref i)) (.ref i)
private def controlDump : IO Unit := do
  for forward in [false,true] do
    let p := badHint forward
    IO.println s!"BAD_HINT {forward} {p.nodes.length} {p.ordinary} {p.eval false (fun _ => 3)}"
#eval controlDump
end CircuitTransport
