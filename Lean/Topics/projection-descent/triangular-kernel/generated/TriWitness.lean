import ClosedProof
open ProjectionDescent Triangular Triangular.Data
private def dump (g : Bool) : IO Unit := do
  for r in parent (ps g) (top::rest g) do
    IO.println s!"ROW {r.1}"
    for t in r.2 do IO.println (toString t.coefficient ++ "|" ++ String.intercalate "," (t.monomial.map toString))
  for p in ps g do IO.println s!"PIVOT {p.id} {p.slot}"
  for i in List.range 153 do IO.println s!"FREE {back (i+1)} {w (back (i+1))}"
#eval dump false
#eval dump true
