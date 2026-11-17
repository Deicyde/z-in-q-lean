import PDGate510Data
import PDGate67830Data
open ProjectionDescent
private def dump (s : String) (rows : Rows) : IO Unit := do
  IO.println s
  for r in rows do
    IO.println s!"ROW {r.1}"
    for t in r.2 do
      IO.println (toString t.coefficient ++ "|" ++ String.intercalate "," (t.monomial.map toString))
#eval dump "510 parent" Gate510.parent
#eval dump "510 compact" Gate510.compact
#eval dump "67830 parent" Gate67830.parent
#eval dump "67830 compact" Gate67830.compact
