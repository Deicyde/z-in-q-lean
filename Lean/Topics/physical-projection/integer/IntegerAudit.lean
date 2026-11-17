import IntegerProjection
namespace Physical130.Audit
open ZeroInput.Sparse CircuitTransport PhysicalProjection Triangular.Data

private def opText : Op→String
  | .var n => s!"v|{n}" | .int c => s!"i|{c}"
  | .add i j => s!"a|{i}|{j}" | .mul i j => s!"m|{i}|{j}"

private def ref : Word→String | .ref n=>toString n | _=>"-"

private def dump (g : Bool) : IO Unit := do
  let ns:=Seeds.nodes g
  IO.println s!"SEED {ns.size}"
  for op in ns do IO.println (opText op)
  let p:=program g
  IO.println s!"PROGRAM {p.nodes.length} {p.ordinary} {p.marked}"
  for op in p.nodes do IO.println (opText op)
  for i in parentSlots do IO.println s!"SLOT {i} {compactSlot i} {finiteLift designated (compactSlot i)}"
  for r in parentRows g do
    IO.println s!"SOURCE {r.1}"
    for t in r.2 do IO.println (toString t.coefficient ++ "|" ++ String.intercalate "," (t.monomial.map toString))
  let b:=Book.make ns
  let early:=cells b (ps g) (base b)
  let ds:=makeDet b early
  for k in detectors do
    let c:=clearRow b (select (base b) early) (timeRow k)
    let d:=ds.atBlock k
    IO.println s!"GUARD {k.e} {ref c.num} {c.den} {ref d.a} {ref d.q} {ref d.bigQ} {ref d.guard}"
  let a:=cells b (ps g) (middleBase b ds)
  let env:=select (middleBase b ds) a
  let cs:=makeCram b ds a
  for pivot in ps g do
    let c:=env pivot.slot
    IO.println s!"PIVOT {pivot.id} {pivot.slot} {ref c.num} {c.den}"
  for k in pairs do
    let f:=line b env k.slot k.f
    let h:=line b env k.slot k.g
    let t:=cs.atPair k
    IO.println s!"PAIR {k.rid} {k.slot} {f.den} {ref f.c} {ref f.u} {ref f.v} {h.den} {ref h.c} {ref h.u} {ref h.v} {ref t.d} {ref t.u} {ref t.v}"
  for r in peakRows g ++ lowRows g do
    let n:=numerator b env cs r
    match occurrence r.1 with
    | none => IO.println s!"ROW {r.1} {ref n} {common env r.2} -"
    | some k => IO.println s!"ROW {r.1} {ref n} {(line b env k.slot r.2).den} {ref (cs.atPair k).d}"
  IO.println s!"MARK {p.eval true (finiteLift designated)}"
  IO.println "END"

#eval dump false
#eval dump true
end Physical130.Audit
