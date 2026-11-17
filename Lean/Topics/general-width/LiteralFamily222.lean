import EncodedTower

/-! The 85-variable integer polynomial for the 222-coordinate family.
The first two variables are the coefficient parameter and original input. -/
open ZInQBlueprint.SunResultant Sun28.Branches Sun28.Compiler
namespace FamilyWidth222
noncomputable section

private def dataSet := EncodedTower.decode (include_str "data/nodes.txt")
  (include_str "data/stages.txt") (include_str "data/tests.txt")
#guard EncodedTower.valid dataSet 84 139 5429 196
private def branch := EncodedTower.asBranch dataSet 84
private def inputs (a x : ℚ) : Fin 2 → ℚ := Fin.cases a (fun _ => x)

def polynomial85 : Poly 85 :=
  RelativeWidth.equation (k:=2) (d:=82) branch.charts

def admits (a x : ℚ) : Prop :=
  ∃ y : Fin 82 → ℚ, branch.accepts (Fin.append (inputs a x) y)

attribute [local irreducible] branch in
set_option maxHeartbeats 2000000 in
theorem projection (a x : ℚ) :
    (∃ y : Fin 82 → ℚ, ∃ w : ℚ,
      value (RelativeWidth.point (inputs a x) y w) polynomial85 = 0) ↔ admits a x := by
  unfold polynomial85 admits
  exact (RelativeWidth.charts_spec (k:=2) (d:=82) branch.charts (inputs a x)).trans
    (exists_congr fun y => Sun28.Compiler.atlas_spec branch.tower branch.equations branch.guards
      (Fin.append (inputs a x) y))

end
end FamilyWidth222
#print axioms FamilyWidth222.projection
