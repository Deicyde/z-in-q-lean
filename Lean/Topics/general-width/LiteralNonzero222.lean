import EncodedTower

/-! The 67-variable integer polynomial for the 222-coordinate family.
The first two variables are the coefficient parameter and original input. -/
open ZInQBlueprint.SunResultant Sun28.Branches Sun28.Compiler
namespace FamilyWidth222.Nonzero
noncomputable section

private def dataSet := EncodedTower.decode (include_str "data-nonzero/nodes.txt")
  (include_str "data-nonzero/stages.txt") (include_str "data-nonzero/tests.txt")
#guard EncodedTower.valid dataSet 66 157 4421 196
private def branch := EncodedTower.asBranch dataSet 66
private def inputs (a x : ℚ) : Fin 2 → ℚ := Fin.cases a (fun _ => x)

def polynomial67 : Poly 67 :=
  RelativeWidth.equation (k:=2) (d:=64) branch.charts

def admits (a x : ℚ) : Prop :=
  ∃ y : Fin 64 → ℚ, branch.accepts (Fin.append (inputs a x) y)

attribute [local irreducible] branch in
set_option maxHeartbeats 2000000 in
theorem projection (a x : ℚ) :
    (∃ y : Fin 64 → ℚ, ∃ w : ℚ,
      value (RelativeWidth.point (inputs a x) y w) polynomial67 = 0) ↔ admits a x := by
  unfold polynomial67 admits
  exact (RelativeWidth.charts_spec (k:=2) (d:=64) branch.charts (inputs a x)).trans
    (exists_congr fun y => Sun28.Compiler.atlas_spec branch.tower branch.equations branch.guards
      (Fin.append (inputs a x) y))

end
end FamilyWidth222.Nonzero
#print axioms FamilyWidth222.Nonzero.projection

namespace FamilyWidth222.Nonzero
noncomputable section

private def replaceScale (a : ℤ) : Fin 67 → Poly 66 :=
  Fin.cases (MvPolynomial.C a) MvPolynomial.X

def polynomial66 (a : ℤ) : Poly 66 := MvPolynomial.bind₁ (replaceScale a) polynomial67

private theorem putScale (a : ℤ) (x : ℚ) (z : Fin 64 → ℚ) (w : ℚ) :
    value (RelativeWidth.point (fun _ : Fin 1 => x) z w) (polynomial66 a) =
      value (RelativeWidth.point (inputs (a : ℚ) x) z w) polynomial67 := by
  unfold polynomial66 value
  rw [MvPolynomial.eval₂Hom_bind₁]
  have coords : (fun i => MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (RelativeWidth.point (fun _ : Fin 1 => x) z w) (replaceScale a i)) =
      RelativeWidth.point (inputs (a : ℚ) x) z w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [replaceScale, Fin.cases_zero, MvPolynomial.eval₂Hom_C]
      rfl
    · simp only [replaceScale, Fin.cases_succ, MvPolynomial.eval₂Hom_X']
      fin_cases j <;> rfl
  rw [coords]

theorem projection66 (a : ℤ) (x : ℚ) :
    (∃ z : Fin 64 → ℚ, ∃ w : ℚ,
      value (RelativeWidth.point (fun _ : Fin 1 => x) z w) (polynomial66 a) = 0) ↔
      admits (a : ℚ) x := by
  simpa only [putScale] using projection (a : ℚ) x

end
end FamilyWidth222.Nonzero
#print axioms FamilyWidth222.Nonzero.projection66
