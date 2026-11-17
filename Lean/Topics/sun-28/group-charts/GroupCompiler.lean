import GroupReadouts
import CompiledEndpoint

namespace Sun28.GroupCharts
open ZInQ WeierstrassCurve.Affine
open Sun28.Compiler Sun28.Branches ZInQBlueprint.SunResultant
noncomputable section

namespace Program

/-- A leaf may return additional polynomial tests using its locally computed outputs. -/
def branchList {m n : ℕ} (T : ParamTower (Poly m) n)
    (prog : Program (Test m n) (Row (Test m n) Unit)) : List (Compiler.Branch m) :=
  prog.rows.map fun r =>
    ⟨n,T,r.equations++r.output.equations,r.guards++r.output.guards⟩

/-- At each specialization of all base parameters the original tower is retained;
all computed arithmetic and group-law intermediates cost zero new root variables. -/
theorem branchList_correct {m n : ℕ} (T : ParamTower (Poly m) n)
    (prog : Program (Test m n) (Row (Test m n) Unit)) (v : Fin m → ℚ) :
    (∃ b ∈ branchList T prog, Solutions b.tower b.equations b.guards v) ↔
      ∃ x : Fin n → ℚ, ParamTower.Satisfies (value v) T x ∧
        (Program.eval (MvPolynomial.eval₂Hom (value v) x) prog).Live (MvPolynomial.eval₂Hom (value v) x) := by
  constructor
  · rintro ⟨b,hb,x,ht,he,hg⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hb
    let φ := MvPolynomial.eval₂Hom (value v) x
    have both : (r.join r.output).Live φ := ⟨he,hg⟩
    obtain ⟨left,right⟩ := (Row.live_join ..).1 both
    have h : Program.eval φ prog=r.output := (rows_correct ..).1 ⟨r,hr,left,rfl⟩
    exact ⟨x,ht,h ▸ right⟩
  · rintro ⟨x,ht,tests⟩
    let φ := MvPolynomial.eval₂Hom (value v) x
    obtain ⟨r,hr,valid,e⟩ := (rows_correct φ prog _).2 rfl
    have both := (Row.live_join φ r r.output).2 ⟨valid,e ▸ tests⟩
    exact ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,x,ht,both.1,both.2⟩
end Program

namespace PointCode
variable {R : Type*} [CommRing R]

def scalarPoint (M : ℕ) (q : PointCode R) := mulProgram M q

def shiftedScalar (M : ℕ) (q : PointCode R) : Program R (PointCode R) :=
  Program.bind (addProgram generator) (scalarPoint M q)

theorem shiftedScalar_correct (φ : R →+* ℚ) (M : ℕ) {q : PointCode R} {Q : curveC.toAffine.Point}
    (hq : Represents φ q Q) :
    Represents φ (Program.eval φ (shiftedScalar M q)) (WitnessIndices.P + M • Q) := by
  rw [shiftedScalar,Program.eval_bind]
  exact add_correct φ (generator_correct φ) (mul_correct φ M hq)

/-- The affine equality input by itself does not assume either coordinate of the curve. -/
def equalityRow (a b : PointCode R) : Row R Unit := ⟨[equalTest a b],[],()⟩
def inequalityRow (a b : PointCode R) : Row R Unit := ⟨[],[equalTest a b],()⟩

theorem eqRow_correct (φ : R →+* ℚ) {p q : PointCode R} {P Q : curveC.toAffine.Point}
    (hp : Represents φ p P) (hq : Represents φ q Q) :
    ((equalityRow p q).Live φ ↔ P=Q) ∧ ((inequalityRow p q).Live φ ↔ P≠Q) := by
  simp [equalityRow,inequalityRow,Row.Live,equalTest_correct φ hp hq]

end PointCode
end
#print axioms Program.branchList_correct
#print axioms PointCode.shiftedScalar_correct
#print axioms PointCode.eqRow_correct
end Sun28.GroupCharts
