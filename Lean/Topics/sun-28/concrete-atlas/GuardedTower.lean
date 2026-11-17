import TowerRootCharts
import CompiledEndpoint

/-! Finite signed root charts with polynomial tests carried through a tower. -/
open Polynomial ZInQBlueprint.SunResultant
namespace Sun28.Concrete
open Sun28.Ordinates Sun28.RootCharts
noncomputable section
variable {R : Type*} [CommRing R] {n : ℕ}

abbrev Test (R : Type*) [CommRing R] (n : ℕ) := MvPolynomial (Fin n) R

structure Row (R : Type*) [CommRing R] (n : ℕ) where
  tower : ParamTower R n
  equations : List (Test R n)
  guards : List (Test R n)

abbrev ev (φ : R →+* ℚ) (x : Fin n → ℚ) := MvPolynomial.eval₂Hom φ x

def Row.Holds (r : Row R n) (φ : R →+* ℚ) (x : Fin n → ℚ) : Prop :=
  ParamTower.Satisfies φ r.tower x ∧
  (∀ f ∈ r.equations, ev φ x f = 0) ∧ ∀ g ∈ r.guards, ev φ x g ≠ 0

def Row.base : Row R 0 := ⟨.base,[],[]⟩

def Row.branch {m : ℕ} (r : Row (Sun28.Branches.Poly m) n) : Sun28.Compiler.Branch m :=
  ⟨n,r.tower,r.equations,r.guards⟩

theorem row_solutions {m : ℕ} (r : Row (Sun28.Branches.Poly m) n) (p : Fin m → ℚ) :
    Sun28.Compiler.Solutions r.branch.tower r.branch.equations r.branch.guards p ↔
      ∃ t, r.Holds (Sun28.Branches.value p) t := Iff.rfl

def liftTest (f : Test R n) : Test R (n+1) := asTest (C f)

@[simp] theorem eval_lift (φ : R →+* ℚ) (x : Fin n → ℚ) (w : ℚ) (f : Test R n) :
    ev φ (Fin.cons w x) (liftTest f) = ev φ x f := by
  change MvPolynomial.eval₂Hom φ _ (asTest _) = _
  rw [eval_asTest]
  simp

def Row.signed (r : Row R n) (k : Branch) (A B D : Test R n) : Row R (n+1) :=
  ⟨stage r.tower k A B D, r.equations.map liftTest ++ (zeroTests k A B).map asTest,
    r.guards.map liftTest ++ (nonzeroTests k A B D).map asTest⟩

theorem signed_iff (r : Row R n) (φ : R →+* ℚ) (x : Fin n → ℚ) (w : ℚ)
    (k : Branch) (A B D : Test R n) :
    (r.signed k A B D).Holds φ (Fin.cons w x) ↔
      r.Holds φ x ∧ guard k (ev φ x A) (ev φ x B) (ev φ x D) w ∧
        ((polynomial k A B D).map (ev φ x)).IsRoot w := by
  rw [guard_polynomials]
  simp only [Row.Holds,Row.signed,stage,ParamTower.Satisfies,Fin.tail_cons,Fin.cons_zero,
    List.forall_mem_append, List.forall_mem_map,eval_lift]
  simp only [ev,eval_asTest]
  tauto

/-- Numerators and common denominator of the actual signed output on the enlarged tower. -/
def signedOutput (k : Branch) (B D : Test R n) : Test R (n+1) × Test R (n+1) × Test R (n+1) :=
  let q := coordinates k B D
  (asTest q.1,asTest q.2.1,asTest q.2.2)

def reads (φ : R →+* ℚ) (x : Fin n → ℚ) (q : Test R n × Test R n × Test R n) (y : K) : Prop :=
  ev φ x q.2.2 ≠ 0 ∧ y = pair (ev φ x q.1 / ev φ x q.2.2) (ev φ x q.2.1 / ev φ x q.2.2)

theorem reads_output (φ : R →+* ℚ) (x : Fin n → ℚ) (k : Branch) (A B D : Test R n) (w : ℚ)
    (hg : guard k (ev φ x A) (ev φ x B) (ev φ x D) w) (y : K) :
    reads φ (Fin.cons w x) (signedOutput k B D) y ↔ y=reconstruct k (ev φ x B) (ev φ x D) w := by
  have h:= coordinates_spec (ev φ x) k A B D w hg
  simp only [reads,signedOutput,ev,eval_asTest]
  simp only [← eval₂_eq_eval_map]
  exact ⟨fun h' => h'.2.trans h.2.symm,fun hy => ⟨h.1,hy.trans h.2⟩⟩

theorem signed_square (r : Row R n) (φ : R →+* ℚ) (x : Fin n → ℚ)
    (A B D : Test R n) (y : K) :
    (r.Holds φ x ∧ ev φ x D ≠ 0 ∧ y^2 = pair (ev φ x A / ev φ x D) (ev φ x B / ev φ x D)) ↔
      ∃ (k : Branch) (w : ℚ), (r.signed k A B D).Holds φ (Fin.cons w x) ∧
        reads φ (Fin.cons w x) (signedOutput k B D) y := by
  rw [square_iff_root (ev φ x) A B D y]
  constructor
  · rintro ⟨hr,k,w,hg,hw,hy⟩
    exact ⟨k,w,(signed_iff ..).2 ⟨hr,hg,hw⟩,(reads_output _ _ _ A _ _ _ hg y).2 hy⟩
  · rintro ⟨k,w,hs,hy⟩
    obtain ⟨hr,hg,hw⟩ := (signed_iff ..).1 hs
    exact ⟨hr,k,w,hg,hw,(reads_output _ _ _ A _ _ _ hg y).1 hy⟩

end
end Sun28.Concrete
#print axioms Sun28.Concrete.row_solutions
#print axioms Sun28.Concrete.eval_lift
#print axioms Sun28.Concrete.signed_iff
#print axioms Sun28.Concrete.reads_output
#print axioms Sun28.Concrete.signed_square
