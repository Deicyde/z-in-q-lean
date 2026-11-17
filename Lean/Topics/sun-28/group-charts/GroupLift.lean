import GroupCompiler

namespace Sun28.GroupCharts
open ZInQ ZInQBlueprint.SunResultant

namespace Quad
variable {R S : Type*} [CommRing R] [CommRing S]

def map (f : R →+* S) (x : Quad R) : Quad S := ⟨f x.re,f x.im,f x.den⟩

theorem value_map (f : R →+* S) (φ : S →+* ℚ) {x : Quad R} {X : K0} :
    Value φ (map f x) X ↔ Value (φ.comp f) x X := by
  constructor <;> rintro ⟨hg,he⟩ <;> exact ⟨hg,he⟩

end Quad

namespace PointCode
variable {R S : Type*} [CommRing R] [CommRing S]

def map (f : R →+* S) : PointCode R → PointCode S
  | .infinity => .infinity
  | .affine x y => .affine (x.map f) (y.map f)

theorem represents_map (f : R →+* S) (φ : S →+* ℚ) {x : PointCode R} {P : curveC.toAffine.Point}
    (h : Represents (φ.comp f) x P) : Represents φ (map f x) P := by
  cases h with
  | infinity => exact .infinity
  | affine h hx hy => exact .affine h ((Quad.value_map f φ).2 hx) ((Quad.value_map f φ).2 hy)

end PointCode

/-- Lift a polynomial in earlier roots to the new tuple whose head is the new root. -/
noncomputable def liftRoot {R : Type*} [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R →+* MvPolynomial (Fin (n+1)) R :=
  (MvPolynomial.finSuccEquiv R n).symm.toRingHom.comp Polynomial.C

theorem eval_liftRoot {R : Type*} [CommRing R] (φ : R →+* ℚ) {n : ℕ} (x : Fin n → ℚ) (w : ℚ) :
    (MvPolynomial.eval₂Hom φ (Fin.cons w x)).comp (liftRoot (R:=R) n)=
      MvPolynomial.eval₂Hom φ x := by
  apply RingHom.ext
  intro p
  change MvPolynomial.eval₂Hom φ (Fin.cons w x) (RootCharts.asTest (Polynomial.C p))=_
  rw [RootCharts.eval_asTest]
  simp

theorem lift_quad {R : Type*} [CommRing R] (φ : R →+* ℚ) {n : ℕ} (x : Fin n → ℚ) (w : ℚ)
    {q : Quad (MvPolynomial (Fin n) R)} {X : K0} (h : Quad.Value (MvPolynomial.eval₂Hom φ x) q X) :
    Quad.Value (MvPolynomial.eval₂Hom φ (Fin.cons w x)) (q.map (liftRoot n)) X := by
  rw [Quad.value_map,eval_liftRoot]
  exact h

theorem lift_point {R : Type*} [CommRing R] (φ : R →+* ℚ) {n : ℕ} (x : Fin n → ℚ) (w : ℚ)
    {p : PointCode (MvPolynomial (Fin n) R)} {P : curveC.toAffine.Point}
    (h : Represents (MvPolynomial.eval₂Hom φ x) p P) :
    Represents (MvPolynomial.eval₂Hom φ (Fin.cons w x)) (p.map (liftRoot n)) P := by
  apply PointCode.represents_map
  rw [eval_liftRoot]
  exact h

#print axioms eval_liftRoot
#print axioms lift_quad
#print axioms lift_point
end Sun28.GroupCharts
