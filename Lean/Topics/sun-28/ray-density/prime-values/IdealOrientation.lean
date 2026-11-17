import PrimeConjugacy

namespace Sun28.PrimeValues
open Sun28.Reciprocity Sun28.RayDensity Sun28.RayDensity.Artin Sun28.FinitePattern
open Sun28.SinglePrime ManuscriptV15.Arithmetic
noncomputable section

abbrev Ideals (L : ℕ) := coprimeIdeals (M (moduli L))
abbrev word {L : ℕ} (J : Ideals L) :=
  idealCoordinates (moduli L) (level_coprime L) (J : idealRay (moduli L))
abbrev norm {L : ℕ} (J : Ideals L) := Nat.card (GaussianInt ⧸ J.val)

/-- The choice is unique because an element of this submonoid is determined by its ideal. -/
def opposite {L : ℕ} (J : Ideals L) : Ideals L :=
  (conjugate_data (moduli L) (level_coprime L) J).choose

theorem opposite_data {L : ℕ} (J : Ideals L) :
    (opposite J).val = J.val.map conjugateRing ∧ norm (opposite J) = norm J ∧
      word (opposite J) = conjugateCoordinate L (word J) :=
  (conjugate_data (moduli L) (level_coprime L) J).choose_spec

theorem opposite_twice {L : ℕ} (J : Ideals L) : opposite (opposite J) = J := by
  apply Subtype.ext
  rw [(opposite_data _).1,(opposite_data J).1,Ideal.map_map]
  have e : conjugateRing.comp conjugateRing = RingHom.id GaussianInt := by
    exact RingHom.ext fun z => star_star z
  rw [e,Ideal.map_id]

def Oriented (L p : ℕ) := {J : Ideals L // norm J=p ∧ admissible L (word J)}
def Unoriented (L p : ℕ) := {J : Ideals L // norm J=p ∧ acceptedClass L (word J)}

theorem oriented_subsingleton {L p : ℕ} (hp : p.Prime) : Subsingleton (Oriented L p) := by
  constructor
  rintro ⟨J,nJ,okJ⟩ ⟨K,nK,okK⟩
  obtain ⟨z,dz,uz,iz,hz,rz⟩:=prime_ideal_data (moduli L) (level_coprime L) J
  obtain ⟨w,dw,uw,iw,hw,rw'⟩:=prime_ideal_data (moduli L) (level_coprime L) K
  change admissible L (idealCoordinates _ _ _) at okJ okK
  rw [rz] at okJ
  rw [rw'] at okK
  obtain ⟨z16,z7,_⟩:=(admissible_generator L _ _ dz uz).1 okJ
  obtain ⟨w16,w7,_⟩:=(admissible_generator L _ _ dw uw).1 okK
  have normZ := (norm_coordinates_int z).symm.trans (hz.symm.trans nJ)
  have normW := (norm_coordinates_int w).symm.trans (hw.symm.trans nK)
  have g:=oriented_unique hp normZ normW z16 w16 z7 w7
  have eq : z=w := Zsqrtd.ext (congrArg Prod.fst g) (congrArg Prod.snd g)
  exact Subtype.ext (Subtype.ext (iz.symm.trans ((congrArg principal eq).trans iw)))

theorem disjoint_conjugates {L : ℕ} {w : RayUnits (moduli L)} (h : admissible L w) :
    ¬admissible L (conjugateCoordinate L w) := by
  intro both
  have y := congrArg Prod.snd h.2.1
  have neg := congrArg Prod.snd both.2.1
  change ((w.2 (seven L) : GR 7).im) = (3 : ZMod 7) at y
  change (star (w.2 (seven L) : GR 7)).im = (3 : ZMod 7) at neg
  simp [y] at neg
  exact (by decide : (-(3:ZMod 7)) ≠ 3) neg

theorem class_of_opposite {L : ℕ} (J : Ideals L) :
    acceptedClass L (word J) ↔ admissible L (word J) ∨ admissible L (word (opposite J)) := by
  rw [acceptedClass_iff,(opposite_data J).2.2]

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.opposite_data
#print axioms Sun28.PrimeValues.opposite_twice
#print axioms Sun28.PrimeValues.oriented_subsingleton
#print axioms Sun28.PrimeValues.disjoint_conjugates
#print axioms Sun28.PrimeValues.class_of_opposite
