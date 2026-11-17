import SelectedRays
import IdealRepresentative

namespace Sun28.Reciprocity
open Sun28.RayDensity Sun28.RayDensity.Artin Sun28.FinitePattern ManuscriptV15.Arithmetic
noncomputable section

/-- A condition wholly on an integral ideal, its residue field size and its finite ideal ray class. -/
def selectedIdeal (L p:ℕ) : Prop :=
  ∃ J:coprimeIdeals (M (moduli L)), Nat.card (GaussianInt ⧸ J.val)=p ∧
    admissible L (idealCoordinates (moduli L) (level_coprime L) (J:idealRay (moduli L)))

theorem norm_coordinates_int (z:GaussianInt) :
    z.norm.natAbs=gaussianNorm (z.re,z.im) := by
  simp [gaussianNorm,Zsqrtd.norm_def,sq]

theorem selected_to_integer {L p:ℕ} (prime:p.Prime) (h:selectedIdeal L p) :
    commonPrime L L p := by
  obtain ⟨J,hp,sel⟩:=h
  obtain ⟨z,dy,odd,_,N,coord⟩:=prime_ideal_data (moduli L) (level_coprime L) J
  rw [coord] at sel
  obtain ⟨h16,h7,cl⟩:=(admissible_generator L _ _ dy odd).1 sel
  exact ⟨prime,(z.re,z.im),(norm_coordinates_int z).symm.trans (N.symm.trans hp),h16,h7,cl⟩

/-- At primes above the cutoff and different from the exceptional prime 7, the
finite ray-class condition is equivalent in both directions to the manuscript predicate. -/
theorem commonPrime_iff_ideal {L p:ℕ} (above:L<p) (away:p≠7) :
    commonPrime L L p ↔ p.Prime ∧ selectedIdeal L p := by
  constructor
  · rintro ⟨prime,⟨a,b⟩,hn,h16,h7,cl⟩
    let z:GaussianInt:=⟨a,b⟩
    have n : z.norm.natAbs=p := (norm_coordinates_int z).trans hn
    have square : a^2+b^2=(p:ℤ) := by
      change (a^2+b^2).natAbs=p at hn
      have e:=congrArg ((↑):ℕ→ℤ) hn
      rwa [Int.natAbs_of_nonneg (by positivity : 0≤a^2+b^2)] at e
    have x : (a:ZMod 16)=9 := by simpa using (ZMod.intCast_eq_intCast_iff ..).2 h16.1
    have y : (b:ZMod 16)=0 := by simpa using (ZMod.intCast_eq_intCast_iff ..).2 h16.2
    have dy : ((a:ZMod 16),(b:ZMod 16))∈primarySet := by rw [x,y];decide
    have odd (i:Slot L): (a:ZMod i.val)^2+(b:ZMod i.val)^2 ≠0 := by
      have eq : (a:ZMod i.val)^2+(b:ZMod i.val)^2=(p:ZMod i.val) := by
        exact_mod_cast congrArg (fun t:ℤ=>(t:ZMod i.val)) square
      have ne : p≠i.val := by rcases i.2.2.2 with small|seven <;> omega
      rw [eq]
      exact (ZMod.unitOfCoprime p ((Nat.coprime_primes prime i.2.1).2 ne)).ne_zero
    let J:=principalIdeal (moduli L) z (generator_unit (moduli L) (level_coprime L) z dy odd)
    refine ⟨prime,J,(quotient_card z).trans n,?_⟩
    rw [show idealCoordinates (moduli L) (level_coprime L) (J:idealRay (moduli L)) =
      primeTuple (moduli L) a b dy odd from idealCoordinates_generator _ _ z dy odd]
    exact (admissible_generator L a b dy odd).2 ⟨h16,h7,cl⟩
  · rintro ⟨hp,hJ⟩
    exact selected_to_integer hp hJ

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.selected_to_integer
#print axioms Sun28.Reciprocity.commonPrime_iff_ideal
