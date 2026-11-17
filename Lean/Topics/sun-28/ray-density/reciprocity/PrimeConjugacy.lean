import PrimeRaySelection
import ConjugateIdeals

namespace Sun28.Reciprocity
open Sun28.RayDensity Sun28.RayDensity.Artin Sun28.FinitePattern SemidirectProduct
noncomputable section
variable {I:Type*} [Fintype I] (q:I→ℕ) [∀i,Fact (q i).Prime]
variable (cop:Pairwise (Function.onFun Nat.Coprime (levels q)))

theorem conjugate_data (J:coprimeIdeals (M q)) :
    ∃ K:coprimeIdeals (M q), K.val=J.val.map conjugateRing ∧
      Nat.card (GaussianInt ⧸ K.val)=Nat.card (GaussianInt ⧸ J.val) ∧
      idealCoordinates q cop (K:idealRay q)=joinedAut q dyadicConj (idealCoordinates q cop (J:idealRay q)) := by
  obtain ⟨K,hK,coord⟩:=conjugate_ideal q cop J
  obtain ⟨z,_,_,hJ,N,_⟩:=prime_ideal_data q cop J
  have r : K.val=principal (star z) := by
    rw [hK,←hJ,Ideal.map_span,Set.image_singleton]
    rfl
  refine ⟨K,hK,?_,coord⟩
  rw [r,quotient_card,N,Zsqrtd.norm_conj]

include cop in
theorem prime_ideal_of_card {p:ℕ} (hp:p.Prime) (J:coprimeIdeals (M q))
    (N:Nat.card (GaussianInt ⧸ J.val)=p) : J.val.IsPrime := by
  obtain ⟨z,_,_,hJ,sz,_⟩:=prime_ideal_data q cop J
  have hz:=gaussian_prime_of_norm hp (sz.symm.trans N)
  rw [←hJ]
  exact (Ideal.span_singleton_prime hz.ne_zero).2 hz

/-- Acceptance by a full conjugacy class. It does not choose a prime over p or an orientation. -/
def acceptedClass (L:ℕ) (w:RayUnits (moduli L)) : Prop :=
  ∃ v:RayUnits (moduli L), admissible L v ∧ IsConj (inl (φ:=rayAction (moduli L)) w) (inl v)

abbrev conjugateCoordinate (L:ℕ) := joinedAut (moduli L) dyadicConj

theorem acceptedClass_iff (L:ℕ) (w:RayUnits (moduli L)) :
    acceptedClass L w ↔ admissible L w ∨ admissible L (conjugateCoordinate L w) := by
  constructor
  · rintro ⟨v,a,h⟩
    rcases (ray_conjugacy (moduli L) w v).1 h with e|e
    · exact Or.inl (e ▸ a)
    · have eq : v=conjugateCoordinate L w := e
      exact Or.inr (eq ▸ a)
  · rintro (h|h)
    · exact ⟨w,h,IsConj.refl _⟩
    · exact ⟨conjugateCoordinate L w,h,(ray_conjugacy (moduli L) _ _).2 (Or.inr rfl)⟩

theorem commonPrime_iff_class {L p:ℕ} (above:L<p) (away:p≠7) :
    commonPrime L L p ↔ p.Prime ∧ ∃ J:coprimeIdeals (M (moduli L)),
      Nat.card (GaussianInt ⧸ J.val)=p ∧
      acceptedClass L (idealCoordinates (moduli L) (level_coprime L) (J:idealRay (moduli L))) := by
  rw [commonPrime_iff_ideal above away]
  apply and_congr_right;intro _
  constructor
  · rintro ⟨J,n,ok⟩
    exact ⟨J,n,(acceptedClass_iff _ _).2 (Or.inl ok)⟩
  · rintro ⟨J,n,ok⟩
    rcases (acceptedClass_iff _ _).1 ok with a|a
    · exact ⟨J,n,a⟩
    · obtain ⟨K,_,e,coord⟩:=conjugate_data (moduli L) (level_coprime L) J
      exact ⟨K,e.trans n,coord.symm ▸ a⟩

/-- The place is an actual Gaussian prime ideal of residue cardinality p. -/
theorem commonPrime_iff_prime_class {L p:ℕ} (above:L<p) (away:p≠7) :
    commonPrime L L p ↔ p.Prime ∧ ∃ J:coprimeIdeals (M (moduli L)),
      J.val.IsPrime ∧ Nat.card (GaussianInt ⧸ J.val)=p ∧
      acceptedClass L (idealCoordinates (moduli L) (level_coprime L) (J:idealRay (moduli L))) := by
  rw [commonPrime_iff_class above away]
  constructor
  · rintro ⟨hp,J,n,ok⟩
    exact ⟨hp,J,prime_ideal_of_card _ (level_coprime L) hp J n,n,ok⟩
  · rintro ⟨hp,J,_,n,ok⟩
    exact ⟨hp,J,n,ok⟩

end
end Sun28.Reciprocity
#print axioms Sun28.Reciprocity.conjugate_data
#print axioms Sun28.Reciprocity.prime_ideal_of_card
#print axioms Sun28.Reciprocity.acceptedClass_iff
#print axioms Sun28.Reciprocity.commonPrime_iff_class
#print axioms Sun28.Reciprocity.commonPrime_iff_prime_class
