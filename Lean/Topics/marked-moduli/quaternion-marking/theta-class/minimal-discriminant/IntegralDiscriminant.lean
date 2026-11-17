import QuadraticChange
import IgusaIdealOrders

/-! Integral Weierstrass equations and their discriminants at a height-one prime.
The two integral polynomials and the coordinate change range over the completion.
The order of the ideal is compared with its local generators. -/
namespace ZInQBlueprint.MinimalDiscriminant
open Polynomial IsDedekindDomain NumberField UniqueFactorizationMonoid WithZero
open JacobianHeight ThetaClass
noncomputable section

/-- The source is y²=f. After completing the square on y²+Qy=P, the
new homogeneous branch form is 4P+Q². The factor 4/e² is for the
direction 'old x = (ax+b)/(cx+d)'. -/
structure IntegralEquation {F : Type*} [Field F] [CharZero F] (v : Valuation F ℤᵐ⁰) (f : ℚ[X]) where
  P : v.integer[X]
  Q : v.integer[X]
  degreeP : P.natDegree ≤ 6
  degreeQ : Q.natDegree ≤ 3
  a : F
  b : F
  c : F
  d : F
  e : F
  det_ne : a*d-b*c ≠ 0
  e_ne : e ≠ 0
  change : ∀ x z : F,
    form (fun i => (((4*P+Q^2).coeff i.val : v.integer) : F)) x z =
      (4/e^2)*form (fun i => (f.coeff i.val : F)) (a*x+b*z) (c*x+d*z)

namespace IntegralEquation
variable {F : Type*} [Field F] [CharZero F] {v : Valuation F ℤᵐ⁰} {f : ℚ[X]}
variable (E : IntegralEquation v f)

/-- Liu's relative discriminant law, including a chart with a root at infinity.
The scalar 256 is the factor 2^8 in the discriminant of y²=f. -/
def discriminant : F := (4/E.e^2)^10*(E.a*E.d-E.b*E.c)^30*((f.discr : F)/4096)

def quadratic : F :=
  fourJ2 (fun i => (((4*E.P+E.Q^2).coeff i.val : v.integer) : F)) / 4

theorem quadratic_integral (two : v (2:F) = 1) : v E.quadratic ≤ 1 := by
  let g : Coefficients v.integer := fun i => (4*E.P+E.Q^2).coeff i.val
  have hg : v (((fourJ2 g : v.integer) : F)) ≤ 1 := (fourJ2 g).property
  have four : v (4:F) = 1 := by rw [show (4:F) = 2^2 by norm_num, map_pow,two,one_pow]
  change v (fourJ2 (fun i => v.integer.subtype (g i)) / 4) ≤ 1
  rw [fourJ2_map,map_div₀,four,div_one]
  exact hg

/-- Both relative invariants acquire the same weight in the absolute quotient. -/
theorem discriminant_eq (h₂ : igusaJ2 f ≠ 0) :
    E.discriminant = ((igusaJ10 f / (igusaJ2 f)^5 : ℚ) : F) * E.quadratic^5 := by
  have h := fourJ2_change (fun i => (f.coeff i.val : F)) _ E.a E.b E.c E.d _ E.det_ne E.change
  rw [show (fun i : Fin 7 => (f.coeff i.val : F)) =
    (fun i => (Rat.castHom F) (f.coeff i.val)) by rfl, fourJ2_map,rational_fourJ2] at h
  change fourJ2 _ = (4/E.e^2)^2*(E.a*E.d-E.b*E.c)^6*((4*igusaJ2 f : ℚ) : F) at h
  push_cast at h
  have nz : (igusaJ2 f : F) ≠ 0 := by exact_mod_cast h₂
  unfold discriminant quadratic
  rw [h]
  unfold igusaJ10
  push_cast
  generalize (4/E.e^2) = t
  generalize (E.a*E.d-E.b*E.c) = m
  field_simp [nz]

theorem valuation_le (h₂ : igusaJ2 f ≠ 0) (two : v (2:F) = 1) :
    v E.discriminant ≤ v ((igusaJ10 f / (igusaJ2 f)^5 : ℚ) : F) := by
  rw [E.discriminant_eq h₂,map_mul,map_pow]
  exact mul_le_of_le_one_right (bot_le) (pow_le_one₀ (bot_le) (E.quadratic_integral two))

end IntegralEquation

variable {K : Type} [Field K] [NumberField K]

abbrev completedVal (w : HeightOneSpectrum (𝓞 K)) : Valuation (w.adicCompletion K) ℤᵐ⁰ := Valued.v

/-- Each local exponent is attained on an integral Weierstrass equation.
HP Definition 4.4 supplies this for the naive minimal discriminant. -/
def RepresentedAtPlaces (f : ℚ[X]) (I : Ideal (𝓞 K)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), ∃ E : IntegralEquation (completedVal w) f,
    completedVal w E.discriminant = WithZero.exp (-((normalizedFactors I).count w.asIdeal : ℤ))

theorem denominator_coprime {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    (SixContact.J u).den.Coprime 12 := by
  have hu0 : u ≠ 0 := fun e => hu (e ▸ (by decide : (0 : ℚ) ∈ ZInQ.contactSet))
  by_contra h
  obtain ⟨p,hp,hd,h12⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have large := SixContactHP.prime_den_large u hu0
    (Nat.mem_primeFactors.mpr ⟨hp,hd,(SixContact.J u).den_nz⟩)
  have h : p ∣ 2*(2*3) := h12
  rcases hp.dvd_mul.mp h with d|d
  · exact (Nat.le_of_dvd (by decide : 0 < 2) d).not_gt (by omega)
  · rcases hp.dvd_mul.mp d with d|d
    · exact (Nat.le_of_dvd (by decide : 0 < 2) d).not_gt (by omega)
    · exact (Nat.le_of_dvd (by decide : 0 < 3) d).not_gt large

/-- Every integral equation at a denominator prime has enough discriminant order,
even when the prime ramifies. Good reduction and a formula for that order are unnecessary. -/
theorem denominator_orders {u : ℚ} (hu : u ∉ ZInQ.contactSet) (I : Ideal (𝓞 K))
    (represented : RepresentedAtPlaces (BinaryCover.paper ℚ u false) I) :
    ∀ P ∈ normalizedFactors (Ideal.span {((SixContact.J u).den : 𝓞 K)}),
      2*(normalizedFactors (Ideal.span {((SixContact.J u).den : 𝓞 K)})).count P ≤
        (normalizedFactors I).count P := by
  intro P hP
  let j := SixContact.J u
  have pr := prime_of_normalized_factor P hP
  let w : HeightOneSpectrum (𝓞 K) := ⟨P,Ideal.isPrime_of_prime pr,pr.ne_zero⟩
  let : w.asIdeal.IsPrime := w.isPrime
  have pole : (j.den : 𝓞 K) ∈ w.asIdeal := Ideal.dvd_span_singleton.mp (dvd_of_mem_normalizedFactors hP)
  obtain ⟨E,attains⟩ := represented w
  have twelve : (12:𝓞 K) ∉ w.asIdeal :=
    Ideal.IsPrime.notMem_of_isCoprime_of_mem (by exact_mod_cast (denominator_coprime hu).cast (R:=𝓞 K)) pole
  have twoO : (2:𝓞 K) ∉ w.asIdeal := fun h => twelve
    (by simpa only [show (6:𝓞 K)*2 = 12 by norm_num] using w.asIdeal.mul_mem_left 6 h)
  have twoK : w.valuation K (2:K) = 1 := by
    simpa only [map_ofNat] using (w.valuation_eq_one_iff_notMem (K:=K)).mpr twoO
  have comp (x : K) : completedVal w (algebraMap K (w.adicCompletion K) x) = w.valuation K x :=
    w.valuedAdicCompletion_eq_valuation' x
  have two : completedVal w 2 = 1 := by
    simpa only [map_ofNat,twoK] using comp (2:K)
  have h := E.valuation_le (paper_igusa_quotient hu).1 two
  rw [attains,(paper_igusa_quotient hu).2] at h
  have base (x : ℚ) : completedVal w (x:w.adicCompletion K) = w.valuation K (x:K) := by
    simpa only [map_ratCast] using comp (x:K)
  rw [base] at h
  change _ ≤ w.valuation K ((SixContactHP.igusaPole j : ℚ) : K) at h
  rw [igusa_valuation_at_denominator w (denominator_coprime hu) pole] at h
  have nz : (j.den : 𝓞 K) ≠ 0 := by exact_mod_cast j.den_nz
  have nzI : Ideal.span {(j.den : 𝓞 K)} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr nz
  rw [w.intValuation_eq_exp_neg_multiplicity nz,← WithZero.exp_nsmul,two_nsmul,
    ← w.count_normalizedFactors_eq_multiplicity nzI] at h
  have h' := (WithZero.exp_le_exp.mp h)
  change 2*(normalizedFactors (Ideal.span {(j.den : 𝓞 K)})).count w.asIdeal ≤
      (normalizedFactors I).count w.asIdeal
  omega

theorem denominator_dvd {u : ℚ} (hu : u ∉ ZInQ.contactSet) (I : Ideal (𝓞 K)) (nz : I ≠ ⊥)
    (represented : RepresentedAtPlaces (BinaryCover.paper ℚ u false) I) :
    (Ideal.span {((SixContact.J u).den : 𝓞 K)})^2 ∣ I :=
  PeriodGaussian.denominator_ideal_dvd _ (SixContact.J u).den_nz I nz (denominator_orders hu I represented)

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.IntegralEquation.quadratic_integral
#print axioms ZInQBlueprint.MinimalDiscriminant.IntegralEquation.discriminant_eq
#print axioms ZInQBlueprint.MinimalDiscriminant.IntegralEquation.valuation_le
#print axioms ZInQBlueprint.MinimalDiscriminant.denominator_orders
#print axioms ZInQBlueprint.MinimalDiscriminant.denominator_dvd
