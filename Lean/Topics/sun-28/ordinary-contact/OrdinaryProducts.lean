import OrdinaryDetector
import Mathlib.Data.Nat.PrimeFin

/-! The five primitive linear forms at a reduced rational parameter. -/
open NumberField IsDedekindDomain
open scoped NumberField
namespace Sun28.Ordinary

def contactForm (t a : ℚ) : ℤ := t.num * a.den - a.num * t.den

private theorem form_eq (t a : ℚ) :
    ((contactForm t a : ℤ) : ℚ) = (t-a)*t.den*a.den := by
  have h (q : ℚ) : q * (q.den:ℚ) = q.num := by
    exact (eq_div_iff (by exact_mod_cast q.den_nz)).mp (Rat.num_div_den q).symm
  unfold contactForm
  push_cast
  linear_combination (a.den:ℚ)*(h t).symm - (t.den:ℚ)*(h a).symm

theorem reduced_min (p : ℕ) [hp : Fact p.Prime] (t : ℚ) :
    min (padicValInt p t.num) (padicValNat p t.den)=0 := by
  by_cases hn : p ∣ t.num.natAbs
  · have hd : ¬p ∣ t.den := fun bad => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp.out,hn,bad⟩) t.reduced
    simp [padicValNat.eq_zero_of_not_dvd hd]
  · simp [padicValInt,padicValNat.eq_zero_of_not_dvd hn]

theorem projective_contact_iff {p : ℕ} [hp : Fact p.Prime] {t a : ℚ}
    (diff : t ≠ a) (unitDen : ¬p ∣ a.den) :
    (0 < padicValInt p (contactForm t a) ∧ Odd (padicValInt p (contactForm t a))) ↔
      (0 < padicValRat p (t-a) ∧ Odd (padicValRat p (t-a))) := by
  have value : padicValRat p (t-a) = (padicValInt p (contactForm t a):ℤ) - padicValNat p t.den := by
    have e := congrArg (padicValRat p) (form_eq t a)
    rw [padicValRat.of_int,padicValRat.mul
      (mul_ne_zero (sub_ne_zero.mpr diff) (by exact_mod_cast t.den_nz)) (by exact_mod_cast a.den_nz),
      padicValRat.mul (sub_ne_zero.mpr diff) (by exact_mod_cast t.den_nz),
      padicValRat.of_nat,padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd unitDen] at e
    omega
  by_cases hd : p ∣ t.den
  · have num : ¬p ∣ t.num.natAbs := fun hn => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp.out,hn,hd⟩) t.reduced
    have pf : ¬(p:ℤ) ∣ contactForm t a := by
      intro z
      have right : (p:ℤ) ∣ a.num*(t.den:ℤ) := dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hd) _
      have prod : (p:ℤ) ∣ t.num*(a.den:ℤ) := by simpa [contactForm] using dvd_add z right
      have prime : Prime (p:ℤ) := by simpa [Int.prime_iff_natAbs_prime] using hp.out
      rcases prime.dvd_mul.mp prod with h|h
      · exact num (by simpa using Int.natAbs_dvd_natAbs.mpr h)
      · exact unitDen (Int.natCast_dvd_natCast.mp h)
    rw [padicValInt.eq_zero_of_not_dvd pf] at value ⊢
    constructor <;> intro bad <;> omega
  · rw [padicValNat.eq_zero_of_not_dvd hd] at value
    simp only [Nat.cast_zero,sub_zero] at value
    rw [value]
    simp

theorem mark_denominator_unit {p : ℕ} (good : ¬p ∣ separation) {a : ℚ}
    (ha : a ∈ marks) : ¬p ∣ a.den := by
  have catalog : ∀ b ∈ marks, b.den ∣ separation := by norm_num [marks,separation,Nat.dvd_iff_mod_eq_zero]
  exact fun h => good (h.trans (catalog a ha))

def contactPrimes (S : Finset ℕ) (t : ℚ) : Finset ℕ :=
  (marks.biUnion fun a => ((contactForm t a).natAbs.primeFactors.filter fun p =>
    Odd (padicValInt p (contactForm t a)))) \ S

theorem mem_contactPrimes {S : Finset ℕ} {t : ℚ} {p : ℕ} :
    p ∈ contactPrimes S t ↔ p.Prime ∧ p ∉ S ∧ ∃ a ∈ marks,
      0 < padicValInt p (contactForm t a) ∧ Odd (padicValInt p (contactForm t a)) := by
  classical
  simp only [contactPrimes,Finset.mem_sdiff,Finset.mem_biUnion,Finset.mem_filter,Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨a,ha,⟨prime,_,_⟩,odd⟩,outside⟩
    exact ⟨prime,outside,a,ha,by obtain ⟨k,hk⟩ := odd; omega,odd⟩
  · rintro ⟨prime,outside,a,ha,pos,odd⟩
    have hn : (contactForm t a).natAbs ≠ 0 := by intro e; simp [padicValInt,e] at pos
    exact ⟨⟨a,ha,⟨prime,dvd_of_one_le_padicValNat pos,hn⟩,odd⟩,outside⟩

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

theorem three_marked_products {ρ : K} (root : ρ^2=2) (σ : K ≃ₐ[ℚ] K) (hs : σ≠1)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β : ℚ) (s t : Fin 3 → ℚ) (M : Finset ℚ) (S : Finset ℕ)
    (hh : h≠0) (hc : h-c≠0)
    (outside : ∀ p : ℕ, p.Prime → p ∉ S → 65<p ∧ ¬(p:ℤ) ∣ c ∧ ¬p ∣ separation ∧ ∀ μ ∈ M, padicValRat p μ=0)
    (localChart : ∀ (p : ℕ) [hp : Fact p.Prime], p ∉ S → ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal →
        OrdinaryFormalChart p w)
    (guard : ∀ j, t j ∉ marks ∧ t j ≠ 3 ∧ s j ≠ 0)
    (accepted : ∀ j, testTrace root σ c h n m β ((s j)^2) (t j) ≠ 0 ∧
      polePredicate M (poleArgument root σ c h n m β ((s j)^2) (t j))) :
    ∀ j, (∏ p ∈ contactPrimes S (t j), (p:ℤ))^64 ∣ lucas (n 1) (n 2) (n 3) ∧
      (∏ p ∈ contactPrimes S (t j), p)^16 ∣ (β-n 0).num.natAbs := by
  apply three_contact_products
  · intro j p mem
    exact (mem_contactPrimes.mp mem).1
  · intro j p mem
    obtain ⟨prime,away,a,ha,pos,odd⟩ := mem_contactPrimes.mp mem
    let : Fact p.Prime := ⟨prime⟩
    obtain ⟨big,an,sep,mul⟩ := outside p prime away
    let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,prime⟩
    obtain ⟨P,maximal,lie⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=𝓞 K) v.asIdeal
    let w : HeightOneSpectrum (𝓞 K) := ⟨P,maximal.isPrime,Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨maximal.isPrime,lie⟩⟩
    let : w.asIdeal.LiesOver v.asIdeal := lie
    have chart := localChart p away w lie
    have aff := (projective_contact_iff (t:=t j) (a:=a) (fun e => (guard j).1 (e ▸ ha)) (mark_denominator_unit sep ha)).mp ⟨pos,odd⟩
    exact marked_pole_divides big w root chart σ hs c h n m β (t j) a (s j) M an hh hc sep
      (guard j).1 (guard j).2.1 (guard j).2.2 ha aff.1 aff.2 mul (accepted j).1 (accepted j).2

end Sun28.Ordinary
#print axioms Sun28.Ordinary.reduced_min
#print axioms Sun28.Ordinary.projective_contact_iff
#print axioms Sun28.Ordinary.mark_denominator_unit
#print axioms Sun28.Ordinary.mem_contactPrimes
#print axioms Sun28.Ordinary.three_marked_products
