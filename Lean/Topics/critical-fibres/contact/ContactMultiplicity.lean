import HeightSix
import ZInQKernel.Hypotheses.Height

/-! Valuations of the three branch parameters of the six-contact map. -/
namespace ZInQBlueprint.ContactMultiplicity
open ZInQBlueprint.SixContact
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

/-- Failure of divisibility by the tame index at one of the three branch values. -/
def badBranch (p : ℕ) (u : ℚ) : Prop :=
  (0 < padicValRat p (J u) ∧ ¬ (4 : ℤ) ∣ padicValRat p (J u)) ∨
  (padicValRat p (J u) < 0 ∧ ¬ (6 : ℤ) ∣ -padicValRat p (J u)) ∨
  (0 < padicValRat p (J u + 16/27) ∧ ¬ (2 : ℤ) ∣ padicValRat p (J u + 16/27))

private lemma val_factorial_divisor (hp : 17 ≤ p) (n : ℕ) (hn : n ∣ Nat.factorial 13) :
    padicValNat p n = 0 := by
  have hprime := (Fact.out : Nat.Prime p)
  have hnot : ¬p ∣ n := by
    intro hd
    have h := hd.trans hn
    have small : p ≤ 13 := (Nat.Prime.dvd_factorial hprime).mp h
    omega
  exact padicValNat.eq_zero_of_not_dvd hnot

private lemma val_nat_unit (hp : 17 ≤ p) (n : ℕ) (hn : n ∣ Nat.factorial 13) :
    padicValRat p (n : ℚ) = 0 := by
  rw [padicValRat.of_nat, val_factorial_divisor hp n hn]; rfl

/-- A single certificate covers every mark difference and every G(c). -/
private lemma val_rat_unit (hp : 17 ≤ p) (r : ℚ) (hn : r.num.natAbs ∣ Nat.factorial 13)
    (hd : r.den ∣ Nat.factorial 13) : padicValRat p r = 0 := by
  rw [padicValRat_def, padicValInt, val_factorial_divisor hp _ hn, val_factorial_divisor hp _ hd]; rfl

private lemma add_integral {x y : ℚ} (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    0 ≤ padicValRat p (x+y) := by
  by_cases h : x+y=0
  · simp [h]
  exact (le_min hx hy).trans (padicValRat.min_le_padicValRat_add h)

private lemma mul_integral {x y : ℚ} (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    0 ≤ padicValRat p (x*y) := by
  by_cases h : x*y=0
  · simp [h]
  rw [padicValRat.mul (left_ne_zero_of_mul h) (right_ne_zero_of_mul h)]
  omega

/-- The term of smaller valuation dominates even if the other term is zero. -/
private lemma dominated {x y : ℚ} (hx : x≠0) (hval : padicValRat p x < padicValRat p y) :
    padicValRat p (x+y)=padicValRat p x := by
  by_cases hy : y=0
  · simp [hy]
  apply padicValRat.add_eq_of_lt _ hx hy hval
  intro h
  have he : x = -y := by linarith
  rw [he,padicValRat.neg] at hval
  omega

private lemma val_F_prod {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    padicValRat p (F u) = ∑ c ∈ ZInQ.contactSet, padicValRat p (u-c) := by
  classical
  have hp (s : Finset ℚ) (h : u ∉ s) :
      padicValRat p (∏ c ∈ s, (u-c)) = ∑ c ∈ s, padicValRat p (u-c) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [padicValRat.mul (sub_ne_zero.mpr (by intro k; exact h ((show u = a from k) ▸ Finset.mem_insert_self _ _)))
        (Finset.prod_ne_zero_iff.mpr (fun x hx => sub_ne_zero.mpr (fun eq : u = x => h (eq ▸ Finset.mem_insert_of_mem hx))))]
      rw [ih (fun hx => h (Finset.mem_insert_of_mem hx))]
  have he : F u = ∏ c ∈ ZInQ.contactSet, (u-c) := by
    norm_num [F,ZInQ.contactSet]; ring
  rw [he,hp _ hu]

private lemma F_ne_zero {u : ℚ} (hu : u ∉ ZInQ.contactSet) : F u ≠ 0 := by
  have hzero : ∀ c ∈ ZInQ.contactSet, u-c ≠ 0 := fun c hc => sub_ne_zero.mpr (fun e => hu (e ▸ hc))
  simpa [ZInQ.contactSet,F,and_assoc] using hzero

private lemma val_J {u : ℚ} (hp : 17 ≤ p) (hu : u ∉ ZInQ.contactSet) :
    padicValRat p (J u) = 2*padicValRat p (F u)-6*padicValRat p (G u) := by
  have hk := val_nat_unit hp 57600 (by decide)
  unfold J
  rw [padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ (F_ne_zero hu)))
    (pow_ne_zero _ (positive_denominator u).ne'), padicValRat.mul (by norm_num) (pow_ne_zero _ (F_ne_zero hu))]
  simp only [padicValRat.neg, padicValRat.pow]
  norm_num at hk ⊢
  rw [hk]

omit [Fact p.Prime] in
private lemma mark_integral {c : ℚ} (hc : c ∈ ZInQ.contactSet) : 0 ≤ padicValRat p c := by
  have hd : c.den = 1 := by
    simp [ZInQ.contactSet] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rw [padicValRat_def,hd]
  simp

private lemma mark_difference_unit (hp : 17 ≤ p) {c d : ℚ}
    (hc : c ∈ ZInQ.contactSet) (hd : d ∈ ZInQ.contactSet) (hne : c ≠ d) :
    padicValRat p (c-d) = 0 := by
  simp [ZInQ.contactSet] at hc hd
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases hd with rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | contradiction | norm_num1; exact val_rat_unit hp _ (by decide) (by decide)

private lemma mark_G_unit (hp : 17 ≤ p) {c : ℚ} (hc : c ∈ ZInQ.contactSet) :
    padicValRat p (G c) = 0 := by
  simp [ZInQ.contactSet] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold G <;> norm_num1 <;>
    exact val_rat_unit hp _ (by decide) (by decide)

private lemma val_F_at_contact (hp : 17 ≤ p) {u c : ℚ} (hu : u ∉ ZInQ.contactSet)
    (hc : c ∈ ZInQ.contactSet) (ha : 0 < padicValRat p (u-c)) :
    padicValRat p (F u) = padicValRat p (u-c) := by
  classical
  rw [val_F_prod hu]
  apply Finset.sum_eq_single c
  · intro d hd hne
    have hdif := mark_difference_unit hp hc hd (Ne.symm hne)
    rw [show u-d=(c-d)+(u-c) by ring, dominated (sub_ne_zero.mpr (Ne.symm hne)) (by omega), hdif]
  · intro h; exact (h hc).elim

private lemma val_G_at_contact (hp : 17 ≤ p) {u c : ℚ}
    (hc : c ∈ ZInQ.contactSet) (ha : 0 < padicValRat p (u-c)) :
    padicValRat p (G u)=0 := by
  have hcu := mark_integral (p:=p) hc
  have hui : 0 ≤ padicValRat p u := by
    simpa using add_integral (le_of_lt ha) hcu
  have hk : 0 ≤ padicValRat p (7*(u+c)+300) :=
    add_integral (mul_integral (zero_le_padicValRat_of_nat 7) (add_integral hui hcu)) (zero_le_padicValRat_of_nat 300)
  have hgc := mark_G_unit hp hc
  rw [show G u=G c+(u-c)*(7*(u+c)+300) by unfold G; ring]
  by_cases hm : (u-c)*(7*(u+c)+300)=0
  · simpa [hm] using hgc
  rw [dominated (positive_denominator c).ne' (by
    rw [padicValRat.mul (left_ne_zero_of_mul hm) (right_ne_zero_of_mul hm)]; omega)]
  exact hgc

private lemma val_quadratic_negative {a b c u : ℚ} (h : padicValRat p u < 0)
    (ha : a≠0) (hva : padicValRat p a=0) (hvb : 0≤padicValRat p b) (hvc : 0≤padicValRat p c) :
    padicValRat p (a*u^2+b*u+c) = 2*padicValRat p u := by
  have hu : u≠0 := by rintro rfl; simp at h
  have hterm : padicValRat p (a*u^2) = 2*padicValRat p u := by
    rw [padicValRat.mul ha (pow_ne_zero _ hu), padicValRat.pow, hva]; norm_num
  have hlinear : padicValRat p u ≤ padicValRat p (b*u) := by
    by_cases hb : b=0
    · simpa [hb] using h.le
    rw [padicValRat.mul hb hu]; omega
  have hsum := dominated (p:=p) (mul_ne_zero ha (pow_ne_zero 2 hu))
    (show padicValRat p (a*u^2) < padicValRat p (b*u) by omega)
  have hn : a*u^2+b*u ≠ 0 := by
    intro eq; rw [eq,padicValRat.zero] at hsum; omega
  rw [dominated hn (show padicValRat p (a*u^2+b*u) < padicValRat p c by omega), hsum, hterm]

private lemma val_F_negative {u : ℚ} (hu : u ∉ ZInQ.contactSet) (hv : padicValRat p u < 0) :
    padicValRat p (F u) = 6*padicValRat p u := by
  have hn : u≠0 := by rintro rfl; simp at hv
  rw [val_F_prod hu]
  calc
    _ = ∑ _c ∈ ZInQ.contactSet, padicValRat p u := by
      apply Finset.sum_congr rfl
      intro c hc
      have h := mark_integral (p:=p) hc
      rw [sub_eq_add_neg, dominated hn (by rw [padicValRat.neg]; omega)]
    _ = _ := by norm_num [ZInQ.contactSet]

private lemma val_G_negative {u : ℚ} (hp : 17≤p) (hv : padicValRat p u < 0) :
    padicValRat p (G u) = 2*padicValRat p u :=
  val_quadratic_negative hv (by norm_num) (val_nat_unit hp 7 (by decide))
    (zero_le_padicValRat_of_nat 300) (zero_le_padicValRat_of_nat 3600)

private lemma val_H_negative {u : ℚ} (hp : 17≤p) (hv : padicValRat p u < 0) :
    padicValRat p (H u) = 6*padicValRat p u := by
  obtain ha := val_quadratic_negative hv (a:=(1:ℚ)) (by norm_num) (by simp)
    (b:=(-60:ℚ)) (by simpa [padicValRat.neg] using (zero_le_padicValRat_of_nat (p:=p) 60))
    (c:=(-1800:ℚ)) (by simpa [padicValRat.neg] using (zero_le_padicValRat_of_nat (p:=p) 1800))
  obtain hb := val_quadratic_negative hv (by norm_num) (val_nat_unit hp 13 (by decide))
    (zero_le_padicValRat_of_nat 480) (zero_le_padicValRat_of_nat 3600)
  obtain hc := val_quadratic_negative hv (by norm_num) (val_nat_unit hp 11 (by decide))
    (zero_le_padicValRat_of_nat 600) (zero_le_padicValRat_of_nat 7200)
  have ha' : padicValRat p (u^2-60*u-1800) = 2*padicValRat p u := by
    convert ha using 2 <;> ring
  have hz := third_fibre_empty u
  unfold H at hz ⊢
  rw [padicValRat.mul (left_ne_zero_of_mul hz) (right_ne_zero_of_mul hz),
    padicValRat.mul (left_ne_zero_of_mul (left_ne_zero_of_mul hz)) (right_ne_zero_of_mul (left_ne_zero_of_mul hz))]
  norm_num at hb hc
  omega

private lemma val_third (hp : 17≤p) (u : ℚ) :
    padicValRat p (J u+16/27)=2*padicValRat p (H u)-6*padicValRat p (G u) := by
  have h16 := val_nat_unit hp 16 (by decide)
  have h27 := val_nat_unit hp 27 (by decide)
  have hg := (positive_denominator u).ne'
  have hh := third_fibre_empty u
  have ident : J u + 16/27 = (16/27)*(H u/(G u)^3)^2 := by
    linear_combination (16/27 : ℚ) * pullback_square u
  rw [ident,padicValRat.mul (by norm_num) (pow_ne_zero _ (div_ne_zero hh (pow_ne_zero _ hg))),
    padicValRat.div (by norm_num : (16:ℚ)≠0) (by norm_num : (27:ℚ)≠0),padicValRat.pow,padicValRat.div hh (pow_ne_zero _ hg),padicValRat.pow]
  norm_num at h16 h27 ⊢
  omega

/-- A nonintegral parameter meets none of the three branch values. -/
theorem negative_parameter_units {u : ℚ} (hp : 17≤p) (hu : u ∉ ZInQ.contactSet)
    (hv : padicValRat p u < 0) :
    padicValRat p (J u)=0 ∧ padicValRat p (J u+16/27)=0 := by
  rw [val_J hp hu,val_third hp,val_F_negative hu hv,val_G_negative hp hv,val_H_negative hp hv]
  constructor <;> ring

theorem third_even (hp : 17≤p) (u : ℚ) : (2 : ℤ) ∣ padicValRat p (J u+16/27) := by
  rw [val_third hp]; exact ⟨_, show _ = 2*(padicValRat p (H u)-3*padicValRat p (G u)) by ring⟩

private lemma G_integral {u : ℚ} (hi : 0≤padicValRat p u) : 0≤padicValRat p (G u) := by
  have hq : 0≤padicValRat p (u^2) := by rw [padicValRat.pow]; positivity
  exact add_integral (add_integral (mul_integral (zero_le_padicValRat_of_nat 7) hq)
    (mul_integral (zero_le_padicValRat_of_nat 300) hi)) (zero_le_padicValRat_of_nat 3600)

private lemma contact_of_F_positive {u : ℚ} (hu : u ∉ ZInQ.contactSet) (h : 0 < padicValRat p (F u)) :
    ∃ c ∈ ZInQ.contactSet, 0 < padicValRat p (u-c) := by
  by_contra! hall
  have hn := Finset.sum_nonpos hall
  rw [val_F_prod hu] at h
  omega

/-- The valuation of J is even for every rational prime and every rational parameter. -/
theorem zero_even (u : ℚ) : (2 : ℤ) ∣ padicValRat p (J u) := by
  have h : J u = - (240 * F u / (G u)^3)^2 := by
    unfold J; field_simp [(positive_denominator u).ne']; ring
  rw [h,padicValRat.neg,padicValRat.pow]
  exact ⟨_,rfl⟩

/-- A contact of order v has order 2v on the zero branch. -/
theorem zero_contact_multiplicity (hp : 17≤p) {u c : ℚ} (hu : u ∉ ZInQ.contactSet)
    (hc : c ∈ ZInQ.contactSet) (hv : 0 < padicValRat p (u-c)) :
    padicValRat p (J u)=2*padicValRat p (u-c) := by
  rw [val_J hp hu,val_F_at_contact hp hu hc hv,val_G_at_contact hp hc hv,mul_zero,sub_zero]

private lemma contact_of_zero_branch (hp : 17≤p) {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (hv : 0 < padicValRat p (J u)) : ∃ c ∈ ZInQ.contactSet, 0 < padicValRat p (u-c) := by
  by_cases hi : padicValRat p u < 0
  · rw [(negative_parameter_units hp hu hi).1] at hv; omega
  have hg := G_integral (le_of_not_gt hi)
  have h := val_J hp hu
  exact contact_of_F_positive hu (by omega)

theorem zero_branch_iff (hp : 17 ≤ p) {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    (0 < padicValRat p (J u) ∧ ¬ (4 : ℤ) ∣ padicValRat p (J u)) ↔
      ∃ c ∈ ZInQ.contactSet, 0 < padicValRat p (u-c) ∧ Odd (padicValRat p (u-c)) := by
  constructor
  · rintro ⟨hpos,hbad⟩
    obtain ⟨c,hc,hv⟩ := contact_of_zero_branch hp hu hpos
    have hm := zero_contact_multiplicity hp hu hc hv
    refine ⟨c,hc,hv,(Int.even_or_odd _).resolve_left ?_⟩
    rintro ⟨k,hk⟩
    exact hbad ⟨k,by omega⟩
  · rintro ⟨c,hc,hv,k,hk⟩
    have hm := zero_contact_multiplicity hp hu hc hv
    refine ⟨by omega,?_⟩
    rintro ⟨l,hl⟩
    omega

theorem pole_multiple (hp : 17 ≤ p) {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (hPole : padicValRat p (J u) < 0) : (6 : ℤ) ∣ -padicValRat p (J u) := by
  have hi : 0 ≤ padicValRat p u := by
    by_contra! hn
    rw [(negative_parameter_units hp hu hn).1] at hPole
    omega
  have hmarks (c : ℚ) (hc : c ∈ ZInQ.contactSet) : padicValRat p (u-c)=0 := by
    have hn : 0 ≤ padicValRat p (u-c) := by
      rw [sub_eq_add_neg]
      exact add_integral hi (by rw [padicValRat.neg]; exact mark_integral hc)
    by_contra hd
    have hm := zero_contact_multiplicity hp hu hc (by omega)
    omega
  have hf : padicValRat p (F u)=0 := (val_F_prod hu).trans (Finset.sum_eq_zero hmarks)
  rw [val_J hp hu,hf]
  exact ⟨padicValRat p (G u),by ring⟩

/-- Exact arithmetic interface for tame-specialization estimates at good rational primes. -/
theorem branch_iff_dvd_contactSupport (hp : 17 ≤ p) {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (S : Finset ℕ) (hS : p ∉ S) : badBranch p u ↔ p ∣ ZInQ.contactSupport S u := by
  rw [ZInQ.prime_dvd_contactSupport_iff hu (Fact.out : Nat.Prime p)]
  constructor
  · rintro (hz | ⟨hv,h⟩ | ⟨_,h⟩)
    · exact ⟨hS,(zero_branch_iff hp hu).mp hz⟩
    · exact (h (pole_multiple hp hu hv)).elim
    · exact (h (third_even hp u)).elim
  · rintro ⟨_,hx⟩; exact Or.inl ((zero_branch_iff hp hu).mpr hx)

#print axioms negative_parameter_units
#print axioms zero_even
#print axioms zero_contact_multiplicity
#print axioms zero_branch_iff
#print axioms pole_multiple
#print axioms third_even
#print axioms branch_iff_dvd_contactSupport
end ZInQBlueprint.ContactMultiplicity



