import BranchUnitObstruction
import ContactRadicands
import Mathlib.Data.Nat.Prime.Infinite

/-! Square-contact counterexamples at primes outside any prescribed finite set. -/
open Polynomial
namespace ZInQBlueprint.BranchHeight.UnitObstruction
open SexticThetaHeight
noncomputable section

abbrev parameterAt (p : ℕ) : ℚ := (p:ℚ)^2

theorem unmarked_at {p : ℕ} [hprime : Fact p.Prime] : parameterAt p ∉ ZInQ.contactSet := by
  have h : 0 < (p:ℚ) := by exact_mod_cast hprime.out.pos
  norm_num [parameterAt,ZInQ.contactSet]
  exact ⟨hprime.out.ne_zero,by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

private theorem unit {p n : ℕ} (h : ¬p ∣ n) : padicValRat p (n:ℚ)=0 := by
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd h]
  rfl

/-- A prime exceeding five divides no divisor of 120, nor of any power of 120. -/
private theorem not_dvd_120pow {p n k : ℕ} [hprime : Fact p.Prime] (hp : 5<p)
    (hn : n ∣ 120^k) : ¬p ∣ n := by
  intro h
  have h120 := hprime.out.dvd_of_dvd_pow (h.trans hn)
  have hfac : p ∣ Nat.factorial 5 := by simpa only [show Nat.factorial 5=120 by decide] using h120
  exact (not_le_of_gt hp) ((Nat.Prime.dvd_factorial hprime.out).mp hfac)

private theorem unit_add_multiple {p n : ℕ} (a : ℕ) (hn : ¬p ∣ n) :
    padicValRat p ((a:ℚ)*p+n) = 0 := by
  norm_cast
  have h : ¬p ∣ a*p+n := fun hd => hn ((Nat.dvd_add_right (dvd_mul_left p a)).mp hd)
  simp only [padicValNat.eq_zero_of_not_dvd h]

private theorem offset_unit {p n : ℕ} (hn : ¬p ∣ n) :
    padicValRat p (parameterAt p+n)=0 := by
  simpa only [parameterAt,pow_two] using unit_add_multiple p hn

private theorem at_zero {p : ℕ} [hprime : Fact p.Prime] :
    padicValRat p (parameterAt p)=2 := by
  rw [parameterAt,padicValRat.pow,padicValRat.self hprime.out.one_lt]
  norm_num

theorem contact_valuations {p : ℕ} [Fact p.Prime] (hp : 5<p)
    (c : ℚ) (hc : c ∈ ZInQ.contactSet) :
    padicValRat p (parameterAt p-c) = if c=0 then 2 else 0 := by
  simp [ZInQ.contactSet] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [sub_zero,ite_true] using at_zero (p:=p)
  · simpa using offset_unit (p:=p) (n:=15) (not_dvd_120pow (k:=1) hp (by decide))
  · simpa using offset_unit (p:=p) (n:=20) (not_dvd_120pow (k:=1) hp (by decide))
  · simpa using offset_unit (p:=p) (n:=24) (not_dvd_120pow (k:=1) hp (by decide))
  · simpa using offset_unit (p:=p) (n:=30) (not_dvd_120pow (k:=1) hp (by decide))
  · simpa using offset_unit (p:=p) (n:=60) (not_dvd_120pow (k:=1) hp (by decide))


theorem uniform_outside_support {p : ℕ} [hprime : Fact p.Prime] (hp : 5<p) (S : Finset ℕ) :
    ¬p ∣ ZInQ.contactSupport S (parameterAt p) := by
  intro h
  obtain ⟨_,c,hc,_,⟨k,hk⟩⟩ :=
    (ZInQ.prime_dvd_contactSupport_iff (unmarked_at (p:=p)) hprime.out).mp h
  rw [contact_valuations hp c hc] at hk
  split at hk <;> omega

/-- For every prime exceeding five, J(p²) has valuation four and the invariant coefficient is a unit. -/
theorem uniform_valuations {p : ℕ} [hprime : Fact p.Prime] (hp : 5<p) :
    padicValRat p (SixContact.J (parameterAt p))=4 ∧ padicValRat p (3779136:ℚ)=0 := by
  have hpp : 0 < (p:ℚ) := by exact_mod_cast hprime.out.pos
  have hu : 0 < parameterAt p := by unfold parameterAt; positivity
  have hoff (n:ℕ) (hn : n ∣ 120^1) : padicValRat p (parameterAt p+n)=0 := offset_unit (not_dvd_120pow hp hn)
  have hf : padicValRat p (SixContact.F (parameterAt p))=2 := by
    unfold SixContact.F
    repeat rw [padicValRat.mul (by positivity) (by positivity)]
    have h15 : padicValRat p (parameterAt p + 15) = 0 := by
      simpa using hoff 15 (by decide)
    have h20 : padicValRat p (parameterAt p + 20) = 0 := by
      simpa using hoff 20 (by decide)
    have h24 : padicValRat p (parameterAt p + 24) = 0 := by
      simpa using hoff 24 (by decide)
    have h30 : padicValRat p (parameterAt p + 30) = 0 := by
      simpa using hoff 30 (by decide)
    have h60 : padicValRat p (parameterAt p + 60) = 0 := by
      simpa using hoff 60 (by decide)
    simp [h15,h20,h24,h30,h60]
  have hg : padicValRat p (SixContact.G (parameterAt p))=0 := by
    convert unit_add_multiple (p:=p) (n:=3600) (7*p^3+300*p) (not_dvd_120pow (k:=2) hp (by decide)) using 1
    congr 1
    unfold SixContact.G parameterAt
    push_cast
    ring
  have hF : SixContact.F (parameterAt p) ≠ 0 := by unfold SixContact.F; positivity
  have hG : SixContact.G (parameterAt p) ≠ 0 := by unfold SixContact.G; positivity
  have h57600 : padicValRat p (57600:ℚ)=0 :=
    unit (n:=57600) (not_dvd_120pow (k:=3) hp (by decide))
  have hc : padicValRat p (3779136:ℚ)=0 :=
    unit (n:=3779136) (not_dvd_120pow (k:=10) hp (by decide))
  refine ⟨?_,hc⟩
  rw [SixContact.J,padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ hF)) (pow_ne_zero _ hG),
    padicValRat.mul (by norm_num) (pow_ne_zero _ hF),padicValRat.neg,padicValRat.pow,padicValRat.pow,
    hf,hg,h57600]
  norm_num

theorem uniform_paper_nonunit {p : ℕ} [hprime : Fact p.Prime] (hp : 5 < p)
    {δ : ℚ} (hδ : δ ≠ 0) {r : Fin 6 → ℂ}
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic (parameterAt p) δ)=0)
    (v : AbsoluteValue (weightField r) ℝ) (hv : IsNonarchimedean v) (hplace : LiesOver p v) :
    ∃ i, v (weights r i) ≠ 1 := by
  obtain ⟨hj,hc⟩ := uniform_valuations hp
  exact paper_nonunit_of_valuations (unmarked_at (p:=p)) hδ (by omega) hc hr hz v hv hplace

/-- Every finite base set admits an unmarked square contact outside it and its support. -/
theorem outside_every_finite_set (S : Finset ℕ) : ∃ p : ℕ, p.Prime ∧ 5<p ∧
    p ∉ S ∧ ¬p ∣ ZInQ.contactSupport S (parameterAt p) ∧
    Even (padicValRat p (rootClass₁ (parameterAt p))) ∧
    Even (padicValRat p (rootClass₂ (parameterAt p))) ∧
    Even (padicValRat p (rootClass₃ (parameterAt p))) := by
  obtain ⟨p,hlen,hp⟩ := Nat.exists_infinite_primes (max 5 (S.sup id)+1)
  have hlarge : 5 < p := by omega
  have htop : S.sup id < p := by omega
  have hout : p ∉ S := fun h => (not_le_of_gt htop) (Finset.le_sup (f:=id) h)
  let : Fact p.Prime := ⟨hp⟩
  have hs := uniform_outside_support hlarge S
  exact ⟨p,hp,hlarge,hout,hs,rootClasses_even (unmarked_at (p:=p)) (by omega) hout hs⟩

end
end ZInQBlueprint.BranchHeight.UnitObstruction
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.unmarked_at
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.contact_valuations
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.uniform_outside_support
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.uniform_valuations
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.uniform_paper_nonunit
#print axioms ZInQBlueprint.BranchHeight.UnitObstruction.outside_every_finite_set
