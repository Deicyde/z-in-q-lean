import HeightTransport
import Mathlib.Data.Rat.Sqrt

/-! Original five projective contacts of the scalar parameter. -/
namespace Sun28.ScalarHeight
open Sun28.Ordinary ZInQ.Mult

def beta (x : ℚ) : ℚ := 2*x^2+3

def scalarRadicand (t : ℚ) : ℚ := t*(t-1)*(t-2401)*(32*t+343)*(2*t-1)

def scalarMarks : Finset ℚ := {0,1,2401,-343/32,1/2}

private def badProduct : ℕ := 2*3*5*7*359*4801

theorem beta_off (x : ℚ) : beta x∉scalarMarks := by
  have irr : ¬IsSquare (1199:ℚ) := by
    rintro ⟨y,ey⟩
    have e := (Rat.exists_mul_self 1199).mp ⟨y,ey.symm⟩
    norm_num [Rat.sqrt_ofNat,show Nat.sqrt 1199=34 by symm; exact Nat.eq_sqrt.mpr (by decide)] at e
  have neq : beta x ≠ 2401 := by
    intro e
    apply irr
    refine ⟨x,?_⟩
    unfold beta at e
    nlinarith
  have low : 3≤beta x := by unfold beta; nlinarith [sq_nonneg x]
  simp only [scalarMarks,Finset.mem_insert,Finset.mem_singleton]
  rintro (e|e|e|e|e) <;> first | exact neq e | linarith

theorem scalar_factorization (t : ℚ) :
    scalarRadicand t=64*∏ a ∈ scalarMarks,(t-a) := by
  norm_num [scalarRadicand,scalarMarks,Finset.prod_insert]
  ring

private theorem small_not_dvd {p n : ℕ} (pos : 0<n) (small : n<p) : ¬p∣n :=
  fun h => (Nat.not_lt_of_ge (Nat.le_of_dvd pos h)) small

private theorem small_unit {p n : ℕ} (pos : 0<n) (small : n<p) :
    padicValRat p (n:ℚ)=0 := by
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd (small_not_dvd pos small)]
  rfl

private theorem separated {p : ℕ} [hp : Fact p.Prime] (large : 76176<p) :
    ¬p ∣ badProduct := by
  have h (n : ℕ) (a : 0<n) (b : n≤76176) := small_not_dvd a (lt_of_le_of_lt b large)
  simp only [badProduct,hp.out.dvd_mul,h 2 (by decide) (by decide),h 3 (by decide) (by decide),
    h 5 (by decide) (by decide),h 7 (by decide) (by decide),h 359 (by decide) (by decide),
    h 4801 (by decide) (by decide),or_self,not_false_eq_true]

private theorem difference_unit {p : ℕ} [hp : Fact p.Prime] (large : 76176<p)
    {a b : ℚ} (ha : a∈scalarMarks) (hb : b∈scalarMarks) (ab : a≠b) :
    padicValRat p (a-b)=0 := by
  have catalog : ∀ a∈scalarMarks, ∀ b∈scalarMarks, a≠b →
      (a-b).num.natAbs∣badProduct^5 ∧ (a-b).den∣badProduct^5 := by
    norm_num [scalarMarks,badProduct,Nat.dvd_iff_mod_eq_zero]
  have away : ¬p∣badProduct^5 := fun d => separated large (hp.out.dvd_of_dvd_pow d)
  obtain ⟨num,den⟩ := catalog a ha b hb ab
  simp only [padicValRat_def,padicValInt,padicValNat.eq_zero_of_not_dvd (fun h => away (h.trans num)),
    padicValNat.eq_zero_of_not_dvd (fun h => away (h.trans den)),Nat.cast_zero,sub_self]

theorem radicand_at_mark {p : ℕ} [Fact p.Prime] (large : 76176<p)
    {t a : ℚ} (off : t∉scalarMarks) (ha : a∈scalarMarks) (pos : 0<padicValRat p (t-a)) :
    padicValRat p (scalarRadicand t)=padicValRat p (t-a) := by
  have live (b : ℚ) (hb : b∈scalarMarks) : t-b≠0 := fun eq => off (sub_eq_zero.mp eq ▸ hb)
  have v64 : padicValRat p (64:ℚ)=0 := by exact small_unit (n:=64) (by decide) (by omega)
  rw [scalar_factorization,padicValRat.mul (by norm_num) (Finset.prod_ne_zero_iff.mpr live),
    v64,zero_add,padicValRat_finset_prod scalarMarks live,Finset.sum_eq_single a]
  · intro b hb ba
    have un := difference_unit large ha hb ba.symm
    have eq : t-b=(a-b)+(t-a) := by ring
    rw [eq,padicValRat.add_eq_of_lt (eq ▸ live b hb) (sub_ne_zero.mpr ba.symm) (live a ha) (un ▸ pos),un]
  · exact fun bad => (bad ha).elim

private theorem finite_form {i : Fin 5} (hi : i≠0) (t : ℚ) :
    ∃ a∈scalarMarks, oldForm i t.num t.den=contactForm t a := by
  fin_cases i
  · exact (hi rfl).elim
  · refine ⟨0,by norm_num [scalarMarks],?_⟩; norm_num [oldForm,contactForm]
  · refine ⟨1,by norm_num [scalarMarks],?_⟩; norm_num [oldForm,contactForm]
  · refine ⟨2401,by norm_num [scalarMarks],?_⟩; norm_num [oldForm,contactForm]
  · refine ⟨-343/32,by norm_num [scalarMarks],?_⟩; norm_num [oldForm,contactForm]; ring

private theorem even_pole {p : ℕ} [hp : Fact p.Prime] (large : 76176<p) (x : ℚ)
    (pos : 0<padicValNat p (beta x).den) : Even (padicValNat p (beta x).den) := by
  let t := beta x
  change 0<padicValNat p t.den at pos
  change Even (padicValNat p t.den)
  have mn := reduced_min p t
  have n0 : padicValInt p t.num=0 := by omega
  have vt : padicValRat p t= -(padicValNat p t.den:ℤ) := by rw [padicValRat_def,n0]; simp
  have neg : padicValRat p t<0 := by omega
  have three : padicValRat p (-(3:ℚ))=0 := by simpa using small_unit (p:=p) (n:=3) (by decide) (by omega)
  have nz : t≠0 := by rintro h; simp [h] at neg
  have sum : t+(-3) = 2*x^2 := by dsimp [t,beta]; ring
  have xn : x≠0 := by
    rintro rfl
    change padicValRat p (2*0^2+3:ℚ)<0 at neg
    norm_num at neg
    have h := small_unit (p:=p) (n:=3) (by decide) (by omega)
    norm_num at h
    omega
  have e := padicValRat.add_eq_of_lt (sum ▸ mul_ne_zero (by norm_num) (pow_ne_zero 2 xn)) nz (by norm_num : -(3:ℚ)≠0) (three ▸ neg)
  have v2 : padicValRat p (2:ℚ)=0 := by exact small_unit (n:=2) (by decide) (by omega)
  rw [sum,padicValRat.mul (by norm_num) (pow_ne_zero 2 xn),padicValRat.pow,
    v2] at e
  rw [even_iff_two_dvd]
  omega

theorem old_scalar_contact {p : ℕ} [Fact p.Prime] (large : 76176<p) (x : ℚ)
    (S : Finset ℕ) (member : p∈oldContactPrimes S (beta x).num (beta x).den) :
    0<padicValRat p (scalarRadicand (beta x)) ∧ Odd (padicValRat p (scalarRadicand (beta x))) := by
  obtain ⟨_,_,i,pos,odd⟩ := mem_oldContactPrimes.mp member
  by_cases hi : i=0
  · subst i
    simp [oldForm,padicValInt] at pos odd
    obtain ⟨k,ek⟩ := even_pole large x pos
    obtain ⟨j,ej⟩ := odd
    omega
  · obtain ⟨a,ha,f⟩ := finite_form hi (beta x)
    rw [f] at pos odd
    have dn : ¬p ∣ a.den := by
      have sizes : ∀ b∈scalarMarks, b.den≤32 := by norm_num [scalarMarks]
      exact small_not_dvd a.den_pos (by have h := sizes a ha; omega)
    have off := beta_off x
    have aff := (projective_contact_iff (t:=beta x) (a:=a) (fun e => off (e.symm ▸ ha)) dn).mp ⟨pos,odd⟩
    rw [radicand_at_mark large off ha aff.1]
    exact aff

theorem beta_primitive (x : ℚ) : Int.gcd (beta x).num (beta x).den=1 := by
  simpa [Int.gcd] using (beta x).reduced.gcd_eq_one

theorem beta_off_forms (x : ℚ) : ∀ i, oldForm i (beta x).num (beta x).den≠0 := by
  let t:=beta x
  intro i
  by_cases hi : i=0
  · subst i; simp [oldForm]
  obtain ⟨a,ha,f⟩ := finite_form hi t
  rw [f]
  intro zero
  have e : t.num*(a.den:ℤ)=a.num*(t.den:ℤ) := sub_eq_zero.mp zero
  have eq : t=a := by
    rw [←Rat.num_div_den t,←Rat.num_div_den a]
    apply (div_eq_div_iff (by exact_mod_cast t.den_nz) (by exact_mod_cast a.den_nz)).mpr
    exact_mod_cast e
  exact beta_off x (show t∈scalarMarks from eq.symm ▸ ha)

end Sun28.ScalarHeight
#print axioms Sun28.ScalarHeight.beta_off
#print axioms Sun28.ScalarHeight.scalar_factorization
#print axioms Sun28.ScalarHeight.old_scalar_contact
#print axioms Sun28.ScalarHeight.beta_off_forms
