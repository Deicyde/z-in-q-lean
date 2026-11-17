import ConicLines

namespace Sun28.ConicCovers
open Sun28.ScalarQuotients
open private support_product from ScalarKernels
noncomputable section

def left {R : Type*} [Ring R] (pos : Bool) (a b : R) :=
  if pos then b-a else a-b

def block {R : Type*} [Ring R] (pos : Bool) (a b : R) :=
  left pos a b*(15*b-a)

def partner {R : Type*} [Ring R] (a b : R) := (a+b)*(15*b+a)

def complementary {R : Type*} [Ring R] (pos : Bool) (a b : R) :=
  left pos a b*(15*b+a)

private theorem collision {a b : ℤ} (ab : a.natAbs.Coprime b.natAbs) {p : ℕ} (pp:p.Prime)
    {c d : ℤ} (h : (p:ℤ)∣a-c*b) (j : (p:ℤ)∣a-d*b) : (p:ℤ)∣c-d := by
  have ip:=Nat.prime_iff_prime_int.mp pp
  have z:(p:ℤ)∣(c-d)*b := by convert dvd_sub j h using 1;ring
  rcases ip.dvd_mul.mp z with e|e
  · exact e
  · have pa:(p:ℤ)∣a := by convert dvd_add h (dvd_mul_of_dvd_right e c) using 1;ring
    exact False.elim ((Nat.not_coprime_of_dvd_of_dvd pp.one_lt
      (by simpa using Int.natAbs_dvd_natAbs.mpr pa) (by simpa using Int.natAbs_dvd_natAbs.mpr e)) ab)

private theorem supports {a b : ℤ} {s : Bool} (ab:a.natAbs.Coprime b.natAbs)
    {p : ℕ} (pp:p.Prime) (h:(p:ℤ)∣block s a b) (j:(p:ℤ)∣partner a b) : p∣210 := by
  let ip:=Nat.prime_iff_prime_int.mp pp
  have h': (p:ℤ)∣a-1*b ∨ (p:ℤ)∣a-15*b := by
    rcases ip.dvd_mul.mp h with h|h
    · left; cases s
      · simpa [left] using h
      · simpa [left] using dvd_neg.mpr h
    · right; simpa using dvd_neg.mpr h
  have j': (p:ℤ)∣a-(-1)*b ∨ (p:ℤ)∣a-(-15)*b := by
    rcases ip.dvd_mul.mp j with j|j
    · left;simpa using j
    · right;simpa [sub_eq_add_neg,add_comm] using j
  rcases h' with h|h <;> rcases j' with j|j <;>
    have pd:=collision ab pp h j <;>
    have pn:=Int.natAbs_dvd_natAbs.mpr pd <;> norm_num at pn <;>
    exact pp.dvd_of_dvd_pow (n:=5) (Nat.dvd_trans pn (by decide : _∣210^5))

/-- A positive binary quadratic cross-factor has squarefree kernel dividing 210. -/
theorem block_support {a b : ℤ} {s : Bool} (ab:a.natAbs.Coprime b.natAbs)
    (pos : 0<block s a b) {c Y:ℤ} (dv:c.natAbs∣210)
    (eqn:block s a b * partner a b=c*Y^2) :
    ∃ d:ℕ, d∣210 ∧ ∃ U:ℤ, block s a b=(d:ℤ)*U^2 := by
  obtain ⟨d,U,sf,du,dv'⟩:=squarefree_factor pos eqn
  refine ⟨d,support_product sf (by decide) ?_,U,du⟩
  intro p pp ph
  have pd : (p:ℤ)∣d:=by exact_mod_cast ph
  have hit : (p:ℤ)∣block s a b :=du ▸ dvd_mul_of_dvd_left pd _
  rcases (Nat.prime_iff_prime_int.mp pp).dvd_mul.mp (pd.trans dv') with q|q
  · exact (show p∣c.natAbs by simpa using Int.natAbs_dvd_natAbs.mpr q).trans dv
  · exact supports ab pp hit q

/-- Homogenize a rational square of degree two at the reduced pair. -/
theorem scaled_square {n:ℤ} {Y B:ℚ} (h:(n:ℚ)=(B*Y)^2) :
    ∃ y:ℤ, n=y^2 := by
  obtain ⟨w,hw⟩:=Rat.isSquare_intCast_iff.mp (show IsSquare (n:ℚ) from ⟨B*Y,by rw [←sq,h]⟩)
  exact ⟨w,by rw [sq,hw]⟩

end
end Sun28.ConicCovers
#print axioms Sun28.ConicCovers.block_support
#print axioms Sun28.ConicCovers.scaled_square
