import CappedRadical
import ZInQKernel.Multiplication.Soundness.RationalHeights

/-! Prime support bounds for rescaling either of the primitive Mordell equations. -/
open UniqueFactorizationMonoid ZInQ
namespace ZInQBlueprint.TwistDescent
noncomputable section

def IsSInteger (S : Finset ℕ) (q : ℚ) : Prop := q.den.primeFactors ⊆ S

/-- Von Känel, Corollary 7.4, over ℤ[1/N], when the nonzero integer
coefficient is supported on S. The product outside S is empty. -/
def SupportedMordell74 : Prop :=
  ∀ (S : Finset ℕ) (a : ℤ) (x y : ℚ), (∀ p ∈ S, Nat.Prime p) →
    a ≠ 0 → a.natAbs.primeFactors ⊆ S → IsSInteger S x → IsSInteger S y →
    y^2 = x^3+(a:ℚ) →
    let A : ℝ := 62208 * ((∏ p ∈ S, p : ℕ):ℝ)^2
    ratHeight x ≤ Real.log (a.natAbs:ℝ) + 4*A*(Real.log A)^2

/-- Splitting exponents modulo three bounds the cube-free part by the squared radical. -/
theorem remove_cubes (w : ℕ) (positive : 0<w) :
    ∃ k e : ℕ, 0<k ∧ 0<e ∧ w=k^3*e ∧ e≤(radical w)^2 := by
  let f := w.primeFactors
  let k := ∏ p ∈ f, p^(w.factorization p/3)
  let e := ∏ p ∈ f, p^(w.factorization p%3)
  have kp : 0<k := Finset.prod_pos fun p hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _
  have ep : 0<e := Finset.prod_pos fun p hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _
  refine ⟨k,e,kp,ep,?_,?_⟩
  · unfold k e
    rw [←Finset.prod_pow,←Finset.prod_mul_distrib]
    calc
      w = ∏ p ∈ f, p ^ w.factorization p := Nat.prod_primeFactors_pow_factorization positive.ne'
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p _
        rw [←pow_mul,←pow_add]
        congr 1
        omega
  · unfold e
    rw [Nat.radical_eq_prod_primeFactors,←Finset.prod_pow]
    apply Finset.prod_le_prod
    intro p hp
    exact Nat.pow_le_pow_right (Nat.pos_of_mem_primeFactors hp) (by omega)

/-- The denominator after rescaling only uses primes of w. -/
theorem scaled_sIntegral {w k : ℕ} (wk : k ∣ w) (wp : 0<w) (kp : 0<k)
    (n j : ℕ) (jp : j≠0) :
    IsSInteger (3*w).primeFactors ((n:ℚ)/(k:ℚ)^j) := by
  have de : ((n:ℚ)/(k:ℚ)^j).den ∣ k^j := by
    have h := Rat.den_dvd (n:ℤ) ((k^j:ℕ):ℤ)
    rw [Rat.divInt_eq_div] at h
    apply Int.natCast_dvd_natCast.mp
    simpa using h
  apply Finset.Subset.trans (Nat.primeFactors_mono de (pow_ne_zero _ kp.ne'))
  rw [Nat.primeFactors_pow k jp]
  exact Nat.primeFactors_mono (wk.trans (dvd_mul_left w 3)) (by positivity)

/-- In the reduced abscissa Z/k² of either Mordell model, at most 729 cancels. -/
theorem numerator_loss {Z k w v c : ℕ} (kp : 0<k) (cw : w.Coprime v)
    (coef : 0<c) (size : c≤27) (kw : k^2 ∣ w) (eqn : Z^3=(c*v)^2+27*w^2) :
    (Z:ℝ) ≤ 729*(max |(((Z:ℚ)/(k:ℚ)^2).num:ℝ)| (((Z:ℚ)/(k:ℚ)^2).den:ℝ)) := by
  let g := (k^2).gcd Z
  have gz : g ∣ Z := Nat.gcd_dvd_right _ _
  have gw : g ∣ w := (Nat.gcd_dvd_left _ _).trans kw
  have gv : g.Coprime (v^2) := (Nat.Coprime.of_dvd_left gw cw).pow_right 2
  have sub : g ∣ (c*v)^2 := by
    have za := gz.trans (dvd_pow_self Z (by decide : 3≠0))
    have wa := dvd_mul_of_dvd_right (gw.trans (dvd_pow_self w (by decide : 2≠0))) 27
    rw [eqn] at za
    exact (Nat.dvd_add_iff_left wa).mpr za
  rw [mul_pow] at sub
  have gc : g ≤ 729 := (Nat.le_of_dvd (pow_pos coef 2) (gv.dvd_mul_right.mp sub)).trans
    (show c^2 ≤ 27^2 from Nat.pow_le_pow_left size 2)
  have gr : (g:ℝ)≤729 := by exact_mod_cast gc
  have qeq : ((Z:ℚ)/(k:ℚ)^2).num = ((Z/g:ℕ):ℤ) := by
    have q : ((Z:ℚ)/(k:ℚ)^2)=mkRat (Z:ℤ) (k^2) := by
      rw [←Rat.divInt_ofNat,Rat.divInt_eq_div]
      push_cast
      rfl
    rw [q,Rat.num_mkRat]
    simp [g,kp.ne',Int.natCast_ediv]
  have mul : (Z:ℝ) = ((Z/g:ℕ):ℝ)*g := by exact_mod_cast (Nat.div_mul_cancel gz).symm
  rw [qeq,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    (Z:ℝ) = _ := mul
    _ ≤ (Z/g:ℕ)*729 := mul_le_mul_of_nonneg_left gr (by positivity)
    _ ≤ _ := by nlinarith [le_max_left ((Z/g:ℕ):ℝ) (((Z:ℚ)/(k:ℚ)^2).den:ℝ)]

end
end ZInQBlueprint.TwistDescent
#print axioms ZInQBlueprint.TwistDescent.remove_cubes
#print axioms ZInQBlueprint.TwistDescent.scaled_sIntegral
#print axioms ZInQBlueprint.TwistDescent.numerator_loss
