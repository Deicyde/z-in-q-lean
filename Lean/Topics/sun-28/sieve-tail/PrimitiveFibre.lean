import MixedChart
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Log

namespace Sun28.SieveTail
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.WeightedSelection

variable {A : Fin 3 → ℚ} {d : ℕ} {H Y : ℝ}

theorem ray_t_ne_zero (a : Candidate A d H Y) (i j : ↥(shifts A)) :
    tcoord (a.gaussian i) (a.gaussian j) ≠ 0 := by
  have hi := (a.rays.ray16 i).1
  have hj := (a.rays.ray16 j).1
  change (a.gaussian i).1 % 16 = 9 at hi
  change (a.gaussian j).1 % 16 = 9 at hj
  unfold tcoord
  omega

/-- First-coordinate divisors and the complementary-coordinate progression.
The latter is independent of the prime chosen from the order difference. -/
theorem primitive_fibre {m : ℕ} (hm : 0 < m) {K x z : ℤ}
    (cong : (m:ℤ) ∣ K-x*z) :
    0 < Int.gcd (m:ℤ) x ∧
    Int.gcd (m:ℤ) x ∣ K.natAbs ∧
    (∀ z' : ℤ, (m:ℤ) ∣ K-x*z' →
      z ≡ z' [ZMOD (m:ℤ)/(Int.gcd (m:ℤ) x:ℤ)]) := by
  refine ⟨Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast hm.ne'),?_,?_⟩
  · apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_natAbs.mpr
    have h₁ := (Int.gcd_dvd_left (m:ℤ) x).trans cong
    have h₂ := dvd_mul_of_dvd_left (Int.gcd_dvd_right (m:ℤ) x) z
    convert dvd_add h₁ h₂ using 1
    ring
  · intro z' hz
    apply Int.ModEq.cancel_left_div_gcd (by exact_mod_cast hm)
    exact (Int.modEq_iff_dvd.mpr cong).trans (Int.modEq_iff_dvd.mpr hz).symm

theorem prime_divisors_card {n : ℕ} (hn : n ≠ 0) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by decide)
  calc
    2^n.primeFactors.card = ∏ _p∈n.primeFactors, 2 := by simp
    _ ≤ ∏ p∈n.primeFactors, p := Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- The same two-square congruence controls primes dividing the chart coordinate:
either p already divides the common divisor g, or the divided-coordinate residue
lies on the ordinary two-point conic fibre. -/
theorem primitive_root {p : ℕ} [Fact p.Prime] {m g U X : ℤ}
    (form : (p:ℤ) ∣ (U*g)^2+(X*g)^2) (m_eq : m = U*g) :
    ((p:ℤ) ∣ g ∧ (p:ℤ) ∣ m) ∨ (X:ZMod p)^2 = -(U:ZMod p)^2 := by
  by_cases h : (p:ℤ) ∣ g
  · exact Or.inl ⟨h, m_eq ▸ dvd_mul_of_dvd_right h U⟩
  apply Or.inr
  have hg : (g:ZMod p)≠0 := fun e => h ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp e)
  have e := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr form
  push_cast at e
  have ze : ((X:ZMod p)^2+(U:ZMod p)^2)*(g:ZMod p)^2=0 := by linear_combination e
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp ze).resolve_right (pow_ne_zero 2 hg))

/-- There are at most two possibilities for the divided coordinate modulo p. -/
theorem roots_card {p : ℕ} [Fact p.Prime] (U : ZMod p) :
    (Finset.univ.filter (fun X : ZMod p => X^2= -U^2)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun X : ZMod p => X^2= -U^2)
  change S.card ≤ 2
  by_cases empty : S.Nonempty
  · obtain ⟨r,hr⟩:=empty
    have rr := (Finset.mem_filter.mp hr).2
    have incl : S ⊆ {r,-r} := by
      intro x hx
      have eq := (Finset.mem_filter.mp hx).2.trans rr.symm
      have sq : (x-r)*(x+r)=0 := by linear_combination eq
      rcases mul_eq_zero.mp sq with a|b
      · simp [sub_eq_zero.mp a]
      · simp [eq_neg_of_add_eq_zero_left b]
    exact (Finset.card_le_card incl).trans (Finset.card_le_two)
  · rw [Finset.not_nonempty_iff_eq_empty.mp empty]
    simp

/-- The primitive chart on actual weighted records, with the two symmetric
choices of coordinate made explicit. -/
theorem candidate_chart {p : ℕ} [Fact p.Prime] (a : Candidate A d H Y)
    (i j : ↥(shifts A)) (ij : i≠j)
    (hp : p ∣ adjacentNorm (a.gaussian i) true)
    (hm : p ∣ adjacentNorm (a.gaussian j) false) :
    let t := tcoord (a.gaussian i) (a.gaussian j)
    let x := xcoord (a.gaussian i) (a.gaussian j)
    let z := zcoord (a.gaussian i) (a.gaussian j)
    let K := gap i j*(a.v:ℤ)^2
    t≠0 ∧ K≠0 ∧ p ∈ (K+2*t).natAbs.primeFactors ∧
      ∃ X Z : ℤ, ((X=x ∧ Z=z) ∨ (X=z ∧ Z=x)) ∧
        (p:ℤ) ∣ t^2+X^2 ∧ (t.natAbs:ℤ) ∣ K-X*Z ∧
        Int.gcd (t.natAbs:ℤ) X ∣ K.natAbs ∧
        (∀ Z' : ℤ, (t.natAbs:ℤ) ∣ K-X*Z' →
          Z ≡ Z' [ZMOD (t.natAbs:ℤ)/(Int.gcd (t.natAbs:ℤ) X:ℤ)]) := by
  dsimp only
  let t := tcoord (a.gaussian i) (a.gaussian j)
  let x := xcoord (a.gaussian i) (a.gaussian j)
  let z := zcoord (a.gaussian i) (a.gaussian j)
  let K := gap i j*(a.v:ℤ)^2
  have tn : t ≠ 0 := ray_t_ne_zero a i j
  have kn : K ≠ 0 := mul_ne_zero (gap_ne_zero ij) (pow_ne_zero 2 (by exact_mod_cast a.positive.ne'))
  obtain ⟨dp,df⟩ := mixed_chart a i j hp hm
  refine ⟨tn,kn,Nat.mem_primeFactors.mpr ⟨Fact.out,?_,?_⟩,?_⟩
  · exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr dp)
  · exact Int.natAbs_ne_zero.mpr (ray_order_difference_ne_zero a i j)
  have ht : (t.natAbs:ℤ) ∣ K-x*z := by
    apply Int.natAbs_dvd.mpr
    exact ⟨_,(hyperbolic a i j).symm⟩
  rcases df with hx|hz
  · obtain ⟨_,dg,uniq⟩ := primitive_fibre (Int.natAbs_pos.mpr tn) ht
    exact ⟨x,z,Or.inl ⟨rfl,rfl⟩,hx,ht,dg,uniq⟩
  · rw [mul_comm x z] at ht
    obtain ⟨_,dg,uniq⟩ := primitive_fibre (Int.natAbs_pos.mpr tn) ht
    exact ⟨z,x,Or.inr ⟨rfl,rfl⟩,hz,ht,dg,uniq⟩

/-- Within a counting rectangle the signed chart and v determine the unique
candidate, since t is nonzero and the hyperbolic equation recovers a-c. -/
theorem chart_injective (boxes : CountingBoxes A d H Y) (N : ℕ)
    (i j : ↥(shifts A)) {a b : Candidate A d H Y}
    (ha : a∈boxes.records N) (hb : b∈boxes.records N)
    (hv : a.v=b.v)
    (ht : tcoord (a.gaussian i) (a.gaussian j)=tcoord (b.gaussian i) (b.gaussian j))
    (hx : xcoord (a.gaussian i) (a.gaussian j)=xcoord (b.gaussian i) (b.gaussian j))
    (hz : zcoord (a.gaussian i) (a.gaussian j)=zcoord (b.gaussian i) (b.gaussian j)) : a=b := by
  have e := hyperbolic a i j
  dsimp only at e
  rw [hv,hx,hz,←hyperbolic b i j,ht] at e
  have re := mul_left_cancel₀ (ray_t_ne_zero b i j) e
  unfold tcoord at ht
  unfold xcoord at hx
  unfold zcoord at hz
  have same : a.gaussian i=b.gaussian i := Prod.ext (by omega) (by omega)
  have en := congrArg gaussianNorm same
  rw [a.rays.norm,b.rays.norm] at en
  have en' := congrArg (fun n : ℕ => (n:ℤ)) en
  rw [a.values.equation i.val i.property,b.values.equation i.val i.property,hv] at en'
  exact boxes.uniquePair N a ha b hb (by exact_mod_cast add_right_cancel en') hv

end Sun28.SieveTail
#print axioms Sun28.SieveTail.ray_t_ne_zero
#print axioms Sun28.SieveTail.primitive_fibre
#print axioms Sun28.SieveTail.prime_divisors_card
#print axioms Sun28.SieveTail.primitive_root
#print axioms Sun28.SieveTail.roots_card
#print axioms Sun28.SieveTail.candidate_chart
#print axioms Sun28.SieveTail.chart_injective
