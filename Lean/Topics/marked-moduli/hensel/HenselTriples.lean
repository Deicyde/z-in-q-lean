import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

namespace ZInQBlueprint.HenselTriples
open Polynomial IsLocalRing
noncomputable section
variable {R : Type*} [CommRing R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]

private theorem monicLift (f : R[X]) (hm : f.Monic) (r : ResidueField R)
    (hz : f.eval₂ (residue R) r = 0) (hd : f.derivative.eval₂ (residue R) r ≠ 0) :
    ∃ x : R, f.IsRoot x ∧ residue R x = r := by
  obtain ⟨a,rfl⟩ := residue_surjective r
  rw [eval₂_at_apply] at hz hd
  obtain ⟨b,hb,hba⟩ := HenselianRing.is_henselian f hm a
    ((residue_eq_zero_iff _).mp hz) (isUnit_iff_ne_zero.mpr hd)
  exact ⟨b,hb,sub_eq_zero.mp (by simpa only [← map_sub] using! (residue_eq_zero_iff _).mpr hba)⟩

/-- A simple residue root lifts for every polynomial, with arbitrary leading
coefficient. The stock Henselian axiom assumes the polynomial is monic. -/
theorem liftSimple (f : R[X]) (r : ResidueField R)
    (hz : f.eval₂ (residue R) r = 0) (hd : f.derivative.eval₂ (residue R) r ≠ 0) :
    ∃ x : R, f.IsRoot x ∧ residue R x = r := by
  obtain ⟨a,ha⟩ := residue_surjective r
  let ρ := residue R
  let c := f.eval a
  let v := f.derivative.eval a
  have hc : ρ c = 0 := by simpa only [← ha, eval₂_at_apply] using hz
  have hv : ρ v ≠ 0 := by simpa only [← ha, eval₂_at_apply] using hd
  -- Removing the constant and linear Taylor terms gives a normalized polynomial
  -- G with f(a+cX)=cG(X), whose reduction is 1+vX.
  let t := f.taylor a
  let h := t.divX.divX
  let G : R[X] := 1 + C v * X + X^2*(C c * h.comp (C c * X))
  have scale (x : R) : f.eval (a+c*x) = c*G.eval x := by
    have e0 := congrArg (Polynomial.eval (c*x)) (divX_mul_X_add t)
    have e1 := congrArg (Polynomial.eval (c*x)) (divX_mul_X_add t.divX)
    simp only [eval_add, eval_mul, eval_X, eval_C] at e0 e1
    have t0 : t.coeff 0 = c := taylor_coeff_zero ..
    have t1 : t.divX.coeff 0 = v := by simp [t,v,coeff_divX,taylor_coeff_one]
    rw [t0] at e0
    rw [t1] at e1
    change h.eval (c*x)*(c*x)+v = t.divX.eval (c*x) at e1
    rw [add_comm, ← f.taylor_eval a (c*x)]
    change t.eval (c*x) = c * G.eval x
    rw [← e0, ← e1]
    simp only [G, eval_add, eval_one, eval_mul, eval_C, eval_X, eval_pow, eval_comp]
    ring
  -- Reflect in degree n+1. The constant term of G is 1, so Q is monic,
  -- and its reduction is X^n (X+v), with a simple nonzero root at -v.
  let n := G.natDegree
  let Q := G.reflect (n+1)
  have hg0 : G.coeff 0 = 1 := by simp [G]
  have hmon : Q.Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one (n+1)
    · exact natDegree_reflect_le.trans (max_le le_rfl (Nat.le_succ _))
    · simpa only [Q, coeff_reflect, revAt_le le_rfl, Nat.sub_self] using hg0
  have hmap : G.map ρ = 1+C (ρ v)*X := by simp [G,hc]
  have hQ : Q.map ρ = X^n*(X + C (ρ v)) := by
    rw [show Q.map ρ = (G.map ρ).reflect (n+1) from (reflect_map ..).symm,
      hmap, reflect_add, reflect_one]
    rw [show C (ρ v)*X = C (ρ v)*X^1 by rw [pow_one], reflect_C_mul_X_pow,
      revAt_le (by omega : 1 ≤ n+1), Nat.add_sub_cancel, pow_succ]
    ring
  have hr : Q.eval₂ ρ (-(ρ v)) = 0 := by rw [eval₂_eq_eval_map,hQ]; simp
  have hder : Q.derivative.eval₂ ρ (-(ρ v)) ≠ 0 := by
    rw [eval₂_eq_eval_map, ← derivative_map, hQ, derivative_mul]
    simpa using pow_ne_zero n (neg_ne_zero.mpr hv)
  obtain ⟨z,hzQ,hzr⟩ := monicLift Q hmon _ hr hder
  have hu : IsUnit z := (residue_ne_zero_iff_isUnit _).mp (hzr ▸ neg_ne_zero.mpr hv)
  obtain ⟨u,rfl⟩ := hu
  -- The lifted reciprocal root is a unit. Its inverse is the required root of G.
  have hrev := eval₂_reflect_eq_zero_iff (RingHom.id R) (↑(u⁻¹) : R) (n+1) G (Nat.le_succ _)
  have hG : G.eval (↑(u⁻¹) : R) = 0 := hrev.mp (by rw [invOf_units, inv_inv]; exact hzQ)
  exact ⟨a+c*(↑(u⁻¹) : R), by change f.eval _ = 0; rw [scale,hG,mul_zero],
    by change ρ (a+c*(↑(u⁻¹) : R)) = r; rw [map_add, map_mul,hc,zero_mul,add_zero]; exact ha⟩


/-- The lifted root is unique in the prescribed residue class. -/
theorem liftSimple_unique (f : R[X]) (r : ResidueField R)
    (hz : f.eval₂ (residue R) r = 0) (hd : f.derivative.eval₂ (residue R) r ≠ 0) :
    ∃! x : R, f.IsRoot x ∧ residue R x = r := by
  obtain ⟨a,ha,har⟩ := liftSimple f r hz hd
  refine ⟨a,⟨ha,har⟩,?_⟩
  rintro b ⟨hb,hbr⟩
  obtain ⟨q,hq⟩ := dvd_iff_isRoot.mpr ha
  have hv : (q.map (residue R)).eval r ≠ 0 := by
    rw [hq, derivative_mul, eval₂_add, eval₂_mul, eval₂_mul] at hd
    simpa [eval_map, derivative_sub, ← har] using hd
  have hunit : IsUnit (q.eval b) := (residue_ne_zero_iff_isUnit _).mp <| by
    rwa [← hbr, eval_map, eval₂_at_apply] at hv
  have hzero : (b-a)*q.eval b=0 := by simpa [hq,IsRoot,eval_mul,eval_sub] using hb
  exact sub_eq_zero.mp ((hunit.mul_left_eq_zero).mp hzero)

/-- The six roots and the exact associated differences in the local ring. -/
structure TwoTriples (f : R[X]) (a : Fin 2 → R) (c : R)
    (ξ : Fin 2 → Fin 3 → ResidueField R) where
  y : Fin 2 → Fin 3 → R
  residue_y : ∀ i j, residue R (y i j) = ξ i j
  root : ∀ i j, f.IsRoot (a i+c*y i j)
  within : ∀ i j k, j ≠ k → ∃ u : Rˣ, (a i+c*y i j)-(a i+c*y i k) = c*(u : R)
  across : ∀ i k, i ≠ k → ∀ j l, IsUnit ((a i+c*y i j)-(a k+c*y k l))
  injective : Function.Injective (fun ij : Fin 2 × Fin 3 ↦ a ij.1+c*y ij.1 ij.2)


omit [HenselianRing R (maximalIdeal R)] [IsLocalRing R] in
/-- Convert a coefficientwise chart calculation into the hypothesis of
`twoTriples`. -/
theorem chartEval {a c : R} {f g : R[X]}
    (h : f.comp (C a+C c*X) = C (c^3)*g) (x : R) :
    f.eval (a+c*x) = c^3*g.eval x := by
  simpa [eval_comp] using congrArg (Polynomial.eval x) h

/-- A coefficientwise chart identity is sufficient; only its evaluation is used. -/
theorem twoTriples [IsDomain R] (f : R[X]) (a : Fin 2 → R) (c : R)
    (g : Fin 2 → R[X]) (ξ : Fin 2 → Fin 3 → ResidueField R)
    (hc : c ≠ 0) (hc0 : residue R c = 0)
    (ha : Function.Injective (fun i ↦ residue R (a i)))
    (chart : ∀ i x, f.eval (a i+c*x) = c^3*(g i).eval x)
    (distinct : ∀ i, Function.Injective (ξ i))
    (zero : ∀ i j, (g i).eval₂ (residue R) (ξ i j) = 0)
    (simple : ∀ i j, (g i).derivative.eval₂ (residue R) (ξ i j) ≠ 0) :
    Nonempty (TwoTriples f a c ξ) := by
  choose y hroot hy using fun i j ↦ liftSimple (g i) (ξ i j) (zero i j) (simple i j)
  have hx (i : Fin 2) (j : Fin 3) : residue R (a i+c*y i j) = residue R (a i) := by
    rw [map_add, map_mul, hc0, zero_mul, add_zero]
  constructor
  refine ⟨y, hy, ?_, ?_, ?_, ?_⟩
  · intro i j
    change f.eval _ = 0
    rw [chart, show (g i).eval (y i j)=0 from hroot i j, mul_zero]
  · intro i j k hjk
    have hu : IsUnit (y i j-y i k) := (residue_ne_zero_iff_isUnit _).mp (by
      rw [map_sub, hy, hy]; exact sub_ne_zero.mpr (fun h ↦ hjk (distinct i h)))
    obtain ⟨u,hu⟩ := hu
    exact ⟨u, by rw [hu]; ring⟩
  · intro i k hik j l
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [map_sub,hx,hx]
    exact sub_ne_zero.mpr (fun h ↦ hik (ha h))
  · rintro ⟨i,j⟩ ⟨k,l⟩ he
    change a i+c*y i j = a k+c*y k l at he
    have hi : i=k := ha <| (hx i j).symm.trans ((congrArg (residue R) he).trans (hx k l))
    subst k
    have hmul : c*y i j = c*y i l := add_left_cancel he
    have hcoord : y i j = y i l := mul_left_cancel₀ hc hmul
    have hres := congrArg (residue R) hcoord
    rw [hy,hy] at hres
    exact Prod.ext rfl (distinct i hres)

omit [HenselianRing R (maximalIdeal R)] in
/-- At degree at most six, the roots above exhaust all roots even after an
injective extension of the coefficient ring. -/
theorem rootsInExtension [IsDomain R] {f : R[X]} {a : Fin 2 → R} {c : R}
    {ξ : Fin 2 → Fin 3 → ResidueField R} (T : TwoTriples f a c ξ) (hf : f ≠ 0)
    (hd : f.natDegree ≤ 6) {K : Type*} [CommRing K] [IsDomain K]
    (ι : R →+* K) (hi : Function.Injective ι) (z : K) :
    (f.map ι).IsRoot z ↔ ∃ i j, z = ι (a i+c*T.y i j) := by
  classical
  let point (ij : Fin 2 × Fin 3) := ι (a ij.1+c*T.y ij.1 ij.2)
  have inj : Function.Injective point := hi.comp T.injective
  let six := Finset.univ.image point
  have card : six.card = 6 := by simp [six, Finset.card_image_of_injective _ inj]
  have hn : f.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hf
  have sub : six ⊆ (f.map ι).roots.toFinset := by
    intro x hx
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp hx
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hn).mpr
    change (f.map ι).eval (ι (a i+c*T.y i j))=0
    rw [eval_map, eval₂_at_apply, show f.eval (a i+c*T.y i j)=0 from T.root i j, map_zero]
  have he : six = (f.map ι).roots.toFinset := Finset.eq_of_subset_of_card_le sub (by
    rw [card]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_map_le.trans hd)))
  rw [← mem_roots hn, ← Multiset.mem_toFinset, ← he]
  constructor
  · intro h
    obtain ⟨⟨i,j⟩,_,e⟩ := Finset.mem_image.mp h
    exact ⟨i,j,e.symm⟩
  · rintro ⟨i,j,rfl⟩
    exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩

omit [HenselianRing R (maximalIdeal R)] in
/-- The polynomial has degree exactly six and splits into six distinct roots
over the given local ring. -/
theorem splitsSix [IsDomain R] {f : R[X]} {a : Fin 2 → R} {c : R}
    {ξ : Fin 2 → Fin 3 → ResidueField R} (T : TwoTriples f a c ξ) (hf : f ≠ 0)
    (hd : f.natDegree ≤ 6) : f.natDegree = 6 ∧ f.roots.Nodup ∧ f.Splits := by
  classical
  let x (ij : Fin 2 × Fin 3) := a ij.1+c*T.y ij.1 ij.2
  have incl : Finset.univ.image x ⊆ f.roots.toFinset := by
    intro z hz
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((mem_roots hf).mpr (T.root i j))
  have inj : Function.Injective x := T.injective
  have card : (Finset.univ.image x).card = 6 := by simp [Finset.card_image_of_injective _ inj]
  have h₁ := Finset.card_le_card incl
  rw [card] at h₁
  have h₂ := Multiset.toFinset_card_le f.roots
  have h₃ := card_roots' f
  exact ⟨by omega, Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega),
    splits_iff_card_roots.mpr (by omega)⟩

end
end ZInQBlueprint.HenselTriples
#print axioms ZInQBlueprint.HenselTriples.liftSimple
#print axioms ZInQBlueprint.HenselTriples.twoTriples
#print axioms ZInQBlueprint.HenselTriples.rootsInExtension
#print axioms ZInQBlueprint.HenselTriples.liftSimple_unique
#print axioms ZInQBlueprint.HenselTriples.splitsSix
#print axioms ZInQBlueprint.HenselTriples.chartEval
