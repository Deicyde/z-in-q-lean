import FilteredAtlas

/-! Eliminate one root subject to a monic equation and further polynomial
equalities and inequalities at that same root. -/
namespace Sun28.Branches
open Polynomial
noncomputable section

private def squares {m} : List (Polynomial (Poly m)) → Polynomial (Poly m)
  | [] => 0
  | f :: fs => f^2 + squares fs

private def ev {m} (x : Fin m → ℚ) (t : ℚ) : Polynomial (Poly m) →+* ℚ :=
  Polynomial.eval₂RingHom (value x) t

private theorem squares_nonneg {m} (x : Fin m → ℚ) (t : ℚ) (fs : List (Polynomial (Poly m))) :
    0 ≤ ev x t (squares fs) := by
  induction fs with
  | nil => simp [squares]
  | cons f fs ih => simpa only [squares,map_add,map_pow] using add_nonneg (sq_nonneg (ev x t f)) ih

private theorem squares_spec {m} (x : Fin m → ℚ) (t : ℚ) (fs : List (Polynomial (Poly m))) :
    ev x t (squares fs) = 0 ↔ ∀ f ∈ fs, ev x t f = 0 := by
  induction fs with
  | nil => simp [squares]
  | cons f fs ih =>
    rw [squares,map_add,map_pow,List.forall_mem_cons,← ih]
    constructor
    · intro h
      constructor <;> nlinarith [squares_nonneg x t fs,sq_nonneg (ev x t f)]
    · rintro ⟨h,j⟩; simp [h,j]

private theorem prod_spec {m} (x : Fin m → ℚ) (t : ℚ) (gs : List (Polynomial (Poly m))) :
    ev x t gs.prod ≠ 0 ↔ ∀ g ∈ gs, ev x t g ≠ 0 := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [ih]

/-- The e-th row adds a coefficient guard recording that H_e is nonzero and
imposes vanishing of all coefficients from the preceding rows. -/
def testsAtlas {m} (P : Polynomial (Poly m)) (eqs guards : List (Polynomial (Poly m))) : List (Chart m) :=
  let B := Mask.determinant P guards.prod
  (List.range (P.natDegree+1)).flatMap fun e =>
    let zeros := (List.range e).flatMap fun j => (List.range ((B.coeff j).natDegree+1)).map (B.coeff j).coeff
    let F := squares (B.coeff e :: eqs)
    (List.range (F.natDegree+1)).flatMap fun d =>
      (List.range ((B.coeff e).natDegree+1)).map fun u =>
        let chart := degreeChart F d
        {chart with guard := (B.coeff e).coeff u, eqs := zeros ++ chart.eqs}

private theorem attach_spec {m} (F : Polynomial (Poly m)) (d : ℕ) (zeros : List (Poly m))
    (g : Poly m) (x : Fin m → ℚ) :
    ({degreeChart F d with eqs := zeros ++ (degreeChart F d).eqs, guard := g} : Chart m).accepts x ↔
      (∀ p ∈ zeros, value x p = 0) ∧ value x g ≠ 0 ∧ (degreeChart F d).accepts x := by
  simp only [Chart.accepts,degreeChart,List.mem_append,map_one]
  constructor
  · rintro ⟨h,hg,hd,hr⟩
    exact ⟨fun p hp => h p (.inl hp),hg,fun p hp => h p (.inr hp),one_ne_zero,hd,hr⟩
  · rintro ⟨h,hg,h',_,hd,hr⟩
    exact ⟨fun p hp => hp.elim (h p) (h' p),hg,hd,hr⟩

private theorem earlier {m} (B : Polynomial (Polynomial (Poly m))) (i : ℕ) (x : Fin m → ℚ) :
    (∀ p ∈ (List.range i).flatMap (fun j => (List.range ((B.coeff j).natDegree+1)).map (B.coeff j).coeff),
      value x p = 0) ↔ ∀ j < i, (B.coeff j).map (value x) = 0 := by
  exact earlier_zero B i x

theorem testsAtlas_spec {m} (P : Polynomial (Poly m)) (hp : P.Monic)
    (eqs guards : List (Polynomial (Poly m))) (x : Fin m → ℚ) :
    (∃ a ∈ testsAtlas P eqs guards, a.accepts x) ↔
      ∃ t : ℚ, (P.map (value x)).IsRoot t ∧ (∀ f ∈ eqs, (f.map (value x)).IsRoot t) ∧
        (∀ g ∈ guards, ¬(g.map (value x)).IsRoot t) := by
  let B := Mask.determinant P guards.prod
  obtain ⟨e,he,low,live,roots⟩ := Mask.rational_specialization (value x) P guards.prod hp
  have val (p : Polynomial (Poly m)) (t : ℚ) : (p.map (value x)).eval t = ev x t p :=
    Polynomial.eval_map ..
  simp only [testsAtlas,List.mem_flatMap,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨a,⟨i,_,d,_,u,_,rfl⟩,ha⟩
    obtain ⟨zeros,gu,hd⟩ := (attach_spec ..).mp ha
    obtain ⟨_,_,t,ht⟩ := (degreeChart_spec ..).mp hd
    have non : (B.coeff i).map (value x) ≠ 0 := by
      intro h
      exact gu (by simpa using congrArg (fun q : ℚ[X] => q.coeff u) h)
    have hz := (earlier B i x).mp zeros
    have id : i = e := by
      rcases lt_trichotomy i e with k | k | k
      · exact False.elim (non (low _ k))
      · exact k
      · exact False.elim (live (hz _ k))
    subst i
    have hh := (squares_spec x t (B.coeff e :: eqs)).mp ((val _ t).symm.trans ht)
    have good := (roots t).mp ((val _ t).trans (hh _ List.mem_cons_self))
    refine ⟨t,good.1,fun f hf => (val f t).trans (hh f (by simp [hf])),?_⟩
    intro g hg hg0
    exact (prod_spec x t guards).mp (fun h => good.2 ((val _ t).trans h)) g hg ((val g t).symm.trans hg0)
  · rintro ⟨t,hp0,hfs,hgs⟩
    have hg : ev x t guards.prod ≠ 0 := (prod_spec x t guards).mpr
      (fun g h hg => hgs g h ((val _ t).trans hg))
    have rt := (roots t).mpr ⟨hp0,fun h => hg ((val _ t).symm.trans h)⟩
    let f := squares (B.coeff e :: eqs)
    have fr : (f.map (value x)).IsRoot t := (val _ t).trans ((squares_spec _ _ _).mpr (by
      rw [List.forall_mem_cons]
      exact ⟨(val _ t).symm.trans rt,fun g h => (val _ t).symm.trans (hfs g h)⟩))
    let u := ((B.coeff e).map (value x)).natDegree
    have hu : u ≤ (B.coeff e).natDegree := natDegree_map_le
    have gun : value x ((B.coeff e).coeff u) ≠ 0 := by
      rw [← coeff_map]; exact leadingCoeff_ne_zero.mpr live
    have fl : f.map (value x) ≠ 0 := by
      intro h
      have all (r : ℚ) : ev x r f = 0 := (val _ r).symm.trans (by rw [h,eval_zero])
      apply live
      apply Polynomial.funext
      intro r
      rw [eval_zero,val]
      exact (squares_spec x r (B.coeff e :: eqs)).mp (all r) _ List.mem_cons_self
    let d := (f.map (value x)).natDegree
    have hdn : d ≤ f.natDegree := natDegree_map_le
    refine ⟨_,⟨e,Nat.lt_succ_of_le he,d,Nat.lt_succ_of_le hdn,u,Nat.lt_succ_of_le hu,rfl⟩,
      (attach_spec ..).mpr ⟨(earlier B e x).mpr low,gun,(degreeChart_spec ..).mpr ⟨fl,rfl,t,fr⟩⟩⟩

/-- Uniform existential projection of a monic root, a conjunction of polynomial
equations, and a conjunction of polynomial inequalities. -/
theorem polynomial_for_tests {m} (P : Polynomial (Poly m)) (hp : P.Monic)
    (eqs guards : List (Polynomial (Poly m))) :
    ∃ F : Poly (m+1), ∀ x : Fin m → ℚ,
      (∃ w : ℚ, value (Fin.cases w x) F = 0) ↔
        ∃ t : ℚ, (P.map (value x)).IsRoot t ∧ (∀ f ∈ eqs, (f.map (value x)).IsRoot t) ∧
          (∀ g ∈ guards, ¬(g.map (value x)).IsRoot t) :=
  ⟨atlasPolynomial (testsAtlas P eqs guards),fun x => (atlas_projection _ _).trans (testsAtlas_spec P hp eqs guards x)⟩

end
end Sun28.Branches
#print axioms Sun28.Branches.testsAtlas_spec
#print axioms Sun28.Branches.polynomial_for_tests
