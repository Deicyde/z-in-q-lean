import DegreeCharts
import GuardDeterminant

/-! A monic univariate polynomial and a guard with integer-polynomial
parameter coefficients compile to a finite atlas, without generic gcd assumptions. -/
namespace Sun28.Branches
open Polynomial
noncomputable section

private def blank {m} (p : Polynomial (Poly m)) : List (Poly m) :=
  (List.range (p.natDegree+1)).map p.coeff

private theorem blank_spec {m} (p : Polynomial (Poly m)) (x : Fin m → ℚ) :
    (∀ q ∈ blank p, value x q = 0) ↔ p.map (value x) = 0 := by
  constructor
  · intro h
    ext j
    rw [coeff_map,coeff_zero]
    by_cases hj : j ≤ p.natDegree
    · apply h
      apply List.mem_map_of_mem
      simp [hj]
    · simp [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hj)]
  · intro h q hq
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    have e := congrArg (fun f : ℚ[X] => f.coeff j) h
    simpa using e

private def Chart.addEqs {m} (a : Chart m) (eqs : List (Poly m)) : Chart m :=
  {a with eqs := eqs ++ a.eqs}

private theorem addEqs_spec {m} (a : Chart m) (e : List (Poly m)) (x : Fin m → ℚ) :
    (a.addEqs e).accepts x ↔ (∀ p ∈ e, value x p = 0) ∧ a.accepts x := by
  simp only [Chart.addEqs,Chart.accepts,List.mem_append]
  constructor
  · rintro ⟨he,hg,hd,hp⟩
    exact ⟨fun p h => he p (.inl h),fun p h => he p (.inr h),hg,hd,hp⟩
  · rintro ⟨hl,hr,hg,hd,hp⟩
    exact ⟨fun p h => h.elim (hl p) (hr p),hg,hd,hp⟩

/-- For each possible first nonzero coefficient, stratify again by its degree
in T. All chart equations live over the original integer parameter ring. -/
def filteredAtlas {m} (P G : Polynomial (Poly m)) : List (Chart m) :=
  let B := Mask.determinant P G
  (List.range (P.natDegree+1)).flatMap fun e =>
    let zeros := (List.range e).flatMap fun i => blank (B.coeff i)
    (List.range ((B.coeff e).natDegree+1)).map fun n =>
      (degreeChart (B.coeff e) n).addEqs zeros

theorem earlier_zero {m} (B : Polynomial (Polynomial (Poly m))) (e : ℕ) (x : Fin m → ℚ) :
    (∀ p ∈ (List.range e).flatMap (fun i => blank (B.coeff i)), value x p = 0) ↔
      ∀ i < e, (B.coeff i).map (value x) = 0 := by
  simp only [List.mem_flatMap,List.mem_range,forall_exists_index,and_imp]
  constructor
  · intro h i hi
    exact (blank_spec _ _).mp (fun p hp => h p i hi hp)
  · intro h p i hi hp
    exact (blank_spec _ _).mpr (h i hi) p hp

theorem filteredAtlas_spec {m} (P G : Polynomial (Poly m)) (hp : P.Monic) (x : Fin m → ℚ) :
    (∃ a ∈ filteredAtlas P G, a.accepts x) ↔
      ∃ t : ℚ, (P.map (value x)).IsRoot t ∧ ¬(G.map (value x)).IsRoot t := by
  let B := Mask.determinant P G
  obtain ⟨e,he,low,live,roots⟩ := Mask.rational_specialization (value x) P G hp
  simp only [filteredAtlas,List.mem_flatMap,List.mem_range,List.mem_map]
  constructor
  · rintro ⟨a,⟨i,hi,n,hn,rfl⟩,ha⟩
    obtain ⟨zeros,hc⟩ := (addEqs_spec ..).mp ha
    obtain ⟨hnz,_,t,ht⟩ := (degreeChart_spec ..).mp hc
    have hz := (earlier_zero B i x).mp zeros
    have id : i = e := by
      rcases lt_trichotomy i e with h | h | h
      · exact False.elim (hnz (low _ h))
      · exact h
      · exact False.elim (live (hz _ h))
    subst i
    exact ⟨t,(roots t).mp ht⟩
  · rintro ⟨t,ht⟩
    let n := ((B.coeff e).map (value x)).natDegree
    have hn : n ≤ (B.coeff e).natDegree := natDegree_map_le
    refine ⟨_,⟨e,Nat.lt_succ_of_le he,n,Nat.lt_succ_of_le hn,rfl⟩,(addEqs_spec ..).mpr ⟨(earlier_zero B e x).mpr low,?_⟩⟩
    exact (degreeChart_spec ..).mpr ⟨live,rfl,t,(roots t).mpr ht⟩

/-- One fixed integer polynomial realizes a rational root with a root-dependent
nonvanishing condition at every rational parameter value. -/
theorem guarded_polynomial {m} (P G : Polynomial (Poly m)) (hp : P.Monic) :
    ∃ F : Poly (m+1), ∀ x : Fin m → ℚ,
      (∃ w : ℚ, value (Fin.cases w x) F = 0) ↔
        ∃ t : ℚ, (P.map (value x)).IsRoot t ∧ ¬(G.map (value x)).IsRoot t := by
  exact ⟨atlasPolynomial (filteredAtlas P G),fun x => (atlas_projection _ _).trans (filteredAtlas_spec P G hp x)⟩

end
end Sun28.Branches
#print axioms Sun28.Branches.filteredAtlas_spec
#print axioms Sun28.Branches.guarded_polynomial
