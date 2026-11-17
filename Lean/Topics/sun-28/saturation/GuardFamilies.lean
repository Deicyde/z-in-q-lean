import GuardSaturation

/-! Univariate equations and inequations after specialization of the parameters. -/
open Polynomial
namespace Sun28.Guard
variable {K : Type*} [Field K] [DecidableEq K]

/-- Successively impose equations by taking gcd with the current polynomial. -/
noncomputable def equations (P : K[X]) : List K[X] → K[X]
  | [] => P
  | E :: rest => equations (EuclideanDomain.gcd P E) rest

theorem equations_dvd (P : K[X]) (eqs : List K[X]) : equations P eqs ∣ P := by
  induction eqs generalizing P with
  | nil => exact dvd_refl _
  | cons E rest ih => exact (ih _).trans (EuclideanDomain.gcd_dvd_left P E)

theorem isRoot_equations (P : K[X]) (eqs : List K[X]) (t : K) :
    (equations P eqs).IsRoot t ↔ P.IsRoot t ∧ ∀ E ∈ eqs, E.IsRoot t := by
  induction eqs generalizing P with
  | nil => simp [equations]
  | cons E rest ih =>
    rw [equations,ih]
    have gcd_roots : (EuclideanDomain.gcd P E).IsRoot t ↔ P.IsRoot t ∧ E.IsRoot t := by
      simpa only [IsRoot,eval₂_id] using (root_gcd_iff_root_left_right
        (ϕ:=RingHom.id K) (f:=P) (g:=E) (α:=t))
    simp only [gcd_roots,List.forall_mem_cons,and_assoc]

omit [DecidableEq K] in
theorem product_guard (guards : List K[X]) (t : K) :
    ¬ guards.prod.IsRoot t ↔ ∀ G ∈ guards, ¬ G.IsRoot t := by
  induction guards with
  | nil => simp [IsRoot]
  | cons G rest ih =>
    simp only [List.prod_cons,IsRoot,eval_mul,mul_ne_zero_iff,List.forall_mem_cons] at ih ⊢
    exact and_congr_right (fun _ => ih)

/-- One polynomial for a nonzero seed, a list of equations and a list of inequations. -/
noncomputable def filtered (P : K[X]) (eqs guards : List K[X]) (N : ℕ) : K[X] :=
  keep (equations P eqs) guards.prod N

theorem isRoot_filtered {P : K[X]} (hP : P≠0) (eqs guards : List K[X]) {N : ℕ}
    (bound : P.natDegree≤N) (t : K) :
    (filtered P eqs guards N).IsRoot t ↔
    P.IsRoot t ∧ (∀ E ∈ eqs, E.IsRoot t) ∧ (∀ G ∈ guards, ¬G.IsRoot t) := by
  have hd := equations_dvd P eqs
  have hn : equations P eqs ≠ 0 := fun e => hP (by rwa [e,zero_dvd_iff] at hd)
  rw [filtered,isRoot_keep hn ((natDegree_le_of_dvd hd hP).trans bound),isRoot_equations,product_guard,and_assoc]

/-- On a parameter fibre, specialize all coefficients *before* applying the gcds.
The uniform exponent is the degree of the seed before specialization. -/
noncomputable def fibre {R : Type*} [CommRing R] (φ : R →+* K)
    (P : R[X]) (eqs guards : List R[X]) : K[X] :=
  filtered (P.map φ) (eqs.map (Polynomial.map φ)) (guards.map (Polynomial.map φ)) P.natDegree

theorem isRoot_fibre {R : Type*} [CommRing R] (φ : R →+* K) (P : R[X])
    (eqs guards : List R[X]) (live : P.map φ ≠ 0) (t : K) :
    (fibre φ P eqs guards).IsRoot t ↔
      P.eval₂ φ t=0 ∧ (∀ E ∈ eqs, E.eval₂ φ t=0) ∧ (∀ G ∈ guards,G.eval₂ φ t≠0) := by
  rw [fibre,isRoot_filtered live _ _ natDegree_map_le]
  simp [IsRoot,eval_map]

/-- Gcd filtering after specialization also recognizes points in every extension
of the specialized field. This form includes all geometric roots over an algebraic closure. -/
theorem map_equations {L : Type*} [Field L] [DecidableEq L] (f : K →+* L)
    (P : K[X]) (eqs : List K[X]) :
    (equations P eqs).map f = equations (P.map f) (eqs.map (Polynomial.map f)) := by
  induction eqs generalizing P with
  | nil => rfl
  | cons E rest ih => simp only [equations,List.map_cons,ih,Polynomial.gcd_map]

theorem isRoot_map_fibre {R L : Type*} [CommRing R] [Field L] [DecidableEq L]
    (φ : R →+* K) (f : K →+* L) (P : R[X]) (eqs guards : List R[X])
    (live : P.map φ≠0) (t : L) :
    ((fibre φ P eqs guards).map f).IsRoot t ↔
    P.eval₂ (f.comp φ) t=0 ∧ (∀ E ∈ eqs, E.eval₂ (f.comp φ) t=0) ∧
      ∀ G ∈ guards, G.eval₂ (f.comp φ) t≠0 := by
  have mapped : (fibre φ P eqs guards).map f=fibre (f.comp φ) P eqs guards := by
    unfold fibre filtered
    rw [map_keep,map_equations]
    have prod_map (gs : List K[X]) :
        gs.prod.map f=(gs.map (Polynomial.map f)).prod := by
      induction gs with
      | nil => simp
      | cons g rest ih => simp only [List.prod_cons,List.map_cons,Polynomial.map_mul,ih]
    rw [prod_map]
    simp only [Polynomial.map_map,List.map_map,Function.comp_def]
  rw [mapped]
  apply isRoot_fibre
  rw [←Polynomial.map_map]
  exact (Polynomial.map_ne_zero_iff f.injective).mpr live

/-- A monic seed stays nonzero at every parameter value, including degree zero. -/
theorem isRoot_fibre_monic {R L : Type*} [CommRing R] [Field L] [DecidableEq L]
    (φ : R →+* K) (f : K →+* L) {P : R[X]} (monic : P.Monic)
    (eqs guards : List R[X]) (t : L) :
    ((fibre φ P eqs guards).map f).IsRoot t ↔
    P.eval₂ (f.comp φ) t=0 ∧ (∀ E ∈ eqs, E.eval₂ (f.comp φ) t=0) ∧
      ∀ G ∈ guards, G.eval₂ (f.comp φ) t≠0 :=
  isRoot_map_fibre φ f P eqs guards (monic.map φ).ne_zero t

#print axioms isRoot_fibre_monic
#print axioms map_equations
#print axioms isRoot_map_fibre
#print axioms equations_dvd
#print axioms isRoot_equations
#print axioms product_guard
#print axioms isRoot_filtered
#print axioms isRoot_fibre
end Sun28.Guard
