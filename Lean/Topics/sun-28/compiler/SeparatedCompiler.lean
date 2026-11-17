import CompilerRows

/-! Uniform elimination of every variable of a monic triangular tower, over
the rationals, subject to arbitrary additional polynomial equations and
inequations. Exactly one rational witness remains. -/
open Polynomial ZInQBlueprint.SunTower ZInQBlueprint.SunResultant
open ZInQBlueprint.SunResultant.ParamTower Sun28.Branches
namespace Sun28.Compiler
noncomputable section
variable {m n : ℕ}

/-- Union of finitely many chart lists whose indices range from zero to B. -/
def indexed {α : Type*} (B : ℕ) (family : ℕ → List α) : List α :=
  (List.range (B+1)).flatMap family

private theorem indexed_spec {α : Type*} (B : ℕ) (family : ℕ → List α) (P : α → Prop) :
    (∃ a ∈ indexed B family, P a) ↔ ∃ j ≤ B, ∃ a ∈ family j, P a := by
  simp only [indexed,List.mem_flatMap,List.mem_range,Nat.lt_succ_iff]
  constructor
  · rintro ⟨a,⟨j,hj,ha⟩,hp⟩
    exact ⟨j,hj,a,ha,hp⟩
  · rintro ⟨j,hj,a,ha,hp⟩
    exact ⟨a,⟨j,hj,ha⟩,hp⟩

/-- All indices and all coefficients are fixed before rational parameters are supplied. -/
def atlas (T : ParamTower (Poly m) n) (E G : List (Test m n)) : List (Chart m) :=
  indexed (bound T) fun b =>
    indexed (T.degreeProduct^2) fun d =>
      indexed T.degreeProduct fun ℓ => row T E G b d ℓ

/-- The target demands one rational tuple satisfying every equation and inequation. -/
def Solutions (T : ParamTower (Poly m) n) (E G : List (Test m n)) (p : Fin m → ℚ) : Prop :=
  ∃ y : Fin n → ℚ, Satisfies (value p) T y ∧
    (∀ f ∈ E, MvPolynomial.eval₂Hom (value p) y f = 0) ∧
    ∀ g ∈ G, MvPolynomial.eval₂Hom (value p) y g ≠ 0

theorem atlas_spec (T : ParamTower (Poly m) n) (E G : List (Test m n)) (p : Fin m → ℚ) :
    (∃ a ∈ atlas T E G, a.accepts p) ↔ Solutions T E G p := by
  classical
  unfold atlas Solutions
  simp_rw [indexed_spec,row_spec]
  constructor
  · rintro ⟨b,_hb,d,hd,ℓ,hℓ,sel,t,ht,eqs,ng⟩
    have hi := (rational_selects_iff T (value p) b).mpr ⟨d,hd,sel⟩
    obtain ⟨y,hy,hs⟩ := (rational_locator_at T (value p) hi t).mp ht
    subst t
    refine ⟨y,hy,fun f hf => (rational_samples T _ f hi y hy).mp (eqs f hf),?_⟩
    apply (product_nonzero (value p) y G).mp
    intro e
    exact ng (((rational_samples T _ G.prod hi y hy).mpr e) ℓ hℓ)
  · rintro ⟨y,hy,eqs,guards⟩
    obtain ⟨b,hb,d,hd,sel⟩ := exists_selection T (value p)
    have hi := (rational_selects_iff T (value p) b).mpr ⟨d,hd,sel⟩
    have nz := (product_nonzero (value p) y G).mpr guards
    have failed : ∃ ℓ ≤ T.degreeProduct,
        ¬ ((sample T b ℓ G.prod).map (value p)).IsRoot (separator (b:ℚ) y) := by
      by_contra! h
      exact nz ((rational_samples T _ G.prod hi y hy).mp h)
    obtain ⟨ℓ,hℓ,ng⟩ := failed
    exact ⟨b,hb,d,hd,ℓ,hℓ,sel,separator (b:ℚ) y,
      (rational_locator_at T (value p) hi _).mpr ⟨y,hy,rfl⟩,
      fun f hf => (rational_samples T _ f hi y hy).mpr (eqs f hf),ng⟩

/-- One explicit integer polynomial works simultaneously for all parameter values. -/
def polynomial (T : ParamTower (Poly m) n) (E G : List (Test m n)) :
    MvPolynomial (Fin (m+1)) ℤ := atlasPolynomial (atlas T E G)

theorem polynomial_spec (T : ParamTower (Poly m) n) (E G : List (Test m n)) (p : Fin m → ℚ) :
    (∃ w : ℚ, value (Fin.cases w p) (polynomial T E G) = 0) ↔ Solutions T E G p :=
  (atlas_projection _ _).trans (atlas_spec T E G p)

theorem polynomial_for_tower (T : ParamTower (Poly m) n) (E G : List (Test m n)) :
    ∃ F : MvPolynomial (Fin (m+1)) ℤ, ∀ p : Fin m → ℚ,
      (∃ w : ℚ, value (Fin.cases w p) F = 0) ↔
        ∃ y : Fin n → ℚ, Satisfies (value p) T y ∧
          (∀ f ∈ E, MvPolynomial.eval₂Hom (value p) y f = 0) ∧
          ∀ g ∈ G, MvPolynomial.eval₂Hom (value p) y g ≠ 0 :=
  ⟨polynomial T E G,polynomial_spec T E G⟩

#print axioms atlas_spec
#print axioms polynomial_spec
#print axioms polynomial_for_tower
end
end Sun28.Compiler
