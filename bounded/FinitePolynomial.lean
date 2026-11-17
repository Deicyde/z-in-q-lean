import ZInQKernel.Syntax.Language.Basic

/-! Polynomial relations over the rationals with finitely many existential variables. -/

namespace ZOverQ.Qualitative

open MvPolynomial ZInQ.Syntax

private noncomputable abbrev evaluate {ι : Type} (x : ι → ℚ) :=
  eval₂Hom (Int.castRingHom ℚ) x

/-- An integer polynomial with visible coordinates indexed by `ι` and a finite
set of existentially quantified rational coordinates. -/
def PolynomialRelation {ι : Type} (R : (ι → ℚ) → Prop) : Prop :=
  ∃ (W : Type) (_ : Finite W) (P : MvPolynomial (ι ⊕ W) ℤ), ∀ a : ι → ℚ,
    (∃ w : W → ℚ, eval₂ (Int.castRingHom ℚ) (Sum.elim a w) P = 0) ↔ R a

private theorem evaluate_rename {ι κ : Type} (f : ι → κ) (p : MvPolynomial ι ℤ)
    (x : κ → ℚ) (y : ι → ℚ) (h : ∀ i, x (f i) = y i) :
    evaluate x (rename f p) = evaluate y p := by
  rw [evaluate, eval₂Hom_rename]
  exact congrArg (fun z => eval₂Hom (Int.castRingHom ℚ) z p) (funext h)

namespace PolynomialRelation

/-- Route the parameters of a template into any specified visible coordinates.
Variables beyond the declared witness range evaluate to zero, as in `ExPoly.Rel`. -/
theorem template {ι : Type} (τ : ExPoly) (f : Fin τ.params → ι) :
    PolynomialRelation (fun a => τ.Rel (a ∘ f)) := by
  classical
  let subst (i : ℕ) : MvPolynomial (ι ⊕ Fin τ.witnesses) ℤ :=
    if h : i < τ.params then X (.inl (f ⟨i, h⟩))
    else if h' : i - τ.params < τ.witnesses then X (.inr ⟨i - τ.params, h'⟩) else 0
  refine ⟨Fin τ.witnesses, inferInstance, bind₁ subst τ.poly, ?_⟩
  intro a
  apply exists_congr
  intro w
  change evaluate (Sum.elim a w) (bind₁ subst τ.poly) = 0 ↔
    ev (assign τ.params τ.witnesses (a ∘ f) w) τ.poly = 0
  suffices he : evaluate (Sum.elim a w) (bind₁ subst τ.poly) =
      ev (assign τ.params τ.witnesses (a ∘ f) w) τ.poly by rw [he]
  rw [evaluate, eval₂Hom_bind₁, ev]
  apply congrArg (fun z => eval₂Hom (Int.castRingHom ℚ) z τ.poly)
  funext i
  unfold subst assign
  split_ifs <;> simp

theorem congr {ι : Type} {R S : (ι → ℚ) → Prop} (h : PolynomialRelation R)
    (e : ∀ a, R a ↔ S a) : PolynomialRelation S := by
  obtain ⟨W, hW, p, hp⟩ := h
  exact ⟨W, hW, p, fun a => (hp a).trans (e a)⟩

/-- A sum of two squares joins two equations with disjoint sets of witnesses. -/
theorem conj {ι : Type} {R S : (ι → ℚ) → Prop}
    (hr : PolynomialRelation R) (hs : PolynomialRelation S) :
    PolynomialRelation (fun a => R a ∧ S a) := by
  classical
  obtain ⟨U, hU, p, hp⟩ := hr
  obtain ⟨V, hV, q, hq⟩ := hs
  let left : ι ⊕ U → ι ⊕ (U ⊕ V) := Sum.map id Sum.inl
  let right : ι ⊕ V → ι ⊕ (U ⊕ V) := Sum.map id Sum.inr
  refine ⟨U ⊕ V, inferInstance, (rename left p)^2 + (rename right q)^2, ?_⟩
  intro a
  have zeros (w : U ⊕ V → ℚ) : evaluate (Sum.elim a w) ((rename left p)^2 + (rename right q)^2) = 0 ↔
      evaluate (Sum.elim a (w ∘ Sum.inl)) p = 0 ∧ evaluate (Sum.elim a (w ∘ Sum.inr)) q = 0 := by
    rw [map_add, map_pow, map_pow,
      evaluate_rename left p _ (Sum.elim a (w ∘ Sum.inl)) (by rintro (i|j) <;> rfl),
      evaluate_rename right q _ (Sum.elim a (w ∘ Sum.inr)) (by rintro (i|j) <;> rfl),
      add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
    simp
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hu, hv⟩ := (zeros w).1 hw
    exact ⟨(hp a).1 ⟨_, hu⟩, (hq a).1 ⟨_, hv⟩⟩
  · rintro ⟨hR, hS⟩
    obtain ⟨u, hu⟩ := (hp a).2 hR
    obtain ⟨v, hv⟩ := (hq a).2 hS
    exact ⟨Sum.elim u v, (zeros _).2 ⟨hu, hv⟩⟩

/-- Quantify the coordinates indexed by `κ` and number all witnesses, keeping
the distinguished rational argument at coordinate zero. -/
theorem project {κ : Type} [Finite κ] {R : (Unit ⊕ κ → ℚ) → Prop} (h : PolynomialRelation R) :
    ∃ n : ℕ, ∃ p : MvPolynomial (Fin (n + 1)) ℤ, ∀ q : ℚ,
      (∃ w : Fin n → ℚ, eval₂ (Int.castRingHom ℚ) (Fin.cons q w) p = 0) ↔
        ∃ u : κ → ℚ, R (Sum.elim (fun _ => q) u) := by
  classical
  obtain ⟨W, hW, p, hp⟩ := h
  let _ := Fintype.ofFinite (κ ⊕ W)
  let n := Fintype.card (κ ⊕ W)
  let e : κ ⊕ W ≃ Fin n := Fintype.equivFin _
  let f : (Unit ⊕ κ) ⊕ W → Fin (n + 1) :=
    Sum.elim (Sum.elim (fun _ => 0) (fun c => (e (.inl c)).succ)) (fun k => (e (.inr k)).succ)
  refine ⟨n, rename f p, ?_⟩
  intro q
  have val (w : Fin n → ℚ) : evaluate (Fin.cons q w) (rename f p) =
      evaluate (Sum.elim (Sum.elim (fun _ => q) (fun c => w (e (.inl c)))) (fun k => w (e (.inr k)))) p := by
    apply evaluate_rename
    rintro ((i|c)|k) <;> simp [f]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨_, (hp _).1 ⟨_, (val w).symm.trans hw⟩⟩
  · rintro ⟨u, hR⟩
    obtain ⟨v, hv⟩ := (hp _).2 hR
    let w := Sum.elim u v ∘ e.symm
    refine ⟨w, (val w).trans ?_⟩
    simpa [w] using hv

end PolynomialRelation
end ZOverQ.Qualitative

#print axioms ZOverQ.Qualitative.PolynomialRelation.template
#print axioms ZOverQ.Qualitative.PolynomialRelation.conj
#print axioms ZOverQ.Qualitative.PolynomialRelation.project
