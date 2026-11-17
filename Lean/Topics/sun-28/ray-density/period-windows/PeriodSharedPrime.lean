import AnchorOrders
import Mathlib.Data.Nat.Factorization.Basic

namespace Sun28.PeriodWindows
open Sun28.QualitativeRows

/-- A prime demands a common orientation exactly past its exponent in the anchor. -/
def excess (C n p : ℕ) : Prop := p.Prime ∧ C.factorization p < n.factorization p

/-- A prime imposes a relation between different marked values if the two chosen
arms exceed the exponent of this prime in the anchor. -/
def shared {ι : Type*} (o : ι → Bool → ℕ) (C p : ℕ) : Prop :=
  ∃ i j : ι, i ≠ j ∧ ∃ s t : Bool, excess C (o i s) p ∧ excess C (o j t) p

theorem common_excess {a b C : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<C) :
    (¬a.gcd b ∣ C) ↔ ∃ p, excess C a p ∧ excess C b p := by
  have hg := Nat.gcd_pos_of_pos_left b ha
  rw [Nat.factorization_le_iff_dvd hg.ne' hc.ne' |>.symm]
  change ¬ (∀ p, (a.gcd b).factorization p ≤ C.factorization p) ↔ _
  push Not
  constructor
  · rintro ⟨p,h⟩
    have prime : p.Prime := by
      by_contra hnp
      rw [Nat.factorization_eq_zero_of_not_prime (a.gcd b) hnp] at h
      omega
    rw [Nat.factorization_gcd ha.ne' hb.ne', Finsupp.inf_apply] at h
    exact ⟨p,⟨prime,(lt_min_iff.mp h).1⟩,⟨prime,(lt_min_iff.mp h).2⟩⟩
  · rintro ⟨p,⟨_,hp⟩,⟨_,hq⟩⟩
    refine ⟨p,?_⟩
    rw [Nat.factorization_gcd ha.ne' hb.ne', Finsupp.inf_apply]
    exact lt_min hp hq

/-- With opposite arms individually compatible and both choices allowed at the
fixed vertices, a single shared prime can always be oriented consistently. -/
theorem balanced_of_one_shared {ι J : Type*} (o : ι → Bool → ℕ) (m r : J → ℕ) (C : ℕ)
    (pos : ∀ i s,0<o i s) (cp : 0<C)
    (single : ∀ i, (o i false).gcd (o i true) ∣ C)
    (pins : ∀ j i s (t : Bool), r j ≡ (if t then C else 0) [MOD (m j).gcd (o i s)])
    (unique : ∀ p q, shared o C p → shared o C q → p=q) :
    ∀ v, ¬Walk (Edge o m r C) v v true := by
  classical
  obtain ⟨q,hq⟩ : ∃ q, ∀ p, shared o C p → p=q := by
    by_cases h : ∃ p, shared o C p
    · obtain ⟨p,hp⟩ := h; exact ⟨p,fun t ht => unique _ _ ht hp⟩
    · exact ⟨0,fun p hp => (h ⟨p,hp⟩).elim⟩
  let f (i : ι) : Bool := decide (excess C (o i true) q)
  have arm (i : ι) (s : Bool) (d : excess C (o i s) q) : f i = s := by
    cases s with
    | true => simp [f,d]
    | false =>
      have hn : ¬excess C (o i true) q := fun e =>
        (common_excess (pos i false) (pos i true) cp).mpr ⟨q,d,e⟩ (single i)
      simp [f,hn]
  have direct {u v d} (e : Constraint o m r C u v d) :
      (u.elim false f ^^ v.elim false f) = d := by
    cases e with
    | pin j i s t bad => exact (bad (pins j i s t)).elim
    | pair i j s t bad =>
      change (f i ^^ f j) = (s ^^ t)
      by_cases same : i=j
      · subst j
        by_cases st:s=t
        · subst t; simp
        · cases s <;> cases t <;> simp_all [Nat.gcd_comm]
      · obtain ⟨p,hp,hp'⟩ := (common_excess (pos i s) (pos j t) cp).mp bad
        have eq := hq p ⟨i,j,same,s,t,hp,hp'⟩
        subst p
        rw [arm i s hp,arm j t hp']
  apply (balanced_iff (Edge o m r C) (fun e => edge_symm e)).mp
  refine ⟨fun i => i.elim false f,?_⟩
  intro u v d edge
  rcases edge with e | e
  · exact direct e
  · rw [Bool.xor_comm]; exact direct e

end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.common_excess
#print axioms Sun28.PeriodWindows.balanced_of_one_shared
