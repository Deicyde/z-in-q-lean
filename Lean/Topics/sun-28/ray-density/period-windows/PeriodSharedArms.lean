import PeriodFrame
namespace Sun28.PeriodWindows
open Sun28.QualitativeRows Sun28.ContactFactors
noncomputable section

/-- An arm is active only when its order exceeds the anchor exponent at some
prime that also exceeds this exponent at a different marked position. -/
def active {ι : Type*} (o : ι → Bool → ℕ) (C : ℕ) (i : ι) (s : Bool) : Prop :=
  ∃ j : ι, i≠j ∧ ∃ t p, excess C (o i s) p ∧ excess C (o j t) p

theorem balanced_of_one_active_arm {ι J : Type*} (o : ι→Bool→ℕ) (m r : J→ℕ) (C : ℕ)
    (pos : ∀ i s,0<o i s) (cp : 0<C)
    (single : ∀ i,(o i false).gcd (o i true) ∣ C)
    (pins : ∀ j i s (t : Bool), r j ≡ (if t then C else 0) [MOD (m j).gcd (o i s)])
    (oneArm : ∀ i, ¬(active o C i true ∧ active o C i false)) :
    ∀ v, ¬Walk (Edge o m r C) v v true := by
  classical
  let f (i : ι) : Bool:=decide (active o C i true)
  have chosen (i : ι) (s : Bool) (act : active o C i s) : f i=s := by
    cases s with
    | true => simp [f,act]
    | false =>
      have hn:¬active o C i true:=fun h=>oneArm i ⟨h,act⟩
      simp [f,hn]
  have direct {u v d} (e : Constraint o m r C u v d) : (u.elim false f ^^ v.elim false f)=d := by
    cases e with
    | pin j i s t bad => exact (bad (pins j i s t)).elim
    | pair i j s t bad =>
      change (f i ^^ f j)=(s ^^ t)
      by_cases same:i=j
      · subst j
        by_cases st:s=t
        · subst t;simp
        · cases s <;> cases t <;> simp_all [Nat.gcd_comm]
      · obtain ⟨p,h,k⟩:=(common_excess (pos i s) (pos j t) cp).mp bad
        rw [chosen i s ⟨j,same,t,p,h,k⟩,chosen j t ⟨i,Ne.symm same,s,p,k,h⟩]
  apply (balanced_iff (Edge o m r C) (fun e=>edge_symm e)).mp
  refine ⟨fun i=>i.elim false f,?_⟩
  intro u v d edge
  rcases edge with e | e
  · exact direct e
  · rw [Bool.xor_comm];exact direct e

theorem point_row_of_one_arm {X : ℤ} {w : Window X} {L : ℕ} (F : PeriodFrame w L)
    (oneArm : ∀ i, ¬(active F.orders (Nat.factorial 576) i true ∧
      active F.orders (Nat.factorial 576) i false)) : PointRow w := by
  refine ⟨F.u,F.v,F.values,F.pos,F.step,F.slope_large,F.rays,F.exclusions,F.roots,F.squares,?_⟩
  have pos i s : 0<F.orders i s := periodAt_positive F.values _ F.roots F.squares i s
  apply balanced_of_one_active_arm F.orders _ _ _ pos (Nat.factorial_pos _) F.individual _ oneArm
  intro j i s t
  exact all_pins (pos i s) (F.dyadic i s) (fun q hp odd le=>F.free q hp odd le i s) j t

/-- The distinct large primes must meet at opposite arms of the very same
position; the two outer positions need not be different from each other. -/
theorem fork_of_no_point_row {X : ℤ} {w : Window X} {L : ℕ} (F : PeriodFrame w L)
    (bad : ¬PointRow w) :
    ∃ i j k, i≠j ∧ i≠k ∧ ∃ p q, p≠q ∧ guard (integerRadicand X) L<p ∧
      guard (integerRadicand X) L<q ∧ ∃ s t,
      excess (Nat.factorial 576) (F.orders i true) p ∧ excess (Nat.factorial 576) (F.orders j s) p ∧
      excess (Nat.factorial 576) (F.orders i false) q ∧ excess (Nat.factorial 576) (F.orders k t) q := by
  classical
  have hh:¬∀ i,¬(active F.orders (Nat.factorial 576) i true ∧ active F.orders (Nat.factorial 576) i false) :=
    fun h=>bad (point_row_of_one_arm F h)
  push Not at hh
  obtain ⟨i,⟨j,ij,s,p,e,e'⟩,k,ik,t,q,f,f'⟩:=hh
  have ne:p≠q:=by
    rintro rfl
    exact ((common_excess (periodAt_positive F.values _ F.roots F.squares i false)
      (periodAt_positive F.values _ F.roots F.squares i true) (Nat.factorial_pos 576)).mpr
      ⟨p,f,e⟩) (F.individual i)
  exact ⟨i,j,k,ij,ik,p,q,ne,F.shared_above ⟨i,j,ij,true,s,e,e'⟩,
    F.shared_above ⟨i,k,ik,false,t,f,f'⟩,s,t,e,e',f,f'⟩
end
end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.balanced_of_one_active_arm
#print axioms Sun28.PeriodWindows.point_row_of_one_arm
#print axioms Sun28.PeriodWindows.fork_of_no_point_row
