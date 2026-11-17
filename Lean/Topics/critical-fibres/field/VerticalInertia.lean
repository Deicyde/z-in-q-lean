import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace ZInQBlueprint.VerticalInertia

variable {G W : Type*} [Group G] [CommGroup W]

private theorem one_or_generator {T : Type*} [Group T] {a x : T}
    (ha : a ^ 2 = 1) (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    have he : n = (2 : ℤ) * k := by omega
    simp [he, zpow_mul, ha]
  · right
    have he : n = (2 : ℤ) * k + 1 := by omega
    simp [he, zpow_add, zpow_mul, ha]

/-- The images of the order-six and order-two inertia generators in a Klein four
quotient are different, and the latter is nontrivial. -/
theorem distinct_branch_images (a b c : W) (hexp : ∀ g : W, g ^ 2 = 1)
    (hcard : Nat.card W = 4) (hprod : a * b * c = 1)
    (hgen : Subgroup.closure {a, b, c} = ⊤) : c ≠ 1 ∧ b ≠ c := by
  have proper (g : W) : Subgroup.zpowers g ≠ ⊤ := by
    intro eq
    have hd := orderOf_dvd_of_pow_eq_one (hexp g)
    rw [← Nat.card_zpowers, eq, Subgroup.card_top, hcard] at hd
    norm_num at hd
  have hab : a = (b * c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [mul_assoc] using hprod
  have inCyclic (g : W) (hb : b ∈ Subgroup.zpowers g) (hc : c ∈ Subgroup.zpowers g) : False := by
    apply proper g
    apply top_unique
    rw [← hgen, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · rw [hab]
      exact (Subgroup.zpowers g).inv_mem ((Subgroup.zpowers g).mul_mem hb hc)
    rcases hx with rfl | hx
    · exact hb
    · have eq : x = c := hx
      exact eq ▸ hc
  constructor
  · intro e
    apply inCyclic b (Subgroup.mem_zpowers b)
    simp [e]
  · intro e
    apply inCyclic c
    · rw [e]
      exact Subgroup.mem_zpowers c
    · exact Subgroup.mem_zpowers c

/-- Two conjugate containments force trivial vertical inertia when the images of
the two horizontal subgroups are distinct lines and the second generator squares to one. -/
theorem vertical_inertia_eq_bot (q : G →* W) (V : Subgroup G) (s t : G)
    (hs : (q s) ^ 2 = 1) (ht : t ^ 2 = 1)
    (ht' : q t ≠ 1) (hst : q s ≠ q t)
    (h₆ : ∃ a : G, V.map (MulAut.conj a).toMonoidHom ≤ Subgroup.zpowers s)
    (h₂ : ∃ b : G, V.map (MulAut.conj b).toMonoidHom ≤ Subgroup.zpowers t) :
    V = ⊥ := by
  obtain ⟨a, ha⟩ := h₆
  obtain ⟨b, hb⟩ := h₂
  apply le_antisymm _ bot_le
  intro x hx
  have hxs := ha (Subgroup.mem_map_of_mem _ hx)
  have hxt := hb (Subgroup.mem_map_of_mem _ hx)
  change a * x * a⁻¹ ∈ Subgroup.zpowers s at hxs
  change b * x * b⁻¹ ∈ Subgroup.zpowers t at hxt
  have qconj (v y : G) : q (v * y * v⁻¹) = q y := by simp
  have hq : q x ∈ Subgroup.zpowers (q s) := by
    obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp hxs
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk, qconj]⟩
  rcases one_or_generator ht hxt with h | h
  · change x = 1
    have h' := congrArg (fun y => b⁻¹ * y * b) h
    simpa [mul_assoc] using h'
  · have eq : q x = q t := (qconj b x).symm.trans (congrArg q h)
    rcases one_or_generator hs hq with h | h
    · exact (ht' (eq.symm.trans h)).elim
    · exact (hst (h.symm.trans eq)).elim

/-- One horizontal involution suffices if the quotient cover is unramified at the
vertical prime and detects this horizontal generator. -/
theorem vertical_inertia_eq_bot_of_unramified_quotient (q : G →* W) (V : Subgroup G) (t : G)
    (ht : t ^ 2 = 1) (hdetect : q t ≠ 1) (hunr : V ≤ q.ker)
    (horiz : ∃ b : G, V.map (MulAut.conj b).toMonoidHom ≤ Subgroup.zpowers t) :
    V = ⊥ := by
  obtain ⟨b,hb⟩ := horiz
  apply le_antisymm _ bot_le
  intro x hx
  have hxt := hb (Subgroup.mem_map_of_mem _ hx)
  change b * x * b⁻¹ ∈ Subgroup.zpowers t at hxt
  rcases one_or_generator ht hxt with h | h
  · change x = 1
    simpa [mul_assoc] using congrArg (fun y => b⁻¹ * y * b) h
  · have hqx : q x = 1 := hunr hx
    have hqt := congrArg q h
    simp [hqx] at hqt
    exact (hdetect hqt.symm).elim

end ZInQBlueprint.VerticalInertia

#print axioms ZInQBlueprint.VerticalInertia.distinct_branch_images
#print axioms ZInQBlueprint.VerticalInertia.vertical_inertia_eq_bot

#print axioms ZInQBlueprint.VerticalInertia.vertical_inertia_eq_bot_of_unramified_quotient
