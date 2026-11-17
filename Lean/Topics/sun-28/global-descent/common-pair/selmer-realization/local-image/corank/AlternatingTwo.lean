import KummerGrowth
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace Sun28.Corank
noncomputable section

/-- A lift of a generator modulo two generates any abelian group of bounded
two-power exponent. The proof lifts coefficients one binary digit at a time. -/
theorem cyclic_of_cyclic_mod_two (G : Type*) [AddCommGroup G]
    (bounded : ∃ j : ℕ, ∀ x : G, (2^j : ℕ) • x = 0)
    [cyclic : IsAddCyclic (quotientAt G 2)] : IsAddCyclic G := by
  obtain ⟨j, bound⟩ := bounded
  obtain ⟨c, generator⟩ := cyclic.exists_generator
  let D := (nsmulAddMonoidHom 2 : G →+ G).range
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective (s:=D) c
  have digit (x : G) : ∃ (a : ℤ) (y : G), x = a • g + (2:ℤ) • y := by
    obtain ⟨a,ha⟩ := generator (QuotientAddGroup.mk x)
    have q : (QuotientAddGroup.mk x : G ⧸ D) = QuotientAddGroup.mk (a • g) := by
      simpa only [QuotientAddGroup.mk_zsmul] using ha.symm
    obtain ⟨y,hy⟩ := QuotientAddGroup.eq_iff_sub_mem.mp q
    have e : (2:ℤ) • y = x - a • g := by simpa [two_smul] using hy
    exact ⟨a,y,by rw [e]; abel⟩
  have lift (k : ℕ) : ∀ x : G, ∃ (a : ℤ) (y : G), x = a • g + (2:ℤ)^k • y := by
    induction k with
    | zero => exact fun x => ⟨0,x,by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨a,y,hxy⟩ := ih x
      obtain ⟨b,z,hyz⟩ := digit y
      refine ⟨a+2^k*b,z,?_⟩
      rw [hxy,hyz,smul_add,add_zsmul,pow_succ,mul_smul,mul_smul,add_assoc]
  refine ⟨g,fun x => ?_⟩
  obtain ⟨a,y,h⟩ := lift j x
  have e : (2:ℤ)^j • y = 0 := by exact_mod_cast bound y
  exact ⟨a,by simpa only [e,add_zero] using h.symm⟩

/-- A nondegenerate alternating finite 2-group has either trivial or at
least four elements in its 2-torsion. Nondegeneracy is imposed on the full
group, as in the Cassels pairing on the reduced group. -/
theorem reduced_trivial {G D : Type*} [AddCommGroup G] [Finite G] [AddCommGroup D]
    (bounded : ∃ j : ℕ, ∀ x : G, (2^j : ℕ) • x = 0)
    (pair : G →+ G →+ D) (alt : ∀ x, pair x x=0)
    (nondeg : ∀ x, (∀ y, pair x y = 0) → x=0)
    (few : Nat.card (torsionAt G 2) ≤ 2) : Subsingleton G := by
  have card : Nat.card (quotientAt G 2) ∣ 2 := by
    rw [finite_quotient]
    have pos : 0 < Nat.card (torsionAt G 2) := Nat.card_pos
    have h : Nat.card (torsionAt G 2)=1 ∨ Nat.card (torsionAt G 2)=2 := by omega
    exact (Nat.dvd_prime (by decide : Nat.Prime 2)).mpr h
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : IsAddCyclic (quotientAt G 2) := isAddCyclic_of_card_dvd_prime card
  obtain ⟨g,gen⟩ := (cyclic_of_cyclic_mod_two G bounded).exists_generator
  have gz : g=0 := nondeg g fun y => by
    obtain ⟨a,rfl⟩ := gen y
    simp [map_zsmul,alt]
  refine ⟨fun x y => ?_⟩
  obtain ⟨a,rfl⟩ := gen x
  obtain ⟨b,rfl⟩ := gen y
  simp [gz]

end
end Sun28.Corank

#print axioms Sun28.Corank.cyclic_of_cyclic_mod_two
#print axioms Sun28.Corank.reduced_trivial
