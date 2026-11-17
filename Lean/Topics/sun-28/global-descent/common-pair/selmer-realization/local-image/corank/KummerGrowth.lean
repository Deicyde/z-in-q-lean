import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Sun28.Corank
noncomputable section

abbrev torsionAt (A : Type*) [AddCommGroup A] (m : ℕ) :=
  (nsmulAddMonoidHom m : A →+ A).ker

abbrev quotientAt (A : Type*) [AddCommGroup A] (m : ℕ) :=
  A ⧸ (nsmulAddMonoidHom m : A →+ A).range

theorem exact_count {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (injects : Function.Injective f)
    (onto : Function.Surjective g) (exactness : f.range = g.ker) :
    Nat.card B = Nat.card A * Nat.card C := by
  have e : Nat.card B = Nat.card (B ⧸ g.ker) * Nat.card g.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have hr : Nat.card A = Nat.card f.range := Nat.card_congr (Equiv.ofInjective f injects)
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g onto).toEquiv,
    ←exactness, ←hr, mul_comm] at e
  exact e

theorem finite_quotient (T : Type*) [AddCommGroup T] [Finite T] (m : ℕ) :
    Nat.card (quotientAt T m) = Nat.card (torsionAt T m) := by
  let φ : T →+ T := nsmulAddMonoidHom m
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α:=φ.range))
    ((AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.range).symm.trans h)

theorem split_finitely_generated (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    ∃ (r : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (A ≃+ (Fin r → ℤ) × T) := by
  obtain ⟨r, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  let T := DirectSum ι fun i => ZMod (p i ^ e i)
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have ht : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let coord : (Fin r →₀ ℤ) ≃+ (Fin r → ℤ) :=
    { Finsupp.equivFunOnFinite with map_add' := fun _ _ => rfl }
  exact ⟨r,T,inferInstance,ht,⟨f.trans (coord.prodCongr (AddEquiv.refl T))⟩⟩

/-- The finite Kummer term at any modulus, using an actual free/finite decomposition. -/
theorem quotient_growth {A T : Type} [AddCommGroup A] [AddCommGroup T] [Finite T]
    {r m : ℕ} (f : A ≃+ (Fin r → ℤ) × T) (hm : m≠0) :
    Nat.card (quotientAt A m) = m^r * Nat.card (torsionAt A m) := by
  let L := Fin r → ℤ
  let φ (G : Type) [AddCommGroup G] := (nsmulAddMonoidHom m : G →+ G)
  have image : (φ (L × T)).range = ((φ L).range).prod ((φ T).range) := by
    ext u
    constructor
    · rintro ⟨⟨v,t⟩,rfl⟩
      exact ⟨⟨v,rfl⟩,⟨t,rfl⟩⟩
    · rintro ⟨⟨v,hv⟩,⟨t,ht⟩⟩
      exact ⟨(v,t),Prod.ext hv ht⟩
  have free_zero (x : L) (h : m • x = 0) : x = 0 := by
    apply AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hm
    simpa only [nsmulAddMonoidHom_apply,smul_zero] using h
  let e : torsionAt A m ≃ torsionAt T m :=
    { toFun := fun x => ⟨(f x).2, by
        change m • (f x).2 = 0
        have h := congrArg (fun a => (f a).2) x.property
        simpa only [nsmulAddMonoidHom_apply,map_nsmul,Prod.smul_snd,map_zero,Prod.snd_zero]
          using h⟩
      invFun := fun t => ⟨f.symm (0,t.val), by
        have h : m • t.val = 0 := t.property
        change m • f.symm (0,t.val) = 0
        rw [←map_nsmul]; simp [Prod.smul_mk,h]⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply f.injective
        rw [f.apply_symm_apply]
        refine Prod.ext ?_ rfl
        have h := congrArg (fun a => (f a).1) x.property
        exact (free_zero _ (by simpa only [nsmulAddMonoidHom_apply,map_nsmul,Prod.smul_fst,
          map_zero,Prod.fst_zero] using h)).symm
      right_inv := fun t => by apply Subtype.ext; simp }
  change (φ A).range.index = _
  have transport : (φ A).range.index = (φ (L × T)).range.index := by
    simpa only [φ, AddEquiv.map_range_nsmulAddMonoidHom] using
      (AddSubgroup.index_map_equiv (φ A).range f).symm
  rw [transport,image,AddSubgroup.index_prod, AddSubgroup.index_range_nsmul L m,
    show Module.finrank ℤ L = r by simp [L], Nat.card_congr e]
  exact congrArg (m^r * ·) (finite_quotient T m)

end
end Sun28.Corank

#print axioms Sun28.Corank.exact_count
#print axioms Sun28.Corank.finite_quotient
#print axioms Sun28.Corank.split_finitely_generated
#print axioms Sun28.Corank.quotient_growth
