import MonicBranchMove

/-! The rational equivalence on the complementary affine opens and the finite group
calculation turning branch-point halves into the full fourth torsion. -/
namespace SixContactFour
noncomputable section

theorem branchScale_ne_zero {K : Type*} [Field K] {c b : K} {r : Fin 5 → K}
    (hc : c ≠ 0) (hb : ∀ i, b ≠ r i) : branchScale c b r ≠ 0 :=
  mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hb i)))

/-- The two rational maps are mutually inverse on x≠b and z≠0 and preserve the curve equation. -/
def affineMovingEquiv {K : Type*} [Field K] (c b : K) (r : Fin 5 → K)
    (hc : c ≠ 0) (hb : ∀ i, b ≠ r i) :
    {P : K×K // P.1 ≠ b ∧ P.2^2=c*(P.1-b)*∏ i, (P.1-r i)} ≃
    {P : K×K // P.1 ≠ 0 ∧ P.2^2=∏ i, (P.1-oddRoot c b r i)} := by
  let D := branchScale c b r
  have dn : D ≠ 0 := branchScale_ne_zero hc hb
  let toPoint (x y : K) := (D/(x-b),y/(x-b)^3*D^2)
  let fromPoint (z w : K) := (b+D/z,w*D/z^3)
  have forward (x y : K) (h : x ≠ b) :
      (toPoint x y).2^2 = ∏ i, ((toPoint x y).1-oddRoot c b r i) ↔
        y^2=c*(x-b)*∏ i, (x-r i) := by
    constructor
    · intro H
      have nz := sub_ne_zero.mpr h
      have factor (i : Fin 5) :
          D/(x-b)-oddRoot c b r i = (-oddRoot c b r i)*(x-r i)/(x-b) := by
        dsimp only [D]
        rw [branchScale_eq c b r i]
        field_simp
        ring
      have scaleProd := monic_product c b r hb
      dsimp only [toPoint] at H
      simp_rw [factor] at H
      rw [Finset.prod_div_distrib,Finset.prod_mul_distrib,scaleProd] at H
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at H
      change (y/(x-b)^3*D^2)^2 = c*D^4*(∏ i, (x-r i))/(x-b)^5 at H
      field_simp [nz] at H
      simpa only [mul_comm c (x-b)] using H
    · exact fun hE => monic_quintic c b r h hb hE
  have inv1 (x y : K) (hx : x ≠ b) :
      fromPoint (toPoint x y).1 (toPoint x y).2=(x,y) := by
    have nz := sub_ne_zero.mpr hx
    dsimp [toPoint,fromPoint]
    apply Prod.ext <;> field_simp [dn,nz] ; ring
  have inv2 (z w : K) (hz : z ≠ 0) :
      toPoint (fromPoint z w).1 (fromPoint z w).2=(z,w) := by
    dsimp [toPoint,fromPoint]
    apply Prod.ext <;> field_simp [dn,hz] <;> ring
  have back (z w : K) (hz : z ≠ 0) (he : w^2=∏ i, (z-oddRoot c b r i)) :
      (fromPoint z w).1 ≠ b ∧ (fromPoint z w).2^2 = c*((fromPoint z w).1-b)*∏ i, ((fromPoint z w).1-r i) := by
    have e : (fromPoint z w).1 ≠ b := by
      dsimp [fromPoint]
      exact fun eq => div_ne_zero dn hz (by linear_combination eq)
    refine ⟨e,(forward _ _ e).mp ?_⟩
    simpa only [inv2 _ _ hz] using he
  exact { toFun := fun P => ⟨toPoint P.1.1 P.1.2,div_ne_zero dn (sub_ne_zero.mpr P.2.1),
    (forward _ _ P.2.1).mpr P.2.2⟩,
          invFun := fun P => ⟨fromPoint P.1.1 P.1.2,back _ _ P.2.1 P.2.2⟩,
          left_inv := fun P => Subtype.ext (inv1 _ _ P.2.1),
          right_inv := fun P => Subtype.ext (inv2 _ _ P.2.1) }

/-- Suppose the five branch classes generate the kernel of doubling, the given subgroup
contains one half of each.
Then all fourth-torsion points are rational. -/
theorem four_torsion_in_subgroup {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (B : Fin 5 → G) (span : ∀ x : G, 2 • x=0 → x ∈ AddSubgroup.closure (Set.range B))
    (halves : ∀ i, ∃ q ∈ H, 2 • q = B i)
    {x : G} (hx : 4 • x=0) : x ∈ H := by
  let two : G →+ G := (2:ℕ) • AddMonoidHom.id G
  have two_eq (y : G) : two y=2 • y := rfl
  have h0 : 2 • (2 • x)=0 := by simpa [←mul_nsmul] using hx
  have kerIn : AddSubgroup.closure (Set.range B) ≤ H := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    obtain ⟨q,hq,eq⟩ := halves i
    rw [←eq]
    exact H.nsmul_mem hq 2
  have lifts : AddSubgroup.closure (Set.range B) ≤ H.map two := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    obtain ⟨q,hq,eq⟩ := halves i
    exact ⟨q,hq,(two_eq q).trans eq⟩
  obtain ⟨y,hy,hyx⟩ := lifts (span (2 • x) h0)
  have eq : 2 • y=2 • x := (two_eq y).symm.trans hyx
  have dy : x-y ∈ H := kerIn (span _ (by rw [nsmul_sub,eq,sub_self]))
  simpa only [sub_add_cancel] using H.add_mem dy hy

end
end SixContactFour
#print axioms SixContactFour.affineMovingEquiv
#print axioms SixContactFour.four_torsion_in_subgroup
