import CrossResidues

namespace Sun28.QuadricSieve
open Finset Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection Sun28.NormSieve
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section

private theorem norm_zero_inert {p : ℕ} [Fact p.Prime] (hi : p%4=3)
    {a b : ZMod p} (h : a^2+b^2=0) : a=0 ∧ b=0 := by
  have sq : a^2= -b^2 := eq_neg_of_add_eq_zero_left h
  have bz : b=0 := by
    by_contra nz
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' nz sq hi
  exact ⟨by simpa [bz] using sq,bz⟩

theorem inert_membership {p : ℕ} [Fact p.Prime] (hi : p%4=3)
    (κ : ZMod p) (x : Coordinates (ZMod p)) :
    x∈crossSet p κ ↔ x.1=(-1,0) ∧ x.2.1=(1,0) ∧ κ*x.2.2^2=0 := by
  rcases x with ⟨⟨a,b⟩,⟨c,e⟩,w⟩
  constructor
  · intro hx
    obtain ⟨rel,plus,minus⟩:=(mem_filter.mp hx).2
    change a^2+b^2-c^2-e^2=κ*w^2 at rel
    have ab:=norm_zero_inert hi plus
    have ce:=norm_zero_inert hi minus
    change a+1=0 ∧ b=0 at ab
    change c-1=0 ∧ e=0 at ce
    have ha : a= -1 := by linear_combination ab.1
    have hc : c=1 := sub_eq_zero.mp ce.1
    simpa [ha,hc,ab.2,ce.2] using (show κ*w^2=0 by simpa [ha,hc,ab.2,ce.2] using rel.symm)
  · rintro ⟨aPair,bPair,h⟩
    have aa : a= -1 := congrArg Prod.fst aPair
    have bb : b=0 := congrArg Prod.snd aPair
    have cc : c=1 := congrArg Prod.fst bPair
    have ee : e=0 := congrArg Prod.snd bPair
    subst a; subst b; subst c; subst e
    change κ*w^2=0 at h
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_,?_⟩
    · change (-1:ZMod p)^2+0^2-1^2-0^2=κ*w^2
      simpa using h.symm
    · norm_num
    · norm_num

/-- Inert good reduction has exactly the single affine class ((-1,0),(1,0),0). -/
theorem inert_singleton {p : ℕ} [Fact p.Prime] (hi : p%4=3) {κ : ZMod p} (hk : κ≠0) :
    crossSet p κ={((-1,0),(1,0),0)} := by
  ext x
  rw [inert_membership hi,mem_singleton]
  constructor
  · rintro ⟨a,b,w⟩
    have z : x.2.2=0 := (pow_eq_zero_iff (by decide : 2≠0)).mp ((mul_eq_zero.mp w).resolve_left hk)
    exact Prod.ext a (Prod.ext b z)
  · rintro rfl
    simp

theorem inert_card {p : ℕ} [Fact p.Prime] (hi : p%4=3) (κ : ZMod p) :
    (crossSet p κ).card=if κ=0 then p else 1 := by
  by_cases hk : κ=0
  · subst κ
    let f (w : ZMod p) : Coordinates (ZMod p) := ((-1,0),(1,0),w)
    have image : crossSet p 0=univ.image f := by
      ext x
      rw [inert_membership hi]
      constructor
      · rintro ⟨a,b,_⟩
        refine mem_image.mpr ⟨x.2.2,mem_univ _,?_⟩
        exact Prod.ext a.symm (Prod.ext b.symm rfl)
      · rintro hx
        obtain ⟨w,_,rfl⟩:=mem_image.mp hx
        simp [f]
    rw [image,card_image_of_injective _ (fun a b e=>congrArg (fun z : Coordinates (ZMod p)=>z.2.2) e)]
    simp
  · simp [inert_singleton hi hk,hk]

theorem inert_numerical {A : Fin 3→ℚ} {d p : ℕ} {H Y : ℝ} [Fact p.Prime]
    (hi : p%4=3) (a : Candidate A d H Y) (i j : ↥(shifts A))
    (hk : (gap i j : ZMod p)≠0)
    (plus : p∣adjacentNorm (a.gaussian i) true) (minus : p∣adjacentNorm (a.gaussian j) false) :
    (a.u:ZMod p)=1 ∧ (a.v:ZMod p)=0 := by
  have ij : i≠j := fun eq=>by simp [eq,gap] at hk
  have hx:=(cross_record a i j ij plus minus).2.2
  rw [inert_singleton hi hk,mem_singleton] at hx
  have xv := congrArg (fun z : Coordinates (ZMod p)=>z.2.2) hx
  change ((a.v:ℤ):ZMod p)=0 at xv
  have v : (a.v:ZMod p)=0 := by simpa using xv
  have xy := congrArg (fun z : Coordinates (ZMod p)=>z.1) hx
  have g:= congrArg (fun z : ZMod p × ZMod p=>z.1^2+z.2^2) xy
  have n : (gaussianNorm (a.gaussian i):ZMod p)=1 := by
    rw [gaussian_residue]
    simpa [reduction,integerPoint,realResidue,imagResidue] using g
  rw [a.rays.norm i] at n
  have e := congrArg (fun z : ℤ => (z:ZMod p)) (a.values.equation i.val i.property)
  push_cast at e
  exact ⟨by simpa [v] using e.symm.trans n,v⟩

end
end Sun28.QuadricSieve
#print axioms Sun28.QuadricSieve.inert_membership
#print axioms Sun28.QuadricSieve.inert_singleton
#print axioms Sun28.QuadricSieve.inert_card
#print axioms Sun28.QuadricSieve.inert_numerical
