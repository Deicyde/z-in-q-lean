import TwistPoints

/-! Each nonbranch slope has four distinct rational lifts on its signed sextic. -/
namespace ZInQBlueprint.TwistCount
open Finset Sun28.FiveDescent ZInQBlueprint.OriginalHeightCount
open scoped Classical
noncomputable section
set_option maxRecDepth 1800
set_option maxHeartbeats 100000
attribute [local irreducible] D E Sun28.Ordinary.glazerConstant24

private def flip (b : Bool) (v : ℚ) := if b then -v else v

private theorem flip_square (b : Bool) (v : ℚ) : (flip b v)^2=v^2 := by
  cases b <;> simp [flip]

private theorem flip_inj {z : ℚ} (nz:z≠0) {a b : Bool} (h : flip a z=flip b z) : a=b := by
  cases a <;> cases b <;> first | rfl | (simp only [flip,Bool.false_eq_true,ite_false,ite_true] at h; exfalso;apply nz;linarith only [h])

/-- Four-to-one comparison for an arbitrary collection of lifts with a recovery map. -/
theorem four_points (C : ℝ) (point : PointCount C) {d e : ℤ} (sd : Squarefree d)
    (se : Squarefree e) (X : Finset ℚ)
    (lifts : ∀x : ↥X, ∃q : ℚ×ℚ, q.1≠0 ∧ q.2≠0 ∧
      (e:ℚ)*q.2^2=sextic d q.1 ∧ parameter d q.1=(x:ℚ)) :
    4*(X.card:ℝ)≤C*primeCost d e := by
  choose g hg using lifts
  let f (b:(Bool×Bool)×↥X) : ℚ×ℚ := (flip b.1.1 (g b.2).1,flip b.1.2 (g b.2).2)
  have recover (b:(Bool×Bool)×↥X) : parameter d (f b).1=(b.2:ℚ) := by
    simpa only [f,parameter,flip_square] using (hg b.2).2.2.2
  have inj : Function.Injective f := by
    rintro ⟨⟨s,t⟩,x⟩ ⟨⟨u,v⟩,y⟩ eq
    have px : x=y := Subtype.ext ((recover ((s,t),x)).symm.trans
      ((congrArg (fun q:ℚ×ℚ=>parameter d q.1) eq).trans (recover ((u,v),y))))
    subst y
    have h1 : flip s (g x).1=flip u (g x).1 := congrArg Prod.fst eq
    have h2 : flip t (g x).2=flip v (g x).2 := congrArg Prod.snd eq
    rw [flip_inj (hg x).1 h1,flip_inj (hg x).2.1 h2]
  let Y:=univ.image f
  have card : Y.card=4*X.card := by
    change (univ.image f).card=4*X.card
    rw [card_image_of_injective _ inj,card_univ,Fintype.card_prod,Fintype.card_prod,
      Fintype.card_bool,Fintype.card_coe]
  have sol (q : ℚ×ℚ) (hq:q∈Y) : q.1≠0 ∧ q.2≠0 ∧ (e:ℚ)*q.2^2=sextic d q.1 := by
    obtain ⟨⟨⟨s,t⟩,x⟩,_,rfl⟩:=mem_image.mp hq
    obtain ⟨un,vn,eq,_⟩:=hg x
    have nonzero (b : Bool) {v : ℚ} (h : v≠0) : flip b v≠0 := by
      cases b <;> simp [flip,h]
    refine ⟨nonzero s un,nonzero t vn,?_⟩
    change (e:ℚ)*(flip t (g x).2)^2=cubic ((d:ℚ)*(flip s (g x).1)^2)
    simpa only [flip_square,sextic] using eq
  have z:=point d e sd se Y sol
  rw [card,Nat.cast_mul,Nat.cast_ofNat] at z
  exact z

end
end ZInQBlueprint.TwistCount
#print axioms ZInQBlueprint.TwistCount.four_points
