import SmallCoverResidues
import TernaryCoverTest
import ZInQKernel.RouteK.Selmer.PadicSquare

namespace Sun28.SmallImage
open Sun28.SelmerRealization
noncomputable section

theorem ternary_image {a b : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (h : Cover ℚ_[3] n a b) : b%3=1 ∧ IsSquare (b:ℚ_[3]) := by
  obtain ⟨x,y,z,t,prim,e,f⟩ := residue_cover 3 h
  change _=11*t^2 at e
  change _=6*t^2 at f
  have rm (i : ℤ) (hi : Squarefree i) : (i:ZMod 27).val%9≠0 := by
    have h9 : ¬(9:ℤ)∣i := fun d=>(by decide : ¬ IsUnit (3:ℤ)) (hi 3 d)
    have V := ZMod.val_intCast (n:=27) i
    norm_num only [Nat.cast_ofNat] at V
    omega
  have loc3 := ternary_table _ _ _ _ _ _ (rm a ha) (rm b hb) prim e f
  have V := ZMod.val_intCast (n:=27) b
  norm_num only [Nat.cast_ofNat] at V
  have result : b%3=1 := by omega
  refine ⟨result,ZInQ.RouteK.Selmer.isSquare_intCast_of_residue (p:=3) (by decide) (by omega) ?_⟩
  have v := ZMod.val_intCast (n:=3) b
  norm_num only [Nat.cast_ofNat] at v
  have eq : (b:ZMod 3)=1 := ZMod.val_injective _ (by change (b:ZMod 3).val=1;omega)
  rw [eq]
  exact ⟨1,by norm_num⟩

theorem local_small {a b : ℤ} (h : (a,b) ∈ localClasses n) :
    0<a ∧ a%2=1 ∧ b%2=1 ∧ b%3=1 ∧ IsSquare (b:ℚ_[3]) := by
  obtain ⟨ha,hb,arch,loc⟩:=h
  have d := dyadic_image ha hb (loc 2)
  have s := ternary_image ha hb (loc 3)
  exact ⟨arch_first (by decide : 0<n) ha.ne_zero hb.ne_zero arch,d.1,d.2,s⟩

end
end Sun28.SmallImage
#print axioms Sun28.SmallImage.ternary_image
#print axioms Sun28.SmallImage.local_small
