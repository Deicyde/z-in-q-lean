import SevenDyadic
import SmallPlaceOrbit

namespace Sun28.SeededPartners
open Sun28.SelmerRealization Sun28.SmallImage ZInQ.RouteK.Selmer
noncomputable section

theorem seven_image {a b : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (h : Cover ℚ_[2] 7 a b) : a%2=1 ∧ b%2=1 := by
  obtain ⟨x,y,z,t,prim,e,f⟩ := residue_cover 5 h
  change _=7*t^2 at e
  change _=21*t^2 at f
  have rm (i : ℤ) (hi : Squarefree i) : (i:ZMod 32).val%4≠0 := by
    have h4 : ¬(4:ℤ)∣i := fun d=>(by decide : ¬ IsUnit (2:ℤ)) (hi 2 d)
    have V := ZMod.val_intCast (n:=32) i
    norm_num only [Nat.cast_ofNat] at V
    omega
  obtain ⟨A,B⟩ := seven_table _ _ _ _ _ _ (rm a ha) (rm b hb) prim e f
  have va := ZMod.val_intCast (n:=32) a
  have vb := ZMod.val_intCast (n:=32) b
  norm_num only [Nat.cast_ofNat] at va vb
  omega


/-- Every squarefree ordered label has these necessary local conditions
on every positive twist in the congruence class used by the rank calculation. -/
theorem small_places {l : ℕ} (r : l%12=11) {a b : ℤ}
    (H : (a,b)∈localClasses l) :
    0<a ∧ a%2=1 ∧ b%2=1 ∧ b%3=1 ∧ IsSquare (b:ℚ_[3]) := by
  obtain ⟨ha,hb,arch,loc⟩:=H
  have lp : 0<l := by omega
  have dy : a%2=1 ∧ b%2=1 := by
    rcases (show l%8=3 ∨ l%8=7 by omega) with c|c
    · have eq : (l:ℤ)≡(n:ℤ) [ZMOD 8] := by change (l:ℤ)%8=3; omega
      have sq := isSquare_intCast_div_two_adic (n:=(n:ℤ)) (by decide) eq
      push_cast at sq
      exact dyadic_image ha hb (cover_of_square_quotient lp (by decide) sq (loc 2))
    · have eq : (l:ℤ)≡7 [ZMOD 8] := by change (l:ℤ)%8=7; omega
      have sq := isSquare_intCast_div_two_adic (n:=7) (by decide) eq
      push_cast at sq
      exact seven_image ha hb (cover_of_square_quotient lp (by decide) sq (loc 2))
  have nres : (n:ZMod 3)=2 := by decide
  have lr : (l:ZMod 3)=2 := by
    apply ZMod.val_injective
    change (l:ZMod 3).val=2
    rw [ZMod.val_natCast];omega
  have eq3 : IsSquare ((((l:ℤ)*(n:ℤ):ℤ):ZMod 3)) := by push_cast; rw [lr,nres];exact ⟨1,by decide⟩
  have sq := isSquare_intCast_div_of_residue (p:=3) (by decide) (m:=(l:ℤ)) (n:=(n:ℤ))
    (by omega) (by decide) eq3
  push_cast at sq
  exact ⟨arch_first lp ha.ne_zero hb.ne_zero arch,dy.1,dy.2,
    ternary_image ha hb (cover_of_square_quotient lp (by decide) sq (loc 3))⟩

end
end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.seven_image
#print axioms Sun28.SeededPartners.small_places
