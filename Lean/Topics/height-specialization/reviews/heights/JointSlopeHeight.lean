import RationalScaleHeight

namespace HeightSpecialization
open IndependentIndices.Assembly

/-- Maximum absolute primitive integral coordinate of the point [1:a:b]. -/
def jointHeight (a b : Rat) : Nat :=
  let d := Nat.lcm a.den b.den
  max d (max (d/a.den*a.num.natAbs) (d/b.den*b.num.natAbs))

private theorem den_product_dvd (x y : Rat) : (x*y).den ∣ x.den*y.den := by
  obtain ⟨g,_,_,h⟩ := Rat.normalize_num_den' (x.num*y.num) (x.den*y.den)
    (Nat.mul_ne_zero x.den_nz y.den_nz)
  rw [← Rat.mul_def] at h
  exact ⟨g,h⟩

private theorem product_cross (x y : Rat) :
    x.num.natAbs*y.num.natAbs*(x*y).den=(x*y).num.natAbs*x.den*y.den := by
  obtain ⟨g,_,en,ed⟩ := Rat.normalize_num_den' (x.num*y.num) (x.den*y.den)
    (Nat.mul_ne_zero x.den_nz y.den_nz)
  rw [← Rat.mul_def] at en ed
  have h := congrArg Int.natAbs en
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at h
  rw [h, Nat.mul_assoc (x*y).num.natAbs x.den y.den, ed]
  grobner

private theorem one_add_square_den (b : Rat) : (1+b^2).den=b.den^2 := by
  have sub (t : Rat) : ((1:Rat)-t).den=t.den := by
    change (Rat.sub (1:Rat) t).den=t.den
    simp [Rat.sub]
  have h : (1:Rat)-(-(b^2))=1+b^2 := by grobner
  rw [← h,sub]
  rfl

private theorem coordinate_bound {a e d D N : Nat} (pos : 0<D) (divides : e∣d)
    (scale : d^4≤D) (cross : a^4*D≤e^4*N) : (d/e*a)^4≤N := by
  apply Nat.le_of_mul_le_mul_right (c:=D) _ pos
  calc
    (d/e*a)^4*D = (d/e)^4*(a^4*D) := by grobner
    _ ≤ (d/e)^4*(e^4*N) := Nat.mul_le_mul_left _ cross
    _ = d^4*N := by rw [←Nat.mul_assoc,←Nat.mul_pow,Nat.div_mul_cancel divides]
    _ ≤ D*N := Nat.mul_le_mul_right N scale
    _ = N*D := Nat.mul_comm ..

private theorem five {p q r s t X Y L : Nat} (hp : p≤X) (hq : q≤X) (hr : r≤Y)
    (hs : s≤L) (ht : t≤L) : p*q*r*s*t≤X^2*Y*L^2 := by
  calc
    _ ≤ X*X*Y*L*L := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp hq) hr) hs) ht
    _ = _ := by grobner

/-- Explicit weighted form of the simultaneous height estimate. -/
theorem weighted_joint_scale_height {l a b : Rat} (live : l≠0) :
    (jointHeight a b)^4≤(H l)^2*(H (a^2*l))^2*H ((1+b^2)^2*l) := by
  let x := a^2*l
  let y := (1+b^2)^2*l
  let d := Nat.lcm a.den b.den
  let D := x.den^2*y.den*l.num.natAbs^2
  let X := x.num.natAbs^2*y.den*l.den^2
  let Y := x.den^2*y.num.natAbs*l.num.natAbs*l.den
  have ln : l.num≠0 := fun h => live (Rat.num_eq_zero.mp h)
  have lp : 0<l.num.natAbs := Int.natAbs_pos.mpr ln
  have pos : 0<D := Nat.mul_pos (Nat.mul_pos (Nat.pow_pos x.den_pos) y.den_pos) (Nat.pow_pos lp)
  have clear (t : Rat) : t.den ∣ (t*l).den*l.num.natAbs := by
    have h := den_product_dvd (t*l) l⁻¹
    rw [←Rat.div_def, Rat.mul_div_cancel live, Rat.den_inv, if_neg ln] at h
    exact h
  have da : a.den^2 ∣ x.den*l.num.natAbs := by simpa only [Rat.den_pow] using clear (a^2)
  have db : b.den^4 ∣ y.den*l.num.natAbs := by
    have h := clear ((1+b^2)^2)
    change ((1+b^2)^2).den ∣ y.den*l.num.natAbs at h
    rw [Rat.den_pow,one_add_square_den,←Nat.pow_mul] at h
    exact h
  have da4 : a.den^4∣D := by
    obtain ⟨k,hk⟩ := da
    refine ⟨k^2*y.den,?_⟩
    calc
      D = (x.den*l.num.natAbs)^2*y.den := by dsimp [D]; grobner
      _ = _ := by rw [hk]; grobner
  have db4 : b.den^4∣D := by
    obtain ⟨k,hk⟩ := db
    refine ⟨k*x.den^2*l.num.natAbs,?_⟩
    calc
      D = (y.den*l.num.natAbs)*x.den^2*l.num.natAbs := by dsimp [D]; grobner
      _ = _ := by rw [hk]; grobner
  have dc : d^4≤D := Nat.le_of_dvd pos (by
    dsimp [d]; rw [←Nat.pow_lcm_pow]; exact Nat.lcm_dvd da4 db4)
  have hx := product_cross (a^2) l
  change (a^2).num.natAbs*l.num.natAbs*x.den=x.num.natAbs*(a^2).den*l.den at hx
  simp only [Rat.num_pow,Int.natAbs_pow,Rat.den_pow] at hx
  have xc : a.num.natAbs^4*D=a.den^4*X := by
    calc
      _ = (a.num.natAbs^2*l.num.natAbs*x.den)^2*y.den := by dsimp [D]; grobner
      _ = _ := by rw [hx]; dsimp [X]; grobner
  have hy := product_cross ((1+b^2)^2) l
  change ((1+b^2)^2).num.natAbs*l.num.natAbs*y.den=y.num.natAbs*((1+b^2)^2).den*l.den at hy
  simp only [Rat.num_pow,Int.natAbs_pow,one_add_square_num,Int.natAbs_natCast,
    Rat.den_pow,one_add_square_den,←Nat.pow_mul] at hy
  have yc : b.num.natAbs^4*D≤b.den^4*Y := by
    have gap := Nat.pow_le_pow_left (Nat.le_add_left (b.num.natAbs^2) (b.den^2)) 2
    calc
      _ ≤ (b.den^2+b.num.natAbs^2)^2*D :=
        Nat.mul_le_mul_right _ (by simpa only [←Nat.pow_mul] using gap)
      _ = ((b.den^2+b.num.natAbs^2)^2*l.num.natAbs*y.den)*(x.den^2*l.num.natAbs) := by
        dsimp [D]; grobner
      _ = _ := by rw [hy]; dsimp [Y]; grobner
  have cap (t : Rat) : t.num.natAbs≤H t ∧ t.den≤H t := ⟨Nat.le_max_left ..,Nat.le_max_right ..⟩
  obtain ⟨lnum,lden⟩:=cap l
  obtain ⟨xnum,xden⟩:=cap x
  obtain ⟨ynum,yden⟩:=cap y
  let bound:=(H x)^2*H y*(H l)^2
  have dcap : D≤bound := by simpa only [D,bound,Nat.pow_two,Nat.mul_assoc] using five xden xden yden lnum lnum
  have xcap : X≤bound := by simpa only [X,bound,Nat.pow_two,Nat.mul_assoc] using five xnum xnum yden lden lden
  have ycap : Y≤bound := by simpa only [Y,bound,Nat.pow_two,Nat.mul_assoc] using five xden xden ynum lnum lden
  have ac:=Nat.le_trans (coordinate_bound pos (Nat.dvd_lcm_left a.den b.den) dc (Nat.le_of_eq xc)) xcap
  have bc:=Nat.le_trans (coordinate_bound pos (Nat.dvd_lcm_right a.den b.den) dc yc) ycap
  have mx {s t : Nat} (hs : s^4≤bound) (ht : t^4≤bound) : (max s t)^4≤bound := by
    rcases Nat.le_total s t with h|h
    · simpa only [Nat.max_eq_right h] using ht
    · simpa only [Nat.max_eq_left h] using hs
  calc
    _ ≤ bound := mx (Nat.le_trans dc dcap) (mx ac bc)
    _ = (H l)^2*(H x)^2*H y := by dsimp [bound]; grobner

/-- Uniform fifth power when the three input slopes have height at most U. -/
theorem joint_scale_height {l a b : Rat} {U : Nat} (live : l≠0) (base : H l≤U)
    (first : H (a^2*l)≤U) (second : H ((1+b^2)^2*l)≤U) :
    (jointHeight a b)^4≤U^5 := by
  calc
    _ ≤ (H l)^2*(H (a^2*l))^2*H ((1+b^2)^2*l) := weighted_joint_scale_height live
    _ ≤ U^2*U^2*U := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left base 2) (Nat.pow_le_pow_left first 2)) second
    _ = _ := by grobner

private theorem integral_height (n : Nat) (pos : 0<n) : H (n:Rat)=n := by
  simp only [H,multiplicativeHeight,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast]
  exact Nat.max_eq_left pos

/-- The three slope heights and the primitive projective height in a family
attaining the exponent 5/4 asymptotically. -/
theorem joint_sharp_family (q : Nat) (pos : 0<q) :
    let U : Nat := (q^2+1)^2
    let a : Rat := U
    let b := (q:Rat)⁻¹
    let l := a⁻¹
    H l=U ∧ H (a^2*l)=U ∧ H ((1+b^2)^2*l)=q^4 ∧ jointHeight a b=U*q := by
  dsimp only
  let U : Nat := (q^2+1)^2
  have up : 0<U := Nat.pow_pos (by omega)
  have qn : (q:Rat)≠0 := fun h => (Nat.ne_of_gt pos) (Rat.natCast_eq_zero_iff.mp h)
  have un : (U:Rat)≠0 := fun h => (Nat.ne_of_gt up) (Rat.natCast_eq_zero_iff.mp h)
  have quo : (U:Rat)^2*(U:Rat)⁻¹=(U:Rat) := by
    rw [Rat.pow_succ,Rat.pow_one,Rat.mul_assoc,Rat.mul_inv_cancel _ un,Rat.mul_one]
  have raised : (1+((q:Rat)⁻¹)^2)^2*(U:Rat)⁻¹=((q:Rat)⁻¹)^4 := by
    have multiply := Rat.mul_inv_cancel (q:Rat) qn
    have lift := Rat.mul_inv_cancel (U:Rat) un
    have cast : (U:Rat)=((q:Rat)^2+1)^2 := by simp [U]
    rw [cast] at lift
    rw [cast]
    grobner
  have qI : (q:Int)≠0 := by omega
  have bd : ((q:Rat)⁻¹).den=q := by
    simp only [Rat.den_inv,Rat.num_natCast,if_neg qI,Int.natAbs_natCast]
  have bn : ((q:Rat)⁻¹).num.natAbs=1 := by
    simp only [Rat.num_inv,Rat.num_natCast,Rat.den_natCast,Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero qI,Int.natAbs_natCast,Nat.one_mul]
  have qq : q≤q*U := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left q up
  have pq : 1≤q*U := Nat.mul_pos pos up
  have j : jointHeight (U:Rat) (q:Rat)⁻¹=U*q := by
    simp only [jointHeight,Rat.den_natCast,bd,Rat.num_natCast,Int.natAbs_natCast,bn,
      Nat.lcm_one_left,Nat.div_one,Nat.div_self pos,Nat.mul_one,
      Nat.max_eq_left pq,Nat.max_eq_right qq]
    exact Nat.mul_comm ..
  change H (U:Rat)⁻¹=U ∧ H ((U:Rat)^2*(U:Rat)⁻¹)=U ∧
    H ((1+((q:Rat)⁻¹)^2)^2*(U:Rat)⁻¹)=q^4 ∧ jointHeight (U:Rat) (q:Rat)⁻¹=U*q
  rw [quo,raised,height_pow,height_inv _ qn,height_inv _ un,integral_height _ up,integral_height _ pos,j]
  exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms weighted_joint_scale_height
#print axioms joint_scale_height
#print axioms joint_sharp_family
end HeightSpecialization
