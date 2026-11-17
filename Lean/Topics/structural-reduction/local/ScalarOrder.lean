import SexticOrder

namespace StructuralReduction
open BinaryQuartic ProgressionWitnesses.SingleContact

/-- The evaluated rational scalar, with the actual numerator U and correction one. -/
structure ScalarValues (r u v q U W b : Rat) : Prop where
  live : U ≠ 0
  numerator : U=u^2+v^2/r
  value : W=U/r^32+r*q^2/U
  linked : b*r=W^2

/-- The signed correction row is −w²+κ b₀ r³=0 on coordinate wires w and b₀.
The other scalar wires supply w²=r²W². Only the nonzero contact factor is cancelled. -/
theorem scalar_signed_link {r w W κ b₀ : Rat} (hr : r≠0)
    (wire : w^2=r^2*W^2) (row : -w^2+κ*b₀*r^3=0) : (κ*b₀)*r=W^2 := by
  have e : ((κ*b₀)*r-W^2)*r^2=0 := by grobner
  have r2 : r^2≠0 := by grind
  have h := (Rat.mul_eq_zero.mp e).resolve_right r2
  grobner

private theorem cancel_rat {m a b : Rat} (hm : m≠0) (h : m*a=m*b) : a=b := by grind

/-- Normalize the four physical reciprocal equations by cancelling their nonzero
denominators. D cannot vanish because r q² is nonzero in its own equation. -/
theorem scalar_from_cleared {r u v q L D T W b : Rat} (hr : r≠0) (hq : q≠0)
    (line : r*L=v^2) (first : r^16*D=u^2+L) (second : D*T=D^2+r*q^2)
    (last : r^16*W=T) (linked : b*r=W^2) :
    ScalarValues r u v q (r^16*D) W b := by
  have Dn : D≠0 := by
    intro z
    have e : r*q^2=0 := by rw [z] at second;grobner
    exact hq (by grind [Rat.mul_eq_zero])
  have rn : r^16≠0 := by grind
  have r32 : r^32=r^16*r^16 := by grobner
  have U0 : r^16*D≠0 := by grind [Rat.mul_eq_zero]
  have Lrep := Rat.div_mul_cancel (a:=v^2) hr
  have eqL : L=v^2/r := by
    apply cancel_rat hr
    rw [line,Rat.mul_comm r, Lrep]
  refine ⟨U0,by rwa [←eqL],?_,linked⟩
  have a := Rat.div_mul_cancel (a:=r^16*D) (b:=r^32) (by rw [r32];grind [Rat.mul_eq_zero])
  have z := Rat.div_mul_cancel (a:=r*q^2) U0
  rw [r32] at a
  have nonzero : r^16*(r^16*D) ≠ 0 := by grind [Rat.mul_eq_zero]
  apply cancel_rat nonzero
  rw [r32]
  calc
    (r^16*(r^16*D))*W=(r^16)*((r^16*D)*W) := by grobner
    _=r^16*(D^2+r*q^2) := by rw [←second,←last];grobner
    _=(r^16*(r^16*D))*(r^16*D/(r^16*r^16)+r*q^2/(r^16*D)) := by
      have alg (c d A B g : Rat) (ha : A*(c*c)=c*d) (hb : B*(c*d)=g) :
          c*(d^2+g)=(c*(c*d))*(A+B) := by grobner
      exact alg (r^16) D _ _ _ a z

/-- A zero coordinate has infinite depth. A nonzero coordinate satisfies a strict
inequality in the ordinary integer normalization. -/
def strictDepth (p : Nat) (n m : Int) (x : Rat) := x≠0 → n<m*order p x

private theorem sum_bounds (o : RationalOrder) {a c : Rat}
    (unequal : a≠0 → c≠0 → o.ord a≠o.ord c) :
    (a≠0 → a+c≠0 ∧ o.ord (a+c)≤o.ord a) ∧
    (c≠0 → a+c≠0 ∧ o.ord (a+c)≤o.ord c) := by
  by_cases ha : a=0
  · rw [ha,Rat.zero_add]
    exact ⟨fun h => False.elim (h rfl),fun h => ⟨h,Int.le_refl _⟩⟩
  by_cases hc : c=0
  · rw [hc,Rat.add_zero]
    exact ⟨fun h => ⟨h,Int.le_refl _⟩,fun h => False.elim (h rfl)⟩
  obtain ⟨nz,eq⟩:=o.addUnequal a c ha hc (unequal ha hc)
  rw [eq]
  exact ⟨fun _=>⟨nz,Int.min_le_left ..⟩,fun _=>⟨nz,Int.min_le_right ..⟩⟩

/-- The sextic and the physical value of W force all three sharp scalar depth
inequalities; they are simultaneous and do not require either component u,v to be nonzero. -/
theorem scalar_depths {p : Nat} (hp : Prime p) (large : 5≤p) (away : p≠17)
    {r u v q U W b : Rat} (hr : r≠0) (odd : OddOrder (order p r))
    (values : ScalarValues r u v q U W b) (point : ThreeCoordinates.Sextic (17*b) (289-17*b)) :
    b≠0 ∧ 0<order p b ∧ 2*order p W>order p r ∧
    strictDepth p (16*order p r) 1 q ∧
    strictDepth p (65*order p r) 4 u ∧ strictDepth p (67*order p r) 4 v := by
  let o:=primeOrder p hp
  change OddOrder (o.ord r) at odd
  obtain ⟨j,hj⟩:=odd
  have U0:=values.live
  obtain ⟨r32,pow32⟩:=power_order o hr 32
  let a:=U/r^32
  let c:=r*q^2/U
  have ea : a*r^32=U := Rat.div_mul_cancel r32
  have an : a≠0 := fun z => U0 (by rw [←ea,z,Rat.zero_mul])
  have oa : o.ord a=o.ord U-32*o.ord r := by
    dsimp only [a];rw [o.div _ _ U0 r32,pow32];rfl
  have qc : c≠0 → q≠0 := by intro cn z;apply cn;dsimp [c];rw [z,show (0:Rat)^2=0 by decide,Rat.mul_zero,Rat.div_def,Rat.zero_mul]
  have oc (cn : c≠0) : o.ord c=o.ord r+2*o.ord q-o.ord U := by
    obtain ⟨q2,oq⟩:=power_order o (qc cn) 2
    dsimp only [c];rw [o.div _ _ (by grind [Rat.mul_eq_zero]) U0,o.mul _ _ hr q2,oq];rfl
  have wc := sum_bounds o (a:=a) (c:=c) (fun _ cn=>by have := oc cn;omega)
  have Wrep : W=a+c:=values.value
  rw [←Wrep] at wc
  obtain ⟨W0,upperA⟩:=wc.1 an
  obtain ⟨wn,wo⟩:=power_order o W0 2
  have hb : b≠0 := fun z=>wn (by rw [←values.linked,z,Rat.zero_mul])
  have eqb:=congrArg o.ord values.linked
  rw [o.mul _ _ hb hr,wo] at eqb
  have ob : OddOrder (order p b) := ⟨o.ord W-j-1,by change o.ord b=_;omega⟩
  have positive : 0<o.ord b := good_prime_positive hp large away hb ob point
  have wl : o.ord r<2*o.ord W := by omega
  refine ⟨hb,positive,wl,?_,?_⟩
  · intro qn
    have qsq := (power_order o qn 2).1
    have prod : r*q^2≠0 := by grind [Rat.mul_eq_zero]
    have cn : c≠0 := fun z => prod (by rw [←Rat.div_mul_cancel (a:=r*q^2) U0];change c*U=0;rw [z,Rat.zero_mul])
    have upperC:=(wc.2 cn).2
    have co:=oc cn
    change 16*o.ord r<1*o.ord q
    omega
  · let a₀:=u^2
    let a₁:=v^2/r
    have v0 (nz : a₁≠0) : v≠0 := by intro vz;apply nz;dsimp [a₁];rw [vz,show (0:Rat)^2=0 by decide,Rat.div_def,Rat.zero_mul]
    have ov (nz : a₁≠0) : o.ord a₁=2*o.ord v-o.ord r := by
      obtain ⟨vs,vo⟩:=power_order o (v0 nz) 2
      dsimp [a₁];rw [o.div _ _ vs hr,vo];rfl
    have ou (nz : a₀≠0) : o.ord a₀=2*o.ord u :=
      (power_order o (fun uz=>nz (by dsimp [a₀];rw [uz];decide)) 2).2
    have num:=sum_bounds o (a:=a₀) (c:=a₁) (fun x y=>by have := ou x;have := ov y;omega)
    have rep : U=a₀+a₁:=values.numerator
    rw [←rep] at num
    constructor
    · intro un
      have uz : a₀≠0 := (power_order o un 2).1
      have upper := (num.1 uz).2
      have uord:=ou uz
      change 65*o.ord r<4*o.ord u
      omega
    · intro vn
      obtain ⟨vs,_⟩:=power_order o vn 2
      have vz : a₁≠0 := fun z=>vs (by rw [←Rat.div_mul_cancel (a:=v^2) hr];change a₁*r=0;rw [z,Rat.zero_mul])
      have upper:=(num.2 vz).2
      have vord:=ov vz
      change 67*o.ord r<4*o.ord v
      omega

end StructuralReduction
