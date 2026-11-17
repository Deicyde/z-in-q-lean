import PhysicalSlope

namespace ProjectionFibres.HeightSupport
open StructuralReduction StructuralReduction.Transfer84 ProjectionFibres.Comparison
open BinaryQuartic ProgressionWitnesses.SingleContact

def exceptional : List Nat := [2,3,5,7,11,13,17,29,37,41,2399]

/-- Primitive homogeneous representatives of 2+1/t, including either sign of t. -/
def mobius (t : Rat) : StructuralHeights.Pair := (2*t.num+(t.den:Int),t.num)

theorem primitive (t : Rat) : StructuralHeights.Primitive (mobius t) := by
  apply Int.gcd_eq_one_iff.mpr
  intro d first second
  have both:=Int.dvd_sub first (Int.dvd_mul_of_dvd_right (b:=2) second)
  have b : d∣(t.den:Int) := by
    change d∣2*t.num+(t.den:Int)-2*t.num at both
    rwa [show 2*t.num+(t.den:Int)-2*t.num=(t.den:Int) by omega] at both
  exact (Int.gcd_eq_one_iff.mp (StructuralHeights.coordinates_primitive t)) d second b

private theorem numerator (t : Rat) : t*((t.den:Int):Rat)=(t.num:Rat) := by
  have ne : (t.den:Rat)≠0 := fun h=>t.den_nz (Rat.natCast_eq_zero_iff.mp h)
  have e:=Rat.num_divInt_den t
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at e
  rw [Rat.intCast_natCast]
  exact (congrArg (fun k:Rat=>k*(t.den:Rat)) e.symm).trans (Rat.div_mul_cancel ne)

theorem represents (t : Rat) (ne : t≠0) : (2+1/t)*((mobius t).2:Rat)=((mobius t).1:Rat) := by
  change (2+1/t)*(t.num:Rat)=((2*t.num+(t.den:Int):Int):Rat)
  simp only [Rat.intCast_add,Rat.intCast_mul,←numerator t]
  have e:=Rat.div_mul_cancel (a:=1) ne
  grobner

/-- The inverse integral fractional linear map changes multiplicative height by at most three. -/
theorem height_change (t : Rat) : IndependentIndices.Assembly.multiplicativeHeight t ≤
    3*max (mobius t).1.natAbs (mobius t).2.natAbs := by
  have triangle:=Int.natAbs_sub_le (2*t.num+(t.den:Int)) (2*t.num)
  rw [show 2*t.num+(t.den:Int)-2*t.num=(t.den:Int) by omega,Int.natAbs_natCast,Int.natAbs_mul] at triangle
  change t.den≤(2*t.num+(t.den:Int)).natAbs+2*t.num.natAbs at triangle
  change max t.num.natAbs t.den≤3*max (2*t.num+(t.den:Int)).natAbs t.num.natAbs
  omega

private theorem prime2399 : Prime 2399 := by
  have small : ∀ d : Fin 49, 2≤d.val → ¬d.val∣2399 := by decide
  refine ⟨by decide,?_⟩
  intro d div
  by_cases one : d=1
  · exact Or.inl one
  right
  obtain ⟨k,eq⟩:=div
  by_cases ko : k=1
  · simpa [ko] using eq.symm
  have dn : d≠0 := by intro h; rw [h,Nat.zero_mul] at eq;contradiction
  have kn : k≠0 := by intro h; rw [h,Nat.mul_zero] at eq;contradiction
  by_cases ld : d<49
  · exact False.elim (small ⟨d,ld⟩ (by change 2≤d;omega) ⟨k,eq⟩)
  by_cases lk : k<49
  · exact False.elim (small ⟨k,lk⟩ (by change 2≤k;omega) ⟨d,by simpa [Nat.mul_comm] using eq⟩)
  have huge:=Nat.mul_le_mul (show 49≤d by omega) (show 49≤k by omega)
  omega

theorem exceptional_units {p : Nat} (hp : Prime p) (away : p∉exceptional) :
    ¬(p:Int)∣210 ∧ ¬(p:Int)∣1952786 ∧ 5≤p ∧ p≠17 := by
  have each (q : Nat) (member : q∈exceptional) (hq : Prime q) : ¬(p:Int)∣(q:Int) := by
    intro d
    rcases hq.2 p (Int.natCast_dvd_natCast.mp d) with e|e
    · have :=hp.1; omega
    · exact away (e ▸ member)
  have n2:=each 2 (by decide) (prime_of_finite (by decide) (by decide))
  have n3:=each 3 (by decide) (prime_of_finite (by decide) (by decide))
  have n5:=each 5 (by decide) (prime_of_finite (by decide) (by decide))
  have n7:=each 7 (by decide) (prime_of_finite (by decide) (by decide))
  have n11:=each 11 (by decide) (prime_of_finite (by decide) (by decide))
  have n37:=each 37 (by decide) (prime_of_finite (by decide) (by decide))
  have n2399:=each 2399 (by decide) prime2399
  have neq2 : p≠2 := fun h=>away (h ▸ (by decide))
  have neq3 : p≠3 := fun h=>away (h ▸ (by decide))
  have neq4 : p≠4 := by intro e;have h:=hp.2 2 (e ▸ (by decide)); omega
  refine ⟨?_,?_,by have :=hp.1;omega,fun h=>away (h ▸ (by decide))⟩
  · rw [show (210:Int)=2*3*5*7 by decide]
    intro div
    simp only [StructuralHeights.prime_dvd_mul hp] at div
    rcases div with ((z|z)|z)|z
    · exact n2 z
    · exact n3 z
    · exact n5 z
    · exact n7 z
  · rw [show (1952786:Int)=2*11*37*2399 by decide]
    intro div
    simp only [StructuralHeights.prime_dvd_mul hp] at div
    rcases div with ((z|z)|z)|z
    · exact n2 z
    · exact n11 z
    · exact n37 z
    · exact n2399 z

private theorem denominator {p : Nat} (hp : Prime p) (constant : ¬(p:Int)∣1952786) (t : Rat)
    (odd : StructuralHeights.OddOrder p (StructuralHeights.quintic (mobius t).1 (mobius t).2)) :
    ¬(p:Int)∣(t.den:Int) := by
  intro den
  let a:=t.num
  let b:=(t.den:Int)
  let e:= -3081901*a^4-1205412*a^3*b-76265*a^2*b^2+32*a*b^3
  have eq : StructuralHeights.quintic (mobius t).1 (mobius t).2=(-1952786)*a^5+b*e := by
    unfold StructuralHeights.quintic;dsimp only [mobius,a,b,e];grobner
  have div:=StructuralHeights.odd_dvd odd
  rw [eq] at div
  have lead : (p:Int)∣(-1952786)*a^5 := (Int.dvd_add_left (Int.dvd_mul_of_dvd_left den)).mp div
  have minus : ¬(p:Int)∣-1952786 := by simpa only [Int.dvd_neg] using constant
  have num:=StructuralHeights.prime_dvd_base hp 5 (((StructuralHeights.prime_dvd_mul hp).mp lead).resolve_left minus)
  have one:=(Int.gcd_eq_one_iff.mp (StructuralHeights.coordinates_primitive t)) _ num den
  have := Nat.eq_one_of_dvd_one (Int.ofNat_dvd_left.mp one)
  have :=hp.1
  omega

theorem oddValue {p : Nat} (hp : Prime p) {a : Int} (h : StructuralHeights.OddOrder p a) :
    (a:Rat)≠0 ∧ OddOrder (order p (a:Rat)) := by
  obtain ⟨k,u,eq,unit⟩:=h
  have base : (p:Rat)≠0 := fun e=>by have z:=Rat.natCast_eq_zero_iff.mp e;have :=hp.1;omega
  have un : (u:Rat)≠0 := fun e=>unit ((Rat.intCast_eq_zero_iff.mp e) ▸ Int.dvd_zero _)
  have pow:=power_order (primeOrder p hp) base (2*k+1)
  have prod:=(primeOrder p hp).mul _ _ pow.1 un
  change order p ((p:Rat)^(2*k+1)*(u:Rat))=order p ((p:Rat)^(2*k+1))+order p (u:Rat) at prod
  have e : order p ((p:Rat)^(2*k+1))=((2*k+1:Nat):Int)*order p (p:Rat) := pow.2
  rw [eq,Rat.intCast_mul,Rat.intCast_pow,Rat.intCast_natCast]
  refine ⟨fun z=>(Rat.mul_eq_zero.mp z).elim pow.1 un,⟨(k:Int),?_⟩⟩
  rw [prod,e,order_prime hp,order_int_unit hp unit]
  omega

private theorem homogenize (t s delta R : Rat) (binding : R*(1952786*s^10*delta^6)=P t) :
    let b:=(t.den:Int)
    let z:=(b:Rat)^2*s^5*delta^3
    R*z^2*((-1952786*b:Int):Rat)=((StructuralHeights.quintic (mobius t).1 (mobius t).2):Rat) := by
  dsimp only
  have n:=numerator t
  have polynomial : (P t)*(((t.den:Int):Rat)^5)=
      -((StructuralHeights.quintic (mobius t).1 (mobius t).2):Rat) := by
    unfold StructuralHeights.quintic P;dsimp only [mobius]
    simp only [Rat.intCast_mul,Rat.intCast_add,Rat.intCast_sub,←n]
    grobner
  rw [←binding] at polynomial
  rw [Rat.intCast_mul]
  grobner

/-- The ordinary primitive five-mark contact by itself supplies both numerical
valuation hypotheses in each literal comparison frame. -/
theorem physical_contact (x : Fin 84→Rat) (f : Frame) (dom : domain x) {p : Nat}
    (hp : Prime p) (away : p∉exceptional) (hit : StructuralHeights.Contact p (mobius (slope x f))) :
    OddOrder (order p (f.data x).R) ∧ 0≤order p (f.data x).delta := by
  obtain ⟨good,const,_,_⟩:=exceptional_units hp away
  let t:=slope x f
  let b:=(t.den:Int)
  let z:=(b:Rat)^2*(scaleRoot x f)^5*(f.data x).delta^3
  let Q:=StructuralHeights.quintic (mobius t).1 (mobius t).2
  have odd : StructuralHeights.OddOrder p Q := (StructuralHeights.contact_iff_quintic hp good _ (primitive t)).mp hit
  have den : ¬(p:Int)∣b := denominator hp const t odd
  have cn : ¬(p:Int)∣(-1952786*b) := fun e=>((StructuralHeights.prime_dvd_mul hp).mp e).elim
        (fun d=>const (Int.dvd_neg.mp d)) den
  have c0 : ((-1952786*b:Int):Rat)≠0 := fun d=>cn ((Rat.intCast_eq_zero_iff.mp d) ▸ Int.dvd_zero _)
  obtain ⟨eq,_,binding⟩:=physical x f dom
  have product : (f.data x).R*z^2*((-1952786*b:Int):Rat)=(Q:Rat) :=
    homogenize t (scaleRoot x f) (f.data x).delta (f.data x).R binding
  obtain ⟨qn,⟨k,qval⟩⟩:=oddValue hp odd
  have prv : (f.data x).R*z^2≠0 := fun e=>qn (by rw [←product,e,Rat.zero_mul])
  have zn : z≠0 := fun e=>prv (by rw [e,show (0:Rat)^2=0 by decide,Rat.mul_zero])
  have rr :=(actualDetector x dom f).1
  have dd :=(actualDetector x dom f).2.1
  let v:=primeOrder p hp
  obtain ⟨z2,vz⟩:=power_order v zn 2
  have uv:=v.mul _ _ prv c0
  have rv:=v.mul _ _ rr z2
  change order p ((f.data x).R*z^2*((-1952786*b:Int):Rat))=
       order p ((f.data x).R*z^2)+order p ((-1952786*b:Int):Rat) at uv
  rw [product,order_int_unit hp cn] at uv
  change order p ((f.data x).R*z^2)=order p (f.data x).R+order p (z^2) at rv
  change order p (z^2)=(2:Int)*order p z at vz
  refine ⟨⟨k-order p z,by change order p (f.data x).R=2*(k-order p z)+1;omega⟩,?_⟩
  have bn : (b:Rat)≠0 := fun d=>den ((Rat.intCast_eq_zero_iff.mp d) ▸ Int.dvd_zero _)
  have digits:=numerator t
  have deq : (f.data x).delta*(b:Rat)=((t.num-b:Int):Rat) := by
    rw [eq,Rat.intCast_sub];change (t-1)*(b:Rat)=_;change t*(b:Rat)=(t.num:Rat) at digits;grobner
  have deltaMul:=v.mul _ _ dd bn
  change order p ((f.data x).delta*(b:Rat))=order p (f.data x).delta+order p (b:Rat) at deltaMul
  rw [deq,order_int hp,order_int_unit hp den] at deltaMul
  omega

end ProjectionFibres.HeightSupport
