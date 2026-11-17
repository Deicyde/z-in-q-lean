import Std

namespace OrbitIdentification.Anchor

def form (u v w t : Int) := u^2+6*v^2-2*w^2-3*t^2
private def binary (k a b : Int) := a^2-k*b^2

private theorem binary_mod_two (a b : Int) :
    binary 3 a b % 4 ≠ 3 ∧
    (binary 3 a b % 2 = 0 →
      (a % 2 = 0 ∧ b % 2 = 0) ∨ binary 3 a b % 8 = 6) := by
  have diff : binary 3 a b - binary 3 (a%4) (b%4) =
      8*(2*(a/4)^2 + (a%4)*(a/4) - 6*(b/4)^2 - 3*(b%4)*(b/4)) := by
    have ha : a=4*(a/4)+a%4 := by omega
    have hb : b=4*(b/4)+b%4 := by omega
    unfold binary
    conv => lhs; lhs; rw [ha,hb]
    grobner
  let A : Fin 4 := ⟨(a%4).toNat,by omega⟩
  let B : Fin 4 := ⟨(b%4).toNat,by omega⟩
  have table : ∀ i j : Fin 4,
      binary 3 i.val j.val % 4 ≠ 3 ∧
      (binary 3 i.val j.val % 2 = 0 →
        (i.val%2=0 ∧ j.val%2=0) ∨ binary 3 i.val j.val % 8=6) := by decide +kernel
  have checked := table A B
  have ha : (A.val:Int)=a%4 := by dsimp [A]; omega
  have hb : (B.val:Int)=b%4 := by dsimp [B]; omega
  rw [ha,hb] at checked
  omega

private theorem binary_mod_three (a b : Int) (h : 3 ∣ binary 2 a b) :
    3 ∣ a ∧ 3 ∣ b := by
  have diff : binary 2 a b - binary 2 (a%3) (b%3) =
      3*(3*(a/3)^2 + 2*(a%3)*(a/3) - 6*(b/3)^2 - 4*(b%3)*(b/3)) := by
    have ha : a=3*(a/3)+a%3 := by omega
    have hb : b=3*(b/3)+b%3 := by omega
    unfold binary
    conv => lhs; lhs; rw [ha,hb]
    grobner
  let A : Fin 3 := ⟨(a%3).toNat,by omega⟩
  let B : Fin 3 := ⟨(b%3).toNat,by omega⟩
  have table : ∀ i j : Fin 3, 3 ∣ binary 2 i.val j.val → i.val=0 ∧ j.val=0 := by decide +kernel
  have checked := table A B
  have ha : (A.val:Int)=a%3 := by dsimp [A]; omega
  have hb : (B.val:Int)=b%3 := by dsimp [B]; omega
  rw [ha,hb] at checked
  omega

/-- A value divisible by eight forces the trace coordinate and its partner even. -/
theorem mod_eight {u v w t : Int} (h : 8 ∣ form u v w t) : 2 ∣ u ∧ 2 ∣ t := by
  have eq : form u v w t=binary 3 u t-2*binary 3 w v := by unfold form binary; grobner
  have e := (binary_mod_two u t).2 (by omega)
  have f := (binary_mod_two w v).1
  omega

/-- The quaternary norm has no primitive zero modulo sixteen. -/
theorem mod_sixteen {u v w t : Int} (h : 16 ∣ form u v w t) :
    2 ∣ u ∧ 2 ∣ v ∧ 2 ∣ w ∧ 2 ∣ t := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := mod_eight (u:=u) (v:=v) (w:=w) (t:=t) (by omega)
  have eq : form u v w t=4*binary 3 a b-2*binary 3 w v := by
    rw [ha,hb]; unfold form binary; grobner
  have e := (binary_mod_two w v).2 (by omega)
  have f := (binary_mod_two a b).1
  omega

/-- The quaternary norm has no primitive zero modulo nine. -/
theorem mod_nine {u v w t : Int} (h : 9 ∣ form u v w t) :
    3 ∣ u ∧ 3 ∣ v ∧ 3 ∣ w ∧ 3 ∣ t := by
  have eq : form u v w t=binary 2 u w-3*binary 2 t v := by unfold form binary; grobner
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := binary_mod_three u w (by omega)
  have e : binary 2 u w=9*binary 2 a b := by rw [ha,hb]; unfold binary; grobner
  have f := binary_mod_three t v (by omega)
  omega

/-- Any primitive integral coordinates on the conic have a denominator prime
    to three, with at most one factor two; when it is even, so is the trace. -/
theorem primitive_denominator {u v w t c : Int} (eq : form u v w t= -2*c^2)
    (primitive : ∀ p ∈ [2,3], ¬(p∣u ∧ p∣v ∧ p∣w ∧ p∣t ∧ p∣c)) :
    (2∣c → 2∣t) ∧ ¬4∣c ∧ ¬3∣c := by
  constructor
  · rintro ⟨a,ha⟩
    apply (mod_eight (u:=u) (v:=v) (w:=w) (t:=t) ?_).2
    exact ⟨-a^2,by rw [eq,ha]; grobner⟩
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨hu,hv,hw,ht⟩ := mod_sixteen (u:=u) (v:=v) (w:=w) (t:=t)
      ⟨-2*a^2,by rw [eq,ha]; grobner⟩
    exact primitive 2 (by decide) ⟨hu,hv,hw,ht,by omega⟩
  · rintro ⟨a,ha⟩
    obtain ⟨hu,hv,hw,ht⟩ := mod_nine (u:=u) (v:=v) (w:=w) (t:=t)
      ⟨-2*a^2,by rw [eq,ha]; grobner⟩
    exact primitive 3 (by decide) ⟨hu,hv,hw,ht,by omega⟩

private def scaled (x : Rat) (c : Nat) (a : Int) := x*(c:Rat)=(a:Rat)

private theorem clear_rat (x : Rat) : scaled x x.den x.num := by
  have e:=Rat.num_divInt_den x
  rw [Rat.divInt_eq_div,Rat.intCast_natCast] at e
  have nz : (x.den:Rat)≠0 := fun h=>x.den_nz (Rat.natCast_eq_zero_iff.mp h)
  exact (congrArg (fun q : Rat=>q*(x.den:Rat)) e.symm).trans (Rat.div_mul_cancel nz)

private theorem extend_scale {x : Rat} {c : Nat} (h : x.den∣c) : ∃ a, scaled x c a := by
  obtain ⟨k,rfl⟩:=h
  refine ⟨x.num*(k:Int),?_⟩
  unfold scaled
  rw [Rat.natCast_mul,Rat.intCast_mul,Rat.intCast_natCast,←Rat.mul_assoc,clear_rat]

private theorem least_positive {P : Nat → Prop} (w : ∃ c, P c) :
    ∃ c, P c ∧ ∀ d, P d → c≤d := by
  obtain ⟨c,h⟩:=w
  induction c using Nat.strongRecOn with
  | ind c previous =>
    by_cases earlier : ∃ d, d<c ∧ P d
    · obtain ⟨d,hd,pd⟩:=earlier
      exact previous d hd pd
    · exact ⟨c,h,fun d pd=>by
        by_cases small : d<c
        · exact False.elim (earlier ⟨d,small,pd⟩)
        · omega⟩

private theorem cancel_scale {x : Rat} {c : Nat} {a b d p : Int}
    (sc : scaled x c a) (pc : (c:Int)=p*d) (pa : a=p*b)
    (dp : 0≤d) (pn : (p:Rat)≠0) : scaled x d.toNat b := by
  have hd : (d.toNat:Rat)=(d:Rat) := by
    rw [←Rat.intCast_natCast,Int.toNat_of_nonneg dp]
  obtain ccast := congrArg (fun n : Int=>(n:Rat)) pc
  rw [Rat.intCast_natCast,Rat.intCast_mul] at ccast
  unfold scaled at sc ⊢
  rw [ccast,pa,Rat.intCast_mul] at sc
  rw [hd]
  have e : (p:Rat)*(x*(d:Rat))=(p:Rat)*(b:Rat) := by grobner
  have inv:=Rat.inv_mul_cancel (p:Rat) pn
  have ee:=congrArg (fun x : Rat=>(p:Rat)⁻¹*x) e
  grobner

private theorem den_divides {x : Rat} {c : Nat} {a : Int} (sc : scaled x c a) : x.den∣c := by
  have canonical := clear_rat x
  unfold scaled at sc canonical
  have cross : x.num*(c:Int)=a*(x.den:Int) := by
    apply Rat.intCast_inj.mp
    simp only [Rat.intCast_mul,Rat.intCast_natCast]
    grobner
  have hd : (x.den:Int)∣x.num*(c:Int) := by rw [cross]; apply Int.dvd_mul_left
  have hn:=Int.ofNat_dvd_left.mp hd
  rw [Int.natAbs_mul,Int.natAbs_natCast] at hn
  exact x.reduced.symm.dvd_of_dvd_mul_left hn

/-- In any rational solution of the literal semilocal conic, the reduced
    denominator of the trace coordinate is prime to two and three. -/
theorem rational_conic {u v w t : Rat} (eq : u^2+6*v^2-2*w^2-3*t^2+2=0) :
    ¬ 2∣t.den ∧ ¬ 3∣t.den := by
  let common := fun c : Nat => 0<c ∧ ∃ U V W T : Int,
    scaled u c U ∧ scaled v c V ∧ scaled w c W ∧ scaled t c T
  have first : ∃ c, common c := by
    let c:=(u.den.lcm v.den).lcm (w.den.lcm t.den)
    have l : u.den.lcm v.den∣c := Nat.dvd_lcm_left ..
    have r : w.den.lcm t.den∣c := Nat.dvd_lcm_right ..
    obtain ⟨U,hu⟩:=extend_scale (Nat.dvd_trans (Nat.dvd_lcm_left ..) l)
    obtain ⟨V,hv⟩:=extend_scale (Nat.dvd_trans (Nat.dvd_lcm_right ..) l)
    obtain ⟨W,hw⟩:=extend_scale (Nat.dvd_trans (Nat.dvd_lcm_left ..) r)
    obtain ⟨T,ht⟩:=extend_scale (Nat.dvd_trans (Nat.dvd_lcm_right ..) r)
    exact ⟨c,Nat.lcm_pos (Nat.lcm_pos u.den_pos v.den_pos) (Nat.lcm_pos w.den_pos t.den_pos),
      U,V,W,T,hu,hv,hw,ht⟩
  obtain ⟨c,⟨pos,U,V,W,T,hu,hv,hw,ht⟩,minimal⟩:=least_positive first
  have hom : form U V W T= -2*(c:Int)^2 := by
    apply Rat.intCast_inj.mp
    dsimp [form]
    unfold scaled at hu hv hw ht
    simp only [Rat.intCast_add,Rat.intCast_sub,Rat.intCast_mul,Rat.intCast_pow,Rat.intCast_neg,
      Rat.intCast_natCast,←hu,←hv,←hw,←ht]
    grobner
  have prim (p : Int) (hp : p∈[2,3]) :
      ¬(p∣U ∧ p∣V ∧ p∣W ∧ p∣T ∧ p∣(c:Int)) := by
    rintro ⟨⟨a,ha⟩,⟨b,hb⟩,⟨f,hf⟩,⟨g,hg⟩,⟨d,hd⟩⟩
    have either : p=2 ∨ p=3 := by simpa using hp
    have small : 0<d ∧ d.toNat<c := by rcases either with rfl|rfl <;> omega
    have pn : (p:Rat)≠0 := by rcases either with rfl|rfl <;> decide
    have atD {x : Rat} {A B : Int} (hx : scaled x c A) (pa : A=p*B) :=
      cancel_scale hx hd pa (Int.le_of_lt small.1) pn
    have m:=minimal d.toNat ⟨by omega,a,b,f,g,atD hu ha,atD hv hb,atD hw hf,atD ht hg⟩
    omega
  obtain ⟨even,notFour,notThree⟩:=primitive_denominator hom prim
  have td:=den_divides ht
  constructor
  · intro b
    have ce : 2∣c := Nat.dvd_trans b td
    obtain ⟨d,hd⟩:=ce
    obtain ⟨g,hg⟩:=even (by omega)
    have pc : (c:Int)=2*(d:Int) := by omega
    have tt:=cancel_scale ht pc hg (Int.natCast_nonneg d) (by decide)
    have both:=Nat.dvd_trans b (den_divides tt)
    simp only [Int.toNat_natCast] at both
    omega
  · intro b
    have h:=Nat.dvd_trans b td
    omega

end OrbitIdentification.Anchor

#print axioms OrbitIdentification.Anchor.mod_eight
#print axioms OrbitIdentification.Anchor.mod_sixteen
#print axioms OrbitIdentification.Anchor.mod_nine
#print axioms OrbitIdentification.Anchor.primitive_denominator
#print axioms OrbitIdentification.Anchor.rational_conic
