import PrimitiveDouble
import ComparisonChart

namespace EllipticHeight.Primitive
open QuadraticInt

private theorem qcomm (a b : R) : mul a b=mul b a := by
  apply Prod.ext <;> dsimp [mul] <;> grobner

private theorem qassoc (a b c : R) : mul (mul a b) c=mul a (mul b c) := by
  apply Prod.ext <;> dsimp [mul] <;> grobner

private theorem plus_comm (a b : R) : plus a b=plus b a := by
  apply Prod.ext <;> dsimp [plus] <;> omega

private theorem times_one (a : R) : mul a (1,0)=a := by
  apply Prod.ext <;> simp [mul]

private theorem times_zero (a : R) : mul a (0,0)=(0,0) := by
  apply Prod.ext <;> simp [mul]

private theorem coprime_swap {a b : R} (pr : coprime a b) : coprime b a := by
  obtain ⟨u,v,h⟩:=pr
  exact ⟨v,u,(plus_comm ..).trans h⟩

private theorem rescale_numerator {a b c d s t : R}
    (bez : plus (mul a s) (mul b t)=(1,0)) (cross : mul a d=mul c b) :
    c=mul a (plus (mul c s) (mul d t)) := by
  calc
    c = mul c (plus (mul a s) (mul b t)) := by rw [bez,times_one]
    _ = plus (mul a (mul c s)) (mul (mul c b) t) := by
      apply Prod.ext <;> dsimp [plus,mul] <;> grobner
    _ = plus (mul a (mul c s)) (mul (mul a d) t) := by rw [cross]
    _ = mul a (plus (mul c s) (mul d t)) := by
      apply Prod.ext <;> dsimp [plus,mul] <;> grobner

/-- Given both Bézout rows, the factors in the two directions are
cu+dv and as+bt. They are inverse units and scale both coordinates. -/
theorem bezout_scales {a b c d u v s t : R}
    (ab : plus (mul a u) (mul b v)=(1,0)) (cd : plus (mul c s) (mul d t)=(1,0))
    (cross : mul a d=mul c b) :
    let k:=plus (mul c u) (mul d v)
    let l:=plus (mul a s) (mul b t)
    c=mul a k ∧ d=mul b k ∧ a=mul c l ∧ b=mul d l ∧ mul k l=(1,0) := by
  dsimp only
  have flip : mul b c=mul d a := (qcomm b c).trans (cross.symm.trans (qcomm a d))
  have cscale:=rescale_numerator ab cross
  have ascale:=rescale_numerator cd cross.symm
  have dscale:=rescale_numerator ((plus_comm ..).trans ab) flip
  have bscale:=rescale_numerator ((plus_comm ..).trans cd) flip.symm
  rw [plus_comm (mul d v)] at dscale
  rw [plus_comm (mul b t)] at bscale
  refine ⟨cscale,dscale,ascale,bscale,?_⟩
  let k:=plus (mul c u) (mul d v)
  change mul k (plus (mul a s) (mul b t))=(1,0)
  calc
    _ = plus (mul (mul a k) s) (mul (mul b k) t) := by
      generalize k = p
      apply Prod.ext <;> dsimp [mul,plus] <;> grobner
    _ = _ := by rw [←cscale,←dscale,cd]

/-- The two Bézout rows give the two integral quotients, including when a
numerator or denominator is zero. -/
theorem mutual_numerator_divisibility {a b c d : R} (ab : coprime a b) (cd : coprime c d)
    (cross : mul a d=mul c b) : divides a c ∧ divides c a := by
  obtain ⟨u,v,ab⟩:=ab
  obtain ⟨s,t,cd⟩:=cd
  obtain ⟨forth,_,back,_,_⟩:=bezout_scales ab cd cross
  exact ⟨⟨_,forth⟩,⟨_,back⟩⟩

theorem primitive_norm_eq {a b c d : R} (ab : coprime a b) (cd : coprime c d)
    (cross : mul a d=mul c b) : (norm a).natAbs=(norm c).natAbs := by
  obtain ⟨ac,ca⟩:=mutual_numerator_divisibility ab cd cross
  exact Nat.dvd_antisymm (norm_dvd ac) (norm_dvd ca)

/-- A change of primitive representative preserves both local conditions
used for all subsequent homogeneous doublings. -/
theorem state_of_cross {a b c d : R} (state : State a b) (pr : coprime c d)
    (cross : mul a d=mul c b) : State c d := by
  obtain ⟨ab,rb,ad⟩:=state
  have flip : mul b c=mul d a := (qcomm b c).trans (cross.symm.trans (qcomm a d))
  obtain ⟨u,hu⟩:=cancel_denominator (coprime_swap ab) flip.symm
  obtain ⟨r,hr⟩:=rb
  have rd : divides rho d := ⟨mul r u,by rw [hu,hr,qassoc]⟩
  obtain ⟨v,hv⟩:=cancel_denominator pr cross
  obtain ⟨w,t,ht⟩:=ad
  rw [hv,qassoc] at ht
  exact ⟨pr,rd,⟨mul v w,t,ht⟩⟩

theorem fraction_exchange (z b d : PhysicalProjection.Comparison.Q2) :
    PhysicalProjection.Comparison.times (PhysicalProjection.Comparison.times z b) d =
      PhysicalProjection.Comparison.times (PhysicalProjection.Comparison.times z d) b := by
  apply Prod.ext <;> dsimp [PhysicalProjection.Comparison.times] <;> grobner

/-- Infinity supplies the initial even index without requiring a finite signed root. -/
theorem infinity_state {x : R} (pr : coprime x (0,0)) : State x (0,0) := by
  have base : State (1,0) (0,0) :=
    ⟨⟨(1,0),(0,0),by decide⟩,⟨(0,0),by decide⟩,⟨(1,0),(0,0),by decide⟩⟩
  exact state_of_cross base pr ((times_zero _).trans (times_zero _).symm)

theorem infinity_double_norm {x u v : R} (source : coprime x (0,0)) (target : coprime u v)
    (cross : mul (top x (0,0)) v=mul u (bottom x (0,0))) :
    (norm (top x (0,0))).natAbs=(norm u).natAbs :=
  primitive_norm_eq (step (infinity_state source)).1 target cross

/-- Any primitive target already divides the unnormalized numerator. -/
theorem target_divides_raw {x y u v : R} (pr : coprime u v)
    (cross : mul (top x y) v=mul u (bottom x y)) : divides u (top x y) :=
  cancel_denominator pr cross

#print axioms bezout_scales
#print axioms mutual_numerator_divisibility
#print axioms primitive_norm_eq
#print axioms state_of_cross
#print axioms infinity_double_norm
#print axioms target_divides_raw
end EllipticHeight.Primitive
