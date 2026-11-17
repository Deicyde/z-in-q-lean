import PhysicalJets

namespace WitnessTransfer
open Lean.Grind FiniteJet IndependentIndices.ChartJets
attribute [local instance] Semiring.natCast Ring.intCast
variable {A : Type} [CommRing A]

private def iterate (t : A) : Nat → A
  | 0 => 0
  | n+1 => t*(1-iterate t n)^2

private theorem iterate_diff (t : A) (n : Nat) :
    ∃ r : A,iterate t (n+1)-iterate t n=t^n*r := by
  induction n with
  | zero => exact ⟨_, by rw [Semiring.pow_zero,Semiring.one_mul]⟩
  | succ n ih =>
    obtain ⟨r,hr⟩:=ih
    refine ⟨r*(iterate t (n+1)+iterate t n-2),?_⟩
    calc
      _=t*(iterate t (n+1)-iterate t n)*(iterate t (n+1)+iterate t n-2) := by
        change t*(1-iterate t (n+1))^2-t*(1-iterate t n)^2=_;grobner
      _=_ := by rw [hr,Semiring.pow_succ];grobner

private theorem fixed_exists (t : A) (N : Nat) (nilp : t^N=0) :
    ∃ w : A,w=t*(1-w)^2 := by
  obtain ⟨r,hr⟩:=iterate_diff t N
  refine ⟨iterate t N,?_⟩
  change t*(1-iterate t N)^2-iterate t N=t^N*r at hr
  rw [nilp] at hr;grobner

private theorem fixed_unique (t a b : A) (ha : a=t*(1-a)^2)
    (hb : b=t*(1-b)^2) (hu : unit (1-t*(a+b-2))) : a=b := by
  apply cancel_unit hu
  have eqn : a-b=t*(1-a)^2-t*(1-b)^2 := (congrArg (fun v:A=>v-b) ha).trans (congrArg (fun v:A=>t*(1-a)^2-v) hb)
  grobner

private theorem product_identity (w t : A) (hw : w=t*(1-w)^2) :
    (1+w)^4*(16*w*(1-w)^2)=t*(2*(1-w^2))^4 := by
  calc
    _=(16*(1+w)^4*(1-w)^2)*w := by grobner
    _=(16*(1+w)^4*(1-w)^2)*(t*(1-w)^2) := congrArg _ hw
    _=_ := by grobner

private theorem candidate (w t d y : A) (hw : w=t*(1-w)^2)
    (hd : (1-6*w+w^2)*d=2*(1-w^2)) (hy : (1+w)^4*y=16*w*(1-w)^2)
    (hu : unit ((1+w)^4)) : y=(t*d^4)*(1-y)^2 := by
  have hgap : (1+w)^4*(1-y)=(1-6*w+w^2)^2 := by
    calc
      _=(1+w)^4-(1+w)^4*y := by grobner
      _=_ := by rw [hy];grobner
  apply cancel_unit hu;apply cancel_unit hu
  calc
    (1+w)^4*((1+w)^4*y)=t*(2*(1-w^2))^4 := by rw [hy,product_identity _ _ hw]
    _=t*(((1-6*w+w^2)*d)^4) := by rw [hd]
    _=t*d^4*(((1-6*w+w^2)^2)^2) := by grobner
    _=(1+w)^4*((1+w)^4*(t*d^4*(1-y)^2)) := by rw [← hgap];grobner

section Integral
variable {K : Type} [CommRing K]

private theorem plug_pow (n) (u a : J K n) (k : Nat) : plug n u (a^k)=(plug n u a)^k := by
  induction k with
  | zero => rw [Semiring.pow_zero,Semiring.pow_zero,← con_one (R:=K) n,plug_con]
  | succ k ih => rw [Semiring.pow_succ,Semiring.pow_succ];exact (plug_times n u _ _).trans (congrArg (fun v=>v*plug n u a) ih)

private theorem plug_sub (n) (u a b : J K n) : plug n u (a-b)=plug n u a-plug n u b := by
  change plug n u (plus n a (scale n (-1) b))=_
  rw [plug_plus,plug_scale];rfl

private theorem q_unit {n} (w : J K (n+1)) (h : w.1=0) : unit ((1+w)^4) := by
  apply unit_from_constant _ _
  intro _;refine ⟨1,?_⟩
  change 1*((_ : J K (n+1))^4 : J K (n+1)).1=1
  simp only [head_pow,head_add,head_one,h];grobner

private theorem s_unit {n} (w : J K (n+1)) (h : w.1=0) : unit (1-6*w+w^2) := by
  apply unit_from_constant _ _
  intro _;refine ⟨1,?_⟩
  change 1*(_+_ : J K (n+1)).1=1
  simp only [head_add,head_mul,head_sub,head_pow,head_one,head_six,h];grobner

/-- The first-coordinate tangent law implies the second one from the implicit
equation for w. -/
theorem derive_double_w {n} (D : K) (w d : J K (n+1))
    (hw : w=con (n+1) D*(X (R:=K) (n+1))^4*(1-w)^2)
    (hd : (1-6*w+w^2)*d=2*(1-w^2)) :
    (1+w)^4*plug (n+1) d w=16*w*(1-w)^2 := by
  let N:=n+1
  let z:J K N:=X N
  let t:=con N D*z^4
  have ht : t.1=0 := by change D*(z^4 : J K N).1=0;rw [head_pow,show z.1=0 from rfl];grobner
  have hw0 : w.1=0 := by
    have h:=congrArg Prod.fst hw
    change w.1=t.1*(_ : J K N).1 at h;rw [ht] at h;grobner
  obtain ⟨inv,hi⟩:=q_unit w hw0
  let y:=inv*(16*w*(1-w)^2)
  have hy : (1+w)^4*y=16*w*(1-w)^2 := by
    change (1+w)^4*(inv*_)=_;rw [← Semiring.mul_assoc,CommSemiring.mul_comm _ inv,hi];grobner
  have eq1 := candidate w t d y hw hd hy ⟨inv,hi⟩
  have eq2 : plug N d w=(t*d^4)*(1-plug N d w)^2 := by
    have h:=congrArg (plug N d) hw
    change plug N d w=plug N d (times N (times N (con N D) (z^4)) ((1-w)^2)) at h
    rw [plug_times,plug_times,plug_con,plug_pow,plug_pow,plug_sub,
        show plug N d z=z*d from plug_X N d,show plug N d (1:J K N)=1 from
          (con_one (R:=K) N) ▸ plug_con N d (1:K)] at h
    calc
      _=con N D*(z*d)^4*(1-plug N d w)^2 := h
      _=(t*d^4)*(1-plug N d w)^2 := by change _=(con N D*z^4*d^4)*_;grobner
  have hu : unit (1-(t*d^4)*(plug N d w+y-2)) := by
    apply unit_from_constant N _
    intro _;refine ⟨1,?_⟩
    change 1*(_-_ : J K N).1=1
    rw [head_sub,head_one,head_mul,head_mul,ht];grobner
  rw [fixed_unique _ _ _ eq2 eq1 hu,hy]

theorem curve_exists (n) (D : K) : ∃ f : CurveData K n,f.D=D := by
  let N:=n+1
  let z:J K N:=X N
  let t:=con N D*z^4
  have hn : t^N=0 := by
    change (con N D*z^4)^N=0
    rw [CommSemiring.mul_pow,pow_power,Nat.mul_comm 4 N,← pow_power,show z^N=0 from X_nil N,
        show (0:J K N)^4=0 from (Semiring.pow_succ _ 3).trans (Semiring.mul_zero _),Semiring.mul_zero]
  obtain ⟨w,hw⟩:=fixed_exists t N hn
  have hw0 : w.1=0 := by
    have h:=congrArg Prod.fst hw
    change w.1=D*(z^4 : J K N).1*(_ : J K N).1 at h
    rw [head_pow,show z.1=0 from rfl] at h;grobner
  obtain ⟨a,ha⟩:=s_unit w hw0
  let d:=a*(2*(1-w^2))
  have hd : (1-6*w+w^2)*d=2*(1-w^2) := by
    change (1-6*w+w^2)*(a*_)=_;rw [← Semiring.mul_assoc,CommSemiring.mul_comm _ a,ha];grobner
  exact ⟨⟨D,w,d,hw,derive_double_w D w d hw hd,hd⟩,rfl⟩

theorem curve_unique {n} (f g : CurveData K n) (sameD : f.D=g.D) :
    f.w=g.w ∧ f.dup=g.dup := by
  let t:J K (n+1):=con (n+1) f.D*(X (R:=K) (n+1))^4
  have ht : t.1=0 := by
    change f.D*((X (R:=K) (n+1))^4:J K (n+1)).1=0
    rw [head_pow,show (X (R:=K) (n+1)).1=0 from rfl];grobner
  have hg : g.w=t*(1-g.w)^2 := by unfold t;rw [sameD];exact g.curve
  have u : unit (1-t*(f.w+g.w-2)) := by
    apply unit_from_constant _ _
    intro _;refine ⟨1,?_⟩
    change 1*(_-_ : J K (n+1)).1=1
    rw [head_sub,head_one,head_mul,ht];grobner
  have w:=fixed_unique t f.w g.w f.curve hg u
  refine ⟨w,cancel_unit (s_unit f.w (w_head f)) ?_⟩
  rw [f.doubleZ,w,g.doubleZ]

/-- The literal rational chart exists uniquely over any integral coefficient
ring in which its integer constant denominator is a unit. -/
theorem integral_chart_exists (c : Parameter) {n} (f : CurveData K n)
    (leading : unit ((c.q.head?.getD 0:Int):K)) :
    ∃ j : J K (n+1), val f.w c.q*j = X (n+1)*val f.w c.a ∧
      ∀ y : J K (n+1),val f.w c.q*y=X (n+1)*val f.w c.a → y=j := by
  have hq : unit (val f.w c.q) := unit_from_constant _ _ (fun _ =>
    show unit (val f.w c.q).1 from (head_poly _ _ (w_head f) c.q) ▸ leading)
  obtain ⟨v,hv⟩:=hq
  let j:=v*(X (n+1)*val f.w c.a)
  have hj : val f.w c.q*j=X (n+1)*val f.w c.a := by
    change val f.w c.q*(v*_)=_;rw [← Semiring.mul_assoc,CommSemiring.mul_comm _ v,hv];grobner
  exact ⟨j,hj,fun y hy => cancel_unit ⟨v,hv⟩ (hy.trans hj.symm)⟩
end Integral

variable {K : Type} [Field K] [IsCharP K 0]

theorem chart_exists (c : Parameter) (f : CurveData K (4*c.k)) :
    ∃ j : J K (4*c.k+1), val f.w c.q*j = X (4*c.k+1)*val f.w c.a ∧
      ∀ y : J K (4*c.k+1),val f.w c.q*y=X (4*c.k+1)*val f.w c.a → y=j :=
  integral_chart_exists c f ⟨_,Field.inv_mul_cancel (chart_q0 c)⟩

#print axioms derive_double_w
#print axioms curve_exists
#print axioms curve_unique
#print axioms integral_chart_exists
#print axioms chart_exists
end WitnessTransfer
