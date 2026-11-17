import PhysicalCurve

namespace WitnessTransfer
open Lean.Grind FiniteJet IndependentIndices.ChartJets
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K] [IsCharP K 0]

/-- At the V1 denominator the actual Padé and short parameters have equal
jets through degree 12. -/
theorem mixed_at_thirteen {n : Nat} (order : n=12) (f : CurveData K n)
    (p s : J K (n+1))
    (hp : val f.w pDenom*p=X (n+1)*val f.w pNumer)
    (hs : val f.w [15]*s=X (n+1)*val f.w IndependentIndices.ChartJets.short) : p=s := by
  let z:J K (n+1):=X _
  have q1 : unit (val f.w (Parameter.pade.q)) := by
    apply unit_of_head _ _
    intro _
    change (val f.w _).1≠0
    rw [head_poly _ f.w (w_head f)];exact chart_q0 .pade
  have q2 : unit (val f.w (Parameter.short.q)) := by
    apply unit_of_head _ _
    intro _
    change (val f.w _).1≠0
    rw [head_poly _ f.w (w_head f)];exact chart_q0 .short
  have cube : z*f.w^3=0 := by
    have ref : f.w=z^4*(con (n+1) f.D*(1-f.w)^2) := f.curve.trans (by change con (n+1) f.D*z^4*(1-f.w)^2=_;grobner)
    rw [ref,CommSemiring.mul_pow,pow_power]
    have nilp : z^13=0 := by subst n;exact X_nil 13
    calc _=z^13*(con (n+1) f.D*(1-f.w)^2)^3 := by
            change z*(z^12*_)=_;rw [show (13:Nat)=12+1 from rfl,Semiring.pow_succ];grobner
         _=0 := by rw [nilp];grobner
  have hm := (substitution_orders f.w).2.2.2
  rw [mixed_value] at hm
  have h : z*(val f.w pNumer*15-val f.w IndependentIndices.ChartJets.short*val f.w pDenom)=0 := by
    rw [hm,← Semiring.mul_assoc,cube];grobner
  have scalar : val f.w [15]=15 := by
    simp only [val]
    rw [Ring.intCast_ofNat];grobner
  apply cancel_unit q1
  apply cancel_unit q2
  change val f.w [15]*(val f.w pDenom*p)=val f.w [15]*(val f.w pDenom*s)
  rw [hp,show val f.w [15]*(val f.w pDenom*s)=val f.w pDenom*(val f.w [15]*s) from by grobner,hs,scalar]
  change (15:J K (n+1))*(z*val f.w pNumer)=val f.w pDenom*(z*val f.w IndependentIndices.ChartJets.short)
  have bal {A : Type} [CommRing A] (z a b : A) (h : z*(a-b)=0) : z*a=z*b := by grobner
  calc _=z*(val f.w pNumer*15) := by grobner
       _=z*(val f.w IndependentIndices.ChartJets.short*val f.w pDenom) := bal _ _ _ h
       _=_ := by grobner

#print axioms mixed_at_thirteen
end WitnessTransfer
