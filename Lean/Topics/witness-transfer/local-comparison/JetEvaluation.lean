import IntegralJet

namespace WitnessTransfer
open Lean.Grind FiniteJet IndependentIndices.ChartJets
attribute [local instance] Semiring.natCast Ring.intCast
variable {O : Type} [CommRing O]

/-- Precision spelled as an integral remainder, so no quotient-ring lift is assumed. -/
def Near (z : O) (n : Nat) (v w : O) := ∃ r : O, v=w+z^n*r

private theorem near_refl (z x : O) (n) : Near z n x x := ⟨0,by grobner⟩
private theorem near_trans {z a b c : O} {n} (u : Near z n a b) (v : Near z n b c) :
    Near z n a c := by obtain ⟨r,hr⟩:=u;obtain ⟨s,hs⟩:=v;exact ⟨r+s,by rw [hr,hs];grobner⟩
private theorem near_add {z a b c d : O} {n} (u : Near z n a b) (v : Near z n c d) :
    Near z n (a+c) (b+d) := by obtain ⟨r,hr⟩:=u;obtain ⟨s,hs⟩:=v;exact ⟨r+s,by rw [hr,hs];grobner⟩
private theorem near_mul {z a b c d : O} {n} (u : Near z n a b) (v : Near z n c d) :
    Near z n (a*c) (b*d) := by
  obtain ⟨r,hr⟩:=u;obtain ⟨s,hs⟩:=v
  exact ⟨r*c+b*s,by rw [hr,hs];grobner⟩
private theorem near_succ {z a b : O} {n} (c : O) (u : Near z n a b) :
    Near z (n+1) (c+z*a) (c+z*b) := by
  obtain ⟨r,hr⟩:=u;exact ⟨r,by rw [hr,Semiring.pow_succ];grobner⟩
private theorem near_lower {z a b : O} {n} (u : Near z (n+1) a b) : Near z n a b := by
  obtain ⟨r,hr⟩:=u;exact ⟨z*r,by rw [hr,Semiring.pow_succ];grobner⟩

private theorem horner_plus (z : O) (n) (f g : J O n) :
    horner z n (plus n f g)=horner z n f+horner z n g := by
  induction n with
  | zero => simp only [horner];grobner
  | succ n ih => simp only [plus,horner,ih];grobner

theorem truncation_at (z : O) (n) (f : J O (n+1)) :
    Near z n (horner z (n+1) f) (horner z n (cut n f)) := by
  induction n with
  | zero => exact ⟨horner z 1 f,by rw [Semiring.pow_zero,Semiring.one_mul];change _=0+_;grobner⟩
  | succ n ih => exact near_succ f.1 (ih f.2)

theorem product_at (z : O) (n) (f g : J O n) :
    Near z n (horner z n f*horner z n g) (horner z n (times n f g)) := by
  induction n with
  | zero => exact ⟨0,by change 0*0=0+z^0*0;grobner⟩
  | succ n ih =>
    change Near z (n+1) ((f.1+z*horner z n f.2)*(g.1+z*horner z n g.2))
      (f.1*g.1+z*horner z n (plus n (scale n f.1 g.2) (times n f.2 (cut n g))))
    rw [horner_plus,horner_scale]
    rw [show (f.1+z*horner z n f.2)*(g.1+z*horner z n g.2) =
       f.1*g.1+z*(f.1*horner z n g.2+horner z n f.2*horner z (n+1) g) from by
          change _=f.1*g.1+z*(f.1*horner z n g.2+horner z n f.2*(g.1+z*horner z n g.2));grobner]
    exact near_succ _ (near_add (near_refl _ _ _) (near_trans
      (near_mul (near_refl ..) (truncation_at z n g)) (ih f.2 (cut n g))))

theorem composition_at (z u : O) (n) (m a : J O n) (slope : expands n z u m) :
    Near z n (horner (z*u) n a) (horner z n (plug n m a)) := by
  induction n with
  | zero => exact near_refl ..
  | succ n ih =>
    have low:=near_trans (near_lower slope) (truncation_at z n m)
    change Near z (n+1) (a.1+(z*u)*horner (z*u) n a.2)
      (a.1+z*horner z n (times n (cut n m) (plug n (cut n m) a.2)))
    rw [Semiring.mul_assoc]
    exact near_succ _ (near_trans (near_mul low (ih (cut n m) a.2 low)) (product_at ..))

/-- Taylor evaluations of the chart at the actual group-multiple parameter and
of the multiplier tail at the source suffice for the composed evaluation. -/
theorem composed_expands (z u v : O) (n) (m a : J O n) (multiplier : expands n z u m)
    (chart_at_multiple : expands n (z*u) v a) : expands n z v (plug n m a) := by
  obtain ⟨r,hr⟩:=chart_at_multiple
  have h : Near z n v (horner (z*u) n a) := ⟨u^n*r,by rw [hr,CommSemiring.mul_pow];grobner⟩
  exact near_trans h (composition_at z u n m a multiplier)

/-- Only finite Taylor evaluations at two actual parameters appear. Their
composition is derived in the valuation ring, with no divisions. -/
structure SourceValue (O K : Type) [CommRing O] [Field K] [IsCharP K 0]
    (incl : RingMap O K) (c : Parameter) (b : Int) (z v vb : O) where
  curve : CurveData K (4*c.k)
  m : J O (4*c.k+1)
  chart : J O (4*c.k+1)
  tangent : coeff _ (incl.jet _ m) 0=(b:K)
  interchanges : plug _ curve.dup (X _*incl.jet _ m) = plug _ (incl.jet _ m) (X _*curve.dup)
  physical : val curve.w c.q*(incl.jet _ chart)=X (4*c.k+1)*val curve.w c.a
  multiplierTail : O
  evaluatesMultiplier : expands (4*c.k+1) z multiplierTail m
  atSource : expands (4*c.k+1) z v chart
  atImage : expands (4*c.k+1) (z*multiplierTail) vb chart

theorem SourceValue.absolute {K : Type} [Field K] [IsCharP K 0] {incl : RingMap O K}
    {c b z v vb} (data : SourceValue O K incl c b z v vb) (inj : Function.Injective incl.map) :
    ∃ e : O,vb-(b:O)*v=z^(4*c.k+1)*e :=
  integral_multiple incl inj c data.curve data.m data.chart b z v vb data.tangent
    ((commutes_iff ..).mpr data.interchanges) data.physical data.atSource
    (composed_expands _ _ _ _ _ _ data.evaluatesMultiplier data.atImage)

#print axioms product_at
#print axioms composition_at
#print axioms SourceValue.absolute
end WitnessTransfer
