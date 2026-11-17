import PairMultiplier

namespace Prime23
open Lean.Grind PhysicalProjection.Comparison StructuralReduction
attribute [local instance] Semiring.natCast Ring.intCast
variable {p : Nat} [NeZero p]

theorem prime_zero : Red p (p:Rat) 0 := by
  have e : ((p:Int):Fin p)=0 := (IsCharP.intCast_eq_zero_iff p (p:Int)).mpr (by simp)
  simpa only [Rat.intCast_natCast,e] using redInt (p:=p) (p:Int)

theorem prime_input {q t : Q2} (depth : q=scale ((p:Rat)^2) t) (it : IntegralPair p t) :
    PairRed p q (0,0) ∧ ∃ h, PairRed p h (0,0) ∧ q=scale (p:Rat) h := by
  obtain ⟨r,hr⟩:=it
  have h0 : PairRed p (scale (p:Rat) t) (0,0) := by
    simpa only [scaleR,Semiring.zero_mul] using hr.scale prime_zero
  have e : q=scale (p:Rat) (scale (p:Rat) t) := by
    rw [depth]; apply Prod.ext <;> dsimp [scale] <;> grobner
  have q0 : PairRed p q (0,0) := by
    rw [e]; simpa only [scaleR,Semiring.zero_mul] using h0.scale prime_zero
  exact ⟨q0,_,h0,e⟩

theorem unit_square_2 (u : Fin 2) (k : u≠0) : u*u=1 := by revert u; decide +kernel
theorem unit_square_3 (u : Fin 3) (k : u≠0) : u*u=1 := by revert u; decide +kernel

theorem unit_input (m : Int) (mn : m≠0) (unit : (m:Fin p)*(m:Fin p)=1)
    {q : Q2} (q0 : PairRed p q (0,0)) :
    ∃ h, PairRed p h (0,0) ∧ q=scale (m:Rat) h := by
  have nz : (m:Rat)≠0 := fun e=>mn (Rat.intCast_eq_zero_iff.mp e)
  have inv : Red p (m:Rat)⁻¹ (m:Fin p) := by
    refine ⟨m,m*m,by rw [Ring.intCast_mul,unit],rfl,?_⟩
    rw [Rat.intCast_mul,←Rat.mul_assoc,Rat.inv_mul_cancel _ nz,Rat.one_mul]
  refine ⟨scale (m:Rat)⁻¹ q,?_,?_⟩
  · simpa only [scaleR,Semiring.mul_zero] using q0.scale inv
  · apply Prod.ext <;> dsimp [scale] <;> rw [←Rat.mul_assoc,Rat.mul_inv_cancel _ nz,Rat.one_mul]

theorem normalized_output {q y t u : Q2} {m c : Rat} {r : Residues p}
    (seed : q=scale c t) (tr : PairRed p t r)
    (step : y=times (scale (m^2) q) u) (ur : PairRed p u (1,0)) :
    ∃ v, PairRed p v r ∧ y=scale (m^2*c) v := by
  refine ⟨times t u,?_,?_⟩
  · simpa [mulR,Semiring.mul_one,Semiring.mul_zero,Semiring.zero_mul,
      AddCommMonoid.add_zero,AddCommMonoid.zero_add] using tr.mul ur
  · rw [step,seed]; apply Prod.ext <;> dsimp [scale,times] <;> grobner

theorem preserve_depth {q t y u : Q2} {m : Int} (depth : q=scale ((p:Rat)^2) t)
    (it : IntegralPair p t) (ur : PairRed p u (1,0)) (step : y=times (scale ((m:Rat)^2) q) u) :
    ∃ t', IntegralPair p t' ∧ y=scale ((p:Rat)^2) t' := by
  obtain ⟨r,rt⟩:=it
  obtain ⟨v,vr,ve⟩:=normalized_output depth rt step ur
  have ms : Red p ((m:Rat)^2) ((m:Fin p)*(m:Fin p)) := by
    rw [show (m:Rat)^2=(m:Rat)*(m:Rat) by grobner]
    exact (redInt m).mul (redInt m)
  refine ⟨scale ((m:Rat)^2) v,⟨_,vr.scale ms⟩,?_⟩
  rw [ve]; apply Prod.ext <;> dsimp [scale] <;> grobner

#print axioms prime_input
#print axioms unit_input
#print axioms preserve_depth
end Prime23
