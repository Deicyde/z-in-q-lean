import CubicMordell

namespace Sun28.HeightCubics
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightFibres ZInQBlueprint.TwistDescent Height
open private int_height height_div from ContactHeight
noncomputable section

def left (r:ThreeRows) (A B:ℤ) : ℤ := det r.center r.b*oldForm r.a A B
def right (r:ThreeRows) (A B:ℤ) : ℤ := det r.a r.center*oldForm r.b A B
def baseRow (r:ThreeRows) (A B:ℤ) : ℤ := det r.a r.b*oldForm r.center A B

def chartN (r:ThreeRows) (A B:ℤ) := conductor (left r A B) (right r A B) (baseRow r A B)

def estimate (N:ℕ) : ℝ :=
  let M:ℝ:=62208*(N:ℝ)^2
  5*Real.log (4*(N:ℝ)^6)+6*M*(Real.log M)^2+35

/-- The input is the published rational S-integral Mordell estimate, with no
smallness or divisibility assumption on the triple. -/
theorem triple_height (published:SupportedMordell74) (r:ThreeRows) {A B:ℤ}
    (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0) :
    pairLogHeight A B≤estimate (chartN r A B) := by
  let P:=left r A B
  let Q:=right r A B
  let R:=baseRow r A B
  let N:=chartN r A B
  let M:ℝ:=62208*(N:ℝ)^2
  have pn:P≠0:=mul_ne_zero (det_ne r.ib) (off _)
  have qn:Q≠0:=mul_ne_zero (det_ne r.ia.symm) (off _)
  have rn:R≠0:=mul_ne_zero (det_ne r.ab) (off _)
  obtain ⟨c,X,Y,cn,cap,support,ix,iy,curve,frac⟩:=mordell_point pn qn rn
    (minor_identity r.a r.b r.center A B)
  have eqn : Y^2=X^3+((c^2:ℤ):ℚ):=by simpa using curve
  have init:=published (places P Q R) (c^2) X Y (fun _ mem=>places_prime mem) (pow_ne_zero _ cn)
    support ix iy eqn
  change ZInQ.ratHeight X≤Real.log ((c^2:ℤ).natAbs:ℝ)+4*M*(Real.log M)^2 at init
  rw [ZInQ.Mult.ratHeight_eq_logHeight₁,Int.natAbs_pow,Nat.cast_pow,Real.log_pow] at init
  have hc:logHeight₁ (c:ℚ)=Real.log (c.natAbs:ℝ):=int_height cn
  have pos:(0:ℝ)<c.natAbs:=by exact_mod_cast Int.natAbs_pos.mpr cn
  have hcBound:=Real.log_le_log pos (show (c.natAbs:ℝ)≤4*(N:ℝ)^6 by exact_mod_cast cap)
  have we:(totalWeight ℚ:ℝ)=1:=by rw [NumberField.totalWeight_eq_finrank];simp
  have yy:=logHeight₁_add_le (X^3) ((c:ℚ)^2)
  rw [←curve,logHeight₁_pow,logHeight₁_pow,logHeight₁_pow,we,one_mul,hc] at yy
  have u:=height_div Y (c:ℚ)
  have v:=logHeight₁_add_le (1:ℚ) (Y/(c:ℚ))
  rw [logHeight₁_one,we,one_mul] at v
  have z:=height_div (1+Y/(c:ℚ)) 2
  have two:logHeight₁ (2:ℚ)=Real.log 2:=by rw [Rat.logHeight₁_eq_log_max];norm_num
  rw [two] at z
  have hj:=crossRatio_height r.a r.b r.center r.ab r.ia.symm r.ib.symm cop off
  change pairLogHeight A B≤logHeight₁ ((P:ℚ)/R)+32 at hj
  rw [frac] at hj
  change pairLogHeight A B≤5*Real.log (4*(N:ℝ)^6)+6*M*(Real.log M)^2+35
  push_cast at yy init
  linarith only [hj,init,hc,hcBound,yy,u,v,z,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

end
end Sun28.HeightCubics
#print axioms Sun28.HeightCubics.triple_height
