import MixedMordell
import CubicSector

namespace Sun28.HeightCubics
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQBlueprint.TwistDescent Height
open private int_height height_div from ContactHeight
noncomputable section

def mixedChart (r:ThreeRows) (A B:ℤ) := mixedN (left r A B) (right r A B) (baseRow r A B)

def mixedEstimate (N:ℕ) : ℝ :=
  let M:ℝ:=62208*(N:ℝ)^2
  60*Real.log (N:ℝ)+12*M*(Real.log M)^2+33

theorem mixed_height (mordell:SupportedMordell74) (r:ThreeRows) {A B:ℤ}
    (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0) :
    pairLogHeight A B≤ mixedEstimate (mixedChart r A B) := by
  let P:=left r A B
  let Q:=right r A B
  let R:=baseRow r A B
  let N:=mixedChart r A B
  let M:ℝ:=62208*(N:ℝ)^2
  have pn:P≠0:=mul_ne_zero (det_ne r.ib) (off _)
  have qn:Q≠0:=mul_ne_zero (det_ne r.ia.symm) (off _)
  have rn:R≠0:=mul_ne_zero (det_ne r.ab) (off _)
  obtain ⟨a,X,Y,an,cap,sub,ix,iy,curve,rep⟩:=mixed_point pn qn rn
    (minor_identity r.a r.b r.center A B)
  have q:=mordell _ a X Y (fun _ m=>mixed_prime m) an sub ix iy curve
  change ZInQ.ratHeight X≤Real.log (a.natAbs:ℝ)+4*M*(Real.log M)^2 at q
  rw [ZInQ.Mult.ratHeight_eq_logHeight₁] at q
  have yy:=logHeight₁_add_le (X^3) (a:ℚ)
  have weight:(totalWeight ℚ:ℝ)=1:=by rw [NumberField.totalWeight_eq_finrank];simp
  rw [←curve,logHeight₁_pow,logHeight₁_pow,weight,one_mul,int_height an] at yy
  have div:=height_div (Y^2) (a:ℚ)
  rw [int_height an] at div
  have base:=crossRatio_height r.a r.b r.center r.ab r.ia.symm r.ib.symm cop off
  change pairLogHeight A B≤logHeight₁ ((P:ℚ)/R)+32 at base
  rw [rep] at base
  have z:=Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr an:(0:ℝ)<a.natAbs)
    (show (a.natAbs:ℝ)≤(N:ℝ)^12 by exact_mod_cast cap)
  rw [Real.log_pow] at z
  rw [logHeight₁_pow] at div
  change pairLogHeight A B≤60*Real.log (N:ℝ)+12*M*(Real.log M)^2+33
  change _ ≤ _+numberLog a at div
  unfold numberLog at div yy
  push_cast at z yy div
  linarith only [q,yy,div,z,base,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

private theorem compare {N:ℕ} (np:0<N) : mixedEstimate N≤2*estimate N := by
  have nn:(0:ℝ)<N:=by exact_mod_cast np
  unfold mixedEstimate estimate
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ nn.ne'),Real.log_pow]
  push_cast
  linarith only [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]

def MixedCovered (A B:ℤ) : Prop :=
  ∃ r:ThreeRows,mixedEstimate (mixedChart r A B)≤glazerConstant24*(oddProduct A B:ℝ)^24

theorem mixed_of_conductor {A B:ℤ} (r:ThreeRows) (modest:mixedChart r A B≤heightRadical A B^11) :
    MixedCovered A B := by
  have pos:0< mixedChart r A B:=Finset.prod_pos fun _ mem=>(mixed_prime mem).pos
  have h:=(compare pos).trans (mul_le_mul_of_nonneg_left
    (small_estimate pos (Nat.mul_pos pos_cutoff (pos_odd _ _)) modest) (by norm_num))
  have scalar : (2:ℝ)*2^30≤2^810 :=by
    rw [mul_comm,←pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by decide)
  rw [←mul_assoc] at h
  exact ⟨r,(h.trans (mul_le_mul_of_nonneg_right scalar (by positivity))).trans (original_margin A B)⟩

theorem five_height_of_mixed (mordell:SupportedMordell74) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (cover:MixedCovered A B) : target A B := by
  obtain ⟨r,small⟩:=cover
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using (mixed_height mordell r cop off).trans small

def MixedRemaining : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) → glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬HeightRefinement.Sharp.Test i A B b c) → ¬HeightBalance.Covered A B →
    ¬HeightBalance.PairCovered A B → ¬Covered A B → ¬MixedCovered A B → target A B

theorem original_iff_mixed (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants)
    (mordell:SupportedMordell74) : OriginalFiveHeight glazerConstant24 oldCutoff ↔ MixedRemaining := by
  constructor
  · exact fun full A B cop off _ _ _ _ _ _ _=>full A B cop off
  · intro rem
    apply (original_iff_cubics units pell classes formula mordell).mpr
    intro A B cop off s l f c p symm
    by_cases m:MixedCovered A B
    · exact five_height_of_mixed mordell cop off m
    · exact rem A B cop off s l f c p symm m

end
end Sun28.HeightCubics
#print axioms Sun28.HeightCubics.mixed_height
#print axioms Sun28.HeightCubics.mixed_of_conductor
#print axioms Sun28.HeightCubics.five_height_of_mixed
#print axioms Sun28.HeightCubics.original_iff_mixed
