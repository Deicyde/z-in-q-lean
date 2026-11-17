import MixedSector

/-! Direct use of the published ordinate inequality in Corollary 7.4. -/
namespace Sun28.HeightCubics.Ordinate
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQBlueprint.TwistDescent Height
open private int_height height_div from ContactHeight
noncomputable section

/-- Both conclusions of von Känel's Corollary 7.4 on Z[1/N] for
a nonzero integer coefficient supported on the chosen finite set. -/
def PublishedCoordinates : Prop :=
  ∀ (S : Finset ℕ) (a : ℤ) (x y : ℚ), (∀ p∈S,p.Prime) → a≠0 →
  a.natAbs.primeFactors⊆S → IsSInteger S x → IsSInteger S y → y^2=x^3+(a:ℚ) →
  let M:ℝ:=62208*(primeProduct S:ℝ)^2
  ZInQ.ratHeight x≤Real.log (a.natAbs:ℝ)+4*M*(Real.log M)^2 ∧
  ZInQ.ratHeight y≤Real.log (a.natAbs:ℝ)+4*M*(Real.log M)^2

theorem supported_abscissa (h:PublishedCoordinates) : SupportedMordell74 :=
  fun S a x y pr an sup ix iy eq=>(h S a x y pr an sup ix iy eq).1

def symmetricBound (N:ℕ) : ℝ :=
  let M:ℝ:=62208*(N:ℝ)^2
  3*Real.log (4*(N:ℝ)^6)+4*M*(Real.log M)^2+34

def mixedBound (N:ℕ) : ℝ :=
  let M:ℝ:=62208*(N:ℝ)^2
  36*Real.log (N:ℝ)+8*M*(Real.log M)^2+32

theorem symmetric_height (published:PublishedCoordinates) (r:ThreeRows) {A B:ℤ}
    (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0) :
    pairLogHeight A B≤ symmetricBound (chartN r A B) := by
  let P:=left r A B
  let Q:=right r A B
  let R:=baseRow r A B
  let N:=chartN r A B
  let M:ℝ:=62208*(N:ℝ)^2
  have pn:P≠0:=mul_ne_zero (det_ne r.ib) (off _)
  have qn:Q≠0:=mul_ne_zero (det_ne r.ia.symm) (off _)
  have rn:R≠0:=mul_ne_zero (det_ne r.ab) (off _)
  obtain ⟨c,X,Y,cn,cap,sub,ix,iy,eq,rep⟩:=mordell_point pn qn rn (minor_identity _ _ _ A B)
  have h:=(published _ (c^2) X Y (fun _ m=>places_prime m) (pow_ne_zero _ cn) sub ix iy (by simpa using eq)).2
  change ZInQ.ratHeight Y≤Real.log ((c^2:ℤ).natAbs:ℝ)+4*M*(Real.log M)^2 at h
  rw [ZInQ.Mult.ratHeight_eq_logHeight₁,Int.natAbs_pow,Nat.cast_pow,Real.log_pow] at h
  have bound:=Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr cn : (0:ℝ)<c.natAbs)
    (show (c.natAbs:ℝ)≤4*(N:ℝ)^6 by exact_mod_cast cap)
  have a:=height_div Y (c:ℚ)
  rw [int_height cn] at a
  have plus:=logHeight₁_add_le (1:ℚ) (Y/(c:ℚ))
  have we:(totalWeight ℚ:ℝ)=1:=by rw [NumberField.totalWeight_eq_finrank];simp
  rw [we,one_mul,logHeight₁_one] at plus
  have div:=height_div (1+Y/(c:ℚ)) 2
  have two:logHeight₁ (2:ℚ)=Real.log 2:=by rw [Rat.logHeight₁_eq_log_max];norm_num
  rw [two] at div
  have base:=crossRatio_height r.a r.b r.center r.ab r.ia.symm r.ib.symm cop off
  change pairLogHeight A B≤logHeight₁ ((P:ℚ)/R)+32 at base
  rw [rep] at base
  change pairLogHeight A B≤3*Real.log (4*(N:ℝ)^6)+4*M*(Real.log M)^2+34
  unfold numberLog at a
  push_cast at h
  linarith only [h,bound,div,plus,a,base,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

theorem mixed_height (published:PublishedCoordinates) (r:ThreeRows) {A B:ℤ}
    (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0) :
    pairLogHeight A B≤ mixedBound (mixedChart r A B) := by
  let P:=left r A B
  let Q:=right r A B
  let R:=baseRow r A B
  let N:=mixedChart r A B
  let M:ℝ:=62208*(N:ℝ)^2
  have pn:P≠0:=mul_ne_zero (det_ne r.ib) (off _)
  have qn:Q≠0:=mul_ne_zero (det_ne r.ia.symm) (off _)
  have rn:R≠0:=mul_ne_zero (det_ne r.ab) (off _)
  obtain ⟨a,X,Y,an,cap,sub,ix,iy,eq,rep⟩:=mixed_point pn qn rn (minor_identity _ _ _ A B)
  have h:=(published _ a X Y (fun _ m=>mixed_prime m) an sub ix iy eq).2
  change ZInQ.ratHeight Y≤Real.log (a.natAbs:ℝ)+4*M*(Real.log M)^2 at h
  rw [ZInQ.Mult.ratHeight_eq_logHeight₁] at h
  have bound:=Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr an : (0:ℝ)<a.natAbs)
    (show (a.natAbs:ℝ)≤(N:ℝ)^12 by exact_mod_cast cap)
  rw [Real.log_pow] at bound
  have div:=height_div (Y^2) (a:ℚ)
  rw [logHeight₁_pow,int_height an] at div
  have base:=crossRatio_height r.a r.b r.center r.ab r.ia.symm r.ib.symm cop off
  change pairLogHeight A B≤logHeight₁ ((P:ℚ)/R)+32 at base
  rw [rep] at base
  change pairLogHeight A B≤36*Real.log (N:ℝ)+8*M*(Real.log M)^2+32
  unfold numberLog at div
  push_cast at bound div
  linarith only [h,bound,div,base]

def Covered (A B:ℤ) : Prop :=
  ∃ r:ThreeRows, min (symmetricBound (chartN r A B)) (mixedBound (mixedChart r A B))≤
    glazerConstant24*(oddProduct A B:ℝ)^24

theorem five_height_of_ordinate (h:PublishedCoordinates) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (cover:Covered A B) : target A B := by
  obtain ⟨r,small⟩:=cover
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using
    (le_min (symmetric_height h r cop off) (mixed_height h r cop off)).trans small

def Remaining : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) → glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬HeightRefinement.Sharp.Test i A B b c) → ¬HeightBalance.Covered A B →
    ¬HeightBalance.PairCovered A B → ¬Covered A B → target A B

theorem original_iff_ordinate (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants)
    (mordell:PublishedCoordinates) : OriginalFiveHeight glazerConstant24 oldCutoff ↔ Remaining := by
  constructor
  · exact fun full A B cop off _ _ _ _ _ _=>full A B cop off
  · intro rem
    apply (original_iff_pairs units pell classes formula).mpr
    intro A B cop off s l f c p
    by_cases good:Covered A B
    · exact five_height_of_ordinate mordell cop off good
    · exact rem A B cop off s l f c p good

end
end Sun28.HeightCubics.Ordinate
#print axioms Sun28.HeightCubics.Ordinate.supported_abscissa
#print axioms Sun28.HeightCubics.Ordinate.symmetric_height
#print axioms Sun28.HeightCubics.Ordinate.mixed_height
#print axioms Sun28.HeightCubics.Ordinate.five_height_of_ordinate
#print axioms Sun28.HeightCubics.Ordinate.original_iff_ordinate
