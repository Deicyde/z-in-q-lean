import WitnessTests
import IndexSoundness
import CommonScalarChart

/-! Forward soundness from nine rational affine inputs and the polynomial pole predicates. -/
namespace Sun28.Forward
open ZInQ Sun28.WitnessIndices Sun28.Ordinary Sun28.Scalar Sun28.ScalarHeight
open NumberField IsDedekindDomain Height
open scoped NumberField
noncomputable section

def ordinaryCoefficient (E : Finset ℕ) : ℝ := ordinaryConstant (fiveHeightConstant E) (3/2) 10

def scalarCoefficient (E : Finset ℕ) : ℝ :=
  glazerConstant24*(∏ p ∈ extraPrimes oldCutoff E,(p:ℝ))^24

def forwardMultiplier (E : Finset ℕ) : ℕ :=
  Sun28.multiplier (ordinaryCoefficient E) (numeratorConstant (ordinaryCoefficient E)) (scalarCoefficient E)

private theorem ordinary_positive (E : Finset ℕ) : 0≤ordinaryCoefficient E := by
  have one : 1≤fiveHeightConstant E := le_max_left _ _
  unfold ordinaryCoefficient ordinaryConstant
  linarith

private theorem scalar_positive (E : Finset ℕ) : 0 ≤ scalarCoefficient E := by
  unfold scalarCoefficient glazerConstant24
  positivity

/-- The three scales are functions of the four actual points. -/
def pointScale (w : NinePoints) (M : ℕ) (j : Fin 3) : ℚ :=
  scaleRoot (rootProduct w M).re (rootProduct w M).im j

/-- Point conditions used for forward soundness. The coordinates in every test are functions
of the nine input doubles, including the two translated families and the six scalar entries. -/
structure PointCertificate (w : NinePoints) (M : ℕ) (c : ℤ) (x η Γ : ℚ) (D : ℕ)
    (ordinaryMu scalarMu : Finset ℚ) : Prop where
  q_nonzero : w.Q≠0
  h_nonzero : w.H≠0
  base_nonzero : translatedBase w c≠0
  odd_N : RationalOddChart w.N
  odd_T : RationalOddChart w.T
  odd_Z : RationalOddChart w.Z
  scale_guard : ∀ j, (pointScale w M j)^2*η ∉ marks ∧ (pointScale w M j)^2*η≠3 ∧ pointScale w M j≠0
  ordinary : ∀ j, let s := pointScale w M j
    ordinaryAccepted w M c (beta x) (s^2) (s^2*η) ordinaryMu
  scalar : scalarAccepted w M (scalarRadicand (beta x)) Γ D scalarMu

private theorem eta_nonzero {w M c x η Γ D Uo Us} (p : PointCertificate w M c x η Γ D Uo Us) : η≠0 := by
  rintro rfl
  have z := (p.scale_guard 0).1
  rw [mul_zero] at z
  exact z (by simp [marks])

/-- All primes below the cutoff and all prime divisors of the fixed numerical data. -/
def commonCutoff (c : ℤ) (Γ : ℚ) (Uo Us : Finset ℚ) : Finset ℕ :=
  exceptional Γ Us ∪ (Uo.biUnion support ∪ (c.natAbs.primeFactors ∪ separation.primeFactors))

theorem commonCutoff_outside {c : ℤ} (hc : c≠0) (Γ : ℚ) (Uo Us : Finset ℚ) :
    ∀ p : ℕ, p.Prime → p ∉ commonCutoff c Γ Uo Us →
      65<p ∧ ¬(p:ℤ)∣c ∧ ¬p∣separation ∧ ∀ μ∈Uo,padicValRat p μ=0 := by
  intro p prime away
  let : Fact p.Prime := ⟨prime⟩
  have ex : p∉exceptional Γ Us := fun h => away (Finset.mem_union_left _ h)
  have big := (exceptional_outside ex).1
  have right : p ∉ Uo.biUnion support ∪ (c.natAbs.primeFactors ∪ separation.primeFactors) :=
    fun h => away (Finset.mem_union_right _ h)
  have cP : ¬(p:ℤ)∣c := by
    intro dvd
    have d : p ∣ c.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr dvd
    exact right (Finset.mem_union_right _ (Finset.mem_union_left _ (Nat.mem_primeFactors.mpr
      ⟨prime,d,Int.natAbs_ne_zero.mpr hc⟩)))
  have sep : ¬p∣separation := fun d => right (Finset.mem_union_right _ (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨prime,d,by decide⟩)))
  refine ⟨by omega,cP,sep,?_⟩
  intro μ mem
  exact support_unit (fun h => right (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨μ,mem,h⟩)))

/-- The original rational input and its first root point are recovered simultaneously.
All height estimates, odd and nonzero index claims, and the scalar anchor are derived. -/
theorem rational_witness_sound_at_cutoff (A : Fin 9 → AffineInput) (c : ℤ) (x η Γ : ℚ)
    (D : ℕ) (Uo Us : Finset ℚ) (E : Finset ℕ)
    (enlarged : exceptional Γ Us ⊆ E) (gn : Γ≠0)
    (outside : ∀ p : ℕ, p.Prime → p ∉ E → 65<p ∧ ¬(p:ℤ)∣c ∧ ¬p∣separation ∧ ∀ μ∈Uo,padicValRat p μ=0)
    (chart : OrdinaryCharts E K0) (five : OriginalFiveHeight glazerConstant24 oldCutoff)
    (accepted : PointCertificate (nineAffine A).doubles (forwardMultiplier E) c x η Γ D Uo Us) :
    ∃ k : ℤ, x=(k:ℚ) ∧ (nineAffine A).doubles.N=(2*k^2+3) • P := by
  let w := (nineAffine A).doubles
  let M := forwardMultiplier E
  let C := rootProduct w M
  obtain ⟨a,e,_⟩ := extract_indices A c (K:=numeratorConstant (ordinaryCoefficient E))
    (ordinary_positive E) (scalar_positive E)
    accepted.q_nonzero accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  change Consequences w M c a at e
  have coords : coordinateProduct a.n=C := rootProduct_eq e.represented
  have scale : ∀ H : ℝ, 1≤H → (∀ j,logHeight₁ ((scaleRoot C.re C.im j)^2*η)≤H) →
      indexSize a.n ^ 2 ≤ (3/2)*H+10 := by
    rw [←coords]
    exact three_scales a.n e.odd η (eta_nonzero accepted)
  have tests : ∀ j, let s:=scaleRoot C.re C.im j
      testTrace sqrt2_sq conjugation c a.h a.n a.m (2*x^2+3) (s^2) (s^2*η)≠0 ∧
      polePredicate Uo (poleArgument sqrt2_sq conjugation c a.h a.n a.m (2*x^2+3) (s^2) (s^2*η)) :=
    fun j => (ordinaryAccepted_iff e ..).1 (accepted.ordinary j)
  have tree := tree_of_points e _ _ _ _ accepted.scalar
  have ht := scalar_sqrt_height_at_cutoff sqrt2_sq a.h (a.n 1) x Γ D Us E enlarged
    e.h_nonzero gn chart five (scalar_point_guard e) tree
  have hs : logHeight₁ (2*x^2+3) ≤ scalarCoefficient E*Real.sqrt (scalarStep a.n:ℝ) := by
    simpa only [beta,scalarCoefficient,scalarStep,Nat.cast_natAbs,Int.cast_abs] using ht
  obtain ⟨eqn,⟨k,hk⟩⟩ := marked_certificate_sound sqrt2_sq conjugation conjugation_nontrivial c a.h a.n a.m
    x C.re C.im η Uo E (c₁:=3/2) (c₂:=10) (by norm_num) (by norm_num) (scalar_positive E)
    e.h_nonzero e.base_nonzero outside chart accepted.scale_guard tests five scale a.q e.q_nonzero e.z_nonzero
    e.anchor hs
  have idx : a.n 0=2*k^2+3 := by rw [hk] at eqn; exact_mod_cast eqn.symm
  exact ⟨k,hk,(e.represented.root_point 0).symm.trans (congrArg (fun j : ℤ => j • P) idx)⟩

/-- The numerical good-prime conditions follow from one explicit finite exceptional set.
Only the original five-contact estimate and a local formal chart remain as theorem inputs. -/
theorem rational_witness_sound (A : Fin 9 → AffineInput) (c : ℤ) (x η Γ : ℚ)
    (D : ℕ) (Uo Us : Finset ℚ) (cn : c≠0) (gn : Γ≠0)
    (chart : OrdinaryCharts (commonCutoff c Γ Uo Us) K0)
    (five : OriginalFiveHeight glazerConstant24 oldCutoff)
    (accepted : PointCertificate (nineAffine A).doubles (forwardMultiplier (commonCutoff c Γ Uo Us)) c x η Γ D Uo Us) :
    ∃ k : ℤ, x=(k:ℚ) ∧ (nineAffine A).doubles.N=(2*k^2+3) • P :=
  rational_witness_sound_at_cutoff A c x η Γ D Uo Us (commonCutoff c Γ Uo Us)
    (fun _ h => Finset.mem_union_left _ h) gn
    (commonCutoff_outside cn Γ Uo Us) chart five accepted

#print axioms commonCutoff_outside
#print axioms rational_witness_sound_at_cutoff
#print axioms rational_witness_sound
end
end Sun28.Forward
