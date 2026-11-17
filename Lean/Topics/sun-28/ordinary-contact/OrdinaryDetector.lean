import OrdinaryContact
import MarkedDetector
import PoleEquations
import OrdinaryChart

/-! The ordinary divisibilities from the literal rational pole predicates. -/
open Sun28.Scalar Sun28.ScalarTrace NumberField IsDedekindDomain
open scoped NumberField
namespace Sun28.Ordinary

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

noncomputable def testTrace {ρ : K} (root : ρ^2=2) (σ : K ≃ₐ[ℚ] K)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β A t : ℚ) :=
  ordinaryTrace (detector A t) (fun i => ordinaryTests root σ c h n m β i /
      (algebraMap ℚ K (t-3))^(orderRequired i+1)) orderRequired

noncomputable def poleArgument {ρ : K} (root : ρ^2=2) (σ : K ≃ₐ[ℚ] K)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β A t : ℚ) :=
  detector A t/(testTrace root σ c h n m β A t)^2

/-- Sun's ordinary Lemma 4.2 for an affine marked contact: the only analytic
input is the classical completed formal chart. -/
theorem marked_pole_divides {p : ℕ} [Fact p.Prime] (large : 65<p)
    (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (chart : OrdinaryFormalChart p w) (σ : K ≃ₐ[ℚ] K) (hs : σ≠1)
    (c h : ℤ) (n m : Fin 4 → ℤ) (β t a s : ℚ) (M : Finset ℚ)
    (anchor : ¬(p:ℤ) ∣ c) (hh : h≠0) (hc : h-c≠0)
    (good : ¬p ∣ separation) (unmarked : t ∉ marks) (guard : t ≠ 3) (scale : s≠0)
    (ha : a ∈ marks) (pos : 0<padicValRat p (t-a)) (odd : Odd (padicValRat p (t-a)))
    (multipliers : ∀ μ ∈ M, padicValRat p μ=0)
    (live : testTrace root σ c h n m β (s^2) t ≠ 0)
    (pole : polePredicate M (poleArgument root σ c h n m β (s^2) t)) :
    (p:ℤ)^64 ∣ lucas (n 1) (n 2) (n 3) ∧ (p:ℤ)^16 ∣ (β-n 0).num := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unram := sqrtTwo_unramified root v w name (by omega)
  let u := discreteOrder (w.valuation K)
  have base {q : ℚ} (nq : q≠0) : u (algebraMap ℚ K q)=((padicValRat p q:ℤ):WithTop ℤ) := by
    simpa [u,name,unram] using prime_order_rat v w nq
  let r := detector (s^2) t
  let T := testTrace root σ c h n m β (s^2) t
  let B := poleArgument root σ c h n m β (s^2) t
  obtain ⟨r0,unit,oddR⟩ := detector_contact good unmarked guard scale ha pos odd
  have bn : B≠0 := div_ne_zero r0 (pow_ne_zero 2 live)
  have oval : padicValRat p B=padicValRat p r-2*padicValRat p T := by
    change padicValRat p (r/T^2)=_
    rw [padicValRat.div r0 (pow_ne_zero 2 live),padicValRat.pow]
    norm_num [r,T]
  have bo : Odd (padicValRat p B) := by
    obtain ⟨b,hb⟩ := oddR
    rw [oval]
    exact ⟨b-padicValRat p T,by dsimp [r]; omega⟩
  have bnon := polePredicate_sound (p:=p) (by omega) M multipliers pole bo
  have pB : 0≤u (algebraMap ℚ K B) := by
    rw [base bn]
    exact WithTop.coe_le_coe.mpr bnon
  have uG : u (algebraMap ℚ K (t-3))=0 := by rw [base (sub_ne_zero.mpr guard),unit]; rfl
  exact (ordinary_contact_divides large w root (ordinaryLogarithms_of_chart w chart) σ hs c h n m β r
    (t-3) anchor hh hc oddR (base r0) uG live pB).2

end Sun28.Ordinary
#print axioms Sun28.Ordinary.marked_pole_divides
