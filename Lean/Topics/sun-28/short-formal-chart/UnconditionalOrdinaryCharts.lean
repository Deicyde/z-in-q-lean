import ShortFormalChart
import CommonScalarChart

/-! The completed valuation at every finite place above p supplies the residue characteristic. -/
namespace Sun28.ShortFormal
open ZInQ.Mult Sun28.Ordinary Sun28.Scalar Sun28.ScalarTrace Sun28.ScalarHeight
open NumberField IsDedekindDomain WithZero
open scoped NumberField
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem completion_order (w : HeightOneSpectrum (𝓞 K)) :
    completionOrder w=vK (w.adicCompletion K) := order_eq _

theorem residue_char {p : ℕ} [hp : Fact p.Prime] (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal]
    (unram : completionOrder w (p:w.adicCompletion K)=1) : ResidueChar (w.adicCompletion K) p 1 := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,hp.out⟩)
  constructor
  · rw [←completion_order w]
    exact unram
  · intro n nd
    have nz : n≠0 := by rintro rfl; exact nd (dvd_zero p)
    have ho := prime_order_rat v w (q:=(n:ℚ)) (by exact_mod_cast nz)
    rw [name,padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd] at ho
    simp only [map_natCast,Nat.cast_zero,mul_zero,WithTop.coe_zero] at ho
    rw [←completion_order w,←map_natCast (algebraMap K (w.adicCompletion K)),completionOrder_algebraMap]
    exact ho

/-- The full ordinary formal chart requires no geometric or analytic assumption.
The requested implication is proved at every prime of each number field above p. -/
theorem ordinaryFormalChart (p : ℕ) [hp : Fact p.Prime] (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal] :
    OrdinaryFormalChart p w := by
  classical
  let _ : CharZero (w.adicCompletion K) := charZero_of_injective_ringHom (algebraMap K (w.adicCompletion K)).injective
  intro b _ unram integral _
  have h := residue_char w unram
  rw [completion_order w] at integral ⊢
  exact generic_chart h integral

theorem ordinaryCharts (S : Finset ℕ) (K : Type*) [Field K] [NumberField K] : OrdinaryCharts S K := by
  intro p hp _ w hw
  let _ := hw
  exact ordinaryFormalChart p w

end
#print axioms completion_order
#print axioms residue_char
#print axioms ordinaryFormalChart
#print axioms ordinaryCharts
end Sun28.ShortFormal
