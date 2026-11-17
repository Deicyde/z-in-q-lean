import SelectedOrdinaryPoints
import PreparedDetector

/-! Recover the detector order and normalization at each selected prime
directly from the actual five cleared shifts. -/
namespace Sun28.SelectedTrace
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open Sun28.ContactFactors NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

theorem selected_contact_orders {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (one : A 0=1) (vp : 0<v) {j : Fin 3} (nz : A j≠0) {p : ℕ} (hp : p∈selected values j)
    (off : ¬p∣dilation A) (good : ¬p∣separation) (unit : padicValRat p (A j)=0) :
    let t:=argument A u v j
    padicValRat p (detector (A j) t)=1 ∧ t≠3 ∧ padicValRat p (t-3)=0 := by
  let _ := Fact.mk (selected_prime values hp)
  obtain ⟨guard,scale⟩ := selected_unit values one vp nz hp off good unit
  let t:=argument A u v j
  let d:=dilation A*v
  have dn : (d:ℚ)≠0 := by exact_mod_cast (Nat.mul_pos (dilation_positive A) vp).ne'
  obtain ⟨a,ha,e⟩ := Finset.mem_image.mp hp
  have nd : ¬p∣d := e ▸ values.unit_at_denominator one vp (shift_mem A j ha) (e ▸ off)
  have dv : padicValRat p (d:ℚ)=0 := by rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd]; rfl
  have sn : scaleFactor d t≠0 :=
    div_ne_zero one_ne_zero (mul_ne_zero (pow_ne_zero 5 dn) (pow_ne_zero 3 (sub_ne_zero.mpr guard)))
  have order := Sun28.FinitePole.ordinary_order (selected values j) (fun _ h => selected_prime values h)
    (T:=1) sn one_ne_zero (detector_factorization values vp j nz) p
  have exactOrder : padicValRat p (detector (A j) t)=1 := by simpa [d,t,hp,scale] using order
  refine ⟨exactOrder,guard,?_⟩
  change padicValRat p (scaleFactor d t)=0 at scale
  unfold scaleFactor at scale
  rw [padicValRat.div one_ne_zero (mul_ne_zero (pow_ne_zero 5 dn) (pow_ne_zero 3 (sub_ne_zero.mpr guard))),
    padicValRat.mul (pow_ne_zero 5 dn) (pow_ne_zero 3 (sub_ne_zero.mpr guard)),padicValRat.pow,padicValRat.pow,dv] at scale
  norm_num at scale
  exact scale

/-- At an actual selected prime the rational detector and unit data follow
from the cleared shift equations. -/
theorem selected_shift_pole {A : Fin 3→ℚ} {u v : ℕ} (values : PrimeValues A u v)
    (one : A 0=1) (vp : 0<v) {j : Fin 3} (nz : A j≠0) {p : ℕ} [hp : Fact p.Prime]
    (sel : p∈selected values j) (large : 65<p) (off : ¬p∣dilation A) (good : ¬p∣separation)
    (unit : padicValRat p (A j)=0) (w : HeightOneSpectrum (𝓞 K0))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal]
    {points : NinePoints} {M : ℕ} {c q h : ℤ} {n : Fin 4→ℤ}
    (represented : Consequences points M c ⟨q,h,n,fun i=>h*n i⟩)
    (β : ℚ) (root : lucas (n 1) (n 2) (n 3)=0) (firstRoot : β=(n 0:ℚ))
    (plus : h • paperGenerator sqrt2_sq ∈ W1 (discreteOrder (w.valuation K0)) (-(3-sqrt2)^2))
    (minus : (h-c) • paperGenerator sqrt2_sq ∈
      W1 ((discreteOrder (w.valuation K0)).comap conjugation.toRingHom) (-(3-sqrt2)^2)) :
    let t:=argument A u v j
    let T:=ordinaryTraceAt points M c β (A j) t
    T≠0 ∧ padicValRat p T=0 ∧ padicValRat p (detector (A j) t/T^2)=1 := by
  obtain ⟨detect,guard,vu⟩ := selected_contact_orders values one vp nz sel off good unit
  exact selected_ordinary_pole_of_formal large w represented β _ _ root firstRoot plus minus detect guard vu

end
end Sun28.SelectedTrace
#print axioms Sun28.SelectedTrace.selected_contact_orders
#print axioms Sun28.SelectedTrace.selected_shift_pole
