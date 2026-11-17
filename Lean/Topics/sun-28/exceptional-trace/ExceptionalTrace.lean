import ExceptionalDetector
import ExceptionalWeights
import FixedData

/-! The rational depth of the ordinary pole, including the ramified dyadic place. -/
namespace Sun28.Exceptional
open Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices Sun28.ScalarTrace Sun28.FixedPreparation
open ZInQ ZInQ.Mult NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

def leafWeight (R h : ℚ) (D : OrdinaryTest → K0) : K0 :=
  weightProduct (algebraMap ℚ K0 R) (normalizedLeaves (algebraMap ℚ K0 h) D) orderRequired

/-- Integrality at a finite place and its conjugate. The same valuations are used
twice at the unique prime in the inert and ramified cases. -/
def IntegralAtBoth (w : HeightOneSpectrum (𝓞 K0)) (D : OrdinaryTest → K0) : Prop :=
  ∀ i, Vge (discreteOrder (w.valuation K0)) 0 (D i) ∧
    Vge (discreteOrder (w.valuation K0)) 0 (conjugation (D i))

private theorem two_order {p : ℕ} [hp : Fact p.Prime] : padicValRat p (2:ℚ)≤1 := by
  by_cases eq : p=2
  · subst p
    exact le_of_eq (padicValRat.self (p:=2) (by decide))
  · have nd : ¬p∣2 := fun d=>eq ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 d)
    change padicValRat p ((2:ℕ):ℚ)≤1
    rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd]
    norm_num

private theorem trace_order (v : AddValuation K0 (WithTop ℤ)) {p : ℕ} [hp : Fact p.Prime]
    {R h : ℚ} (D : OrdinaryTest → K0) {e α ν : ℤ} (ep : 0<e)
    (base : ∀ a : ℚ,a≠0 → v (algebraMap ℚ K0 a)=((e*padicValRat p a:ℤ):WithTop ℤ))
    (rorder : v (algebraMap ℚ K0 R)=((e*(ν-6*α):ℤ):WithTop ℤ))
    (horder : v (algebraMap ℚ K0 h)=((e*(α-ν):ℤ):WithTop ℤ))
    (integer : ∀ i,Vge v 0 (D i) ∧ Vge v 0 (conjugation (D i))) (large : 6+211*|α|≤ν) :
    let T:=ordinaryTrace R (normalizedLeaves (algebraMap ℚ K0 h) D) orderRequired
    leafWeight R h D≠0 ∧ T≠0 ∧ padicValRat p T=padicValRat p 2 := by
  let T:=ordinaryTrace R (normalizedLeaves (algebraMap ℚ K0 h) D) orderRequired
  have a:=inverse_weight_congruent v D ep rorder horder (fun i=>(integer i).1) large
  have b:=inverse_weight_congruent v (fun i=>conjugation (D i)) ep rorder horder (fun i=>(integer i).2) large
  have trace : algebraMap ℚ K0 T=(leafWeight R h D)⁻¹+
      (leafWeight R h (fun i=>conjugation (D i)))⁻¹ := by
    dsimp only [T]
    rw [ordinaryTrace_eq conjugation conjugation_nontrivial]
    simp [leafWeight,normalizedLeaves]
    rfl
  have close : Vge v (2*e) (algebraMap ℚ K0 T-2) := by
    change Vge v (2*e) ((leafWeight R h D)⁻¹-1) at a
    change Vge v (2*e) ((leafWeight R h (fun i=>conjugation (D i)))⁻¹-1) at b
    convert a.add b using 1
    rw [trace]
    ring
  have vt : v (2:K0)=((e*padicValRat p 2:ℤ):WithTop ℤ) := by
    simpa only [map_ofNat] using base 2 (by norm_num)
  have bound : e*padicValRat p 2+1≤2*e := by nlinarith [mul_le_mul_of_nonneg_left (two_order (p:=p)) ep.le]
  have exactOrder := val_add_eq vt (close.mono bound)
  rw [add_sub_cancel] at exactOrder
  have nz : T≠0 := by
    rintro eq
    rw [eq,map_zero,v.map_zero] at exactOrder
    exact WithTop.top_ne_coe exactOrder
  rw [base T nz] at exactOrder
  have cancel := WithTop.coe_inj.mp exactOrder
  exact ⟨inverse_ne_zero v ep a,nz,mul_left_cancel₀ ep.ne' cancel⟩

theorem ordinary_depth_at_prime {p : ℕ} [hp : Fact p.Prime] (fixed : p∈primes)
    (place : HeightOneSpectrum (𝓞 K0))
    [place.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal]
    (points : NinePoints) (M : ℕ) (c : ℤ) (β A u w t : ℚ)
    (an : A≠0) (un : u≠0) (wn : w≠0) (slope : t=A*u/w^2) (unit : padicValRat p u=0)
    (large : 6+211*|padicValRat p A|≤padicValRat p (w^2))
    (integer : IntegralAtBoth place (ordinaryAt points M c β)) :
    let R:=detector A t
    let T:=ordinaryTraceAt points M c β A t
    t∉marks ∧ t≠3 ∧ R≠0 ∧ leafWeight R (t-3) (ordinaryAt points M c β)≠0 ∧ T≠0 ∧
    padicValRat p (t-3)=padicValRat p A-padicValRat p (w^2) ∧
    padicValRat p R=padicValRat p (w^2)-6*padicValRat p A ∧ padicValRat p T=padicValRat p 2 ∧
    padicValRat p (R/T^2)=padicValRat p (w^2)-6*padicValRat p A-2*padicValRat p 2 ∧
    4≤padicValRat p (R/T^2) := by
  let α:=padicValRat p A
  let ν:=padicValRat p (w^2)
  let R:=detector A t
  let T:=ordinaryTraceAt points M c β A t
  let D:=ordinaryAt points M c β
  let v:=discreteOrder (place.valuation K0)
  let e:ℤ:=place.asIdeal.ramificationIdx (𝓞 ℚ)
  let q:=(Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv q).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,hp.out⟩)
  have ep : 0<e := by
    dsimp [e]
    exact_mod_cast (Ideal.ramificationIdx_pos_of_isDedekindDomain' place.asIdeal q.ne_bot)
  have base (x : ℚ) (xn : x≠0) : v (algebraMap ℚ K0 x)=((e*padicValRat p x:ℤ):WithTop ℤ) := by
    simpa only [v,e,name] using prime_order_rat q place xn
  change 6+211*|α|≤ν at large
  have gap : α-ν< -1 := by linarith [le_abs_self α,abs_nonneg α]
  obtain ⟨off,guard,rn,ho,ro⟩:=detector_orders an un wn slope unit gap (fun _ m=>marks_order fixed m)
  have voR : v (algebraMap ℚ K0 R)=((e*(ν-6*α):ℤ):WithTop ℤ) := by rw [base R rn,ro]
  have voh : v (algebraMap ℚ K0 (t-3))=((e*(α-ν):ℤ):WithTop ℤ) := by rw [base _ (sub_ne_zero.mpr guard),ho]
  obtain ⟨live,nonzero,tv⟩:=trace_order v D ep base voR voh integer large
  have tr : padicValRat p T=padicValRat p 2 := tv
  change T≠0 at nonzero
  change R≠0 at rn
  change padicValRat p R=ν-6*α at ro
  have b : padicValRat p (R/T^2)=ν-6*α-2*padicValRat p 2 := by
    rw [padicValRat.div rn (pow_ne_zero _ nonzero),padicValRat.pow,tr,ro]
    norm_num
  have two:=two_order (p:=p)
  exact ⟨off,guard,rn,live,nonzero,ho,ro,tr,b,by rw [b]; linarith [le_abs_self α,abs_nonneg α]⟩

end
#print axioms ordinary_depth_at_prime
end Sun28.Exceptional
