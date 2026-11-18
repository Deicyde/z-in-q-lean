import PicardLocal
import PicardSextic
import Mathlib.Data.Nat.Squarefree

/-! The global quadratic twist and its local models for a rational Picard
parameter. One positive squarefree integer fixes all even branch valuations. -/
namespace ZOverQ.Qualitative.PrimitiveTwist

open Polynomial IsLocalRing IsDiscreteValuationRing
open ZInQ.QualitativeHeight ZOverQ.Qualitative.PicardLocal

noncomputable section

/-- The homogeneous branch form evaluated on a reduced fraction. -/
def branchInteger (s : ℚ) : ℤ :=
  let x := s.num
  let y : ℤ := s.den
  x*y*(x-y)*(x+y)*(x-3*y)*(x+3*y)

theorem cast_branch (s : ℚ) : (branchInteger s : ℚ) = primitiveBranch s := by
  simp [branchInteger, primitiveBranch, branchForm]

def twistPrimes (s : ℚ) : Finset ℕ :=
  let n := (branchInteger s).natAbs
  n.primeFactors.filter fun p => 3 < p ∧ n.factorization p % 4 = 2

def twist (s : ℚ) : ℕ := ∏ p ∈ twistPrimes s, p

private lemma selected_prime {s : ℚ} {p : ℕ} (h : p ∈ twistPrimes s) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1

theorem positive (s : ℚ) : 0 < twist s := Finset.prod_pos fun _ h => (selected_prime h).pos

theorem twist_order (s : ℚ) (p : ℕ) :
    (twist s).factorization p =
      if 3 < p ∧ (branchInteger s).natAbs.factorization p % 4 = 2 then 1 else 0 := by
  have mem : p ∈ twistPrimes s ↔ 3 < p ∧ (branchInteger s).natAbs.factorization p % 4 = 2 := by
    simp only [twistPrimes, Finset.mem_filter]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro zero
    simp [zero] at h
  unfold twist
  rw [Nat.factorization_prod_apply (fun q h => (selected_prime h).ne_zero)]
  calc
    _ = ∑ q ∈ twistPrimes s, if q=p then 1 else 0 := by
      exact Finset.sum_congr rfl fun q h => by
        simp only [(selected_prime h).factorization, Finsupp.single_apply]
    _ = (if p ∈ twistPrimes s then 1 else 0) := Finset.sum_ite_eq' _ _ (fun _ => 1)
    _ = _ := if_congr mem rfl rfl

theorem squarefree (s : ℚ) : Squarefree (twist s) := by
  apply Nat.squarefree_of_factorization_le_one (positive s).ne'
  intro p
  rw [twist_order]; split <;> decide

/-- Both common conventions for a quadratic twist give the same affine curve. -/
theorem twist_ordinate {K : Type*} [Field K] [CharZero K] {e y f : K} (he : e ≠ 0) :
    2*e*y^2 = f ↔ (2*e*y)^2 = 2*e*f := by
  have hn : 2*e ≠ 0 := mul_ne_zero (by norm_num) he
  constructor
  · intro h; rw [← h]; ring
  · intro h; apply mul_left_cancel₀ hn; linear_combination h

section MixedCharacteristic

variable (p : ℕ) [Fact p.Prime]
local notation "W" => WittRing p
local notation "κ" => ResidueField W

private def residueEquiv : κ ≃+* AlgebraicClosure (ZMod p) :=
  (Ideal.quotEquivOfEq (WittVector.irreducible p).maximalIdeal_eq).trans WittVector.quotientPEquiv

private local instance : CharP κ p :=
  charP_of_injective_ringHom (f := (residueEquiv p).symm.toRingHom) (residueEquiv p).symm.injective p

private local instance : IsAlgClosed κ := IsAlgClosed.of_ringEquiv _ _ (residueEquiv p).symm

private local instance : HenselianRing W (IsLocalRing.maximalIdeal W) := by
  rw [(WittVector.irreducible p).maximalIdeal_eq]
  infer_instance

private lemma nat_unit {n : ℕ} (h : ¬ p ∣ n) : IsUnit (n : W) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rwa [map_natCast, Ne, CharP.cast_eq_zero_iff κ p]

private lemma nat_val {n : ℕ} (hn : n ≠ 0) : addVal W (n : W) = (n.factorization p : ℕ∞) := by
  have hu := nat_unit p (Nat.not_dvd_ordCompl Fact.out hn)
  apply addVal_def _ hu.unit (WittVector.irreducible p)
  rw [hu.unit_spec, mul_comm]
  simpa only [Nat.cast_mul,Nat.cast_pow] using
    congrArg (fun k : ℕ => (k : W)) (Nat.ordProj_mul_ordCompl_eq_self n p).symm

private lemma int_val {z : ℤ} (hz : z ≠ 0) : addVal W (z : W) = (z.natAbs.factorization p : ℕ∞) := by
  have h := nat_val p (n := z.natAbs) (by simpa using hz)
  rcases Int.natAbs_eq z with hpos | hneg
  · have eqn : (z : W) = (z.natAbs : W) := by
      simpa only [Int.cast_natCast] using congrArg (fun a : ℤ => (a : W)) hpos
    rw [eqn]; exact h
  · have eqn : (z : W) = -(z.natAbs : W) := by
      simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun a : ℤ => (a : W)) hneg
    rw [eqn, AddValuation.map_neg]; exact h

theorem twist_val (s : ℚ) : addVal W (twist s : W) =
    ((if 3 < p ∧ (branchInteger s).natAbs.factorization p % 4 = 2 then 1 else 0 : ℕ) : ℕ∞) := by
  rw [nat_val p (positive s).ne', twist_order]

private lemma small (hp : 3 < p) (n : ℕ) (hn : 0 < n) (hn' : n ≤ 3) : IsUnit (n : W) :=
  nat_unit p (Nat.not_dvd_of_pos_of_lt hn (by omega))

/-- The field of the Picard coefficients embeds in the unramified completion
by choosing a simple lift of a root of X²+3. -/
theorem exists_rho (hp : 3 < p) : ∃ ρ : W, ρ^2 = -3 := by
  have h₂ : (2 : κ) ≠ 0 := by simpa only [map_ofNat] using
    (residue_ne_zero_iff_isUnit _).mpr (show IsUnit (2:W) from small p hp 2 (by decide) (by decide))
  have h₃ : (3 : κ) ≠ 0 := by simpa only [map_ofNat] using
    (residue_ne_zero_iff_isUnit _).mpr (show IsUnit (3:W) from small p hp 3 (by decide) (by decide))
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (-3:κ) (by decide : 0<2)
  have hn : z ≠ 0 := by intro e; simp [e,h₃] at hz
  have deriv : (X^2+3 : W[X]).derivative = 2*X := by simp [derivative_pow,map_ofNat]
  obtain ⟨ρ,eqn,_⟩ := ZInQBlueprint.HenselTriples.liftSimple (X^2+3 : W[X]) z
    (by simp [hz]) (by rw [deriv]; simpa only [eval₂_mul, eval₂_X, eval₂_ofNat] using mul_ne_zero h₂ hn)
  exact ⟨ρ,by simpa [IsRoot,eq_neg_iff_add_eq_zero] using eqn⟩

def plus (s : ℚ) (ρ : W) : W := (s.num : W) + ρ*(s.den : W)
def minus (s : ℚ) (ρ : W) : W := (s.num : W) - ρ*(s.den : W)

private lemma rho_unit (hp : 3 < p) {ρ : W} (hρ : ρ^2 = -3) : IsUnit ρ := by
  have h : IsUnit (ρ*ρ) := by rw [← sq, hρ]; exact (small p hp 3 (by decide) (by decide)).neg
  exact isUnit_of_mul_isUnit_left h

theorem primitive_pair (hp : 3 < p) (s : ℚ) {ρ : W} (hρ : ρ^2 = -3) :
    IsUnit (plus p s ρ) ∨ IsUnit (minus p s ρ) := by
  let σ := residue W
  obtain ⟨a,b,bez⟩ := s.isCoprime_num_den.intCast (R:=W)
  have hb : σ a * σ (s.num : W) + σ b * σ (s.den : W) = 1 := by
    simpa only [map_add, map_mul, map_one, Int.cast_natCast] using congrArg σ bez
  have h2 : (2:κ) ≠ 0 := by simpa only [map_ofNat] using
    (residue_ne_zero_iff_isUnit _).mpr (show IsUnit (2:W) from small p hp 2 (by decide) (by decide))
  have hr : σ ρ ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr (rho_unit p hp hρ)
  by_contra! hn
  have hplus : σ (s.num : W) + σ ρ*σ (s.den : W) = 0 := by
    simpa only [plus, map_add, map_mul] using not_ne_iff.mp (fun h => hn.1 ((residue_ne_zero_iff_isUnit _).mp h))
  have hminus : σ (s.num : W) - σ ρ*σ (s.den : W) = 0 := by
    simpa only [minus, map_sub, map_mul] using not_ne_iff.mp (fun h => hn.2 ((residue_ne_zero_iff_isUnit _).mp h))
  have hx : σ (s.num : W) = 0 := (mul_eq_zero.mp (show 2*σ (s.num : W) = 0 by
    linear_combination hplus+hminus)).resolve_left h2
  have hy : σ (s.den : W) = 0 := (mul_eq_zero.mp (show (2*σ ρ)*σ (s.den : W) = 0 by
    linear_combination hplus-hminus)).resolve_left (mul_ne_zero h2 hr)
  simp [hx,hy] at hb

theorem branch_difference (s : ℚ) {ρ : W} (hρ : ρ^2 = -3) :
    plus p s ρ ^ 6 - minus p s ρ ^ 6 = 12*ρ*(branchInteger s : W) := by
  simp [plus, minus, branchInteger]
  linear_combination (40*(s.num:W)^3*(s.den:W)^3*ρ +
    12*(s.num:W)*(s.den:W)^5*ρ*(ρ^2-3))*hρ

theorem branch_order (hp : 3 < p) (s : ℚ) (h : branchInteger s ≠ 0)
    {ρ : W} (hρ : ρ^2 = -3) :
    addVal W (plus p s ρ^6 - minus p s ρ^6) = ((branchInteger s).natAbs.factorization p : ℕ∞) := by
  have h12 : IsUnit (12:W) := by
    rw [show (12:W) = 2^2*3 by norm_num]
    exact ((small p hp 2 (by decide) (by decide)).pow 2).mul (small p hp 3 (by decide) (by decide))
  rw [branch_difference p s hρ, addVal_mul, addVal_eq_zero_iff.mpr (h12.mul (rho_unit p hp hρ)),
    zero_add, int_val p h]

private theorem nonzero_pair (s : ℚ) {ρ : W} (hρ : ρ^2 = -3) :
    plus p s ρ ≠ 0 ∧ minus p s ρ ≠ 0 := by
  have hd : (0 : ℤ) < s.den := by exact_mod_cast s.den_pos
  have h : (s.num)^2 + 3 * (s.den:ℤ)^2 ≠ 0 := by positivity
  have hh := int_val p h
  have hc : (((s.num)^2+3*(s.den:ℤ)^2 : ℤ):W) ≠ 0 := by
    rintro e; rw [e,addVal_zero] at hh; exact ENat.top_ne_natCast _ hh
  have hn : (s.num:W)^2 + 3 * (s.den:W)^2 ≠ 0 := by simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_pow,Int.cast_natCast] using hc
  apply mul_ne_zero_iff.mp
  convert hn using 1
  unfold plus minus
  linear_combination -(s.den:W)^2*hρ

private theorem power_unit {x : W} {m : ℕ} (hx : addVal W x = (m:ℕ∞)) :
    ∃ b : Wˣ, x = (p:W)^m*(b:W) := by
  have hn : x ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨n,b,h⟩ := eq_unit_mul_pow_irreducible hn (WittVector.irreducible p)
  have he := ENat.natCast_inj.mp ((addVal_def x b (WittVector.irreducible p) n h).symm.trans hx)
  exact ⟨b,by rw [← he,h,mul_comm]⟩

/-- The four possible sets of integral local parameters. The second and
third cases become the same chart after the reciprocal change of variable. -/
inductive FibreCase (u v e : W) : Prop
  | distinct (hu : IsUnit u) (hv : IsUnit v) (hd : IsUnit (u^6-v^6)) (he : IsUnit e)
  | zeroFirst (r : ℕ) (hr : 0 < r) (a : Wˣ) (hu : u=(p:W)^r*(a:W)) (hv : IsUnit v) (he : IsUnit e)
  | zeroSecond (r : ℕ) (hr : 0 < r) (a : Wˣ) (hv : v=(p:W)^r*(a:W)) (hu : IsUnit u) (he : IsUnit e)
  | twoTriples (r : ℕ) (hr : 0 < r) (d : Wˣ) (hu : IsUnit u) (hv : IsUnit v)
      (hd : u^6 = v^6 + ((p:W)^r)^2*(d:W)) (he : addVal W e = (r%2 : ℕ))

private lemma nonunit_power {x : W} (hn : x ≠ 0) (hu : ¬ IsUnit x) :
    ∃ r : ℕ, 0 < r ∧ ∃ b : Wˣ, x = (p:W)^r*(b:W) := by
  obtain ⟨r,b,h⟩ := eq_unit_mul_pow_irreducible hn (WittVector.irreducible p)
  refine ⟨r, ?_, b, by rw [h, mul_comm]⟩
  by_contra! hr
  apply hu
  rw [h, Nat.eq_zero_of_le_zero hr, pow_zero, mul_one]
  exact b.isUnit

/-- The single twist of a rational parameter supplies the input coefficients
of the smooth, single-triple, reciprocal or two-triple Witt model at every
prime of even or zero contact. -/
theorem cases_of_even (hp : 3 < p) (s : ℚ) (hb : primitiveBranch s ≠ 0)
    (hev : ¬ Odd (padicValRat p (primitiveBranch s))) {ρ : W} (hρ : ρ^2 = -3) :
    FibreCase p (plus p s ρ) (minus p s ρ) (twist s : W) := by
  let u := plus p s ρ
  let v := minus p s ρ
  let m := (branchInteger s).natAbs.factorization p
  have zne : branchInteger s ≠ 0 := fun z => hb (by rw [← cast_branch,z,Int.cast_zero])
  have valD : addVal W (u^6-v^6) = (m:ℕ∞) := branch_order p hp s zne hρ
  have cmp : padicValRat p (primitiveBranch s) = (m:ℤ) := by
    rw [← cast_branch,padicValRat.of_int,padicValInt,← Nat.factorization_def _ Fact.out]
  have even : m%2 = 0 := by rw [cmp] at hev; simp [Int.odd_iff] at hev; omega
  have he := twist_val p s
  change addVal W (twist s : W) = ((if 3 < p ∧ m%4=2 then 1 else 0 : ℕ):ℕ∞) at he
  have prim : IsUnit u ∨ IsUnit v := primitive_pair p hp s hρ
  have nn : u ≠ 0 ∧ v ≠ 0 := nonzero_pair p s hρ
  by_cases zero : m=0
  · have de : IsUnit (u^6-v^6) := addVal_eq_zero_iff.mp (by simpa [zero] using valD)
    have te : IsUnit (twist s : W) := addVal_eq_zero_iff.mp (by simpa [zero] using he)
    by_cases hu : IsUnit u
    · by_cases hv : IsUnit v
      · exact .distinct hu hv de te
      · obtain ⟨r,hr,a,ha⟩ := nonunit_power p nn.2 hv
        exact .zeroSecond r hr a ha hu te
    · obtain ⟨r,hr,a,ha⟩ := nonunit_power p nn.1 hu
      exact .zeroFirst r hr a ha (prim.resolve_left hu) te
  · let r := m/2
    have mr : m=2*r := by dsimp [r]; omega
    have pos : 0 < r := by omega
    have nunit : ¬ IsUnit (u^6-v^6) := by
      intro h
      have e : (m:ℕ∞) = 0 := valD.symm.trans (addVal_eq_zero_iff.mpr h)
      exact zero (by exact_mod_cast e)
    have rz : residue W (u^6-v^6) = 0 :=
      not_ne_iff.mp fun h => nunit ((residue_ne_zero_iff_isUnit _).mp h)
    have same : (residue W u)^6 = (residue W v)^6 := by
      apply sub_eq_zero.mp
      simpa only [map_sub,map_pow] using rz
    have units : IsUnit u ∧ IsUnit v := by
      simp only [← residue_ne_zero_iff_isUnit] at prim ⊢
      rcases prim with hu | hv
      · exact ⟨hu,fun h => (pow_ne_zero 6 hu) (same.trans (by simp [h]))⟩
      · exact ⟨fun h => (pow_ne_zero 6 hv) (same.symm.trans (by simp [h])),hv⟩
    obtain ⟨d,hd⟩ := power_unit p (x := u^6-v^6) (m := 2*r) (mr ▸ valD)
    refine .twoTriples r pos d units.1 units.2 ?_ ?_
    · rw [show (p:W)^(2*r) = ((p:W)^r)^2 by rw [Nat.mul_comm,pow_mul]] at hd
      linear_combination hd
    · have h : (if 3 < p ∧ m%4=2 then 1 else 0) = r%2 := by split <;> omega
      simpa only [h] using he

/-- At every eligible prime one can choose a root of −3, and either
choice gives one of the four integral models for the same rational twist. -/
theorem local_models (hp : 3 < p) (s : ℚ) (hb : primitiveBranch s ≠ 0)
    (hev : ¬ Odd (padicValRat p (primitiveBranch s))) :
    ∃ ρ : W, ρ^2 = -3 ∧ FibreCase p (plus p s ρ) (minus p s ρ) (twist s : W) := by
  obtain ⟨ρ,hr⟩ := exists_rho p hp
  exact ⟨ρ,hr,cases_of_even p hp s hb hev hr⟩

end MixedCharacteristic
end
end ZOverQ.Qualitative.PrimitiveTwist

#print axioms ZOverQ.Qualitative.PrimitiveTwist.squarefree
#print axioms ZOverQ.Qualitative.PrimitiveTwist.twist_ordinate
#print axioms ZOverQ.Qualitative.PrimitiveTwist.exists_rho
#print axioms ZOverQ.Qualitative.PrimitiveTwist.primitive_pair
#print axioms ZOverQ.Qualitative.PrimitiveTwist.branch_order
#print axioms ZOverQ.Qualitative.PrimitiveTwist.cases_of_even

#print axioms ZOverQ.Qualitative.PrimitiveTwist.local_models
