import HenselTriples
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
# Residue polynomials of the bielliptic Picard sextic

The coordinate changes take place over an arbitrary coefficient ring. For
local lifting we work in a Henselian local domain with algebraically closed
residue field of characteristic different from two and three.
-/

namespace ZOverQ.Qualitative.PicardLocal

open Polynomial IsLocalRing ZInQBlueprint.HenselTriples
noncomputable section

section Equations

variable {R : Type*} [CommRing R]

def quadratic : R[X] := X^2 + 2*X - 2

def quartic (U V : R) : R[X] := 4*C U*(2*X-1) - C V*X^3*(X+4)

def sextic (U V : R) : R[X] := quadratic * quartic U V

theorem quartic_contact (U V : R) :
    quartic U V = -C V*quadratic^2 + 4*C (U-V)*(2*X-1) := by
  simp only [quartic, quadratic, map_sub]
  ring

theorem diagonal_fibre (V : R) : sextic V V = -C V*quadratic^3 := by
  rw [sextic, quartic_contact, sub_self, C_0]
  ring

theorem zero_fibre (V : R) :
    sextic 0 V = -C V*X^3*(X+4)*quadratic := by
  simp only [sextic, quartic, C_0]
  ring

/-- Divide the transformed quartic by `u ^ 6` before reducing. -/
def zeroChart (u V : R) : R[X] :=
  4*(2*C u^2*X-1) - C V*X^3*(C u^2*X+4)

theorem zero_chart_identity (u V : R) :
    (quartic (u^6) V).comp (C u^2*X) = C (u^6)*zeroChart u V := by
  simp [quartic, zeroChart, Polynomial.comp, eval₂_add, eval₂_sub,
    eval₂_pow, eval₂_mul]
  ring

theorem zero_chart_mod {k : Type*} [CommRing k] (φ : R →+* k) {u : R} (hu : φ u = 0) (V : R) :
    (zeroChart u V).map φ = -4*(1+C (φ V)*X^3) := by
  simp [zeroChart, hu]
  ring

def tangent (a c : R) : R[X] := X*(C (2*a+2) + C c*X)

/-- The polynomial left after extracting the cube of the disc radius. -/
def contactChart (a c V d : R) : R[X] :=
  tangent a c * (-C V*(tangent a c)^2 + 4*C d*(C (2*a-1)+2*C c*X))

theorem quadratic_chart {a : R} (ha : quadratic.eval a = 0) (c : R) :
    quadratic.comp (C a+C c*X) = C c*tangent a c := by
  have hz : a^2+2*a-2=0 := by simpa [quadratic] using ha
  have hz' := congrArg (C : R →+* R[X]) hz
  simp only [map_add, map_sub, map_pow, map_mul, map_ofNat, map_zero] at hz'
  simp [quadratic, tangent, Polynomial.comp, eval₂_sub, eval₂_pow, eval₂_add, eval₂_mul]
  norm_num only [map_ofNat]
  linear_combination hz'

theorem contact_chart_identity {a : R} (ha : quadratic.eval a = 0) (c V d : R) :
    (sextic (V+c^2*d) V).comp (C a+C c*X) = C (c^3)*contactChart a c V d := by
  simp only [sextic, quartic_contact, add_sub_cancel_left, add_comp, mul_comp, neg_comp,
    C_comp, pow_comp, quadratic_chart ha, sub_comp, X_comp, one_comp, contactChart]
  norm_num [Polynomial.comp, eval₂_mul, eval₂_ofNat, map_ofNat]
  ring

/-- Cubic on an even-contact disc. -/
def contactResidual (s v b : R) : R[X] := C s*X*(C b-C v*(C s*X)^2)

theorem contact_chart_mod {k : Type*} [CommRing k] (φ : R →+* k) (a : R) {c : R}
    (hc : φ c = 0) (V d : R) :
    (contactChart a c V d).map φ =
      contactResidual (2*φ a+2) (φ V) (4*φ d*(2*φ a-1)) := by
  simp [contactChart, tangent, contactResidual, hc]
  norm_num only [map_ofNat]
  ring

theorem quadratic_eval (x : R) : quadratic.eval x = x^2+2*x-2 := by simp [quadratic]
theorem quadratic_derivative (x : R) : quadratic.derivative.eval x = 2*x+2 := by
  simp [quadratic, derivative_pow]

theorem quartic_eval (U V x : R) : (quartic U V).eval x = 4*U*(2*x-1)-V*x^3*(x+4) := by
  simp [quartic]

theorem quartic_derivative (U V x : R) : (quartic U V).derivative.eval x = 8*U-4*V*x^2*(x+3) := by
  simp [quartic, derivative_pow]
  ring

/-- The vanishing of a quartic and its derivative forces a root of one of two
fixed factors whenever `6V` is nonzero. -/
theorem quartic_derivative_identity (U V x : R) :
    2*(quartic U V).eval x - (2*x-1)*(quartic U V).derivative.eval x =
      6*V*x^2*quadratic.eval x := by
  rw [quartic_eval, quartic_derivative, quadratic_eval]
  ring

theorem sextic_map {k : Type*} [CommRing k] (φ : R →+* k) (U V : R) :
    (sextic U V).map φ = sextic (φ U) (φ V) := by
  simp [sextic, quartic, quadratic]

theorem sextic_degree [IsDomain R] (U : R) {V : R} (hV : V ≠ 0) :
    (sextic U V).natDegree = 6 := by
  unfold sextic quartic quadratic
  compute_degree!

end Equations

section Fields

variable {k : Type*} [Field k]

theorem residue_characteristic (p : ℕ) [CharP k p] (hp : 3 < p) :
    (2 : k) ≠ 0 ∧ (3 : k) ≠ 0 := by
  constructor
  · intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((CharP.cast_eq_zero_iff k p 2).mp h)
    omega
  · intro h
    have hle := Nat.le_of_dvd (by decide : 0 < 3) ((CharP.cast_eq_zero_iff k p 3).mp h)
    omega

/-- At a quadratic root the derivative and the linear factor in the contact
perturbation are units. Its residue is distinct from zero and minus four. -/
theorem quadratic_root_units (h₂ : (2:k) ≠ 0) (h₃ : (3:k) ≠ 0) {x : k}
    (hx : quadratic.IsRoot x) :
    2*x+2 ≠ 0 ∧ 2*x-1 ≠ 0 ∧ x ≠ 0 ∧ x ≠ -4 := by
  have hz : x^2+2*x-2=0 := by simpa [IsRoot, quadratic_eval] using hx
  have h12 : (12:k) ≠ 0 := by
    rw [show (12:k) = 2^2*3 by norm_num]; exact mul_ne_zero (pow_ne_zero _ h₂) h₃
  have h6 : (6:k) ≠ 0 := by rw [show (6:k)=2*3 by norm_num]; exact mul_ne_zero h₂ h₃
  refine ⟨fun h => h12 ?_, fun h => h₃ ?_, fun h => h₂ ?_, fun h => h6 ?_⟩
  · linear_combination (2*x+2)*h - 4*hz
  · linear_combination (2*x+5)*h - 4*hz
  · subst x; simpa using hz
  · subst x; linear_combination hz

/-- Every geometric root off the three bad parameter divisors is simple. -/
theorem good_root_simple (h₂ : (2:k) ≠ 0) (h₃ : (3:k) ≠ 0) {U V : k}
    (hU : U ≠ 0) (hV : V ≠ 0) (hD : U-V ≠ 0) {x : k} (hx : (sextic U V).IsRoot x) :
    (sextic U V).derivative.eval x ≠ 0 := by
  have h4 : (4:k) ≠ 0 := by rw [show (4:k)=2*2 by norm_num]; exact mul_ne_zero h₂ h₂
  have h6 : (6:k) ≠ 0 := by rw [show (6:k)=2*3 by norm_num]; exact mul_ne_zero h₂ h₃
  have noCommon (hq : quadratic.IsRoot x) : (quartic U V).eval x ≠ 0 := by
    rw [quartic_contact]
    have hql : quadratic.eval x = 0 := hq
    simpa [hql] using mul_ne_zero (mul_ne_zero h4 hD) (quadratic_root_units h₂ h₃ hq).2.1
  have hx' : quadratic.eval x * (quartic U V).eval x = 0 := by simpa [IsRoot, sextic] using hx
  rw [sextic, derivative_mul, eval_add, eval_mul, eval_mul]
  rcases mul_eq_zero.mp hx' with hq | hg
  · rw [hq, zero_mul, add_zero, quadratic_derivative]
    exact mul_ne_zero (quadratic_root_units h₂ h₃ hq).1 (noCommon hq)
  · have hq : quadratic.eval x ≠ 0 := fun h => noCommon h hg
    rw [hg, mul_zero, zero_add]
    refine mul_ne_zero hq fun hd => ?_
    have hzero := quartic_derivative_identity U V x
    rw [hg, hd, mul_zero, mul_zero, sub_self] at hzero
    have hn : x ≠ 0 := by
      rintro rfl
      apply (mul_ne_zero h4 hU)
      simpa [quartic_eval] using hg
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h6 hV) (pow_ne_zero 2 hn)) hq) hzero.symm

/-- The sextic is separable over the original field, without a splitting assumption. -/
theorem good_fibre_separable (h₂ : (2:k) ≠ 0) (h₃ : (3:k) ≠ 0) {U V : k}
    (hU : U ≠ 0) (hV : V ≠ 0) (hD : U-V ≠ 0) : (sextic U V).Separable := by
  let K := AlgebraicClosure k
  let φ := algebraMap k K
  have nz {x : k} (h : x ≠ 0) : φ x ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr h
  rw [separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed k K]
  intro x
  rw [← eval_map_algebraMap, ← eval_map_algebraMap, ← derivative_map]
  change ((sextic U V).map φ).eval x ≠ 0 ∨ ((sextic U V).map φ).derivative.eval x ≠ 0
  rw [sextic_map]
  exact or_iff_not_imp_left.mpr fun hx => good_root_simple
    (by simpa only [map_ofNat] using nz h₂) (by simpa only [map_ofNat] using nz h₃)
    (nz hU) (nz hV) (by simpa only [map_sub] using nz hD) (not_not.mp hx)

/-- A separable binomial of degree n supplies n distinct nonzero roots over
an algebraically closed residue field. -/
private theorem power_roots [IsAlgClosed k] (n : ℕ) (hn : (n:k) ≠ 0) (a : k) (ha : a ≠ 0) :
    ∃ w : Fin n → k, Function.Injective w ∧ ∀ i, w i ≠ 0 ∧ w i^n=a := by
  classical
  let P : k[X] := X^n-C a
  have sep : P.Separable := separable_X_pow_sub_C a hn ha
  have card : Fintype.card P.roots.toFinset = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots sep),
      IsAlgClosed.card_roots_eq_natDegree]
    exact natDegree_X_pow_sub_C
  let e := (Fintype.equivFinOfCardEq card).symm
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i
  have root := (mem_roots sep.ne_zero).mp (Multiset.mem_toFinset.mp (e i).property)
  have eqn : (e i).val^n=a := by simpa [P, IsRoot, sub_eq_zero] using root
  refine ⟨fun z => ha ?_, eqn⟩
  change (e i).val = 0 at z
  rw [← eqn, z, zero_pow (by rintro rfl; simp at hn)]

private theorem quadratic_roots [IsAlgClosed k] (h₂ : (2:k) ≠ 0) (h₃ : (3:k) ≠ 0) :
    ∃ z : Fin 2 → k, Function.Injective z ∧ ∀ i, quadratic.IsRoot (z i) := by
  obtain ⟨w, hw, eqs⟩ := power_roots 2 h₂ (3:k) h₃
  refine ⟨fun i => w i-1, fun _ _ h => hw (sub_left_inj.mp h), fun i => ?_⟩
  rw [IsRoot, quadratic_eval]
  linear_combination (eqs i).2

/-- The three outer roots in the residue fibre at zero contact. -/
theorem zero_outer_roots [IsAlgClosed k] (h₂ : (2:k) ≠ 0) (h₃ : (3:k) ≠ 0)
    {V : k} (hV : V ≠ 0) : ∃ w : Fin 3 → k, Function.Injective w ∧ ∀ i, w i ≠ 0 ∧
      (sextic 0 V).IsRoot (w i) ∧ (sextic 0 V).derivative.eval (w i) ≠ 0 := by
  have h4 : (4:k) ≠ 0 := by rw [show (4:k)=2*2 by norm_num]; exact mul_ne_zero h₂ h₂
  have h6 : (6:k) ≠ 0 := by rw [show (6:k)=2*3 by norm_num]; exact mul_ne_zero h₂ h₃
  obtain ⟨z, hz, hq⟩ := quadratic_roots h₂ h₃
  refine ⟨Fin.cons (-4) z, Fin.cons_injective_of_injective ?_ hz, ?_⟩
  · rintro ⟨i, hi⟩
    exact (quadratic_root_units h₂ h₃ (hq i)).2.2.2 hi
  · have deriv (x : k) : (sextic 0 V).derivative.eval x =
        -3*V*x^2*(x+4)*quadratic.eval x - V*x^3*quadratic.eval x
        - V*x^3*(x+4)*(2*x+2) := by
      rw [zero_fibre]
      simp [derivative_pow, quadratic_derivative]
      ring
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (-4:k) ≠ 0 ∧ (sextic 0 V).IsRoot (-4) ∧ (sextic 0 V).derivative.eval (-4) ≠ 0
      refine ⟨neg_ne_zero.mpr h4, by simp [IsRoot, zero_fibre], ?_⟩
      have hq4 : quadratic.eval (-4:k) = 6 := by rw [quadratic_eval]; ring
      rw [deriv, hq4]
      simpa only [neg_add_cancel, mul_zero, zero_mul, zero_sub, sub_zero, neg_ne_zero] using
        (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hV (pow_ne_zero 3 (neg_ne_zero.mpr h4))) h6))
    · change z j ≠ 0 ∧ (sextic 0 V).IsRoot (z j) ∧ (sextic 0 V).derivative.eval (z j) ≠ 0
      obtain ⟨hs, _, hn, h4z⟩ := quadratic_root_units h₂ h₃ (hq j)
      have qz : quadratic.eval (z j) = 0 := hq j
      refine ⟨hn, by simp [IsRoot, zero_fibre, qz], ?_⟩
      rw [deriv, qz]
      simp only [mul_zero, sub_zero, zero_sub, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hV (pow_ne_zero 3 hn))
        (by contrapose! h4z; linear_combination h4z)) hs

/-- The three simple nonzero roots in the zero-contact chart. -/
theorem zero_residual_roots [IsAlgClosed k] (h₂ : (2:k) ≠ 0) (h₃ : (3:k) ≠ 0) {V : k}
    (hV : V ≠ 0) :
    ∃ w : Fin 3 → k, Function.Injective w ∧ ∀ i, w i ≠ 0 ∧
      ((-4*(1+C V*X^3) : k[X]).IsRoot (w i)) ∧
      (-4*(1+C V*X^3) : k[X]).derivative.eval (w i) ≠ 0 := by
  have h4 : (4:k) ≠ 0 := by rw [show (4:k)=2*2 by norm_num]; exact mul_ne_zero h₂ h₂
  obtain ⟨w, hw, eqs⟩ := power_roots 3 h₃ (-V⁻¹) (neg_ne_zero.mpr (inv_ne_zero hV))
  refine ⟨w, hw, fun i => ⟨(eqs i).1, ?_, ?_⟩⟩
  · simp [IsRoot, (eqs i).2, hV]
  · have formula : (-4*(1+C V*X^3) : k[X]).derivative.eval (w i) =
        -(4*3*V*(w i)^2) := by
      simp [derivative_pow]; ring
    rw [formula]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 h₃) hV)
      (pow_ne_zero 2 (eqs i).1))

/-- The two nonzero roots of the residual quadratic and their common centre
give three pairwise distinct, simple roots in one contact disc. -/
theorem contact_residual_roots [IsAlgClosed k] (h₂ : (2:k) ≠ 0)
    {s v b : k} (hs : s ≠ 0) (hv : v ≠ 0) (hb : b ≠ 0) :
    ∃ w : Fin 3 → k, Function.Injective w ∧ ∀ i,
      (contactResidual s v b).IsRoot (w i) ∧
      (contactResidual s v b).derivative.eval (w i) ≠ 0 := by
  have den := mul_ne_zero hv (pow_ne_zero 2 hs)
  obtain ⟨w, hw, eqs⟩ := power_roots 2 h₂ (b/(v*s^2)) (div_ne_zero hb den)
  refine ⟨Fin.cons 0 w, Fin.cons_injective_of_injective ?_ hw, ?_⟩
  · rintro ⟨i, hi⟩; exact (eqs i).1 hi
  · have ev (x : k) : (contactResidual s v b).eval x = s*x*(b-v*(s*x)^2) := by
      simp [contactResidual]
    have deriv (x : k) : (contactResidual s v b).derivative.eval x = s*(b-3*v*s^2*x^2) := by
      simp [contactResidual, derivative_pow]; ring
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (contactResidual s v b).eval 0 = 0 ∧ _
      rw [ev]
      change _ ∧ (contactResidual s v b).derivative.eval 0 ≠ 0
      simpa [deriv] using mul_ne_zero hs hb
    · change (contactResidual s v b).eval (w j) = 0 ∧
        (contactResidual s v b).derivative.eval (w j) ≠ 0
      have eqn : (w j)^2*(v*s^2)=b := (eq_div_iff den).mp (eqs j).2
      rw [ev, deriv]
      constructor
      · have : b-v*(s*w j)^2 = 0 := by linear_combination -eqn
        rw [this, mul_zero]
      · have : b-3*v*s^2*(w j)^2 = -(2*b) := by linear_combination -3*eqn
        rw [this]
        exact mul_ne_zero hs (neg_ne_zero.mpr (mul_ne_zero h₂ hb))

end Fields

section LocalRings

variable {R : Type*} [CommRing R] [IsLocalRing R]

private theorem liftMapped [HenselianRing R (maximalIdeal R)]
    (f : R[X]) {F : (ResidueField R)[X]} (hm : f.map (residue R) = F)
    {z : ResidueField R} (hz : F.IsRoot z) (hd : F.derivative.eval z ≠ 0) :
    ∃ x : R, f.IsRoot x ∧ residue R x = z := by
  apply liftSimple f z
  · rw [eval₂_eq_eval_map, hm]; exact hz
  · rw [eval₂_eq_eval_map, ← derivative_map, hm]; exact hd

section Hensel

variable [IsDomain R] [HenselianRing R (maximalIdeal R)] [IsAlgClosed (ResidueField R)]

/-- At even contact the two lifted quadratic roots are centres of two
triples. Within a triple every difference has the form `c` times a unit.
Differences between triples are units. -/
theorem even_contact_triples
    (h₂ : (2 : ResidueField R) ≠ 0) (h₃ : (3 : ResidueField R) ≠ 0)
    {c V d : R} (hc : c ≠ 0) (hc₀ : residue R c = 0)
    (hV : residue R V ≠ 0) (hd : residue R d ≠ 0) :
    ∃ (a : Fin 2 → R) (ξ : Fin 2 → Fin 3 → ResidueField R),
      Nonempty (TwoTriples (sextic (V+c^2*d) V) a c ξ) := by
  let ρ := residue R
  have h4 : (4 : ResidueField R) ≠ 0 := by
    rw [show (4 : ResidueField R)=2*2 by norm_num]; exact mul_ne_zero h₂ h₂
  obtain ⟨z, hinj, hz⟩ := quadratic_roots h₂ h₃
  have each (i : Fin 2) : ∃ x : R, quadratic.IsRoot x ∧ ρ x = z i := by
    apply liftMapped (quadratic : R[X]) (F := quadratic) (by simp [quadratic]) (hz i)
    rw [quadratic_derivative]
    exact (quadratic_root_units h₂ h₃ (hz i)).1
  choose a ha hra using each
  have hainj : Function.Injective (fun i => residue R (a i)) := by
    intro i j h
    exact hinj ((hra i).symm.trans (h.trans (hra j)))
  have data (i : Fin 2) := contact_residual_roots h₂ (quadratic_root_units h₂ h₃ (hz i)).1
    hV (mul_ne_zero (mul_ne_zero h4 hd) (quadratic_root_units h₂ h₃ (hz i)).2.1)
  choose ξ hξ roots using data
  have hm (i : Fin 2) : (contactChart (a i) c V d).map (residue R) =
      contactResidual (2*z i+2) (ρ V) (4*ρ d*(2*z i-1)) := by
    rw [contact_chart_mod (residue R) (a i) hc₀]
    change contactResidual (2*ρ (a i)+2) (ρ V) (4*ρ d*(2*ρ (a i)-1)) = _
    rw [hra]
  refine ⟨a, ξ, twoTriples _ a c _ ξ hc hc₀ hainj
    (fun i => chartEval (contact_chart_identity (ha i) c V d)) hξ ?_ ?_⟩
  · intro i j; rw [eval₂_eq_eval_map, hm]; exact (roots i j).1
  · intro i j; rw [eval₂_eq_eval_map, ← derivative_map, hm]; exact (roots i j).2

theorem even_contact_splits
    (h₂ : (2 : ResidueField R) ≠ 0) (h₃ : (3 : ResidueField R) ≠ 0)
    {c V d : R} (hc : c ≠ 0) (hc₀ : residue R c = 0)
    (hV : residue R V ≠ 0) (hd : residue R d ≠ 0) :
    (sextic (V+c^2*d) V).roots.Nodup ∧ (sextic (V+c^2*d) V).Splits := by
  obtain ⟨_, _, ⟨T⟩⟩ := even_contact_triples h₂ h₃ hc hc₀ hV hd
  have deg := sextic_degree (V+c^2*d) (show V ≠ 0 by rintro rfl; exact hV (map_zero _))
  exact (splitsSix T (fun h => by simp [h] at deg) deg.le).2

end Hensel

/-- The six roots at zero contact consist of the three points `u² * inner i`
and the three points `outer i`. The two sets of residual coordinates are
each pairwise distinct and avoid zero. -/
structure ZeroFibreRoots (u V : R) where
  inner : Fin 3 → R
  outer : Fin 3 → R
  innerRoot : ∀ i, (sextic (u^6) V).IsRoot (u^2*inner i)
  outerRoot : ∀ i, (sextic (u^6) V).IsRoot (outer i)
  innerUnit : ∀ i, IsUnit (inner i)
  outerUnit : ∀ i, IsUnit (outer i)
  innerDistinct : Function.Injective (fun i => residue R (inner i))
  outerDistinct : Function.Injective (fun i => residue R (outer i))

/-- Construct all the outer unit roots and all three roots with normalised
coordinate a unit, using the two different residue polynomials. -/
theorem zero_contact_lifts [HenselianRing R (maximalIdeal R)] [IsAlgClosed (ResidueField R)]
    (h₂ : (2 : ResidueField R) ≠ 0) (h₃ : (3 : ResidueField R) ≠ 0)
    {u V : R} (hu₀ : residue R u = 0) (hV : residue R V ≠ 0) :
    Nonempty (ZeroFibreRoots u V) := by
  obtain ⟨z, hz, rz⟩ := zero_residual_roots h₂ h₃ hV
  obtain ⟨w, hw, rw'⟩ := zero_outer_roots h₂ h₃ hV
  choose y hr hy using fun i => liftMapped (zeroChart u V)
    (zero_chart_mod (residue R) hu₀ V) (rz i).2.1 (rz i).2.2
  have hem : (sextic (u^6) V).map (residue R) = sextic 0 (residue R V) := by
    rw [sextic_map, map_pow, hu₀, zero_pow (by decide)]
  choose l hl hrl using fun i => liftMapped _ hem (rw' i).2.1 (rw' i).2.2
  refine ⟨⟨y, l, ?_, hl, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    have he := congrArg (Polynomial.eval (y i)) (zero_chart_identity u V)
    have hzy : (zeroChart u V).eval (y i) = 0 := hr i
    have hq : (quartic (u^6) V).eval (u^2*y i) = 0 := by simpa [eval_comp, hzy] using he
    simp [IsRoot, sextic, hq]
  · intro i; apply (residue_ne_zero_iff_isUnit _).mp; rw [hy]; exact (rz i).1
  · intro i; apply (residue_ne_zero_iff_isUnit _).mp; rw [hrl]; exact (rw' i).1
  · intro i j h; exact hz ((hy i).symm.trans (h.trans (hy j)))
  · intro i j h; exact hw ((hrl i).symm.trans (h.trans (hrl j)))

/-- Two inner roots in the zero-contact fibre differ by the square of `u`
times a unit; all other pairs of roots have unit difference. -/
theorem zero_contact_distances {u V : R} (T : ZeroFibreRoots u V)
    (hu₀ : residue R u = 0) :
    (∀ i j, i ≠ j → ∃ e : Rˣ, u^2*T.inner i-u^2*T.inner j = u^2*(e:R)) ∧
    (∀ i j, i ≠ j → IsUnit (T.outer i-T.outer j)) ∧
    (∀ i j, IsUnit (u^2*T.inner i-T.outer j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h : IsUnit (T.inner i-T.inner j) := (residue_ne_zero_iff_isUnit _).mp (by
      rw [map_sub]; exact sub_ne_zero.mpr (fun h => hij (T.innerDistinct h)))
    obtain ⟨e, he⟩ := h
    exact ⟨e, by rw [he, mul_sub]⟩
  · intro i j hij
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [map_sub]; exact sub_ne_zero.mpr (fun h => hij (T.outerDistinct h))
  · intro i j
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa [hu₀] using (residue_ne_zero_iff_isUnit _).mpr (T.outerUnit j)

theorem zero_contact_splits [IsDomain R] {u V : R} (T : ZeroFibreRoots u V)
    (hu : u ≠ 0) (hu₀ : residue R u = 0) (hV : V ≠ 0) :
    (sextic (u^6) V).roots.Nodup ∧ (sextic (u^6) V).Splits := by
  classical
  let f := sextic (u^6) V
  let x : Fin 3 ⊕ Fin 3 → R := Sum.elim (fun i => u^2*T.inner i) T.outer
  have deg : f.natDegree = 6 := sextic_degree _ hV
  change f.roots.Nodup ∧ f.Splits
  have hf : f ≠ 0 := by intro h; simp [h] at deg
  have inj : Function.Injective x := by
    rintro (i|i) (j|j) he
    · exact congrArg Sum.inl (T.innerDistinct (congrArg (residue R)
        (mul_left_cancel₀ (pow_ne_zero 2 hu) he)))
    · exact False.elim ((zero_contact_distances T hu₀).2.2 i j |>.ne_zero <| sub_eq_zero.mpr he)
    · exact False.elim ((zero_contact_distances T hu₀).2.2 j i |>.ne_zero <| sub_eq_zero.mpr he.symm)
    · exact congrArg Sum.inr (T.outerDistinct (congrArg (residue R) he))
  have inclus : Finset.univ.image x ⊆ f.roots.toFinset := by
    intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots hf).mpr
    cases i with
    | inl j => exact T.innerRoot j
    | inr j => exact T.outerRoot j
  have card : (Finset.univ.image x).card = 6 := by
    simp [Finset.card_image_of_injective _ inj]
  have h₁ := Finset.card_le_card inclus
  rw [card] at h₁
  have h₂ := Multiset.toFinset_card_le f.roots
  have h₃ := card_roots' f
  exact ⟨Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega), splits_iff_card_roots.mpr (by omega)⟩

end LocalRings

/-! The characteristic, Hensel and closed residue-field hypotheses hold in the
specific discrete valuation ring of Witt vectors on the algebraic closure of
the prime field. This gives a single ring in which both splittings occur. -/

section Witt

variable (p : ℕ) [Fact p.Prime]

abbrev WittRing := WittVector p (AlgebraicClosure (ZMod p))

private theorem witt_maximal : maximalIdeal (WittRing p) = Ideal.span {(p : WittRing p)} :=
  (show Irreducible (p : WittRing p) from WittVector.irreducible p).maximalIdeal_eq

private def wittResidue : ResidueField (WittRing p) ≃+* AlgebraicClosure (ZMod p) :=
  (Ideal.quotEquivOfEq (witt_maximal p)).trans WittVector.quotientPEquiv

private local instance : IsAlgClosed (ResidueField (WittRing p)) :=
  IsAlgClosed.of_ringEquiv _ _ (wittResidue p).symm

private local instance : CharP (ResidueField (WittRing p)) p :=
  charP_of_injective_ringHom (f := (wittResidue p).symm.toRingHom) (wittResidue p).symm.injective p

private local instance : HenselianRing (WittRing p) (maximalIdeal (WittRing p)) := by
  rw [witt_maximal]
  infer_instance

private theorem witt_radius {r : ℕ} (hr : 0 < r) :
    (p : WittRing p)^r ≠ 0 ∧ residue (WittRing p) ((p : WittRing p)^r) = 0 := by
  refine ⟨pow_ne_zero _ (WittVector.irreducible p).ne_zero, ?_⟩
  rw [map_pow, map_natCast, CharP.cast_eq_zero, zero_pow hr.ne']

/-- The two-triple configuration and splitting for the even-contact model
over a specified Witt ring, for every prime `p > 3`. -/
theorem witt_even_contact (hp : 3 < p) {r : ℕ} (hr : 0 < r) (V d : (WittRing p)ˣ) :
    let c := (p : WittRing p)^r
    let f := sextic ((V : WittRing p)+c^2*(d : WittRing p)) (V : WittRing p)
    (∃ (a : Fin 2 → WittRing p) (ξ : Fin 2 → Fin 3 → ResidueField (WittRing p)),
      Nonempty (TwoTriples f a c ξ)) ∧ f.roots.Nodup ∧ f.Splits := by
  obtain ⟨h₂, h₃⟩ := residue_characteristic (k := ResidueField (WittRing p)) p hp
  obtain ⟨hc, hc₀⟩ := witt_radius p hr
  have hv := (residue_ne_zero_iff_isUnit (V : WittRing p)).mpr V.isUnit
  have hd := (residue_ne_zero_iff_isUnit (d : WittRing p)).mpr d.isUnit
  exact ⟨even_contact_triples h₂ h₃ hc hc₀ hv hd, even_contact_splits h₂ h₃ hc hc₀ hv hd⟩

/-- At a zero of positive order `r`, the three inner roots and three outer
roots in this Witt ring exhaust the roots and are distinct. -/
theorem witt_zero_contact (hp : 3 < p) {r : ℕ} (hr : 0 < r) (e V : (WittRing p)ˣ) :
    let u := (p : WittRing p)^r*(e : WittRing p)
    Nonempty (ZeroFibreRoots u (V : WittRing p)) ∧ (sextic (u^6) (V : WittRing p)).roots.Nodup ∧
      (sextic (u^6) (V : WittRing p)).Splits := by
  obtain ⟨h₂, h₃⟩ := residue_characteristic (k := ResidueField (WittRing p)) p hp
  obtain ⟨hc, hc₀⟩ := witt_radius p hr
  have hu := mul_ne_zero hc e.ne_zero
  have hu₀ : residue (WittRing p) ((p : WittRing p)^r*(e : WittRing p)) = 0 := by
    rw [map_mul, hc₀, zero_mul]
  obtain ⟨T⟩ := zero_contact_lifts h₂ h₃ hu₀ ((residue_ne_zero_iff_isUnit _).mpr V.isUnit)
  exact ⟨⟨T⟩, zero_contact_splits T hu hu₀ V.ne_zero⟩

end Witt

end
end ZOverQ.Qualitative.PicardLocal

#print axioms ZOverQ.Qualitative.PicardLocal.good_fibre_separable
#print axioms ZOverQ.Qualitative.PicardLocal.even_contact_triples
#print axioms ZOverQ.Qualitative.PicardLocal.even_contact_splits
#print axioms ZOverQ.Qualitative.PicardLocal.zero_contact_lifts
#print axioms ZOverQ.Qualitative.PicardLocal.zero_contact_distances
#print axioms ZOverQ.Qualitative.PicardLocal.zero_contact_splits
#print axioms ZOverQ.Qualitative.PicardLocal.witt_even_contact
#print axioms ZOverQ.Qualitative.PicardLocal.witt_zero_contact
