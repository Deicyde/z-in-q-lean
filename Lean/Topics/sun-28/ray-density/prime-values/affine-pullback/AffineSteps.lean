import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! The exact change of subgroup, difference steps and base average in
Glazer v18, Lemma v18tz:lem:norm. The inputs are real, so conjugation is trivial. -/

namespace Sun28.AffinePullback
open Finset
noncomputable section

def dilation (E n : ℕ) : ZMod n →+ ZMod (E*n) :=
  ZMod.lift n ⟨(E : ℕ) • Int.castAddHom (ZMod (E*n)), by
    simp only [AddMonoidHom.nsmul_apply, Int.coe_castAddHom, Int.cast_natCast, nsmul_eq_mul]
    simpa only [← Nat.cast_mul] using ZMod.natCast_self (E*n)⟩

@[simp] theorem dilation_int (E n : ℕ) (x : ℤ) :
    dilation E n (x : ZMod n) = (E*x : ℤ) := by
  simp [dilation, nsmul_eq_mul]

theorem dilation_injective {E : ℕ} (hE : 0 < E) (n : ℕ) :
    Function.Injective (dilation E n) := by
  intro x y heq
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨y,rfl⟩ := ZMod.intCast_surjective y
  rw [dilation_int, dilation_int, ZMod.intCast_eq_intCast_iff] at heq
  apply (ZMod.intCast_eq_intCast_iff ..).2
  exact Int.ModEq.mul_left_cancel' (c := (E:ℤ)) (by exact_mod_cast hE.ne') (by simpa using heq)

def affine (E n : ℕ) (t : ZMod (E*n)) (x : ZMod n) : ZMod (E*n) := t + dilation E n x

theorem affine_injective {E : ℕ} (hE : 0 < E) (n : ℕ) (t : ZMod (E*n)) :
    Function.Injective (affine E n t) :=
  fun _ _ eq => dilation_injective hE n (add_left_cancel eq)

def extend (E n : ℕ) (t : ZMod (E*n)) (F : ZMod n → ℝ) : ZMod (E*n) → ℝ :=
  Function.extend (affine E n t) F 0

@[simp] theorem extend_affine {E : ℕ} (hE : 0 < E) (n : ℕ) (t : ZMod (E*n))
    (F : ZMod n → ℝ) (x : ZMod n) : extend E n t F (affine E n t x) = F x :=
  Function.Injective.extend_apply (affine_injective hE n t) ..

theorem extend_eq_zero {E n : ℕ} {t : ZMod (E*n)} {F : ZMod n → ℝ} {y : ZMod (E*n)}
    (out : y ∉ Set.range (affine E n t)) : extend E n t F y = 0 :=
  Function.extend_apply' _ _ _ out

theorem same_residue {E : ℕ} (hE : 0<E) (q i j : ℕ) :
    q*i ≡ q*j [MOD E] ↔ i % (E/E.gcd q) = j % (E/E.gcd q) := by
  constructor
  · exact Nat.ModEq.cancel_left_div_gcd hE
  · intro same
    have a : (q/E.gcd q)*i ≡ (q/E.gcd q)*j [MOD E/E.gcd q] :=
      Nat.ModEq.mul_left _ same
    have b := a.mul_left' (E.gcd q)
    simpa only [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _),
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)] using b

theorem cast_zero_step {E : ℕ} (hE : 0<E) (q i j : ℕ) :
    ((q:ZMod E)*((i:ZMod E)-j) = 0) ↔ i%(E/E.gcd q) = j%(E/E.gcd q) := by
  rw [mul_sub, sub_eq_zero, ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  exact same_residue hE q i j

theorem step_formula (E : ℕ) (q i j : ℕ)
    (same : i%(E/E.gcd q)=j%(E/E.gcd q)) :
    (q : ℤ)*((i:ℤ)-j) = E*((q/E.gcd q:ℕ)*((i/(E/E.gcd q):ℕ)-(j/(E/E.gcd q):ℕ):ℤ)) := by
  let h := E/E.gcd q
  let k := q/E.gcd q
  let g := E.gcd q
  have e : g*h=E := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have v : g*k=q := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have s : (i%h:ℤ) = (j%h:ℤ) := by exact_mod_cast same
  have ai : (i%h:ℤ)+(h:ℤ)*(i/h:ℕ)=i := by exact_mod_cast Nat.mod_add_div i h
  have aj : (j%h:ℤ)+(h:ℤ)*(j/h:ℕ)=j := by exact_mod_cast Nat.mod_add_div j h
  have dq : (g:ℤ)*k=q := by exact_mod_cast v
  have de : (g:ℤ)*h=E := by exact_mod_cast e
  change (q:ℤ)*((i:ℤ)-j)=(E:ℤ)*((k:ℤ)*((i/h:ℕ)-(j/h:ℕ):ℤ))
  have diff : (i:ℤ)-j=(h:ℤ)*((i/h:ℕ)-(j/h:ℕ):ℤ) := by linarith
  rw [diff, ← dq, ← de]
  ring


theorem residue_affine (E n : ℕ) (t : ZMod (E*n)) (x : ZMod n) :
    ZMod.castHom (dvd_mul_right E n) (ZMod E) (affine E n t x) =
      ZMod.castHom (dvd_mul_right E n) (ZMod E) t := by
  obtain ⟨x,rfl⟩ := ZMod.intCast_surjective x
  simp [affine, dilation_int]

theorem shifted_mem_iff {E : ℕ} (hE : 0<E) (n q i j : ℕ)
    (t : ZMod (E*n)) (x : ZMod n) :
    affine E n t x + ((q:ℤ)*((i:ℤ)-j) : ℤ) ∈ Set.range (affine E n t) ↔
      i%(E/E.gcd q) = j%(E/E.gcd q) := by
  constructor
  · rintro ⟨z,hz⟩
    have eq := congrArg (ZMod.castHom (dvd_mul_right E n) (ZMod E)) hz
    rw [map_add, residue_affine, residue_affine, map_intCast] at eq
    apply (cast_zero_step hE ..).1
    simpa using (show ((((q:ℤ)*((i:ℤ)-j):ℤ) : ZMod E)) = 0 from by simpa using eq.symm)
  · intro h
    let v : ℤ := (q/E.gcd q : ℕ) * ((i/(E/E.gcd q):ℕ)-(j/(E/E.gcd q):ℕ):ℤ)
    refine ⟨x+(v:ZMod n), ?_⟩
    simp only [affine, map_add, dilation_int, ← add_assoc]
    rw [step_formula E q i j h]

theorem derivative {E : ℕ} (hE : 0<E) (n q i j : ℕ) (t : ZMod (E*n))
    (F : ZMod n → ℝ) (y : ZMod (E*n)) :
    extend E n t F y * extend E n t F (y+((q:ℤ)*((i:ℤ)-j):ℤ)) =
      if i%(E/E.gcd q) = j%(E/E.gcd q) then
        extend E n t (fun x => F x * F (x + ((q/E.gcd q:ℕ)*((i/(E/E.gcd q):ℕ)-(j/(E/E.gcd q):ℕ):ℤ):ℤ))) y
      else 0 := by
  classical
  by_cases hy : y ∈ Set.range (affine E n t)
  · obtain ⟨x,rfl⟩ := hy
    rw [extend_affine hE]
    by_cases h : i%(E/E.gcd q) = j%(E/E.gcd q)
    · rw [ite_eq_left h, extend_affine hE]
      congr 1
      let v : ℤ := (q/E.gcd q:ℕ)*((i/(E/E.gcd q):ℕ)-(j/(E/E.gcd q):ℕ):ℤ)
      have eq : affine E n t x + ((q:ℤ)*((i:ℤ)-j):ℤ) = affine E n t (x+(v:ZMod n)) := by
        simp only [affine, map_add, dilation_int, ← add_assoc]
        rw [step_formula E q i j h]
      rw [eq, extend_affine hE]
    · rw [ite_eq_right h, extend_eq_zero (fun m => h ((shifted_mem_iff hE n q i j t x).1 m)),mul_zero]
  · by_cases h : i%(E/E.gcd q) = j%(E/E.gcd q)
    · simp only [ite_eq_left h, extend_eq_zero hy, zero_mul]
    · simp only [ite_eq_right h, extend_eq_zero hy, zero_mul]

end
end Sun28.AffinePullback

#print axioms Sun28.AffinePullback.dilation_injective
#print axioms Sun28.AffinePullback.same_residue
#print axioms Sun28.AffinePullback.step_formula
#print axioms Sun28.AffinePullback.shifted_mem_iff
#print axioms Sun28.AffinePullback.derivative
