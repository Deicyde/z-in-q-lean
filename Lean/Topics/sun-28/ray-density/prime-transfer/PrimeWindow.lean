import FixedClass
import WeightedGrid

namespace Sun28.PrimeTransfer
open Finset Sun28.FinitePattern Sun28.ContactFactors Sun28.PrimeValues
open scoped Classical
noncomputable section
variable {n : ℕ} [NeZero n]

def coefficients (A : Fin 3 → ℚ) : Finset ℤ := (shifts A).image (offset (dilation A))

theorem zero_coefficient (A : Fin 3 → ℚ) : 0 ∈ coefficients A := by
  have shift : (0:ℚ) ∈ shifts A := by
    simpa using shift_mem A 0 (show (0:ℚ)∈Sun28.Ordinary.marks by simp [Sun28.Ordinary.marks])
  exact mem_image.mpr ⟨0,shift,by simp [offset]⟩

/-- The same fixed Gaussian class at every input. The central strip removes cyclic wrap-around. -/
def window (K b V N : ℕ) (x : ZMod n) : ℝ :=
  if N/2 < b+V*x.val ∧ b+V*x.val ≤ N ∧ n ≤ 4*x.val ∧ 4*x.val < 3*n
  then classWeight K (b+V*x.val) else 0

def innerPoint (b V d : ℕ) (p : ℕ × ZMod n) : ℕ × ℕ := (b+V*p.2.val, V*d*p.1)

theorem unwrap {x : ZMod n} {z : ℤ} (lo : n ≤ 4*x.val) (hi : 4*x.val < 3*n)
    (short : 4*z.natAbs ≤ n) :
    (((x + (z:ZMod n)).val:ℕ):ℤ) = x.val+z := by
  have l : -(n:ℤ) ≤ 4*z := by omega
  have u : 4*z ≤ (n:ℤ) := by omega
  have h1 : (0:ℤ) ≤ x.val+z := by omega
  have h2 : (x.val:ℤ)+z < n := by omega
  have red := ZMod.val_intCast (n:=n) ((x.val:ℤ)+z)
  simp only [Int.cast_add,Int.cast_natCast,ZMod.natCast_zmod_val] at red
  simpa only [Int.emod_eq_of_lt h1 h2] using red

private theorem inner_injective {b V d : ℕ} (vpos : 0 < V) (dpos : 0 < d) :
    Function.Injective (innerPoint (n:=n) b V d) := by
  rintro ⟨t,x⟩ ⟨u,y⟩ eq
  have hx : b+V*x.val=b+V*y.val := congrArg Prod.fst eq
  have ht : V*d*t=V*d*u := congrArg Prod.snd eq
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left (by positivity : 0 < V*d) ht)
    (ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left vpos (Nat.add_left_cancel hx)))

/-- A sample on one residue progression and on steps divisible by Vd contributes
its full cyclic weight to the actual numerical prime mass. -/
theorem window_le_base (A : Fin 3 → ℚ) {K b V d N W M : ℕ}
    (vpos : 0 < V) (dpos : 0 < d) (width : V*d*M ≤ W)
    (short : ∀ h ∈ coefficients A, 4*(V*d^2*h.natAbs*M^2) ≤ n)
    (f : ZMod n → ℝ) (fpos : ∀ x, 0 ≤ f x) (dom : ∀ x, f x ≤ window K b V N x) :
    circleMass (coefficients A) f ((V*d^2:ℕ):ZMod n) M ≤ patternMass A d K K N W := by
  classical
  let S := (Icc 1 M) ×ˢ (univ : Finset (ZMod n))
  let H : ZMod n := (V*d^2:ℕ)
  let F (p : ℕ×ZMod n) := ∏ h ∈ coefficients A, f (p.2+H*(h:ZMod n)*(p.1:ZMod n)^2)
  let live := S.filter fun p => F p ≠ 0
  let vals := innerPoint (n:=n) b V d
  let box := ((Ioc (N/2) N ×ˢ Icc 1 W).filter (fun p : ℕ×ℕ => d ∣ p.2))
  have center (p : ℕ×ZMod n) (hp : p∈live) :
      N/2 < b+V*p.2.val ∧ b+V*p.2.val ≤ N ∧ n ≤ 4*p.2.val ∧ 4*p.2.val < 3*n := by
    by_contra h
    have wz : window K b V N p.2=0 := ite_eq_right h
    have fz := le_antisymm ((dom _).trans_eq wz) (fpos _)
    apply (mem_filter.mp hp).2
    apply prod_eq_zero (zero_coefficient A)
    simpa using fz
  have mapped (p : ℕ×ZMod n) (hp : p∈live) : vals p∈box := by
    have time := mem_Icc.mp (mem_product.mp (mem_filter.mp hp).1).1
    have mid := center p hp
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨mid.1,mid.2.1⟩,mem_Icc.mpr ⟨?_,?_⟩⟩,?_⟩
    · exact Nat.mul_pos (Nat.mul_pos vpos dpos) time.1
    · exact (Nat.mul_le_mul_left _ time.2).trans width
    · exact dvd_mul_of_dvd_left (dvd_mul_left d V) _
  have compare (p : ℕ×ZMod n) (hp : p∈live) : F p ≤ patternWeight A K K (vals p) := by
    let h (r : ℚ) := offset (dilation A) r
    rw [show F p=∏ r ∈ shifts A, f (p.2+H*(h r:ZMod n)*(p.1:ZMod n)^2) from
      Finset.prod_image (fun _ ha _ hb e => offset_injective ha hb e)]
    rw [patternWeight,←Finset.prod_attach (shifts A) (fun r => f (p.2+H*(h r:ZMod n)*(p.1:ZMod n)^2))]
    apply prod_le_prod₀ (fun r _ => fpos _) (fun r _ => ?_)
    let z : ℤ := (V:ℤ)*d^2 * h r * (p.1:ℤ)^2
    let y := p.2 + (z:ZMod n)
    have iy : p.2+H*(h r:ZMod n)*(p.1:ZMod n)^2=y := by dsimp [H,y,z]; push_cast; ring
    have mem : h r ∈ coefficients A := mem_image_of_mem _ r.property
    have tM := (mem_Icc.mp (mem_product.mp (mem_filter.mp hp).1).1).2
    have sz : 4*z.natAbs ≤ n := by
      calc
        _ = 4*(V*d^2*(h r).natAbs*p.1^2) := by simp [z,Int.natAbs_mul,Int.natAbs_pow]
        _ ≤ 4*(V*d^2*(h r).natAbs*M^2) := by gcongr
        _ ≤ n := short _ mem
    have mid := center p hp
    have yy : (y.val:ℤ) = p.2.val+z := unwrap mid.2.2.1 mid.2.2.2 sz
    have eq : (b+V*y.val:ℕ) = form A (vals p) r := by
      change ((b+V*y.val:ℕ):ℤ) = ((b+V*p.2.val:ℕ):ℤ)+h r*((V*d*p.1:ℕ):ℤ)^2
      push_cast; rw [yy]; dsimp [z]; ring
    rw [iy,←eq]
    apply (dom y).trans
    unfold window
    split
    next => exact (class_weight_le _ _).2
    next => exact (class_weight_le _ _).1.trans (class_weight_le _ _).2
  have sub : live.image vals ⊆ box := by
    rintro _ hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    exact mapped p hp
  calc
    circleMass (coefficients A) f H M = ∑ p∈live,F p := by
      symm; rw [sum_filter]; apply sum_congr rfl; intro p _
      split <;> simp_all [F]
    _ ≤ ∑ p∈live,patternWeight A K K (vals p) := sum_le_sum compare
    _ = ∑ q∈live.image vals,patternWeight A K K q :=
      (sum_image (fun a _ b _ he => inner_injective vpos dpos he)).symm
    _ ≤ patternMass A d K K N W := sum_le_sum_of_subset_of_nonneg sub (fun q _ _ => base_nonneg _ _ _)

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.zero_coefficient
#print axioms Sun28.PrimeTransfer.unwrap
#print axioms Sun28.PrimeTransfer.window_le_base
