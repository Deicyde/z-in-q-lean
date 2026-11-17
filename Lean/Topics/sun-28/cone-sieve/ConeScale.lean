import ConeRecords

namespace Sun28.ConeSieve
open Finset Sun28.SinglePrime Sun28.MediumSieve Sun28.ContactFactors
open Sun28.WeightedSelection Sun28.SieveTail Filter Topology
noncomputable section

def level (t : ℕ) := 2^t

theorem level_pos (t : ℕ) : 0<level t := by unfold level;positivity

/-- At fixed sufficiently narrow aspect ratio every actual prime value exceeds the sieve level. -/
theorem values_above_level {A : Fin 3→ℚ} {d j t : ℕ} {H Y : ℝ}
    (narrow : 8*(maxCoefficient A+1)≤j+1) (ht : 1≤t)
    {a : Candidate A d H Y} (ha : a∈box (lengthAt t) (rowWidth j (lengthAt t)))
    (k : ↥(shifts A)) : level t < a.values.value k.val := by
  let B:=side t
  let W:=rowWidth j (lengthAt t)
  let M:=maxCoefficient A
  have step : W*(j+1)≤B := by
    dsimp [W,rowWidth,lengthAt,B];rw [Nat.sqrt_eq' _];exact Nat.div_mul_le_self _ _
  have wb : W≤B := (Nat.le_mul_of_pos_right _ (by omega : 0<j+1)).trans step
  have wm : 4*M*W≤B := (show (4*M)*W≤(j+1)*W from Nat.mul_le_mul_right W (by dsimp [M];omega)).trans (by simpa [Nat.mul_comm] using step)
  have quad : 4*M*W^2≤lengthAt t := by
    change _ ≤ B^2; simpa [pow_two,Nat.mul_assoc] using Nat.mul_le_mul wm wb
  obtain ⟨low,_,v⟩:=box_mem ha
  have mul : 4*M*a.v^2≤lengthAt t := (Nat.mul_le_mul_left (4*M) (Nat.pow_le_pow_left v 2)).trans quad
  have lowInt : (lengthAt t:ℤ)<2*(a.u:ℤ) := by exact_mod_cast low
  have mulInt : 4*(M:ℤ)*(a.v:ℤ)^2≤(lengthAt t:ℤ) := by exact_mod_cast mul
  have c : -(M:ℤ)≤offset (dilation A) k.val := by
    have h := le_sup (f:=fun r : ↥(shifts A)=>(offset (dilation A) r.val).natAbs) (mem_univ k)
    have h' : |offset (dilation A) k.val|≤(M:ℤ) := by rw [←Int.natCast_natAbs]; exact_mod_cast h
    exact (abs_le.mp h').1
  have lower := mul_le_mul_of_nonneg_right c (sq_nonneg (a.v:ℤ))
  have lev : 4*level t ≤ lengthAt t := by
    rw [length_pow];unfold level
    rw [show (4:ℕ)=2^2 by decide,←pow_add];apply Nat.pow_le_pow_right (by decide);omega
  have levInt : 4*(level t:ℤ) ≤ (lengthAt t:ℤ) := by exact_mod_cast lev
  have eq:=a.values.equation k.val k.property
  exact_mod_cast (show (level t:ℤ)<(a.values.value k.val:ℤ) by linarith only [eq,levInt,mulInt,lowInt,lower])

/-- The level is B^(1/200) at side B. Four extra level factors cost 2^(4t). -/
theorem power_budget (t : ℕ) :
    (level t:ℝ)^4 * (2:ℝ)^(559*t) ≤ (2:ℝ)^(599*t) := by
  unfold level;push_cast;rw [←pow_mul,←pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2);omega

/-- Tenth power of the rank-five congruence error at exponent 5/2+1/10.
The two moduli are the collision prime and the auxiliary squarefree part. -/
theorem congruence_power {t p d : ℕ} (hp : p≤level t) (hd : d≤(level t)^2) :
    (side t * (p*d))^26 ≤ (2^(528*t):ℕ)^10 := by
  have mul := Nat.mul_le_mul_left (side t) (Nat.mul_le_mul hp hd)
  apply (Nat.pow_le_pow_left mul 26).trans
  unfold side level
  rw [←pow_mul,←pow_add,←pow_add,←pow_mul,←pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  omega

/-- Integer rounding on a sufficiently wide dyadic row costs at most a factor of two. -/
theorem error_on_row {t j : ℕ} (wide : j+1 ≤ side t) {E C : ℝ}
    (non : 0≤C) (err : E≤C*(2:ℝ)^(559*t)) :
    (level t:ℝ)^4*E ≤ (2*((j:ℝ)+1)*C)*((lengthAt t:ℝ)*rowWidth j (lengthAt t))/(2:ℝ)^t := by
  let W:=rowWidth j (lengthAt t)
  have width : W = side t/(j+1) := by dsimp [W,rowWidth,lengthAt];rw [Nat.sqrt_eq' _]
  have wb : 1≤W := by rw [width];exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using wide)
  have floors : side t≤2*((j+1)*W) := by
    have h:=Nat.mod_add_div (side t) (j+1)
    have lt:=Nat.mod_lt (side t) (by omega : 0<j+1)
    have pos:=Nat.mul_le_mul_left (j+1) wb
    rw [←width] at h
    nlinarith only [h,lt,pos]
  have bound : (side t:ℝ) ≤ 2*(((j:ℝ)+1)*W) := by exact_mod_cast floors
  have full : (2:ℝ)^(599*t)*(2:ℝ)^t = (lengthAt t:ℝ)*(side t:ℝ) := by
    rw [length_pow];unfold side;push_cast;rw [←pow_add,←pow_add];congr 1;omega
  apply (le_div_iff₀ (by positivity : 0<(2:ℝ)^t)).mpr
  calc _ ≤ ((level t:ℝ)^4*(C*(2:ℝ)^(559*t)))*(2:ℝ)^t := by gcongr
       _ = C*(((level t:ℝ)^4*(2:ℝ)^(559*t))*(2:ℝ)^t) := by ring
       _ ≤ C*((2:ℝ)^(599*t)*(2:ℝ)^t) := by gcongr;exact power_budget t
       _ ≤ C*((lengthAt t:ℝ)*(2*(((j:ℝ)+1)*W))) := by rw [full];gcongr
       _ = _ := by dsimp [W];ring

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.values_above_level
#print axioms Sun28.ConeSieve.power_budget
#print axioms Sun28.ConeSieve.congruence_power
#print axioms Sun28.ConeSieve.error_on_row
