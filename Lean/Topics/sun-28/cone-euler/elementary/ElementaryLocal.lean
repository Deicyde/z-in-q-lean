import EulerPoint
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

namespace Sun28.ConeEuler.Elementary
open Finset ArithmeticFunction
noncomputable section

def chi : ArithmeticFunction ℝ := ⟨fun n => (ZMod.χ₄ (n:ZMod 4):ℤ), by norm_num⟩

def gaussian : ArithmeticFunction ℝ := (zeta:ArithmeticFunction ℝ)*chi
def oneFun : ArithmeticFunction ℝ := (zeta:ArithmeticFunction ℝ)

theorem chi_mult : chi.IsMultiplicative := by
  refine ⟨?_,?_⟩
  · norm_num [chi]
  · intro m n _
    change ((ZMod.χ₄ ((m*n:ℕ):ZMod 4):ℤ):ℝ)=_
    simp [chi,map_mul]

theorem gaussian_mult : gaussian.IsMultiplicative := isMultiplicative_zeta.natCast.mul chi_mult

theorem gaussian_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    gaussian (p^e)=∑ i∈range (e+1), (chi p)^i := by
  unfold gaussian
  rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl;intro i _
  change ((ZMod.χ₄ ((p^i:ℕ):ZMod 4):ℤ):ℝ)=_
  simp [chi,map_pow]

theorem gaussian_bounds {p : ℕ} (hp : p.Prime) (e : ℕ) :
    0≤gaussian (p^e) ∧ gaussian (p^e)≤e+1 := by
  rw [gaussian_pow hp]
  have vals : chi p=0 ∨ chi p=1 ∨ chi p= -1 := by
    dsimp [chi]
    rcases ZMod.isQuadratic_χ₄ (p:ZMod 4) with a|a|a
    · left;exact_mod_cast a
    · right;left;exact_mod_cast a
    · right;right;exact_mod_cast a
  rcases vals with h|h|h
  · simp [h, sum_range_succ']
  · simp [h];positivity
  · rw [h,neg_one_geom_sum];split_ifs <;> constructor <;> first | positivity | linarith [Nat.cast_nonneg (α:=ℝ) e]

theorem gaussian_nonneg (n : ℕ) : 0≤gaussian n := by
  rcases eq_or_ne n 0 with rfl|nz
  · simp
  · rw [gaussian_mult.multiplicative_factorization _ nz]
    exact prod_nonneg fun p hp=>(gaussian_bounds (Nat.prime_of_mem_primeFactors hp) _).1

def weight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n=>f n/n,by simp⟩

theorem weight_mult {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) : (weight f).IsMultiplicative := by
  refine ⟨?_,?_⟩
  · simp [weight,hf.1]
  · intro m n cop
    change f (m*n)/((m*n:ℕ):ℝ)=f m/m*(f n/n)
    rw [hf.2 cop,Nat.cast_mul];ring

theorem tail_geometric (e : ℕ) :
    (∑ j∈range e,((j:ℝ)+3)/(2:ℝ)^j)+(2*e+8)/(2:ℝ)^e=8 := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    rw [sum_range_succ,pow_succ,Nat.cast_succ]
    have eqn : ((e:ℝ)+3)/2^e+(2*((e:ℝ)+1)+8)/(2^e*2)=(2*e+8)/2^e := by ring
    linarith only [ih,eqn]

theorem local_majorant (v : ℕ→ℝ) {p : ℕ} (hp : p.Prime) (v0 : v 0=1)
    (nn : ∀ j,0≤v j) (bd : ∀ j,v j≤((j:ℝ)+1)/(p:ℝ)^j) (e : ℕ) :
    (∑ j∈range (e+1),v j) ≤ 1 + v 1 + 8/(p:ℝ)^2 := by
  have pp : (0:ℝ)<p := by exact_mod_cast hp.pos
  have two : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have tail : ∀ j : ℕ,v (j+1+1)≤(((j:ℝ)+3)/2^j)/(p:ℝ)^2 := by
    intro j
    apply (bd _).trans
    push_cast
    rw [show (p:ℝ)^(j+1+1)=p^j*p^2 by ring]
    rw [div_div]
    rw [show (j:ℝ)+1+1+1=j+3 by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) two j) (sq_nonneg _))
  have sum:=Finset.sum_le_sum (s:=range e) (fun j _=>tail j)
  rw [←sum_div] at sum
  have s : (∑ j∈range e,((j:ℝ)+3)/2^j)≤8 :=
    (le_add_of_nonneg_right (by positivity : 0≤(2*(e:ℝ)+8)/2^e)).trans_eq (tail_geometric e)
  have ht:=div_le_div_of_nonneg_right s (sq_nonneg (p:ℝ))
  have ext : (∑ j∈range (e+1),v j) ≤ ∑ j∈range (e+1+1),v j := by
    rw [sum_range_succ (f:=v) (e+1)];linarith only [nn (e+1)]
  have eq : (∑ j∈range (e+1+1),v j)=(∑ j∈range e,v (j+1+1))+v 1+1 := by
    rw [sum_range_succ' (f:=v) (e+1),sum_range_succ' (f:=fun i=>v (i+1)) e,v0]
  linarith only [sum,ht,ext,eq]

end
end Sun28.ConeEuler.Elementary
#print axioms Sun28.ConeEuler.Elementary.gaussian_mult
#print axioms Sun28.ConeEuler.Elementary.gaussian_pow
#print axioms Sun28.ConeEuler.Elementary.gaussian_bounds
#print axioms Sun28.ConeEuler.Elementary.gaussian_nonneg
#print axioms Sun28.ConeEuler.Elementary.weight_mult
#print axioms Sun28.ConeEuler.Elementary.tail_geometric
#print axioms Sun28.ConeEuler.Elementary.local_majorant
