import ElementaryMertens
import NumericalEuler

namespace Sun28.RayDensity
open Finset
noncomputable section

def both (q : ℕ) : ℝ := 1-4/((q:ℝ)-1)
def plusInv (q : ℕ) : ℝ := 1+(q:ℝ)⁻¹

theorem local_logs {p : ℕ} (big : 11≤p) : 0<both p ∧
    -(48/(p:ℝ)^2) ≤ Real.log (both p)+4*Real.log (plusInv p) := by
  let x : ℝ := p
  have x11 : 11≤x := by dsimp [x];exact_mod_cast big
  have xp : 0<x := by linarith
  have m1 : 0<x-1 := by linarith
  have m5 : 0<x-5 := by linarith
  have p1 : 0<x+1 := by linarith
  have f : both p=(x-5)/(x-1) := by change 1-4/(x-1)=_;field_simp;ring
  have g : plusInv p=(x+1)/x := by change 1+x⁻¹=_;field_simp
  have bf : 0<both p := f ▸ div_pos m5 m1
  have bg : 0<plusInv p := g ▸ div_pos p1 xp
  refine ⟨bf,?_⟩
  have h1:=Real.one_sub_inv_le_log_of_pos bf
  have h2:=Real.one_sub_inv_le_log_of_pos bg
  rw [f,inv_div] at h1
  rw [g,inv_div] at h2
  rw [f,g]
  apply le_trans _ (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ)≤4)))
  change -(48/x^2)≤1-(x-1)/(x-5)+4*(1-x/(x+1))
  field_simp
  nlinarith only [mul_nonneg (sub_nonneg.mpr x11) (show 0≤x+3 by linarith)]

/-- Product over any set of the new primes; no analytic prime-distribution premise. -/
theorem two_sign_product {L : ℕ} (large : 2≤L) (P : Finset ℕ)
    (primes : ∀ p∈P,p.Prime ∧ 11≤p ∧ p≤L) :
    Real.exp (-48)/(2*(1+4*Real.log L))^4 ≤ ∏ p∈P,both p := by
  let D := 2*(1+4*Real.log (L:ℝ))
  let U := ∏ p∈P, plusInv p
  let B := ∏ p∈P, both p
  have lgn := Real.log_nonneg (by exact_mod_cast (show 1≤L by omega) : 1≤(L:ℝ))
  have dp : 0<D := by dsimp [D];linarith
  have u (p : ℕ) : 0<plusInv p := by dsimp [plusInv];positivity
  have b (p : ℕ) (hp : p∈P) := (local_logs (primes p hp).2.1).1
  have up : 0<U := prod_pos (fun p _ => u p)
  have bp : 0<B := prod_pos b
  have um : U≤D := squarefree_product large P (fun p h=>⟨(primes p h).1,(primes p h).2.2⟩)
  have out : 1∉P := by intro h;have hn := (primes 1 h).2.1;omega
  have err:=Sun28.ConeEuler.error_budget (insert 1 P) (by norm_num : (0:ℝ)≤48)
  rw [sum_insert out] at err
  norm_num at err
  have err' : (∑ p∈P,48/(p:ℝ)^2)≤48 := by
    linarith only [err,Sun28.ConeEuler.Elementary.squareSum_le_two]
  have all:=sum_le_sum (fun p hp=>(local_logs (primes p hp).2.1).2)
  rw [sum_neg_distrib,sum_add_distrib,←mul_sum,←Real.log_prod (fun p h=>(b p h).ne'),
      ←Real.log_prod (fun p _=>(u p).ne')] at all
  have lb : -48≤Real.log B+4*Real.log D := by
    change -(∑ p∈P,48/(p:ℝ)^2)≤Real.log B+4*Real.log U at all
    linarith only [Real.log_le_log up um,all,err']
  have ex:=Real.exp_le_exp.mpr lb
  rw [Real.exp_add,Real.exp_log bp,show (4:ℝ)=((4:ℕ):ℝ) from rfl,Real.exp_nat_mul,Real.exp_log dp] at ex
  exact (div_le_iff₀ (pow_pos dp _)).mpr ex

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.local_logs
#print axioms Sun28.RayDensity.two_sign_product
