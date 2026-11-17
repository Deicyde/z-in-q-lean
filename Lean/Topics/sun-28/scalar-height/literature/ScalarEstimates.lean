import ScalarPencil
import ContactHeight

namespace Sun28.ScalarPencil
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.Ordinary Sun28.FiveMarkUnits
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK Height
open private int_height height_div from ContactHeight
noncomputable section
set_option maxRecDepth 8192

theorem data (x:ℚ) :
    let A:=(beta x).num
    let B:ℤ:=(beta x).den
    let T:=heightRadical A B
    ∃ h k v w:ℤ, h≠0 ∧ k≠0 ∧
      (6:ℤ).natAbs.primeFactors⊆support A B ∧
      h.natAbs.primeFactors⊆support A B ∧ k.natAbs.primeFactors⊆support A B ∧
      (6:ℕ)≤2^32*T ∧ h.natAbs≤2^32*T ∧ k.natAbs≤2^32*T ∧
      6*(x.den:ℤ)^2-h*v^2= -4*x.num^2 ∧ 6*(x.den:ℤ)^2-k*w^2= -6*x.num^2 := by
  let A:ℤ:=(beta x).num
  let B:ℤ:=(beta x).den
  let T:=heightRadical A B
  let G:ℤ:=Nat.gcd 2 (x.den^2)
  have g0:0<G:=by dsimp [G];exact_mod_cast Nat.gcd_pos_of_pos_left _ (by decide:0<2)
  have gl:G≤2:=by dsimp [G];exact_mod_cast Nat.le_of_dvd (by decide:0<2) (Nat.gcd_dvd_left 2 (x.den^2))
  obtain ⟨v,w,_,_,e₁,e₂⟩:=integer_pencil x
  have off:=beta_off_forms x
  have live (i:Fin 5):kernel i A B≠0:=(sqfInt_spec (off i)).1.ne_zero
  have cpos (s:ℤ) (a : 2 ≤ s) (b : s ≤ 3):0<s*G∧(s*G).natAbs≤6:=by
    have m:=mul_le_mul_of_nonneg_right b g0.le
    have l:3*G≤6:=by omega
    have pos:0<s*G:=mul_pos (by omega) g0
    refine ⟨pos,?_⟩
    exact_mod_cast (show ((s*G).natAbs:ℤ) ≤ 6 by simp only [Int.natCast_natAbs,abs_of_pos pos]; exact m.trans l)
  have d₂:=cpos 2 (by decide) (by decide)
  have d₃:=cpos 3 (by decide) (by decide)
  have scale (c:ℤ) (i:Fin 5) (b:c.natAbs≤6):
      (c*kernel i A B).natAbs≤2^32*T:=by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (b.trans (by decide)) (kernel_bound off i)
  have one:1≤T:=Nat.mul_pos pos_cutoff (pos_odd A B)
  have six:(6:ℤ).natAbs.primeFactors⊆support A B:=by
    intro p hp
    have h:p≤6:=Nat.le_of_dvd (by decide) (Nat.dvd_of_mem_primeFactors hp)
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),Nat.prime_of_mem_primeFactors hp⟩)
  exact ⟨2*G*kernel 1 A B,3*G*kernel 2 A B,v,w,mul_ne_zero d₂.1.ne' (live 1),
    mul_ne_zero d₃.1.ne' (live 2),six,coefficient_support x d₂.1.ne' d₂.2,coefficient_support x d₃.1.ne' d₃.2,
    (show (6:ℕ)≤2^32*1 by decide).trans (Nat.mul_le_mul_left _ one),scale _ _ d₂.2,scale _ _ d₃.2,e₁,e₂⟩

theorem shifted_log {a:ℤ} (ha:a≠0) (n:ℤ) (ln:n≠0) (cap:n.natAbs≤6) :
    numberLog (n*a^2)≤2*numberLog a+6 := by
  have p:(0:ℝ)<n.natAbs:=by exact_mod_cast Int.natAbs_pos.mpr ln
  have h:((n.natAbs:ℕ):ℝ)≤6:=by exact_mod_cast cap
  rw [sq,log_mul_int ln (mul_ne_zero ha ha),log_mul_int ha ha]
  change Real.log (n.natAbs:ℝ)+_≤_
  linarith only [Real.log_le_sub_one_of_pos p,h]

theorem beta_height (x:ℚ) : logHeight₁ (beta x)≤2*logHeight₁ x+4:=by
  have p:=logHeight₁_mul_le (2:ℚ) (x^2)
  have q:=logHeight₁_add_le (2*x^2) (3:ℚ)
  have wt:(totalWeight ℚ:ℝ)=1:=by rw [NumberField.totalWeight_eq_finrank];simp
  have two:logHeight₁ (2:ℚ)=Real.log 2:=by rw [Rat.logHeight₁_eq_log_max];norm_num
  have three:logHeight₁ (3:ℚ)=Real.log 3:=by rw [Rat.logHeight₁_eq_log_max];norm_num
  rw [two,logHeight₁_pow] at p
  rw [wt,one_mul,three] at q
  norm_num at p
  unfold beta
  linarith only [p,q,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2),Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<3)]

theorem frac_height {x:ℚ} {a:ℤ} {t:ℚ} (na:a≠0) (eq:x=(a:ℚ)/t) :
    logHeight₁ (beta x)≤2*numberLog a+2*logHeight₁ t+4:=by
  have h:=height_div (a:ℚ) t
  rw [←eq,int_height na] at h
  linarith only [beta_height x,h]

theorem denominator_log (pell:PublishedPell312) (regulator:Regulator35)
    (disc:ConductorDiscriminants) (x:ℚ) (nonzero:x≠0) :
    let T:ℝ:=heightRadical (beta x).num (beta x).den
    numberLog (x.den:ℤ)≤2^170*T^2*(ell T)^7+2^160*T*(ell T)^4*(2*numberLog x.num+6) := by
  let A:ℤ:=(beta x).num
  let B:ℤ:=(beta x).den
  let T:ℝ:=heightRadical A B
  obtain ⟨h,k,v,w,nh,nk,s₀,s₁,s₂,b₀,b₁,b₂,e₁,e₂⟩:=data x
  have a:=Rat.num_ne_zero.mpr nonzero
  have aa:0<x.num^2:=sq_pos_of_ne_zero a
  have t:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  apply integral_pell pell regulator disc (S:=support A B) (fun _ hp=>support_primes hp)
    (a:=(x.den:ℤ)) (b:=v) (c:=w) t (congrArg (fun n:ℕ=>(n:ℝ)) (product_support A B))
    (by linarith only [nonneg_numberLog a]) (by decide: (6:ℤ)≠0) nh nk s₀ s₁ s₂
    (by change (6:ℝ)≤2^32*T;simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr b₀)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr b₁)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr b₂)
    (mul_ne_zero (by decide: (-4:ℤ)≠0) aa.ne') (mul_ne_zero (by decide: (-6:ℤ)≠0) aa.ne') (by omega)
    (shifted_log a (-4) (by decide) (by decide)) (shifted_log a (-6) (by decide) (by decide)) e₁ e₂

end
end Sun28.ScalarPencil
#print axioms Sun28.ScalarPencil.data
#print axioms Sun28.ScalarPencil.shifted_log
#print axioms Sun28.ScalarPencil.beta_height
#print axioms Sun28.ScalarPencil.frac_height
#print axioms Sun28.ScalarPencil.denominator_log
