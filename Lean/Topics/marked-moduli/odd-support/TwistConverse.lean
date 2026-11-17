import FixedCover

/-! Recover the signed squarefree kernel from any affine rational point on
a squarefree twist, away from the branch points and the inverse chart pole. -/
open ZInQ ZInQ.Mult
namespace ZInQBlueprint.OddSupport
noncomputable section

theorem inverse_parity {x y : ℚ} {d : ℤ} (hd : Squarefree d) (ny : y≠0) (nx : x≠5)
    (point : 30*(d:ℚ)*y^2=quintic x) :
    let u : ℚ := 120/(x-5)
    u ∉ contactSet ∧ X u=x ∧
      ∀ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → 5<p →
         (p ∣ d.natAbs ↔ p ∣ contactSupport S u) := by
  dsimp only
  let u : ℚ := 120/(x-5)
  have hu0 : u≠0 := div_ne_zero (by norm_num) (sub_ne_zero.mpr nx)
  have hx : X u=x := by simp only [X,u]; field_simp [sub_ne_zero.mpr nx]; ring
  have hdq : (d:ℚ)≠0 := by exact_mod_cast hd.ne_zero
  have id : contactPoly u=(d:ℚ)*(y*u^3/8)^2 := by
    have tr := transform u hu0
    rw [hx,←point] at tr
    linear_combination -tr/1920
  have hr : y*u^3/8≠0 := div_ne_zero (mul_ne_zero ny (pow_ne_zero _ hu0)) (by norm_num)
  have hu : u ∉ contactSet := fun hm => (mul_ne_zero hdq (pow_ne_zero _ hr))
    (id.symm.trans ((contactPoly_eq_zero_iff u).mpr hm))
  refine ⟨hu,hx,?_⟩
  intro S p hp hS h5
  have : Fact p.Prime := ⟨hp⟩
  rw [prime_dvd_contactSupport_iff' hu hp,←odd_poly_iff hu h5,squarefree_odd_order hd,id,
    padicValRat.mul hdq (pow_ne_zero _ hr),padicValRat.pow]
  rw [and_iff_right hS]
  constructor
  · rintro ⟨k,e⟩
    exact ⟨k+padicValRat p (y*u^3/8),by push_cast; omega⟩
  · rintro ⟨k,e⟩
    exact ⟨k-padicValRat p (y*u^3/8),by push_cast at e; omega⟩

/-- Recovering a rational point recovers precisely the original signed
squarefree integer, including its sign. -/
theorem inverse_kernel {x y : ℚ} {d : ℤ} (hd : Squarefree d) (ny : y≠0) (nx : x≠5)
    (point : 30*(d:ℚ)*y^2=quintic x) :
    ∃ e : ℤ, IsKernel (120/(x-5)) d e := by
  let u : ℚ := 120/(x-5)
  obtain ⟨hu,hx,_⟩ := inverse_parity hd ny nx point
  obtain ⟨k,e,hk⟩ := exists_kernel u
  have uk : k ≠ 0 := (Kernel_nonzero hu hk).1
  have hsq : (k:ℚ)*(8*(e:ℚ)/(u.num:ℚ)^3)^2=(d:ℚ)*y^2 := by
    obtain ⟨eq,_,_,_⟩ := twist_point hu hk
    rw [hx] at eq
    linarith [eq,point]
  have ek : 8*(e:ℚ)/(u.num:ℚ)^3 ≠ 0 := (twist_point hu hk).2.1
  have dq : (d:ℚ)≠0 := by exact_mod_cast hd.ne_zero
  have kq : (k:ℚ)≠0 := by exact_mod_cast uk
  have primes : k.natAbs.primeFactors=d.natAbs.primeFactors := by
    ext p
    rw [Nat.mem_primeFactors_of_ne_zero (by simpa using uk),Nat.mem_primeFactors_of_ne_zero (by simpa using hd.ne_zero)]
    apply and_congr_right
    intro hp
    have : Fact p.Prime := ⟨hp⟩
    rw [squarefree_odd_order hk.1,squarefree_odd_order hd]
    have val := congrArg (padicValRat p) hsq
    rw [padicValRat.mul kq (pow_ne_zero _ ek),padicValRat.mul dq (pow_ne_zero _ ny),
      padicValRat.pow,padicValRat.pow] at val
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a+padicValRat p (8*(e:ℚ)/(u.num:ℚ)^3)-padicValRat p y,by push_cast at val; omega⟩
    · rintro ⟨a,ha⟩
      exact ⟨a-padicValRat p (8*(e:ℚ)/(u.num:ℚ)^3)+padicValRat p y,by push_cast at val; omega⟩
  have ab : k.natAbs=d.natAbs := by
    rw [←Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hk.1),primes,
      Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hd)]
  have sign : k=d := by
    obtain a|a := Int.natAbs_eq_natAbs_iff.mp ab
    · exact a
    · by_contra h
      have eq0 : ((k:ℚ))*((8*(e:ℚ)/(u.num:ℚ)^3)^2+y^2)=0 := by
        rw [a] at hsq ⊢
        push_cast at hsq ⊢
        linarith
      have zero := (mul_eq_zero.mp eq0).resolve_left kq
      nlinarith [sq_pos_of_ne_zero ny,sq_nonneg (8*(e:ℚ)/(u.num:ℚ)^3)]
  exact ⟨e,sign ▸ hk⟩

#print axioms inverse_parity
#print axioms inverse_kernel
end
end ZInQBlueprint.OddSupport
