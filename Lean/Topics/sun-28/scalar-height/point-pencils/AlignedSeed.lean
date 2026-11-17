import GaussianCentres

/-! A pigeonhole construction of a Gaussian divisor of a primitive norm,
with the orientation fixed modulo its norm, even for composite squarefree d. -/
namespace Sun28.PointPencils

/-- Small lattice representatives for the homogeneous congruence ub=va mod d. -/
theorem short_vector (a b : ℤ) (d : ℕ) (hd : d≠0) :
    ∃ u v : ℤ, (u≠0 ∨ v≠0) ∧
      |u| ≤(d.sqrt:ℤ) ∧ |v| ≤(d.sqrt:ℤ) ∧ (d:ℤ) ∣ u*b-v*a := by
  let _ : NeZero d:=⟨hd⟩
  let F:=Fin (d.sqrt+1) × Fin (d.sqrt+1)
  let f (x:F) : ZMod d := (x.1.val:ZMod d)*b-(x.2.val:ZMod d)*a
  have sz : Fintype.card (ZMod d)<Fintype.card F := by
    simp only [F,ZMod.card,Fintype.card_prod,Fintype.card_fin]
    simpa only [sq] using Nat.lt_succ_sqrt' d
  obtain ⟨x,y,ne,eq⟩:=Fintype.exists_ne_map_eq_of_card_lt f sz
  let u:ℤ:=(x.1.val:ℤ)-y.1.val
  let v:ℤ:=(x.2.val:ℤ)-y.2.val
  have small (i j : Fin (d.sqrt+1)) : |(i.val:ℤ)-j.val| ≤(d.sqrt:ℤ) := by
    have hi:=i.isLt
    have hj:=j.isLt
    exact abs_le.mpr (by omega)
  refine ⟨u,v,?_,small ..,small ..,(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp ?_⟩
  · by_contra! eq0
    apply ne
    apply Prod.ext <;> apply Fin.ext
    · dsimp only [u] at eq0;omega
    · dsimp only [v] at eq0;omega
  · dsimp only [u,v]
    push_cast
    dsimp only [f] at eq
    linear_combination eq

private theorem sqrt_sq_lt {d : ℕ} (sf : Squarefree d) (nd : d≠1) :
    d.sqrt^2<d := by
  refine lt_of_le_of_ne (Nat.sqrt_le' d) ?_
  intro eq
  have unit:=sf d.sqrt (by rw [←sq,eq])
  have one : d.sqrt=1:=Nat.isUnit_iff.mp unit
  exact nd (by rw [←eq,one];norm_num)

private theorem coprime_den (a b : ℤ) (cop : IsCoprime a b) {d : ℤ}
    (de : d ∣ a^2+b^2) : IsCoprime d b := by
  have h : IsCoprime (a^2+b^2) b := by
    have h' := (show IsCoprime (a^2) b from cop.pow_left).add_mul_left_left b
    simpa only [←sq b] using h'
  exact h.of_isCoprime_of_dvd_left de

/-- The normalized components (Ua+Vb)/d and (Ub−Va)/d are integral
simultaneously. The input direction determines the permissible orientations. -/
theorem aligned_seed (a b : ℤ) (cop : IsCoprime a b) (d : ℕ) (sf : Squarefree d)
    (de : (d:ℤ) ∣ a^2+b^2) :
    ∃ u v : ℤ, u^2+v^2=(d:ℤ) ∧ (d:ℤ)∣u*b-v*a ∧ (d:ℤ)∣u*a+v*b := by
  by_cases unit : d=1
  · subst d; exact ⟨1,0,by norm_num,by simp,by simp⟩
  obtain ⟨u,v,nonzero,hu,hv,dk⟩:=short_vector a b d sf.ne_zero
  let D:ℤ:=d
  have hd : 0<D := by dsimp [D];exact_mod_cast Nat.pos_of_ne_zero sf.ne_zero
  have copB:=coprime_den a b cop de
  obtain ⟨s,hs⟩:=dk
  obtain ⟨n,hn⟩:=de
  have dp : D ∣ u*a+v*b := by
    apply copB.dvd_of_dvd_mul_right
    refine ⟨a*s+v*n,?_⟩
    linear_combination a*hs+v*hn
  have dq : D ∣ u^2+v^2 := by
    apply copB.dvd_of_dvd_mul_right
    obtain ⟨t,ht⟩:=dp
    refine ⟨u*s+v*t,?_⟩
    linear_combination u*hs+v*ht
  have pos : 0<u^2+v^2 := by
    rcases nonzero with h|h
    · linarith only [sq_pos_of_ne_zero h,sq_nonneg v]
    · linarith only [sq_pos_of_ne_zero h,sq_nonneg u]
  have strict : (d.sqrt:ℤ)^2<D := by dsimp [D];exact_mod_cast sqrt_sq_lt sf unit
  have u2:=mul_self_le_mul_self (abs_nonneg u) hu
  have v2:=mul_self_le_mul_self (abs_nonneg v) hv
  have lt : u^2+v^2<2*D := by nlinarith only [u2,v2,strict,sq_abs u,sq_abs v]
  obtain ⟨k,hk⟩:=dq
  have kn : 0<k := by apply (pos_of_mul_pos_right (hk ▸ pos) hd.le)
  have ke : k<2 := by
    apply lt_of_mul_lt_mul_left (a:=D)
    nlinarith only [hk,lt]
    exact hd.le
  have one : k=1 := by omega
  exact ⟨u,v,by rw [hk,one,mul_one],⟨s,hs⟩,dp⟩

end Sun28.PointPencils
#print axioms Sun28.PointPencils.short_vector
#print axioms Sun28.PointPencils.aligned_seed
