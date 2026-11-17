import RowWeight

namespace Sun28.ConeReal
open Sun28.QuadricSieve Sun28.ConeSieve Sun28.SinglePrime Sun28.WeightedSelection Sun28.SieveTail
  Sun28.ContactFactors Sun28.MediumSieve Finset
open scoped Classical
noncomputable section

def scaled (B : ℕ) (x : Coordinates ℤ) : Coordinates ℝ :=
  (((x.1.1:ℝ)/B,(x.1.2:ℝ)/B),((x.2.1.1:ℝ)/B,(x.2.1.2:ℝ)/B),(x.2.2:ℝ)/B)

private theorem shift_bound {A : Fin 3→ℚ} (i : ↥(shifts A)) :
    -(maxCoefficient A:ℝ) ≤ (offset (dilation A) i.val : ℝ) ∧
      (offset (dilation A) i.val : ℝ) ≤ (maxCoefficient A:ℝ) := by
  have h:=le_sup (f:=fun k : ↥(shifts A)=>(offset (dilation A) k.val).natAbs) (mem_univ i)
  have e : |offset (dilation A) i.val| ≤ (maxCoefficient A:ℤ) := by
    rw [←Int.natCast_natAbs];exact_mod_cast h
  exact_mod_cast abs_le.mp e

private theorem radial_window {B u w c M : ℝ} (hB:0<B) (lo:B^2<2*u) (hi:u≤B^2)
    (hc:-M≤c ∧ c≤M) (win:4*M*w^2≤B^2) :
    (u+c*w^2)/B^2∈Set.Icc (1/4:ℝ) (5/4) := by
  have cl:=mul_le_mul_of_nonneg_right hc.1 (sq_nonneg w)
  have cu:=mul_le_mul_of_nonneg_right hc.2 (sq_nonneg w)
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hB)).mpr;linarith
  · apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr;linarith

theorem lattice_weight {A : Fin 3→ℚ} (j t p : ℕ) [Fact p.Prime] (i k : ↥(shifts A))
    (narrow : 8*(maxCoefficient A+1)≤j+1) {x : Coordinates ℤ}
    (hx : x∈lattice p i k (lengthAt t) (rowWidth j (lengthAt t))) :
    weight j (scaled (side t) x)=1 := by
  let B:=side t
  let W:=rowWidth j (lengthAt t)
  let M:=maxCoefficient A
  let n:=norm1 x
  let v:=x.2.2
  let c:=offset (dilation A) i.val
  let e:=offset (dilation A) k.val
  let u:=n-c*v^2
  have reg:=(mem_filter.mp hx).1
  obtain ⟨box,cone,l,h⟩:=mem_filter.mp reg
  have vin := (mem_Icc.mp (mem_product.mp (mem_product.mp box).2).2)
  change 1≤v ∧ v≤(W:ℤ) at vin
  change (B^2:ℕ)<2*u at l
  change u≤(B^2:ℕ) at h
  have bp : 0<B := by dsimp [B,side];positivity
  have br : 0<(B:ℝ) := by exact_mod_cast bp
  have size : W*(j+1)≤B := by dsimp [W,rowWidth,lengthAt,B];rw [Nat.sqrt_eq' _];exact Nat.div_mul_le_self _ _
  have wb : W≤B := (Nat.le_mul_of_pos_right _ (by omega : 0<j+1)).trans size
  have mb : 4*M*W≤B := (Nat.mul_le_mul_right W (by dsimp [M];omega : 4*M≤j+1)).trans (by simpa [Nat.mul_comm] using size)
  have mw : 4*M*W^2≤B^2 := by simpa [pow_two,mul_assoc] using Nat.mul_le_mul mb wb
  have vw : v^2≤(W:ℤ)^2 := by nlinarith [mul_nonneg (show 0≤(W:ℤ)-v by linarith [vin.2]) (show 0≤(W:ℤ)+v by linarith [vin.1])]
  have zw : 4*(M:ℤ)*v^2≤(B:ℤ)^2 := (mul_le_mul_of_nonneg_left vw (by positivity)).trans (by exact_mod_cast mw)
  have zz : 4*(M:ℝ)*(v:ℝ)^2≤(B:ℝ)^2 := by exact_mod_cast zw
  have lo : (B:ℝ)^2<2*(u:ℝ) := by exact_mod_cast l
  have hi : (u:ℝ)≤(B:ℝ)^2 := by exact_mod_cast h
  apply plateau
  · convert! radial_window br lo hi (shift_bound i) zz using 1
    dsimp [scaled,rad,u,n,norm1,c,v,B];push_cast;ring
  · have two : x.2.1.1^2+x.2.1.2^2 = u+e*v^2 := by
      dsimp [onCone,gap] at cone
      dsimp [u,n,norm1,c,e,v];linarith
    have real_eq : (x.2.1.1:ℝ)^2+(x.2.1.2:ℝ)^2=(u:ℝ)+(e:ℝ)*(v:ℝ)^2 := by exact_mod_cast two
    have rr:= radial_window br lo hi (shift_bound k) zz
    change ((x.2.1.1:ℝ)/(B:ℝ))^2+((x.2.1.2:ℝ)/(B:ℝ))^2∈_
    rw [div_pow,div_pow,←add_div,real_eq]
    exact rr
  · change |(v:ℝ)/(B:ℝ)| ≤ ((j:ℝ)+1)⁻¹
    rw [abs_of_nonneg (div_nonneg (by exact_mod_cast (show 0≤v by omega)) br.le),←one_div,div_le_div_iff₀ br (by positivity)]
    have vb : v*((j:ℤ)+1)≤(B:ℤ) :=
      (mul_le_mul_of_nonneg_right vin.2 (by positivity)).trans (by exact_mod_cast size)
    have vr : (v:ℝ)*((j:ℝ)+1)≤(B:ℝ) := by exact_mod_cast vb
    simpa using vr

end
end Sun28.ConeReal
#print axioms Sun28.ConeReal.lattice_weight
