import RowLattice

namespace Sun28.ConeReal
open Sun28.QuadricSieve Sun28.ConeSieve Sun28.SinglePrime Sun28.WeightedSelection Sun28.SieveTail
  Sun28.ContactFactors Sun28.MediumSieve Set Finset
open scoped Classical
noncomputable section

def cube (B : ℕ) : Finset (Coordinates ℤ) :=
  let I:=ConeSieve.interval (2*B)
  (I ×ˢ I) ×ˢ (I ×ˢ I) ×ˢ I

theorem mem_cube_of_weight {j B : ℕ} (hB:0<B) {x:Coordinates ℤ} (hx:weight j (scaled B x)≠0) :
    x∈cube B := by
  have b:=support_norm j (subset_closure (show scaled B x∈Function.support (weight j) from hx))
  have br : 0<(B:ℝ):=by exact_mod_cast hB
  have each (a:ℤ) (h:|(a:ℝ)/(B:ℝ)|≤2) : a∈ConeSieve.interval (2*B) := by
    rw [abs_div,abs_of_pos br,div_le_iff₀ br,abs_le] at h
    apply Finset.mem_Icc.mpr
    exact_mod_cast h
  simp only [scaled,Prod.norm_def,sup_le_iff,Real.norm_eq_abs] at b
  exact mem_product.mpr ⟨mem_product.mpr ⟨each _ b.1.1,each _ b.1.2⟩,
    mem_product.mpr ⟨mem_product.mpr ⟨each _ b.2.1.1,each _ b.2.1.2⟩,each _ b.2.2⟩⟩

def sample (p : ℕ) [Fact p.Prime] (κ : ℤ) (B : ℕ) : Finset (Coordinates ℤ) :=
  (cube B).filter fun x=>onCone κ x ∧ reduction p x∈residues p κ

def majorant {A : Fin 3→ℚ} (j t p : ℕ) [Fact p.Prime] (i k : ↥(shifts A))
    (narrow : 8*(maxCoefficient A+1)≤j+1) :
    Majorant p i k (lengthAt t) (rowWidth j (lengthAt t)) where
  support := sample p (gap i k) (side t)
  weight x := weight j (scaled (side t) x)
  nonneg x _ := (weight_bounds _ _).1
  contains x hx := by
    have one:=lattice_weight j t p i k narrow hx
    have cube':x∈cube (side t):=mem_cube_of_weight (by unfold side;positivity) (by rw [one];norm_num)
    obtain ⟨reg,_,mod⟩:=mem_filter.mp hx
    exact mem_filter.mpr ⟨cube',(mem_filter.mp reg).2.1,mod⟩
  majorizes x hx := (lattice_weight j t p i k narrow hx).ge

theorem off_cube {j B : ℕ} (hB:0<B) {x:Coordinates ℤ} (hx:x∉cube B) :
    weight j (scaled B x)=0 := by
  by_contra h;exact hx (mem_cube_of_weight hB h)

end
end Sun28.ConeReal
#print axioms Sun28.ConeReal.mem_cube_of_weight
#print axioms Sun28.ConeReal.majorant
#print axioms Sun28.ConeReal.off_cube
