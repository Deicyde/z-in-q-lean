import CMPointCounts
import ZInQKernel.Density.Description

namespace Sun28.PrimeClasses
open ZInQ ZInQ.Density ManuscriptV15.Arithmetic Sun28.CMReduction

/-- Frobenius trace of the fixed good reduction y²=x³−x at each odd prime. -/
noncomputable def traceAt (p : ℕ) : ℤ := (p : ℤ)+1-(pointCount p (-1) : ℤ)

/-- The sign with odd coordinate congruent to one modulo four. -/
noncomputable def root (p : ℕ) : ℤ :=
  if (traceAt p/2)%4=1 then traceAt p/2 else -(traceAt p/2)

theorem trace_alternatives {p : ℕ} [Fact p.Prime] (h : InClass p) :
    traceAt p=2*cp p ∨ traceAt p= -(2*cp p) := by
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mpr (by have := h.mod_four; omega)
  have nz : i≠0 := by rintro rfl; simp at hi
  have coeff : (-1:ZMod p) = i^2*1 := by simpa [sq] using hi
  unfold traceAt
  rw [pointCount_eq h.ne_two,coeff,jac_sq_mul nz,jac_one_eq h.ne_two]
  rcases quadraticChar_dichotomy nz with s|s <;> rw [s] <;> omega

theorem root_representation {p : ℕ} [Fact p.Prime] (h : InClass p) :
    (root p)%4=1 ∧ ∃ b : ℤ, (p:ℤ)=(root p)^2+b^2 := by
  have odd := cp_odd h
  obtain ⟨b,hb⟩ := exists_sq_add_sq h
  rcases trace_alternatives h with s|s <;>
    unfold root <;> rw [s] <;> split <;> rename_i cond
  all_goals
    have eq : 2*cp p/2=cp p := by omega
    have eq' : -(2*cp p)/2= -(cp p) := by omega
    constructor
    · omega
    · refine ⟨b,?_⟩
      simp only [eq,eq',neg_sq,neg_neg]; exact hb

theorem root_of_ray {p : ℕ} (pp : p.Prime) {z : Gaussian}
    (hz : gaussianNorm z=p) (h16 : gaussianCongruent 16 z (9,0))
    (h7 : gaussianCongruent 7 z (1,3)) : root p=z.1 := by
  let _ : Fact p.Prime := ⟨pp⟩
  obtain ⟨res,b,rep⟩ := root_representation (selected_class hz h16 h7)
  have norm := archive_norm z
  rw [hz] at norm
  have even : z.2%2=0 := h16.2.of_dvd (by decide : (2:ℤ)∣16)
  have real : z.1%4=1 := h16.1.of_dvd (by decide : (4:ℤ)∣16)
  rcases odd_coordinate_unique pp norm.symm rep.symm even (by omega) with e|e
  · exact e
  · omega

theorem ray_norms {p : ℕ} (pp : p.Prime) {z : Gaussian} (hz : gaussianNorm z=p)
    (h16 : gaussianCongruent 16 z (9,0)) (h7 : gaussianCongruent 7 z (1,3)) (sign : Bool) :
    (adjacentNorm z sign : ℤ)=(p:ℤ)+1+(if sign then 2*root p else -(2*root p)) := by
  rw [root_of_ray pp hz h16 h7]
  have n := archive_norm z
  rw [hz] at n
  cases sign <;> simp [adjacentNorm,archive_norm,n] <;> ring

end Sun28.PrimeClasses
#print axioms Sun28.PrimeClasses.trace_alternatives
#print axioms Sun28.PrimeClasses.root_representation
#print axioms Sun28.PrimeClasses.root_of_ray
#print axioms Sun28.PrimeClasses.ray_norms
