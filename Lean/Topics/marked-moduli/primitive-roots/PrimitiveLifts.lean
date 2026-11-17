import ClusterRoots
import WittBasis

/-! Three distinct linear factors of each residual cubic are enough to lift the full sextic. -/
namespace ZInQBlueprint.PrimitiveLifts
open Polynomial IsLocalRing ZInQBlueprint.ClusterRoots ZInQBlueprint.HenselTriples
noncomputable section

variable {K : Type*} [Field K]

structure SimpleTriple (P : K[X]) where
  x : Fin 3 → K
  distinct : Function.Injective x
  roots : ∀ j, P.eval (x j)=0
  simple : ∀ j, P.derivative.eval (x j) ≠ 0

def linearProduct (A x y z : K) : K[X] := C A * (X-C x) * (X-C y) * (X-C z)

theorem three_linear {A x y z : K} (hA : A ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : Nonempty (SimpleTriple (linearProduct A x y z)) := by
  refine ⟨⟨![x,y,z], ?_, ?_, ?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hxy,Ne.symm hxz,Ne.symm hyz]
  · intro j
    fin_cases j <;> simp [linearProduct]
  · intro j
    fin_cases j <;> simp [linearProduct,derivative_mul,sub_ne_zero.mpr hxy,sub_ne_zero.mpr hxz,
      sub_ne_zero.mpr hyz,sub_ne_zero.mpr hxy.symm,sub_ne_zero.mpr hxz.symm,
      sub_ne_zero.mpr hyz.symm,hA]

theorem symmetric {A B r : K} (hA : A ≠ 0) (hr : r ≠ 0) (h₂ : (2:K) ≠ 0)
    (hB : B = -A*r^2) : Nonempty (SimpleTriple (C A*X^3+C B*X)) := by
  have hn : r ≠ -r := by
    intro e
    apply mul_ne_zero h₂ hr
    linear_combination e
  have hp : C A*X^3+C B*X = linearProduct A 0 r (-r) := by
    rw [hB]; simp [linearProduct]; ring
  rw [hp]
  exact three_linear hA (Ne.symm hr) (Ne.symm (neg_ne_zero.mpr hr)) hn

theorem binomial {A B r w : K} (hA : A ≠ 0) (hr : r ≠ 0) (h₃ : (3:K) ≠ 0)
    (hw : w^2+w+1=0) (hB : B = -A*r^3) : Nonempty (SimpleTriple (C A*X^3+C B)) := by
  have hw3 : w^3=1 := by linear_combination (w-1)*hw
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw3
  have hw1 : w ≠ 1 := by intro h; apply h₃; rw [h] at hw; linear_combination hw
  have hw2 : w^2 ≠ 1 := by
    intro h
    apply hw1
    calc w = w^2*w := by rw [h,one_mul]
         _ = 1 := by rw [← pow_succ,hw3]
  have h12 : w ≠ w^2 := by
    intro h
    apply hw1
    exact ((mul_right_inj' hw0).mp (by linear_combination -h : w*w=w*1))
  have hxy : r ≠ r*w := by
    intro h
    apply hw1
    exact mul_left_cancel₀ hr (by simpa only [mul_one] using h.symm : r*w=r*1)
  have hxz : r ≠ r*w^2 := by
    intro h
    apply hw2
    exact mul_left_cancel₀ hr (by simpa only [mul_one] using h.symm : r*w^2=r*1)
  have hyz : r*w ≠ r*w^2 := (mul_right_inj' hr).not.mpr h12
  have hp : C A*X^3+C B = linearProduct A r (r*w) (r*w^2) := by
    have hW := congrArg (C : K →+* K[X]) hw
    have hW3 := congrArg (C : K →+* K[X]) hw3
    simp only [map_add,map_pow,map_one,map_zero] at hW hW3
    rw [hB]; simp only [linearProduct,map_neg,map_mul,map_pow]
    linear_combination (C A*C r*X^2-C A*(C r)^2*C w*X)*hW + (C A*(C r)^3)*hW3
  rw [hp]
  exact three_linear hA hxy hxz hyz

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]
theorem lift_rows {f : R[X]} {c : R} {a : Fin 2 → R}
    (hc : c ≠ 0) (hc0 : residue R c=0) (ha : Function.Injective (fun i => residue R (a i)))
    (hf : f ≠ 0) (hd : f.natDegree ≤ 6) (g : Fin 2 → R[X]) (P : Fin 2 → (ResidueField R)[X])
    (chart : ∀ i x, f.eval (a i+c*x) = c^3*(g i).eval x)
    (reduction : ∀ i, (g i).map (residue R) = P i)
    (rows : ∀ i, Nonempty (SimpleTriple (P i))) : Nonempty (SexticFibre f c) := by
  let r i := (rows i).some
  have hz (i j) : (g i).eval₂ (residue R) ((r i).x j)=0 := by
    rw [← eval_map,reduction]; exact (r i).roots j
  have hs (i j) : (g i).derivative.eval₂ (residue R) ((r i).x j) ≠ 0 := by
    rw [← eval_map,← derivative_map,reduction]; exact (r i).simple j
  obtain ⟨T⟩ := twoTriples f a c g (fun i => (r i).x) hc hc0 ha chart (fun i => (r i).distinct) hz hs
  exact ⟨⟨a,_,T,hf,hd⟩⟩

open ZInQBlueprint.ResidueExtension
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "κ" => ResidueField W

theorem small_residue (n : ℕ) (hn : 0<n) (hp : n<p) : (n : κ) ≠ 0 := by
  intro h
  have H := congrArg (residueFieldEquiv p) h
  simp only [map_natCast,map_zero] at H
  exact (Nat.not_dvd_of_pos_of_lt hn hp) ((CharP.cast_eq_zero_iff (QuadraticField p) p n).mp H)

theorem small_unit (n : ℕ) (hn : 0<n) (hp : n<p) : IsUnit (n : ℤ_[p]) := by
  apply IsUnit.of_map (algebraMap ℤ_[p] W)
  rw [map_natCast]
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  exact small_residue p n hn hp

theorem uniformizer_scale (m : ℕ) (hm : 0<m) :
    (p:W)^m ≠ 0 ∧ residue W ((p:W)^m)=0 := by
  refine ⟨pow_ne_zero _ (uniformizer p).ne_zero,?_⟩
  have h : residue W (p:W)=0 := by
    apply (residueFieldEquiv p).injective
    rw [map_natCast,map_natCast,map_zero,CharP.cast_eq_zero]
  rw [map_pow,h,zero_pow hm.ne']

end
end ZInQBlueprint.PrimitiveLifts
#print axioms ZInQBlueprint.PrimitiveLifts.three_linear
#print axioms ZInQBlueprint.PrimitiveLifts.symmetric
#print axioms ZInQBlueprint.PrimitiveLifts.binomial
#print axioms ZInQBlueprint.PrimitiveLifts.lift_rows
#print axioms ZInQBlueprint.PrimitiveLifts.small_residue
#print axioms ZInQBlueprint.PrimitiveLifts.small_unit
#print axioms ZInQBlueprint.PrimitiveLifts.uniformizer_scale
