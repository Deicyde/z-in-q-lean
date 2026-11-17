import QuarticCoordinates

namespace ZInQBlueprint.BranchId
open Diagonal210
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def PublishedOpen (i : Fin 4) (K : Type*) [Field K] [CharZero K] :=
  {v : K × K // v.2^2=published i v.1 ∧ v.2≠0}

def OmittedOpen (i : Fin 4) (K : Type*) [Field K] [CharZero K] :=
  {v : K × (Fin 3→K) // omitted i v.1 v.2 ∧ readout i 2 v.2≠0}

private theorem readout_forward (i : Fin 4) (k : Fin 3) (x Y : K) :
    readout i k (fun j=>quad i j x/Y) = (![x^2,x,1] : Fin 3 → K) k/Y := by
  rw [←inverse_times_forward i (![x^2,x,1] : Fin 3 → K) k]
  simp only [readout,quad,lin]
  ring

theorem to_omitted {i : Fin 4} {x Y : K}
    (curve : Y^2=published i x) (live : Y≠0) :
    omitted i (numerator i x/Y^2) (fun j=>quad i j x/Y) ∧
      readout i 2 (fun j=>quad i j x/Y)≠0 := by
  constructor
  · intro j
    rw [div_pow,covariants,←curve]
    field_simp
  · rw [readout_forward]
    exact div_ne_zero one_ne_zero live

/-- The conic equation recovers the factor Y in front of all three signed
coordinates from the last row of the inverse matrix. -/
theorem reconstruct_coordinates {i : Fin 4} {s : K} {z : Fin 3 → K}
    (hit : omitted i s z) (live : readout i 2 z≠0) :
    ∀ j,quad i j (readout i 1 z/readout i 2 z)=z j/readout i 2 z := by
  let r := readout i 2 z
  let x := readout i 1 z/r
  have ver : (![x^2,x,1] : Fin 3 → K) = fun k=>readout i k z/r := by
    funext k
    fin_cases k
    · change (readout i 1 z/r)^2=readout i 0 z/r
      field_simp [r,live]
      linear_combination -(parametrizing_conic hit)
    · rfl
    · change 1=r/r
      exact (div_self live).symm
  intro j
  change lin (forwardCoeffs i j) ![x^2,x,1] = z j/r
  rw [ver,←forward_times_inverse i j z]
  unfold lin
  ring

/-- Cancellation using two different finite marks recovers both the ordinate
and the actual marked quotient coordinate. -/
theorem recover_slope {i : Fin 4} {s x Y : K} {z : Fin 3 → K} (hit : omitted i s z)
    (live : Y≠0) (coords : ∀ j,quad i j x=z j*Y) :
    Y^2=published i x ∧ numerator i x/Y^2=s := by
  let c (j : Fin 3) : K := coefficient (keep i j)
  let a (j : Fin 3) : K := mark (keep i j)
  have nz (j : Fin 3) : c j≠0 := by fin_cases i <;> fin_cases j <;> norm_num [c,keep,coefficient]
  have diff : a 0 - a 1 ≠ 0 := by fin_cases i <;> norm_num [a,mark,keep]
  have h (j : Fin 3) : (s-a j)*Y^2=numerator i x-a j*published i x := by
    have H:=covariants i j x
    rw [coords,mul_pow,hit j] at H
    apply mul_left_cancel₀ (nz j)
    simpa only [c,a,mul_assoc] using H
  have prod : (a 0-a 1)*(Y^2-published i x)=0 := by linear_combination h 1-h 0
  have y2:=sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left diff)
  refine ⟨y2,(div_eq_iff (pow_ne_zero 2 live)).mpr ?_⟩
  have H:=h 0
  rw [←y2] at H
  linear_combination -H

/-- An equivalence of dense affine charts of the *published quartic itself*
with the omitted-coordinate quotient of the common diagonal cover. -/
def quarticEquiv (i : Fin 4) : PublishedOpen i K ≃ OmittedOpen i K where
  toFun v := ⟨(numerator i v.1.1/v.1.2^2,fun j=>quad i j v.1.1/v.1.2),to_omitted v.2.1 v.2.2⟩
  invFun v := by
    let r:=readout i 2 v.1.2
    let x:=readout i 1 v.1.2/r
    let Y:K:=1/r
    have n : Y≠0 := div_ne_zero one_ne_zero v.2.2
    have C (j) : quad i j x=v.1.2 j*Y := by
      simpa only [x,Y,r,div_eq_mul_inv,one_mul] using reconstruct_coordinates v.2.1 v.2.2 j
    exact ⟨(x,Y),(recover_slope v.2.1 n C).1,n⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · change readout i 1 (fun j=>quad i j v.1.1/v.1.2)/readout i 2 (fun j=>quad i j v.1.1/v.1.2)=v.1.1
      rw [readout_forward,readout_forward]
      change (v.1.1/v.1.2)/(1/v.1.2)=v.1.1
      field_simp [v.2.2]
    · change 1/readout i 2 (fun j=>quad i j v.1.1/v.1.2)=v.1.2
      rw [readout_forward]
      change 1/(1/v.1.2)=v.1.2
      simp
  right_inv v := by
    let r:=readout i 2 v.1.2
    have n : (1/r:K)≠0 := div_ne_zero one_ne_zero v.2.2
    have C (j) : quad i j (readout i 1 v.1.2/r)=v.1.2 j*(1/r) := by
      simpa only [r,div_eq_mul_inv,one_mul] using reconstruct_coordinates v.2.1 v.2.2 j
    apply Subtype.ext
    apply Prod.ext
    · exact (recover_slope v.2.1 n C).2
    · funext j
      exact (div_eq_iff n).mpr (C j)

omit [CharZero K] in
theorem full_involution (i : Fin 4) (x Y : K) :
    numerator i x/(-Y)^2=numerator i x/Y^2 ∧
    ∀j,quad i j x/(-Y)= -(quad i j x/Y) := by
  constructor
  · simp
  · intro j
    simp only [div_eq_mul_inv,inv_neg,mul_neg]

end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.to_omitted
#print axioms ZInQBlueprint.BranchId.reconstruct_coordinates
#print axioms ZInQBlueprint.BranchId.recover_slope
#print axioms ZInQBlueprint.BranchId.quarticEquiv
#print axioms ZInQBlueprint.BranchId.full_involution
