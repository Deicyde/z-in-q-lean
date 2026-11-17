import CrossRatioForms

/-! Projective height change controlled by the adjugate of the two cross-ratio rows. -/
namespace Sun28.FiveMarkTriples
open Sun28.Ordinary Sun28.FiveMarkUnits Height

private theorem linear_bound {u v U V : ℤ} (hc : |u|+|v|≤2^32) :
    |u*U+v*V|≤2^32*pairHeight U V := by
  have hu : |U|≤pairHeight U V := le_max_left _ _
  have hv : |V|≤pairHeight U V := le_max_right _ _
  have pos : 0≤pairHeight U V := (abs_nonneg U).trans hu
  calc
    |u*U+v*V| ≤ |u*U|+|v*V| := abs_add_le _ _
    _ ≤ |u| *pairHeight U V+|v| *pairHeight U V := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _)) (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
    _ = (|u|+|v|)*pairHeight U V := (add_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hc pos

/-- From a primitive integral pair proportional to a nonzero pair one obtains an
integer proportionality factor. Bézout gives it without performing any division. -/
private theorem proportional {A B C D : ℤ} (primitive : Int.gcd A B=1) (cross : A*D=B*C) (live : C≠0 ∨ D≠0) :
    pairHeight A B ≤ pairHeight C D := by
  obtain ⟨a,b,bez⟩ := Int.isCoprime_iff_gcd_eq_one.mpr primitive
  let t:=a*C+b*D
  have ca : t*A=C := by dsimp [t];linear_combination C*bez+b*cross
  have db : t*B=D := by dsimp [t];linear_combination D*bez-a*cross
  have nz : t≠0 := by
    intro z
    simp [z] at ca db
    exact live.elim (fun c => c ca.symm) (fun d => d db.symm)
  have bound (q : ℤ) : |q|≤|t*q| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right (show (1:ℤ)≤|t| by have h := abs_pos.mpr nz;omega) (abs_nonneg q)
  exact max_le_max (ca ▸ bound A) (db ▸ bound B)

theorem adjugate_height (i j k : Fin 5) {A B : ℤ} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (primitive : Int.gcd A B=1) (off : ∀ n,oldForm n A B≠0) :
    pairHeight A B≤2^32*pairHeight (crossRatio i j k A B).num (crossRatio i j k A B).den := by
  let q:=crossRatio i j k A B
  let U:=q.num
  let V:ℤ:=q.den
  let a:=det k j*coeffA i
  let b:=det k j*coeffB i
  let c:=det i j*coeffA k
  let d:=det i j*coeffB k
  have Δ : a*d-b*c≠0 := by
    have eq : a*d-b*c=det k j*det i j*det i k := by dsimp [a,b,c,d,det];ring
    rw [eq]
    exact mul_ne_zero (mul_ne_zero (det_ne jk.symm) (det_ne ij)) (det_ne ik)
  have x : a*A+b*B=det k j*oldForm i A B := by rw [form_coeff];dsimp [a,b];ring
  have y : c*A+d*B=det i j*oldForm k A B := by rw [form_coeff];dsimp [c,d];ring
  have yn : c*A+d*B≠0 := by rw [y];exact mul_ne_zero (det_ne ij) (off k)
  have vn : V≠0 := by change (q.den:ℤ)≠0;exact_mod_cast q.den_nz
  have qeq : (U:ℚ)/(V:ℚ)= ((a*A+b*B:ℤ):ℚ)/((c*A+d*B:ℤ):ℚ) := by rw [x,y];exact Rat.num_div_den q
  have eqZ : U*(c*A+d*B)=(a*A+b*B)*V := by
    exact_mod_cast (div_eq_div_iff (by exact_mod_cast vn) (by exact_mod_cast yn)).mp qeq
  let C:=d*U+(-b)*V
  let D:=(-c)*U+a*V
  have cross : A*D=B*C := by dsimp [D,C];linear_combination -eqZ
  have live : C≠0 ∨ D≠0 := by
    by_contra! h
    have zero : (a*d-b*c)*V=0 := by dsimp [C,D] at h;linear_combination c*h.1+d*h.2
    exact (mul_ne_zero Δ vn) zero
  have catalog : ∀ i j k : Fin 5,
      |det i j*coeffB k|+|det k j*coeffB i|≤2^32 ∧
      |det i j*coeffA k|+|det k j*coeffA i|≤2^32 := by decide
  have bounds := catalog i j k
  have cb : |C|≤2^32*pairHeight U V := linear_bound (by simpa [d,b] using bounds.1)
  have db : |D|≤2^32*pairHeight U V := linear_bound (by simpa [c,a] using bounds.2)
  exact (proportional primitive cross live).trans (max_le cb db)

theorem crossRatio_height (i j k : Fin 5) {A B : ℤ} (ij : i≠j) (ik : i≠k) (jk : j≠k)
    (primitive : Int.gcd A B=1) (off : ∀ n,oldForm n A B≠0) :
    pairLogHeight A B≤logHeight₁ (crossRatio i j k A B)+32 := by
  let q:=crossRatio i j k A B
  have h : (pairHeight A B:ℝ)≤2^32*(pairHeight q.num q.den:ℝ) := by exact_mod_cast adjugate_height i j k ij ik jk primitive off
  have p : 0 < (pairHeight A B:ℝ) := by exact_mod_cast pairHeight_pos A B (Or.inr (off_triple off).2.1)
  have p' : 0 < (pairHeight q.num q.den:ℝ) := by exact_mod_cast pairHeight_pos q.num q.den (Or.inr (by exact_mod_cast q.den_nz))
  have orig : logHeight₁ q=pairLogHeight q.num q.den := by
    rw [Rat.logHeight₁_eq_log_max]
    unfold pairLogHeight pairHeight
    congr 1
    norm_cast
    simp
  have logs := Real.log_le_log p h
  rw [Real.log_mul (by norm_num) p'.ne',Real.log_pow] at logs
  have l2 := Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  change pairLogHeight A B≤logHeight₁ q+32
  rw [orig]
  unfold pairLogHeight
  norm_num at logs
  linarith only [logs,l2]

end Sun28.FiveMarkTriples
#print axioms Sun28.FiveMarkTriples.adjugate_height
#print axioms Sun28.FiveMarkTriples.crossRatio_height
