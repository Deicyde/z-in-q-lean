import GaussianHeader

namespace Sun28.GaussianSelection
open ManuscriptV15.Arithmetic Sun28.ContactFactors Sun28.Ordinary

theorem shifts_card_le (A : Fin 3→ℚ) : (shifts A).card≤13 := by
  let nonzero:=marks.erase 0
  let remainder:=(Finset.univ : Finset (Fin 3)).biUnion fun j=>nonzero.image (fun a=> -a/A j)
  have sub : shifts A⊆insert 0 remainder := by
    intro r hr
    obtain ⟨j,_,hrj⟩:=Finset.mem_biUnion.mp hr
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hrj
    by_cases za : a=0
    · simp [za]
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
        Finset.mem_image.mpr ⟨a,Finset.mem_erase.mpr ⟨za,ha⟩,rfl⟩⟩)
  have count : nonzero.card=4 := by norm_num [nonzero,marks,Finset.card_insert_of_notMem]
  have bound : remainder.card≤12 := calc
    _ ≤ ∑ j : Fin 3,(nonzero.image (fun a=> -a/A j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin 3,nonzero.card := Finset.sum_le_sum (fun _ _=> Finset.card_image_le)
    _ = 12 := by norm_num [count]
  have ins:=Finset.card_insert_le 0 remainder
  have le:=Finset.card_le_card sub
  omega

noncomputable def primeSize (A : Fin 3→ℚ) (Y : ℝ) : ℝ :=
  1+|Y|+dilation A+separation+∑ j,(|(A j).num|+(A j).den : ℤ)

theorem size_bounds (A : Fin 3→ℚ) (Y : ℝ) :
    0<primeSize A Y ∧ Y≤primeSize A Y ∧ (dilation A:ℝ)≤primeSize A Y ∧
    (separation:ℝ)≤primeSize A Y ∧
    ∀ j,((A j).num.natAbs:ℝ)≤primeSize A Y ∧ ((A j).den:ℝ)≤primeSize A Y := by
  let f (j : Fin 3) : ℤ := |(A j).num|+(A j).den
  have each (j) : 0≤f j := by dsimp [f]; positivity
  have pos : 0≤∑ j,f j := Finset.sum_nonneg (fun j _=>each j)
  have posR : (0:ℝ)≤↑(∑ j,f j) := by exact_mod_cast pos
  have zero : (0:ℝ)≤dilation A := by positivity
  have se : (0:ℝ) ≤ separation := by positivity
  change 0<1+|Y|+dilation A+separation+↑(∑ j,f j) ∧ _
  have bound (j) : ((A j).num.natAbs:ℝ)≤primeSize A Y ∧ ((A j).den:ℝ)≤primeSize A Y := by
    have le : f j≤∑ i,f i := Finset.single_le_sum (fun i _=>each i) (Finset.mem_univ j)
    have n : ((A j).num.natAbs:ℤ)≤∑ i,f i := (by simp [f] : ((A j).num.natAbs:ℤ)≤f j).trans le
    have d : ((A j).den:ℤ)≤∑ i,f i := (by simp [f] : ((A j).den:ℤ)≤f j).trans le
    have nr := (Int.cast_le (R:=ℝ)).mpr n
    simp only [Int.cast_natCast] at nr
    have dr : ((A j).den:ℝ)≤↑(∑ i,f i) := by exact_mod_cast d
    change _≤1+|Y|+dilation A+separation+↑(∑ i,f i) ∧ _≤_
    constructor <;> change _≤1+|Y|+dilation A+separation+↑(∑ i,f i) <;> linarith [abs_nonneg Y]
  refine ⟨by linarith [abs_nonneg Y],?_,?_,?_,bound⟩
  all_goals change _≤1+|Y|+dilation A+separation+↑(∑ i,f i)
  all_goals linarith [abs_nonneg Y,le_abs_self Y]

/-- A lower bound on the prime avoids both supports of each nonzero rational scale. -/
theorem large_prime_exclusions (A : Fin 3→ℚ) (Y : ℝ) (alive : ∀ j,A j≠0) {p : ℕ}
    (hp : primeSize A Y<(p:ℝ)) :
    Y<(p:ℝ) ∧ ¬p∣dilation A ∧ ¬p∣separation ∧ ∀ j,padicValRat p (A j)=0 := by
  obtain ⟨_,y,d,s,each⟩:=size_bounds A Y
  have off (n : ℕ) (pos : 0<n) (bound : (n:ℝ)≤primeSize A Y) : ¬p∣n :=
    Nat.not_dvd_of_pos_of_lt pos (by exact_mod_cast bound.trans_lt hp)
  refine ⟨y.trans_lt hp,off _ (dilation_positive A) d,off _ (by decide) s,?_⟩
  intro j
  have n0 : 0<(A j).num.natAbs := Int.natAbs_pos.mpr (by simpa using alive j)
  rw [padicValRat_def]
  unfold padicValInt
  rw [padicValNat.eq_zero_of_not_dvd (off _ n0 (each j).1),
    padicValNat.eq_zero_of_not_dvd (off _ (A j).pos (each j).2)]
  simp

end Sun28.GaussianSelection
#print axioms Sun28.GaussianSelection.shifts_card_le
#print axioms Sun28.GaussianSelection.size_bounds
#print axioms Sun28.GaussianSelection.large_prime_exclusions
