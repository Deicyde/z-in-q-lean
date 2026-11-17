import AnchorOrders
import RaySelection
import CompleteClass

namespace Sun28.QualitativeRows
open Sun28.ContactFactors Sun28.ContactSieve Sun28.ScalarPlaces Sun28.FixedPreparation
open ManuscriptV15.Arithmetic
noncomputable section

/-- The kernel congruence and the exact local depth residues required by Sun §6. -/
def fixedMod (r : ℤ) : Option ↥(supportPlaces r) → ℕ
  | none => kernelMod r
  | some q => q.val^(comparisonDepth r q.val+1)

def fixedRes (r : ℤ) : Option ↥(supportPlaces r) → ℕ
  | none => 0
  | some q => q.val^comparisonDepth r q.val

private theorem mod_pos (r : ℤ) (j) : 0 < fixedMod r j := by
  cases j with
  | none => exact kernel_positive r
  | some p => exact pow_pos (support_prime p.property).pos _

private theorem fixed_compatible (r : ℤ) (i j) :
    fixedRes r i ≡ fixedRes r j [MOD (fixedMod r i).gcd (fixedMod r j)] := by
  have kernel (p : ↥(supportPlaces r)) :
      0 ≡ p.val^comparisonDepth r p.val [MOD (kernelMod r).gcd (p.val^(comparisonDepth r p.val+1))] := by
    have prime := support_prime p.property
    have b : (kernelMod r).factorization p.val ≤ comparisonDepth r p.val := by
      rw [Nat.factorization_def _ prime]
      unfold comparisonDepth
      omega
    obtain ⟨j, _, eq⟩ := (Nat.dvd_prime_pow prime).mp
      (Nat.gcd_dvd_right (kernelMod r) (p.val^(comparisonDepth r p.val+1)))
    have cd := Nat.gcd_dvd_left (kernelMod r) (p.val^(comparisonDepth r p.val+1))
    rw [eq] at cd ⊢
    exact (Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow _ (((prime.pow_dvd_iff_le_factorization
      (kernel_positive r).ne').mp cd).trans b))).symm
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some p => exact kernel p
  | some p =>
    cases j with
    | none => simpa only [fixedMod,fixedRes,Nat.gcd_comm] using (kernel p).symm
    | some q =>
      by_cases same : p=q
      · subst q; rfl
      · have ne : p.val ≠ q.val := fun eq => same (Subtype.ext eq)
        have cp : p.val.Coprime q.val := (support_prime p.property).coprime_iff_not_dvd.mpr
          (fun dvd => ne ((Nat.prime_dvd_prime_iff_eq (support_prime p.property) (support_prime q.property)).mp dvd))
        simpa only [fixedMod,fixedRes,((cp.pow_left _).pow_right _).gcd_eq_one] using
          (Nat.modEq_one (a:=p.val^comparisonDepth r p.val) (b:=q.val^comparisonDepth r q.val))

def OrderGraph {ι : Type*} (π : ι → Gaussian) (r : ℤ) : Option ι → Option ι → Bool → Prop :=
  Edge (fun i s => adjacentNorm (π i) s) (fixedMod r) (fixedRes r) ((Nat.factorial 576))

/-- A purely finite graph condition on the two actual integral Gaussian orders per position. -/
def BalancedOrders {ι : Type*} (π : ι → Gaussian) (r : ℤ) : Prop :=
  ∀ i, ¬Walk (OrderGraph π r) i i true

theorem solve_orders {ι : Type*} [Fintype ι] (π : ι → Gaussian) (r : ℤ)
    (ray : ∀ i, gaussianCongruent 16 (π i) (9,0)) (clear : BalancedOrders π r) :
    ∃ (flip : ι → Bool) (h₀ : ℤ) (L : ℕ), 0<L ∧ ∀ k : ℤ,
      let h := h₀+(L:ℤ)*k
      ((kernelMod r : ℕ) : ℤ) ∣ h ∧
      (∀ p∈ supportPlaces r, h ≡ (p:ℤ)^comparisonDepth r p [ZMOD (p:ℤ)^(comparisonDepth r p+1)]) ∧
      ∀ i, (adjacentNorm (π i) (flip i):ℤ) ∣ h ∧
        (adjacentNorm (π i) (!(flip i)):ℤ) ∣ (h-anchor) := by
  have nz (i : ι) (s : Bool) : 0 < adjacentNorm (π i) s := by
    apply Nat.pos_of_ne_zero
    intro z
    cases s with
    | false => have hz := (Sun28.GaussianSelection.ray_dyadic (ray i)).2; rw [z,padicValNat_zero_right] at hz; contradiction
    | true => have hz := (Sun28.GaussianSelection.ray_dyadic (ray i)).1; rw [z,padicValNat_zero_right] at hz; contradiction
  obtain ⟨x,h,L,pos,all⟩ := (graph_criterion (fun i s => adjacentNorm (π i) s)
    (fixedMod r) (fixedRes r) (Nat.factorial 576) nz (mod_pos r) (fixed_compatible r)).mp clear
  refine ⟨x,h,L,pos,fun k => ⟨Int.modEq_zero_iff_dvd.mp (all k (.inl none)),?_,?_⟩⟩
  · intro p mem
    simpa only [comparisonMod,comparisonRes,fixedMod,fixedRes,Nat.cast_pow] using
      all k (.inl (some ⟨p,mem⟩))
  · intro i
    have a := all k (.inr (i,x i))
    have b := all k (.inr (i,!(x i)))
    simp only [comparisonMod,comparisonRes,Bool.xor_self,Bool.false_eq_true,ite_false,Nat.cast_zero] at a
    refine ⟨Int.modEq_zero_iff_dvd.mp a,?_⟩
    apply Int.modEq_iff_dvd.mp
    have flip : (!(x i) ^^ x i)=true := by cases x i <;> rfl
    simpa only [comparisonMod,comparisonRes,flip,ite_true,anchor] using b.symm

end
end Sun28.QualitativeRows

#print axioms Sun28.QualitativeRows.solve_orders
