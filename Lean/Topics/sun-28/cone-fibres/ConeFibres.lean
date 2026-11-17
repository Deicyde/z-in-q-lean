import NormMoments

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace Sun28.ConeFibres
open Finset Sun28.MixedSieve Sun28.QuadricSieve
open scoped Classical
noncomputable section

variable {p : ℕ} [Fact p.Prime]
def norm (z : ZMod p × ZMod p) : ZMod p := z.1^2 + z.2^2

def normWindow (κ : ZMod p) (T : ZMod p → Finset (ZMod p)) : Finset (Coordinates (ZMod p)) :=
  univ.filter fun x => onCone κ x ∧ norm x.1 ∈ T x.2.2

private def splitWindow (κ : ZMod p) (T : ZMod p → Finset (ZMod p)) :
    ↥(normWindow κ T) ≃ (Σ w : ZMod p, Σ t : ↥(T w), Circle p t.val × Circle p (t.val-κ*w^2)) := by
  refine ⟨fun ⟨x,hx⟩ => ?_, fun ⟨w,⟨t,ht⟩,⟨u,hu⟩,⟨v,hv⟩⟩ => ?_, ?_, ?_⟩
  · obtain ⟨eq,inc⟩ := (mem_filter.mp hx).2
    refine ⟨x.2.2,⟨norm x.1,inc⟩,⟨x.1,rfl⟩,⟨x.2.1,?_⟩⟩
    dsimp [onCone] at eq
    dsimp [norm]
    linear_combination -eq
  · refine ⟨(u,v,w),mem_filter.mpr ⟨mem_univ _,?_,?_⟩⟩
    · dsimp [onCone]
      linear_combination hu-hv
    · change norm u∈T w
      change norm u=t at hu
      rwa [hu]
  · intro x
    rfl
  · rintro ⟨w,⟨t,ht⟩,⟨u,hu⟩,⟨v,hv⟩⟩
    change norm u = t at hu
    subst t
    rfl

theorem norm_window_card (κ : ZMod p) (T : ZMod p → Finset (ZMod p)) :
    ((normWindow κ T).card:ℤ) = ∑ w : ZMod p, ∑ t ∈ T w, circleCount t * circleCount (t-κ*w^2) := by
  have aux := Fintype.card_congr (splitWindow κ T)
  have natCount : (normWindow κ T).card =
      ∑ w : ZMod p, ∑ t ∈ T w, Fintype.card (Circle p t)*Fintype.card (Circle p (t-κ*w^2)) := by
    simp only [Fintype.card_coe,Fintype.card_sigma,Fintype.card_prod] at aux
    rw [aux]
    apply sum_congr rfl
    intro w _
    exact Finset.sum_coe_sort (T w) (fun t => Fintype.card (Circle p t)*Fintype.card (Circle p (t-κ*w^2)))
  dsimp only [circleCount]
  exact_mod_cast natCount

def nonzeroCone (κ : ZMod p) := (normWindow κ (fun _ => univ)).erase 0

theorem nonzero_cone_card (odd : p≠2) {κ : ZMod p} (nz : κ≠0) :
    ((nonzeroCone κ).card:ℤ) = (p:ℤ)^4-1 := by
  let S := normWindow κ (fun _=>univ)
  have z : (0:Coordinates (ZMod p))∈S := by simp [S,normWindow,onCone]
  have er : ((nonzeroCone κ).card:ℤ)+1 = S.card := by
    exact_mod_cast card_erase_add_one z
  have f := norm_window_card κ (fun _=>univ)
  simp_rw [restricted_moment odd univ _ (mem_univ _) (mem_univ _)] at f
  simp [nz,sum_add_distrib,ZMod.card] at f
  change (S.card:ℤ) = _ at f
  linear_combination f + er

def targets (C : Finset (ZMod p)) (w : ZMod p) := C.image fun c => -c*w^2

def flagClasses (κ : ZMod p) (C : Finset (ZMod p)) :=
  (normWindow κ (targets C)).erase 0

def zeroNorm (p : ℕ) [Fact p.Prime] : ℤ := (p:ℤ)+((p:ℤ)-1)*chi p

def flagPolynomial (p : ℕ) [Fact p.Prime] (k : ℕ) : ℤ :=
  ((p:ℤ)-1)*((p:ℤ)-chi p)*(2*zeroNorm p+((k:ℤ)-2)*((p:ℤ)-chi p)) + (zeroNorm p)^2-1

theorem flag_classes_card (odd : p≠2) {κ : ZMod p} (nz : κ≠0) (C : Finset (ZMod p))
    (cz : 0∈C) (ck : -κ∈C) : ((flagClasses κ C).card:ℤ) = flagPolynomial p C.card := by
  let a : ℤ := (p:ℤ)-chi p
  let b : ℤ := (p:ℤ)*chi p
  have zmem (w : ZMod p) : 0 ∈ targets C w :=
    mem_image.mpr ⟨0,cz,by simp⟩
  have kmem (w : ZMod p) : κ*w^2 ∈ targets C w :=
    mem_image.mpr ⟨-κ,ck,by simp⟩
  have zs : targets C 0 = {0} := by
    ext t
    constructor
    · intro ht
      obtain ⟨v,_,rfl⟩:=mem_image.mp ht
      simp
    · intro ht
      simpa only [mem_singleton.mp ht] using zmem 0
  have cardinal (w : ZMod p) (wn : w≠0) : (targets C w).card = C.card :=
    card_image_of_injective _ fun _ _ eq => neg_injective (mul_right_cancel₀ (pow_ne_zero 2 wn) eq)
  let H : ℤ := (C.card:ℤ)*a^2+2*a*b
  have layer (w : ZMod p) : ∑ t ∈ targets C w, circleCount t * circleCount (t-κ*w^2) =
      H + if w=0 then (a+b)^2-H else 0 := by
    rw [restricted_moment odd _ _ (zmem w) (kmem w)]
    by_cases wn : w=0
    · subst w
      simp [zs,H,a,b]
      <;> ring
    · simp [wn,nz,cardinal w wn,H,a,b]
  have total := norm_window_card κ (targets C)
  simp_rw [layer] at total
  simp [sum_add_distrib,ZMod.card] at total
  have z : (0:Coordinates (ZMod p))∈normWindow κ (targets C) := by
    apply mem_filter.mpr
    exact ⟨mem_univ _, by simp [onCone],by simpa [norm] using zmem 0⟩
  have er : ((flagClasses κ C).card:ℤ)+1 = (normWindow κ (targets C)).card := by
    exact_mod_cast card_erase_add_one z
  dsimp [flagPolynomial,zeroNorm,H,a,b] at total ⊢
  linear_combination total + er

end
end Sun28.ConeFibres
#print axioms Sun28.ConeFibres.norm_window_card
#print axioms Sun28.ConeFibres.nonzero_cone_card
#print axioms Sun28.ConeFibres.flag_classes_card
