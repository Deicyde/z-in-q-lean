import MarkedDetector

namespace Sun28.ContactFactors
open Sun28.Ordinary
noncomputable section

def shifts (A : Fin 3 → ℚ) : Finset ℚ :=
  Finset.univ.biUnion fun j => marks.image (fun a => -a/A j)

theorem shift_mem (A : Fin 3 → ℚ) (j : Fin 3) {a : ℚ} (ha : a∈marks) :
    -a/A j∈shifts A := Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩

def dilation (A : Fin 3 → ℚ) : ℕ := ∏ r ∈ shifts A, r.den

theorem dilation_positive (A : Fin 3 → ℚ) : 0<dilation A :=
  Finset.prod_pos (fun r _ => r.pos)

def offset (D : ℕ) (r : ℚ) : ℤ := r.num*((D/r.den : ℕ):ℤ)*D

theorem offset_eq {A : Fin 3→ℚ} {r : ℚ} (hr : r∈shifts A) :
    (offset (dilation A) r:ℚ)=r*(dilation A:ℚ)^2 := by
  have div : r.den∣dilation A := Finset.dvd_prod_of_mem _ hr
  have cast : ((dilation A/r.den:ℕ):ℚ)*(r.den:ℚ)=(dilation A:ℚ) := by
    exact_mod_cast Nat.div_mul_cancel div
  have reduce : r*(r.den:ℚ)=(r.num:ℚ) :=
    (eq_div_iff (by exact_mod_cast r.den_ne_zero)).mp (Rat.num_div_den r).symm
  unfold offset
  simp only [Int.cast_mul,Int.cast_natCast]
  rw [← reduce]
  linear_combination r*(dilation A:ℚ)*cast

theorem offset_injective {A : Fin 3→ℚ} {r s : ℚ} (hr : r∈shifts A) (hs : s∈shifts A)
    (eqn : offset (dilation A) r=offset (dilation A) s) : r=s := by
  have e := congrArg (fun x : ℤ => (x:ℚ)) eqn
  rw [offset_eq hr,offset_eq hs] at e
  exact mul_right_cancel₀ (pow_ne_zero 2 (by exact_mod_cast (dilation_positive A).ne')) e

theorem enough_shifts (A : Fin 3 → ℚ) (one : A 0=1) : 5≤(shifts A).card := by
  let sub := marks.image (fun a : ℚ => -a/A 0)
  have incl : sub⊆shifts A := fun _ hr => by
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hr
    exact shift_mem A 0 ha
  have card : sub.card=5 := by
    change (marks.image (fun a : ℚ => -a/A 0)).card=5
    rw [Finset.card_image_of_injective _ (fun a b e => by simpa [one] using e)]
    norm_num [marks, Finset.card_insert_of_notMem]
  exact card ▸ Finset.card_le_card incl

end
end Sun28.ContactFactors
#print axioms Sun28.ContactFactors.shift_mem
#print axioms Sun28.ContactFactors.dilation_positive
#print axioms Sun28.ContactFactors.offset_eq
#print axioms Sun28.ContactFactors.offset_injective
#print axioms Sun28.ContactFactors.enough_shifts
