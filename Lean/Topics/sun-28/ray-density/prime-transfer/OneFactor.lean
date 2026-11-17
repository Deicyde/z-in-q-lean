import PrimeWindow

namespace Sun28.PrimeTransfer
open Finset
open scoped Classical
noncomputable section
variable {n : ℕ} [NeZero n]

def mixedMass (c D : Finset ℤ) (f g : ZMod n → ℝ) (H : ZMod n) (M : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 M ×ˢ (univ : Finset (ZMod n))),
    ∏ h ∈ c, (if h∈D then g else f) (p.2+H*(h:ZMod n)*(p.1:ZMod n)^2)

def singleError (c D : Finset ℤ) (h : ℤ) (f g : ZMod n → ℝ) (H : ZMod n) (M : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 M ×ˢ (univ : Finset (ZMod n))),
    let atShift (i : ℤ) := p.2+H*(i:ZMod n)*(p.1:ZMod n)^2
    (g (atShift h) - f (atShift h))*
      ∏ i ∈ c.erase h,(if i∈D then g else f) (atShift i)

theorem mixed_insert (c D : Finset ℤ) {h : ℤ} (inC : h∈c) (fresh : h∉D)
    (f g : ZMod n→ℝ) (H : ZMod n) (M : ℕ) :
    mixedMass c (insert h D) f g H M - mixedMass c D f g H M = singleError c D h f g H M := by
  classical
  unfold mixedMass singleError
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  let x (i : ℤ) := p.2+H*(i:ZMod n)*(p.1:ZMod n)^2
  have fix : (∏ i∈c.erase h,(if i∈insert h D then g else f) (x i))=
      ∏ i∈c.erase h,(if i∈D then g else f) (x i) := by
    apply prod_congr rfl
    intro i hi
    simp only [mem_insert,or_iff_right (mem_erase.mp hi).1]
  change (∏ i∈c,(if i∈insert h D then g else f) (x i)) -
    (∏ i∈c,(if i∈D then g else f) (x i))=_
  rw [←mul_prod_erase c _ inC,←mul_prod_erase c (fun i => (if i∈D then g else f) (x i)) inC,fix]
  simp only [mem_insert_self,ite_true,ite_eq_right fresh]
  exact (sub_mul ..).symm

/-- Uniform signed one-coordinate replacement estimates imply an error of at most kε. -/
theorem compare_models (c : Finset ℤ) (f g : ZMod n→ℝ) (H : ZMod n)
    (M : ℕ) (er : ℝ)
    (replaceOne : ∀ D ⊆ c, ∀ h∈c, h∉D → singleError c D h f g H M ≤ er) :
    circleMass c g H M ≤ circleMass c f H M + c.card*er := by
  classical
  have prefixBound (D : Finset ℤ) (hD : D⊆c) :
      mixedMass c D f g H M ≤ mixedMass c ∅ f g H M+D.card*er := by
    induction D using Finset.induction_on with
    | empty => simp
    | @insert h D fresh ih =>
      have ih' := ih (fun i hi => hD (mem_insert_of_mem hi))
      have st := mixed_insert c D (hD (mem_insert_self ..)) fresh f g H M
      have bound := replaceOne D (fun i hi => hD (mem_insert_of_mem hi)) h (hD (mem_insert_self ..)) fresh
      rw [card_insert_of_notMem fresh,Nat.cast_add,Nat.cast_one]
      linarith
  have full : mixedMass c c f g H M = circleMass c g H M := by
    apply sum_congr rfl
    intro p _
    exact prod_congr rfl (fun i hi=>by rw [ite_eq_left hi])
  have final := prefixBound c Subset.rfl
  rw [full] at final
  simpa [mixedMass,circleMass] using final

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.mixed_insert
#print axioms Sun28.PrimeTransfer.compare_models
