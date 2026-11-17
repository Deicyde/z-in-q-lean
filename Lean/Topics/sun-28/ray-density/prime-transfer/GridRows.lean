import MomentRows

namespace Sun28.PrimeTransfer
open Finset
open scoped Classical
noncomputable section

/-- A signed quadratic pattern in the ordinary interval of labels {0,...,B−1}. -/
def Recurrent (c : Finset ℤ) (s B : ℕ) : Prop :=
  ∀ S : Finset (Fin B), B ≤ 2*s*S.card →
    ∃ a : Fin B, ∃ m ∈ Icc 1 B, ∀ h ∈ c, ∃ b ∈ S, (b.val:ℤ) = a.val + h*m^2

variable {n B : ℕ} [NeZero n]

def labels (E : Finset (ZMod n)) (D x : ZMod n) (B : ℕ) : Finset (Fin B) :=
  univ.filter fun b => x+D*(b.val:ZMod n) ∈ E

def good (E : Finset (ZMod n)) (D : ZMod n) (s B : ℕ) : Finset (ZMod n) :=
  univ.filter fun x => B ≤ 2*s*(labels E D x B).card

theorem labels_sum (E : Finset (ZMod n)) (D : ZMod n) (B : ℕ) :
    ∑ x : ZMod n, (labels E D x B).card = B*E.card := by
  classical
  simp only [labels,card_filter]
  rw [sum_comm]
  have col (b : Fin B) : (∑ x : ZMod n, if x+D*(b.val:ZMod n) ∈ E then 1 else 0) = E.card := by
    calc
      _ = ∑ x : ZMod n, if x ∈ E then 1 else 0 :=
        Equiv.sum_comp (Equiv.addRight (D*(b.val:ZMod n))) (fun x => if x ∈ E then 1 else 0)
      _ = E.card := by rw [←card_filter]; simp
  simp only [col,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]

theorem good_card (E : Finset (ZMod n)) (D : ZMod n) {s B : ℕ}
    (hB : 0 < B) (density : n ≤ s*E.card) :
    n ≤ 2*s*(good E D s B).card := by
  classical
  let G := good E D s B
  have bound (x : ZMod n) : 2*s*(labels E D x B).card ≤
      B + (if x ∈ G then 2*s*B else 0) := by
    have small : (labels E D x B).card ≤ B := by
      simpa only [labels,card_univ,Fintype.card_fin] using (card_le_card (filter_subset _ (univ : Finset (Fin B))))
    by_cases hx : x ∈ G
    · simpa only [ite_eq_left hx] using (Nat.le_add_left_of_le (Nat.mul_le_mul_left (2*s) small) : 2*s*(labels E D x B).card ≤ _)
    · have := not_le.mp (show ¬B ≤ 2*s*(labels E D x B).card by simpa [G,good] using hx)
      simp only [ite_eq_right hx,add_zero]; omega
  have total := sum_le_sum (s:=univ) (fun x _ => bound x)
  rw [←mul_sum,labels_sum,sum_add_distrib] at total
  have indicator : (∑ x : ZMod n, if x∈G then 2*s*B else 0) = G.card*(2*s*B) := by
    rw [←Finset.sum_filter]; simp
  rw [indicator] at total
  simp only [sum_const,card_univ,ZMod.card,smul_eq_mul] at total
  change n ≤ 2*s*G.card
  apply Nat.le_of_mul_le_mul_right (c:=B) _ hB
  nlinarith only [Nat.mul_le_mul_right B density,total]

end
end Sun28.PrimeTransfer
#print axioms Sun28.PrimeTransfer.labels_sum
#print axioms Sun28.PrimeTransfer.good_card
