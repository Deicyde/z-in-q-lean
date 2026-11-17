import LocalAverage
import Mathlib.Algebra.BigOperators.Intervals

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace Sun28.MixedSieve
open Finset
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ordinary probability of a pattern of units, with u averaged first. -/
noncomputable def unitRate (c : ι→F p) : ℝ :=
  (∑ w : F p, ∑ u : F p, if ∀ i,norms c u w i≠0 then (1:ℝ) else 0)/(p:ℝ)^2

omit [DecidableEq ι] in
theorem units_lower (c : ι→F p) :
    1 - (Fintype.card ι:ℝ)/p ≤ unitRate c := by
  classical
  have hp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have row (w : F p) : (p:ℝ)-Fintype.card ι ≤
     ∑ u : F p, if ∀ i,norms c u w i≠0 then (1:ℝ) else 0 := by
    let zeros:=univ.image fun i : ι => -(c i*w^2)
    have en (u : F p) : (∀ i,norms c u w i≠0) ↔ u∉zeros := by
      simp only [zeros,mem_image,mem_univ,true_and,not_exists]
      constructor
      · intro h i e; apply h i; dsimp [norms]; linear_combination -e
      · intro h i e; apply h i; dsimp [norms] at e; linear_combination -e
    simp_rw [en]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    have nzs : univ.filter (fun u : F p => u∉zeros)=zerosᶜ := by ext; simp
    rw [nzs,Finset.card_compl,ZMod.card]
    have bound : zeros.card≤Fintype.card ι := Finset.card_image_le
    have bd := Finset.card_le_univ zeros
    rw [ZMod.card] at bd
    rw [Nat.cast_sub bd]
    exact sub_le_sub_left (by exact_mod_cast bound) _
  unfold unitRate
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  calc
    _ = ∑ _ : F p,((p:ℝ)-Fintype.card ι) := by simp [ZMod.card]; field_simp
    _ ≤ _ := Finset.sum_le_sum fun w _ => row w

noncomputable def relativeLoss (c : ι→F p) : ℝ := averageLoss c / unitRate c

theorem relative_nonneg (c : ι→F p) : 0≤relativeLoss c := by
  classical
  have l (u w : F p) : 0≤loss c u w := by dsimp only [loss]; split <;> positivity
  have h : 0≤averageLoss c := div_nonneg (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun u _ => l u w) (by positivity)
  have units : 0≤unitRate c := by
    apply div_nonneg _ (by positivity)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split <;> norm_num
  exact div_nonneg h units

theorem relative_bound (hp : 2<p) (hk : 2*Fintype.card ι≤p) (c : ι→F p) :
    relativeLoss c ≤ (8*(Fintype.card ι:ℝ)^2+4*Fintype.card ι)/((p:ℝ)-1)^2 := by
  have P : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have Q : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
  have H : 2*(Fintype.card ι:ℝ)≤p := by exact_mod_cast hk
  have small : (Fintype.card ι:ℝ)/p ≤ 1/2 := (div_le_iff₀ P).mpr (by linarith)
  have ur :=units_lower c
  have half : 1/2≤unitRate c := by linarith
  have up : 0<unitRate c := by linarith
  have quad : (0:ℝ)<((p:ℝ)-1)^2 := sq_pos_of_pos (by linarith)
  let C : ℝ := 8*(Fintype.card ι:ℝ)^2+4*Fintype.card ι
  have cn : 0≤C := by dsimp [C]; positivity
  have b := average_bound hp c
  apply (div_le_iff₀ up).mpr
  calc
    averageLoss c ≤ _ := b
    _ ≤ C/((p:ℝ)-1)^2*(1/2) := by
      dsimp [C]; field_simp [P.ne',sub_ne_zero.mpr Q.ne']
      nlinarith [show 0≤(Fintype.card ι:ℝ)*((p:ℝ)-1) by positivity]
    _ ≤ _ := mul_le_mul_of_nonneg_left half (div_nonneg cn quad.le)

/-- The paper has k ≤ 13. The simpler constant is uniform in all coefficients. -/
theorem thirteen (hp : 26≤p) (hk : Fintype.card ι≤13) (c : ι→F p) :
    relativeLoss c ≤ 1404/((p:ℝ)-1)^2 := by
  have c13 : (Fintype.card ι:ℝ)≤13 := by exact_mod_cast hk
  apply (relative_bound (by omega) (by omega) c).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h := mul_self_le_mul_self (by positivity : 0≤(Fintype.card ι:ℝ)) c13
  nlinarith

/-- Elementary Bonferroni inequality for independent good proportions. -/
theorem product_good {α : Type*} (S : Finset α) (r : α→ℝ)
    (non : ∀ i∈S,0≤r i) (one : ∀ i∈S,r i≤1) :
    1-∑ i∈S,r i ≤ ∏ i∈S,(1-r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S h ih =>
    have ra:=non a (mem_insert_self a S)
    have rb:=one a (mem_insert_self a S)
    have s0 (i) (hi : i∈S) := non i (mem_insert_of_mem hi)
    have s1 (i) (hi : i∈S) := one i (mem_insert_of_mem hi)
    have step:=mul_le_mul_of_nonneg_left (ih s0 s1) (by linarith : 0≤1-r a)
    rw [sum_insert h,prod_insert h]
    have pos:=mul_nonneg ra (sum_nonneg s0)
    nlinarith only [step,pos]

private theorem telescoping (a n : ℕ) :
    (∑ j∈range n,(1/(a+j:ℝ)-1/((a+j:ℝ)+1)))=1/(a:ℝ)-1/(a+n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih]; push_cast; ring

/-- The sum of the normalized losses at any finite set of large places. -/
theorem uniform_sum (S : Finset ℕ) (loss : ℕ→ℝ) (large : ∀ p∈S,2810≤p)
    (bound : ∀ p∈S,loss p≤1404/((p:ℝ)-1)^2) : (∑ p∈S,loss p) ≤ 1/2 := by
  classical
  let U:=S.sup id+1
  let T:=Finset.image (fun p : ℕ => p-2810) S
  have ts : T⊆range U := by
    intro j h
    obtain ⟨p,hp,rfl⟩:=mem_image.mp h
    have le : p≤S.sup id := Finset.le_sup (f:=id) hp
    exact mem_range.mpr (by dsimp [U]; omega)
  let g (j : ℕ) : ℝ:=1/(2808+j:ℝ)-1/((2808+j:ℝ)+1)
  have gn (j : ℕ) : 0≤g j := by dsimp [g]; apply sub_nonneg.mpr; exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have single (p) (hp : p∈S) : loss p ≤1404*g (p-2810) := by
    have n := large p hp
    apply (bound p hp).trans
    have e : (↑(p-2810):ℝ)=(p:ℝ)-2810 := by rw [Nat.cast_sub n]; norm_num
    have A : (0:ℝ)<p-2 := sub_pos.mpr (by exact_mod_cast (show 2<p by omega))
    dsimp [g]; rw [e]
    have eq : (2808:ℝ)+(p-2810)=p-2 := by ring
    rw [eq]
    have eq2 : (p:ℝ)-2+1=p-1 := by ring
    rw [eq2]
    have B : 0<(p:ℝ)-1 := by linarith
    field_simp [A.ne',B.ne']
    nlinarith [A,B]
  have sum_le : (∑ p∈S,loss p) ≤ 1/2 := by
    calc
      _ ≤ ∑ p∈S,1404*g (p-2810) := Finset.sum_le_sum single
      _ = 1404*∑ j∈T,g j := by
        rw [Finset.mul_sum,Finset.sum_image]
        intro a ha b hb eq
        change a-2810=b-2810 at eq
        have h₁:=large a ha
        have h₂:=large b hb
        omega
      _ ≤ 1404*∑ j∈range U,g j := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg ts fun j _ _ => gn j) (by norm_num)
      _ ≤ 1/2 := by
        rw [show (∑ j∈range U,g j)=1/(2808:ℝ)-1/(2808+U:ℝ) by exact telescoping 2808 U]
        have : 0≤1/(2808+(U:ℝ)) := by positivity
        linarith
  exact sum_le

/-- A cutoff-independent lower bound for the entire product on primes above 2810. -/
theorem uniform_product (S : Finset ℕ) (loss : ℕ→ℝ) (large : ∀ p∈S,2810≤p)
    (non : ∀ p∈S,0≤loss p) (bound : ∀ p∈S,loss p≤1404/((p:ℝ)-1)^2) :
    1/2 ≤ ∏ p∈S,(1-loss p) := by
  have sum_le := uniform_sum S loss large bound
  apply le_trans (by linarith : (1:ℝ)/2≤1-∑ p∈S,loss p) (product_good S loss non ?_)
  intro p hp
  have :=non p hp
  have := Finset.single_le_sum (f:=loss) non hp
  linarith

end Sun28.MixedSieve
#print axioms Sun28.MixedSieve.units_lower
#print axioms Sun28.MixedSieve.relative_nonneg
#print axioms Sun28.MixedSieve.relative_bound
#print axioms Sun28.MixedSieve.thirteen
#print axioms Sun28.MixedSieve.product_good
#print axioms Sun28.MixedSieve.uniform_sum
#print axioms Sun28.MixedSieve.uniform_product
