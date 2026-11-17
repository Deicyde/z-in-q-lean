import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

/-! An elementary upper bound for positive integers with small squarefree part.
The integer d in the finite enumeration need not be squarefree. -/
namespace ZInQBlueprint.SmallKernelCount

private def row (B d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (B/d).sqrt).image (fun u => d*u^2)

/-- Positive integers at most B represented as d times a square, with 1 ≤ d ≤ K. -/
def smallValues (B : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | K+1 => smallValues B K ∪ row B (K+1)

private theorem mem_row {n B d : ℕ} (hd : 0<d) :
    n∈row B d ↔ 0<n ∧ n≤B ∧ ∃ u : ℕ, n=d*u^2 := by
  constructor
  · rintro h
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨pos,small⟩:=Finset.mem_Icc.mp hu
    refine ⟨Nat.mul_pos hd (pow_pos pos 2),?_,u,rfl⟩
    simpa only [Nat.mul_comm d] using (Nat.le_div_iff_mul_le hd).mp (Nat.le_sqrt'.mp small)
  · rintro ⟨pos,cap,u,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨u,Finset.mem_Icc.mpr ⟨?_,Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hd).mpr ?_)⟩,rfl⟩
    · by_contra! hz
      have : u=0 := by omega
      simp [this] at pos
    · simpa only [Nat.mul_comm d] using cap

theorem mem_smallValues {n B K : ℕ} :
    n∈smallValues B K ↔ 0<n ∧ n≤B ∧ ∃ d u : ℕ, 0<d ∧ d≤K ∧ n=d*u^2 := by
  induction K with
  | zero => simp [smallValues]
  | succ k ih =>
    rw [smallValues,Finset.mem_union,ih,mem_row (Nat.succ_pos _)]
    constructor
    · rintro (⟨hn,cap,d,u,hd,hk,eq⟩|⟨hn,cap,u,eq⟩)
      · exact ⟨hn,cap,d,u,hd,by omega,eq⟩
      · exact ⟨hn,cap,k+1,u,by omega,le_rfl,eq⟩
    · rintro ⟨hn,cap,d,u,hd,hk,eq⟩
      by_cases low : d≤k
      · exact Or.inl ⟨hn,cap,d,u,hd,low,eq⟩
      · have same : d=k+1 := by omega
        exact Or.inr ⟨hn,cap,u,by simpa only [same] using eq⟩

theorem mem_of_repr {B K d u n : ℕ} (hn : 0<n) (cap : n≤B)
    (hd : 0<d) (hk : d≤K) (eq : n=d*u^2) : n∈smallValues B K :=
  mem_smallValues.mpr ⟨hn,cap,d,u,hd,hk,eq⟩

private theorem row_card (B k : ℕ) :
    ((row B (k+1)).card:ℝ) ≤ Real.sqrt (B:ℝ) / Real.sqrt ((k:ℝ)+1) := by
  let U:ℕ:=(B/(k+1)).sqrt
  have upper : (row B (k+1)).card ≤ U := by
    apply Finset.card_image_le.trans
    simp [Nat.card_Icc,U]
  have paid := (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mp (Nat.sqrt_le' (B/(k+1)))
  have cost : (U:ℝ)^2*((k:ℝ)+1) ≤ B := by exact_mod_cast paid
  have hroot : (Real.sqrt ((k:ℝ)+1))^2 = (k:ℝ)+1 := Real.sq_sqrt (by positivity)
  have mul : (U:ℝ)*Real.sqrt ((k:ℝ)+1) ≤ Real.sqrt (B:ℝ) :=
    Real.le_sqrt_of_sq_le (by rw [mul_pow,hroot];exact cost)
  exact (show ((row B (k+1)).card:ℝ)≤U by exact_mod_cast upper).trans
    ((le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))).mpr mul)

/-- Telescope the strict drop between consecutive square roots. -/
private theorem sqrt_step (k : ℕ) :
    1/Real.sqrt ((k:ℝ)+1) ≤ 2*(Real.sqrt ((k:ℝ)+1)-Real.sqrt (k:ℝ)) := by
  let a:=Real.sqrt (k:ℝ)
  let b:=Real.sqrt ((k:ℝ)+1)
  have a2 : a^2=(k:ℝ) := Real.sq_sqrt (by positivity)
  have b2 : b^2=(k:ℝ)+1 := Real.sq_sqrt (by positivity)
  have pos : 0<b := Real.sqrt_pos.mpr (by positivity)
  change 1/b≤2*(b-a)
  apply (div_le_iff₀ pos).mpr
  nlinarith only [sq_nonneg (b-a),a2,b2]

theorem card_smallValues (B K : ℕ) :
    ((smallValues B K).card:ℝ) ≤ 2*Real.sqrt (B:ℝ)*Real.sqrt (K:ℝ) := by
  induction K with
  | zero => simp [smallValues]
  | succ k ih =>
    have cards:=Finset.card_union_le (smallValues B k) (row B (k+1))
    have add:((smallValues B (k+1)).card:ℝ) ≤ ((smallValues B k).card:ℝ)+((row B (k+1)).card:ℝ) :=
      by exact_mod_cast cards
    have step := mul_le_mul_of_nonneg_left (sqrt_step k) (Real.sqrt_nonneg (B:ℝ))
    rw [mul_one_div] at step
    rw [Nat.cast_succ]
    linarith only [add,ih,row_card B k,step]

end ZInQBlueprint.SmallKernelCount
#print axioms ZInQBlueprint.SmallKernelCount.mem_smallValues
#print axioms ZInQBlueprint.SmallKernelCount.mem_of_repr
#print axioms ZInQBlueprint.SmallKernelCount.card_smallValues
