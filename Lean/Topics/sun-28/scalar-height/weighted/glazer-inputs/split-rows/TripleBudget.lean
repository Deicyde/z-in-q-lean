import SplitCount
import Mathlib.NumberTheory.Harmonic.Bounds

/-! A product budget for three integral squareclasses costs two harmonic sums. -/
namespace ZInQBlueprint.SplitRows
open Finset ZInQBlueprint.OriginalHeightCount
open scoped Classical
set_option maxRecDepth 12000
noncomputable section

def productTriples (K : ℕ) : Finset Triple :=
  ((Icc 1 K) ×ˢ ((Icc 1 K) ×ˢ (Icc 1 K))).filter fun t=>t.1*t.2.1*t.2.2≤K

theorem mem_productTriples {i j k K : ℕ} (pi : 0 < i) (pj : 0 < j) (pk : 0 < k)
    (p : i*j*k≤K) : (i,j,k)∈productTriples K := by
  have cij := Nat.le_mul_of_pos_right (i*j) pk
  have ci := Nat.le_mul_of_pos_right i pj
  have cj := Nat.le_mul_of_pos_left j pi
  have ck := Nat.le_mul_of_pos_left k (Nat.mul_pos pi pj)
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨pi,(ci.trans cij).trans p⟩,
    mem_product.mpr ⟨mem_Icc.mpr ⟨pj,(cj.trans cij).trans p⟩,mem_Icc.mpr ⟨pk,ck.trans p⟩⟩⟩,p⟩

theorem productTriples_card (K : ℕ) :
    ((productTriples K).card:ℝ) ≤ (K:ℝ)*(1+Real.log (K:ℝ))^2 := by
  let I:=Icc 1 K
  let S:=productTriples K
  let f (z : Triple) := (z.1,z.2.1)
  have maps : (S:Set Triple).MapsTo f ((I ×ˢ I : Finset (ℕ×ℕ)) : Set _) := by
    intro z hz
    obtain ⟨a,b⟩:=mem_product.mp (mem_filter.mp hz).1
    change (z.1,z.2.1)∈I ×ˢ I
    exact mem_product.mpr ⟨a,(mem_product.mp b).1⟩
  have fibre (q : ℕ × ℕ) (hq:q∈I ×ˢ I) :
      ((S.filter fun z=>f z=q).card:ℝ) ≤ (K:ℝ)*(q.1:ℝ)⁻¹*(q.2:ℝ)⁻¹ := by
    obtain ⟨i,j⟩:=q
    have ip : 0 < i := (mem_Icc.mp (mem_product.mp hq).1).1
    have jp : 0 < j := (mem_Icc.mp (mem_product.mp hq).2).1
    have ij := Nat.mul_pos ip jp
    have bound : (S.filter fun z=>f z=(i,j)).card≤(Icc 1 (K/(i*j))).card := by
      apply card_le_card_of_injOn (fun (z:Triple)=>z.2.2)
      · intro z hz
        obtain ⟨hS,hf⟩:=mem_filter.mp hz
        obtain ⟨pos,lim⟩:=mem_filter.mp hS
        obtain ⟨r,s,t⟩:=z
        have id : r=i ∧ s=j := Prod.mk.inj hf
        obtain ⟨rfl,rfl⟩:=id
        exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_product.mp (mem_product.mp pos).2).2).1,
          (Nat.le_div_iff_mul_le ij).mpr (by simpa [Nat.mul_comm t] using lim)⟩
      · intro z hz w hw eq
        have e : f z=f w := (mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm
        have hh := Prod.mk.inj (show (z.1,z.2.1)=(w.1,w.2.1) from e)
        exact Prod.ext hh.1 (Prod.ext hh.2 eq)
    have bound' : (S.filter fun z=>f z=(i,j)).card ≤ K/(i*j) := by
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using bound
    have cost := (Nat.le_div_iff_mul_le ij).mp bound'
    have real : (((S.filter fun z=>f z=(i,j)).card:ℕ):ℝ)*((i:ℝ)*j)≤K := by exact_mod_cast cost
    have ir : (i:ℝ)≠0 := by exact_mod_cast ip.ne'
    have jr : (j:ℝ)≠0 := by exact_mod_cast jp.ne'
    change _≤(K:ℝ)*(i:ℝ)⁻¹*(j:ℝ)⁻¹
    rw [←div_eq_mul_inv,←div_eq_mul_inv]
    apply (le_div_iff₀ (by exact_mod_cast jp)).mpr
    apply (le_div_iff₀ (by exact_mod_cast ip)).mpr
    convert real using 1; ring
  have total := card_eq_sum_card_fiberwise (s:=S) (t:=I ×ˢ I) (f:=f) maps
  have lifted : (S.card:ℝ)=∑ q ∈ I ×ˢ I, ((S.filter fun z=>f z=q).card:ℝ) := by exact_mod_cast total
  have harmonicSum : ∑ i ∈ I, (i:ℝ)⁻¹=(harmonic K:ℝ) := by
    simp only [I,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  have harmNon : 0≤(harmonic K:ℝ) := by rw [←harmonicSum];positivity
  calc
    ((productTriples K).card:ℝ) = _ := lifted
    _ ≤ ∑ q ∈ I ×ˢ I, (K:ℝ)*(q.1:ℝ)⁻¹*(q.2:ℝ)⁻¹ := sum_le_sum fibre
    _ = (K:ℝ)*(harmonic K:ℝ)^2 := by
      rw [sum_product]
      simp_rw [←Finset.mul_sum,harmonicSum]
      rw [←Finset.sum_mul,←Finset.mul_sum,harmonicSum];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ harmNon (harmonic_le_one_add_log K) 2) (by positivity)

theorem count_with_product (S : Finset ℚ) {B K : ℕ}
    (rep : ∀ x∈S, ∃ s : Record x B K, s.i*s.j*s.k≤K) :
    (S.card:ℝ) ≤ 18*(size B:ℝ)*K*(1+Real.log (K:ℝ))^2 := by
  have count:=count_with_triples S (B:=B) (K:=K) (productTriples K) (by
    intro x hx
    obtain ⟨s,h⟩:=rep x hx
    exact ⟨s,mem_productTriples s.ip s.jp s.kp h⟩)
  have real : (S.card:ℝ)≤18*(size B:ℝ)*((productTriples K).card:ℝ) := by exact_mod_cast count
  calc
    _ ≤ _ := real
    _ ≤ 18*(size B:ℝ)*((K:ℝ)*(1+Real.log (K:ℝ))^2) :=
      mul_le_mul_of_nonneg_left (productTriples_card K) (by positivity)
    _ = _ := by ring

end
end ZInQBlueprint.SplitRows
#print axioms ZInQBlueprint.SplitRows.mem_productTriples
#print axioms ZInQBlueprint.SplitRows.productTriples_card
#print axioms ZInQBlueprint.SplitRows.count_with_product
