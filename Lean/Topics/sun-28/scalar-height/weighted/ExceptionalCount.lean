import PointwiseHeight
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Data.Int.Interval

namespace Sun28.ScalarDepth
open Finset Height Sun28.ScalarHeight Sun28.ScalarLucas Sun28.Ordinary Sun28.PointPencils
noncomputable section

private def window (n : ℕ) : Finset ℤ := Icc (-(n:ℤ)) (n:ℤ)
private def naiveBox (B : ℕ) : Finset ℚ :=
  ((window B ×ˢ Icc (1:ℤ) (B:ℤ)).image fun (a,b) => (a:ℚ)/(b:ℚ)).filter
    fun x : ℚ => max x.num.natAbs x.den ≤ B

theorem mem_box (x : ℚ) (B : ℕ) : x∈naiveBox B ↔ max x.num.natAbs x.den≤B := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    refine mem_filter.mpr ⟨mem_image.mpr ⟨(x.num,(x.den:ℤ)),mem_product.mpr ⟨?_,?_⟩,?_⟩,h⟩
    · apply mem_Icc.mpr
      apply abs_le.mp
      rw [←Int.natCast_natAbs]
      exact_mod_cast (max_le_iff.mp h).1
    · apply mem_Icc.mpr
      change 1 ≤ (x.den:ℤ) ∧ (x.den:ℤ) ≤ B
      exact ⟨by exact_mod_cast (show 1≤x.den from x.den_pos),by exact_mod_cast (max_le_iff.mp h).2⟩
    · simpa using x.num_div_den

/-- Rational inputs up to naive height B that violate Glazer's original scalar inequality. -/
def exceptionalInputs (B : ℕ) : Finset ℚ :=
  (naiveBox B).filter fun x => glazerConstant24*(radical x:ℝ)^24 < logHeight₁ (beta x)

private def parameters (B K : ℕ) := (window K.sqrt ×ˢ window K.sqrt) ×ˢ
  ((window (2*B).sqrt ×ˢ window (2*B).sqrt) ×ˢ (univ : Finset Bool))

private def value : (ℤ×ℤ) × (ℤ×ℤ) × Bool → ℚ
  | ((u,v),(m,n),swap) =>
    let (p,c) := if swap then (2*m*n,m^2-n^2) else (m^2-n^2,2*m*n)
    ((u*p-v*c:ℤ):ℚ)/((v*p+u*c:ℤ):ℚ)

private theorem root_mem {i : ℤ} {n : ℕ} (h : i^2 ≤ (n:ℤ)) : i∈window n.sqrt := by
  have bound : i.natAbs^2≤n := by
    have t : (i.natAbs:ℤ)^2 ≤ (n:ℤ) := by rw [Int.natCast_natAbs,sq_abs];exact h
    exact_mod_cast t
  have small := Nat.le_sqrt'.mpr bound
  apply mem_Icc.mpr
  apply abs_le.mp
  rw [←Int.natCast_natAbs]
  exact_mod_cast small

theorem circle_parametrization {x : ℚ} {B K d w : ℕ} {u v p c : ℤ}
    (box : max x.num.natAbs x.den≤B) (small : d≤K) (h : Circle x d w u v p c) :
    x ∈ (parameters B K).image value := by
  obtain ⟨m,n,legs,eqw,_,_⟩ := PythagoreanTriple.coprime_classification.mp
    ⟨(show PythagoreanTriple p c (w:ℤ) by simpa only [PythagoreanTriple,pow_two] using h.equation),
     Int.isCoprime_iff_gcd_eq_one.mp h.primitive⟩
  have eq : (w:ℤ)=m^2+n^2 := eqw.resolve_right (by have := h.positive; nlinarith [sq_nonneg m,sq_nonneg n])
  have seed := h.seed
  have ks : (d:ℤ)≤K := by exact_mod_cast small
  have uw := root_mem (show u^2≤(K:ℤ) by linarith only [seed,ks,sq_nonneg v])
  have vw := root_mem (show v^2≤(K:ℤ) by linarith only [seed,ks,sq_nonneg u])
  have wd : x.num^2+(x.den:ℤ)^2=(d:ℤ)*(w:ℤ)^2 := by
    rw [h.point.1,h.point.2,←h.seed,←h.equation];ring
  have absn : |x.num|≤(B:ℤ) := by
    rw [←Int.natCast_natAbs];exact_mod_cast (max_le_iff.mp box).1
  have den : (x.den:ℤ)≤B := by exact_mod_cast (max_le_iff.mp box).2
  have ua := mul_self_le_mul_self (abs_nonneg x.num) absn
  have ub := mul_self_le_mul_self (Int.natCast_nonneg x.den) den
  have lower : 1≤(d:ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h.squarefree.ne_zero
  have wbound : (w:ℤ) ≤ 2*B := by
    rw [←sq_abs x.num] at wd
    by_contra! high
    nlinarith only [wd,ua,ub,mul_nonneg (sub_nonneg.mpr lower) (sq_nonneg (w:ℤ)),
      mul_pos (sub_pos.mpr high) (show 0<(w:ℤ)+2*B by have := h.positive; positivity),sq_nonneg (B:ℤ)]
  have mn := root_mem (n:=(2*B)) (i:=m) (by push_cast; linarith only [eq,wbound,sq_nonneg n])
  have nn := root_mem (n:=(2*B)) (i:=n) (by push_cast; linarith only [eq,wbound,sq_nonneg m])
  have out : ((x.num:ℚ)/(x.den:ℚ))=x := x.num_div_den
  rcases legs with l|r
  · refine mem_image.mpr ⟨((u,v),(m,n),false), mem_product.mpr
      ⟨mem_product.mpr ⟨uw,vw⟩, mem_product.mpr ⟨mem_product.mpr ⟨mn,nn⟩,mem_univ _⟩⟩,?_⟩
    change (((u*(m^2-n^2)-v*(2*m*n):ℤ):ℚ)/((v*(m^2-n^2)+u*(2*m*n):ℤ):ℚ))=x
    rw [←l.1,←l.2,←h.point.1,←h.point.2]
    simpa using out
  · refine mem_image.mpr ⟨((u,v),(m,n),true), mem_product.mpr
      ⟨mem_product.mpr ⟨uw,vw⟩, mem_product.mpr ⟨mem_product.mpr ⟨mn,nn⟩,mem_univ _⟩⟩,?_⟩
    change (((u*(2*m*n)-v*(m^2-n^2):ℤ):ℚ)/((v*(2*m*n)+u*(m^2-n^2):ℤ):ℚ))=x
    rw [←r.1,←r.2,←h.point.1,←h.point.2]
    simpa using out

theorem exceptional_count {B K : ℕ} (threshold : 2*Real.log (B:ℝ)+4 ≤ ((K+1:ℕ):ℝ)^24) :
    (exceptionalInputs B).card ≤ 2*(2*K.sqrt+1)^2*(2*(2*B).sqrt+1)^2 := by
  classical
  have sub : exceptionalInputs B ⊆ (parameters B K).image value := by
    intro x hx
    have ⟨b,f⟩ := mem_filter.mp hx
    have box := (mem_box _ _).mp b
    obtain ⟨d,w,u,v,p,c,h⟩ := realized_circle x
    have cut := (exceptional_kernel box f h).trans_le threshold
    have dk : d≤K := by
      by_contra! no
      have le : ((K+1:ℕ):ℝ) ≤ d := by exact_mod_cast no
      exact (not_le_of_gt cut) (pow_le_pow_left₀ (by positivity) le 24)
    exact circle_parametrization box dk h
  have win (n : ℕ) : (window n).card=2*n+1 := by simp only [window,Int.card_Icc];omega
  apply (card_le_card sub).trans
  apply card_image_le.trans
  apply le_of_eq
  simp only [parameters,card_product,win,card_univ,Fintype.card_bool]
  ring

end
end Sun28.ScalarDepth
#print axioms Sun28.ScalarDepth.mem_box
#print axioms Sun28.ScalarDepth.circle_parametrization
#print axioms Sun28.ScalarDepth.exceptional_count
