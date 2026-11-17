import DiagonalApplication
import BoxesAt
import SeparateEstimates

namespace Sun28.SinglePrime
open Sun28.ContactFactors Sun28.SieveTail Sun28.WeightedSelection Sun28.MixedSieve
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ}

def pairBound (N V R : ℕ) (i j : ↥(shifts A)) : ℚ :=
  if i=j then
    let B:=Nat.sqrt (N+(offset (dilation A) i.val).natAbs*V^2)
    (2*(B:ℚ)+1)*(Nat.log 2 (B^2+1):ℚ)*((2*(B:ℚ)+1)/R+1)
  else
    let B:=radius N V i j
    let K:=gap i j*(V:ℤ)^2
    let L:=2*(B:ℚ)+1
    K.natAbs.divisors.card*(8*(Nat.log 2 (K.natAbs+2*B):ℚ)*(L/R+1))*(L*harmonic B+B)

theorem pair_bound (boxes : CountingBoxes A d H Y) (N V R : ℕ) (two : 2≤R) (i j : ↥(shifts A)) :
    ((pairRecords boxes N V R i j).card:ℚ)≤pairBound N V R i j := by
  by_cases h : i=j
  · subst j;simpa [pairBound] using diagonal_records boxes N V R two i
  · simpa only [pairBound,ite_eq_right h] using offdiag_records boxes (by omega : 0<R) i j h

def indices (A : Fin 3→ℚ) (W : ℕ) : Finset (ℕ×(↥(shifts A)×↥(shifts A))) :=
  (Finset.Icc 1 W) ×ˢ Finset.univ

def maxCoefficient (A : Fin 3→ℚ) : ℕ :=
  Finset.univ.sup (fun i : ↥(shifts A)=> (offset (dilation A) i.val).natAbs)

def weightBound (A : Fin 3→ℚ) (N W : ℕ) : ℝ :=
  (Real.log ((N+maxCoefficient A*W^2+1:ℕ):ℝ))^(shifts A).card

theorem weight_bound (a : Record A d H Y) {N W : ℕ} (u : a.u≤N) (v : a.v≤W) :
    weight a ≤ weightBound A N W := by
  let n:=N+maxCoefficient A*W^2+1
  have each (i : ↥(shifts A)) : a.values.value i.val≤n := by
    have c : (offset (dilation A) i.val).natAbs≤ maxCoefficient A :=
      Finset.le_sup (f:=fun r : ↥(shifts A)=>(offset (dilation A) r.val).natAbs) (Finset.mem_univ i)
    have coe : offset (dilation A) i.val≤(maxCoefficient A:ℤ) :=
      (le_abs_self _).trans (by rw [←Int.natCast_natAbs];exact_mod_cast c)
    have pos:=Nat.pow_le_pow_left v 2
    have bound : (a.values.value i.val:ℤ) ≤ (N:ℤ)+(maxCoefficient A:ℤ)*(W:ℤ)^2 := by
      rw [a.values.equation i.val i.property]
      exact add_le_add (by exact_mod_cast u) ((mul_le_mul_of_nonneg_right coe (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast pos) (by positivity)))
    exact_mod_cast bound.trans (show (N:ℤ)+(maxCoefficient A:ℤ)*(W:ℤ)^2≤(n:ℤ) by dsimp [n];omega)
  have h := Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun i : ↥(shifts A)=>Real.log (a.values.value i.val:ℝ)) (g:=fun _ : ↥(shifts A)=>Real.log (n:ℝ))
    (fun i _=>Real.log_nonneg (by exact_mod_cast (a.values.prime i.val i.property).one_lt.le))
    (fun i _=>Real.log_le_log (by exact_mod_cast (a.values.prime i.val i.property).pos) (by exact_mod_cast each i))
  simpa only [weight,weightBound,Finset.prod_const,Finset.card_univ,Fintype.card_coe,n] using h

/-- The full removed weight is bounded by an explicit finite sum over the denominator
and the ordered pair of shifts, including the diagonal. -/
theorem removed_le_sum (boxes : CountingBoxes A d H Y) (N R : ℕ) (two : 2≤R) (T : Finset ℕ) (κ : ℕ)
    (hT : ∀ p∈T,p≤R) (hκ : ∀ p∈κ.primeFactors,p≤R) :
    removedMass T κ R (boxes.records N) ≤ weightBound A N (boxes.width N)*
      (∑ k∈indices A (boxes.width N),pairBound N k.1 R k.2.1 k.2.2 : ℚ) := by
  let S := (boxes.records N).filter (fun a=> below a T κ R ∧ tail a T κ R)
  let J:=indices A (boxes.width N)
  let P := fun k : ℕ×(↥(shifts A)×↥(shifts A))=>pairRecords boxes N k.1 R k.2.1 k.2.2
  have cover : S⊆J.biUnion P := by
    intro a ha
    obtain ⟨ar,_,p,pp,odd,_,large,lost⟩:=Finset.mem_filter.mp ha
    let _ : Fact p.Prime:=⟨pp⟩
    have h:=atPrime_iff_fibre a T κ p odd (fun mem=>large.not_ge (hT p mem)) (fun mem=>large.not_ge (hκ p mem))
    obtain ⟨i,j,plus,minus⟩:= (fibre_obstructed_iff a p).mp (Classical.not_not.mp (fun miss=>lost (h.mpr miss)))
    refine Finset.mem_biUnion.mpr ⟨(a.v,i,j),Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨a.positive,(boxes.inBox N a ar).2.2⟩,Finset.mem_univ _⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨ar,rfl,p,pp,large,plus,minus⟩
  have card : (S.card:ℚ)≤∑ k∈J,pairBound N k.1 R k.2.1 k.2.2 := calc
    _ ≤ ((J.biUnion P).card:ℚ) := by exact_mod_cast Finset.card_le_card cover
    _ ≤ ∑ k∈J,((P k).card:ℚ) := by exact_mod_cast Finset.card_biUnion_le (s:=J) (t:=P)
    _ ≤ _ := Finset.sum_le_sum (fun k _=>pair_bound boxes N k.1 R two k.2.1 k.2.2)
  let M:=weightBound A N (boxes.width N)
  have non : 0≤M := pow_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 _))) _
  change (∑ a∈S,weight a) ≤ _
  calc
    _ ≤ ∑ _∈S,M := Finset.sum_le_sum (fun a ha=>by
      have q:=boxes.inBox N a (Finset.mem_filter.mp ha).1
      exact weight_bound a q.2.1 q.2.2)
    _ = M*(S.card:ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast card) non

theorem numerical_tail (N W R : ℕ) (two : 2≤R) (T : Finset ℕ) (κ : ℕ)
    (hT : ∀ p∈T,p≤R) (hκ : ∀ p∈κ.primeFactors,p≤R) :
    removedMass T κ R (box (A:=A) (d:=d) (H:=H) (Y:=Y) N W) ≤ weightBound A N W*
      (∑ k∈indices A W,pairBound N k.1 R k.2.1 k.2.2 : ℚ) := by
  obtain ⟨boxes,w,rec⟩:=boxes_at A d H Y N W
  simpa only [w,rec] using removed_le_sum boxes N R two T κ hT hκ

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.pair_bound
#print axioms Sun28.SinglePrime.weight_bound
#print axioms Sun28.SinglePrime.removed_le_sum
#print axioms Sun28.SinglePrime.numerical_tail
