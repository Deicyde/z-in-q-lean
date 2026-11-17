import BranchWeights
import ThomaeBranchPoints

/-! Reciprocal coordinates on the six branch points. Each pair of the five finite
indices represents a partition of the original six points into two triples. -/
namespace ZInQBlueprint.BranchFormula
open ThetaPeriod BranchI4
noncomputable section

structure Row where
  p : Fin 5
  q : Fin 5
  a : Fin 5
  b : Fin 5
  c : Fin 5
deriving DecidableEq

def row : Fin 10 → Row := ![⟨0,1,2,3,4⟩, ⟨0,2,1,3,4⟩, ⟨0,3,1,2,4⟩, ⟨0,4,1,2,3⟩, ⟨1,2,0,3,4⟩, ⟨1,3,0,2,4⟩, ⟨1,4,0,2,3⟩, ⟨2,3,0,1,4⟩, ⟨2,4,0,1,3⟩, ⟨3,4,0,1,2⟩]

private theorem ordered (i : Fin 10) : (row i).p < (row i).q ∧
    (row i).a < (row i).b ∧ (row i).b < (row i).c := by decide +revert

def pair (i : Fin 10) : Partition :=
  ⟨{(row i).p,(row i).q}, by have h := (ordered i).1.ne; simp [h]⟩

def pairs : Fin 10 ≃ Partition := Equiv.ofBijective pair (by decide)

private theorem complement (i : Fin 10) : Finset.univ \ (pair i).val =
    {(row i).a,(row i).b,(row i).c} := by decide +revert

private theorem pair_differences (v : Fin 5 → ℂ) {p q : Fin 5} (h : p < q) :
    differences v {p,q} = v p - v q := by
  simp [differences,Finset.filter_insert,Finset.filter_singleton, h,h.ne, not_lt_of_ge h.le]

private theorem triple_differences (v : Fin 5 → ℂ) {a b c : Fin 5} (hab : a<b) (hbc : b<c) :
    differences v {a,b,c} = (v a-v b)*(v a-v c)*(v b-v c) := by
  have hac := hab.trans hbc
  simp [differences,Finset.filter_insert,Finset.filter_singleton, hab,hbc,hac,hab.ne,hbc.ne,hac.ne,
    not_lt_of_ge hab.le, not_lt_of_ge hbc.le, not_lt_of_ge hac.le]

theorem branch_row (v : Fin 5 → ℂ) (i : Fin 10) :
    branchValue v (pairs i) =
      ((v (row i).p-v (row i).q) *
       ((v (row i).a-v (row i).b)*(v (row i).a-v (row i).c)*(v (row i).b-v (row i).c)))^2 := by
  obtain ⟨hpq,hab,hbc⟩ := ordered i
  change (differences v {(row i).p,(row i).q} * differences v (Finset.univ \ (pair i).val))^2 = _
  rw [complement, pair_differences v hpq,triple_differences v hab hbc]

def distance (r : Fin 6 → ℂ) (i : Fin 5) := r i.castSucc - r (Fin.last 5)
def denominator (r : Fin 6 → ℂ) := ∏ i, distance r i

theorem denominator_ne {r : Fin 6 → ℂ} (hr : Function.Injective r) : denominator r ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hr.ne (Fin.castSucc_ne_last i)))

private theorem reciprocal_difference {r : Fin 6 → ℂ} (hr : Function.Injective r) (i j : Fin 5) :
    (finiteBranches r i - finiteBranches r j)*(distance r i * distance r j) =
      -(r i.castSucc-r j.castSucc) := by
  have hn (k : Fin 5) : distance r k ≠ 0 := sub_ne_zero.mpr (hr.ne (Fin.castSucc_ne_last k))
  change ((distance r i)⁻¹ - (distance r j)⁻¹) * _ = _
  rw [sub_mul]
  calc ((distance r i)⁻¹ * (distance r i * distance r j) -
        (distance r j)⁻¹ * (distance r i * distance r j)) =
        distance r j-distance r i := by field_simp [hn]
       _ = _ := by unfold distance; ring

theorem denominator_five (r : Fin 6 → ℂ) : denominator r =
    distance r 0 * distance r 1 * distance r 2 * distance r 3 * distance r 4 := by
  simp only [denominator, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change distance r 0*(distance r 1*(distance r 2*(distance r 3*distance r 4))) = _
  ac_rfl

private theorem denominator_row (r : Fin 6 → ℂ) (i : Fin 10) :
    denominator r = distance r (row i).p * distance r (row i).q * distance r (row i).a *
      distance r (row i).b * distance r (row i).c := by
  rw [denominator_five]
  fin_cases i <;> dsimp [row] <;> ring

def vandermonde (r : Fin 6 → ℂ) : ℂ :=
  ∏ i, ∏ j, if i < j then r i-r j else 1

private def edgeWeight (e : Fin 6 → Fin 6 → ℂ) (i : Fin 10) :=
  let t := row i
  let a := t.a.castSucc
  let b := t.b.castSucc
  let c := t.c.castSucc
  let p := t.p.castSucc
  let q := t.q.castSucc
  ((e p q * e p 5 * e q 5) * (e a b * e a c * e b c))^2

def rowWeight (r : Fin 6 → ℂ) (i : Fin 10) :=
  edgeWeight (fun j k => r j-r k) i

private theorem regroup (e f g h p q a b c : ℂ) :
    (e*(f*g*h))^2 * (p*q*a*b*c)^4 =
      ((e*(p*q))*((f*(a*b))*(g*(a*c))*(h*(b*c)))*p*q)^2 := by ring

theorem clear_row {r : Fin 6 → ℂ} (hr : Function.Injective r) (i : Fin 10) :
    branchValue (finiteBranches r) (pairs i) * denominator r^4 = rowWeight r i := by
  rw [branch_row,denominator_row r i,regroup]
  simp only [reciprocal_difference hr]
  dsimp [rowWeight, edgeWeight, distance]
  ring

theorem sum_rowWeights (r : Fin 6 → ℂ) : ∑ i, rowWeight r i = weightSum r := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change rowWeight r 0 + (rowWeight r 1 + (rowWeight r 2 + (rowWeight r 3 + (rowWeight r 4 + (rowWeight r 5 + (rowWeight r 6 + (rowWeight r 7 + (rowWeight r 8 + (rowWeight r 9))))))))) = _
  change weight r 0 1 2 3 4 + (weight r 0 2 1 3 4 + (weight r 0 3 1 2 4 + (weight r 0 4 1 2 3 + (weight r 1 2 0 3 4 + (weight r 1 3 0 2 4 + (weight r 1 4 0 2 3 + (weight r 2 3 0 1 4 + (weight r 2 4 0 1 3 + (weight r 3 4 0 1 2))))))))) = _
  unfold weightSum
  abel

/-- Each edge occurs in four of the ten partitions. Each contribution is a square. -/
theorem prod_rowWeights (r : Fin 6 → ℂ) :
    ∏ i, rowWeight r i = (vandermonde r)^8 := by
  let e (j k : Fin 6) : ℂ := r j-r k
  change (∏ i, edgeWeight e i) = _
  have formula (w : Fin 6 → Fin 6 → ℂ) :
      (∏ i, edgeWeight w i) = (∏ j, ∏ k, if j < k then w j k else 1)^8 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    norm_num [edgeWeight,row, Fin.lt_def]
    ring
  exact formula e

end
end ZInQBlueprint.BranchFormula
#print axioms ZInQBlueprint.BranchFormula.pairs
#print axioms ZInQBlueprint.BranchFormula.branch_row
#print axioms ZInQBlueprint.BranchFormula.denominator_ne
#print axioms ZInQBlueprint.BranchFormula.clear_row
#print axioms ZInQBlueprint.BranchFormula.sum_rowWeights
#print axioms ZInQBlueprint.BranchFormula.prod_rowWeights
