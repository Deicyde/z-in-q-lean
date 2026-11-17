import MonicBranchMove
import RationalReduction

/-! The two triples and the actual twist force even orders of all the fourth-division radicands. -/
namespace SixContactFour
open Finset Polynomial IsDiscreteValuationRing
open ZInQBlueprint.ClusterRoots ZInQBlueprint.ClusterPicture
noncomputable section

def fixedBranch : Index := (0,0)
def others : Fin 5 → Index := ![(0,1),(0,2),(1,0),(1,1),(1,2)]

private theorem other_neq (i : Fin 5) : fixedBranch ≠ others i := by fin_cases i <;> decide
private theorem others_inj : Function.Injective others := by decide

/-- Number of within-triple differences in the product. It is one or three, for all ten pairs. -/
private def withinCount (i j : Fin 5) : ℕ :=
    (if (others i).1=(others j).1 then 1 else 0) +
      ∑ k ∈ (univ.erase i).erase j, (if fixedBranch.1=(others k).1 then 1 else 0)

private theorem withinCount_val (i j : Fin 5) (hij : i ≠ j) :
    withinCount i j=1 ∨ withinCount i j=3 := by
  revert i j
  decide

private theorem valuation_prod {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (t : Finset (Fin 5)) (f : Fin 5 → S) :
    addVal S (∏ i ∈ t, f i) = ∑ i ∈ t, addVal S (f i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => simp [hi,ih]

/-- Field-independent finite valuations for integral roots of the moved quintic. -/
theorem oddRoot_order {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (r : Index → S) (c : S) (lead d : ℕ) (hc : addVal S c=(lead:ℕ∞))
    (dist : ∀ i j : Index, i ≠ j → addVal S (r i-r j) =
      ((if i.1=j.1 then d else 0 : ℕ):ℕ∞))
    (i j : Fin 5) (hij : i ≠ j) :
    addVal S (oddRoot c (r fixedBranch) (r ∘ others) i-oddRoot c (r fixedBranch) (r ∘ others) j) =
      ((lead+withinCount i j*d : ℕ):ℕ∞) := by
  rw [oddRoot_sub _ _ _ _ _ hij,addVal_mul,addVal_mul,AddValuation.map_neg,hc,valuation_prod]
  change (lead:ℕ∞)+addVal S (r (others i)-r (others j))+
    ∑ k ∈ (univ.erase i).erase j, addVal S (r fixedBranch-r (others k)) = _
  rw [dist _ _ (fun h => hij (others_inj h))]
  simp_rw [dist _ _ (other_neq _)]
  unfold withinCount
  rw [add_mul,Finset.sum_mul]
  simp only [ite_mul,one_mul,zero_mul,Nat.cast_add,Nat.cast_sum]
  simp only [add_assoc]

/-- If leading order plus the depth is even, all finite branch differences of the quintic
have even noninfinite order. This includes ordinary fibres by taking depth zero. -/
theorem all_even {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (r : Index → S) (c : S) (lead d : ℕ) (hc : addVal S c=(lead:ℕ∞))
    (dist : ∀ i j : Index, i ≠ j → addVal S (r i-r j) =
      ((if i.1=j.1 then d else 0 : ℕ):ℕ∞))
    (parity : Even (lead+d)) (i j : Fin 5) (hij : i ≠ j) :
    ∃ e : ℕ, addVal S (oddRoot c (r fixedBranch) (r ∘ others) i -
      oddRoot c (r fixedBranch) (r ∘ others) j)=((2*e:ℕ):ℕ∞) := by
  rw [oddRoot_order r c lead d hc dist i j hij]
  obtain ⟨q,hq⟩ := parity
  rcases withinCount_val i j hij with he|he
  · exact ⟨q, by rw [he]; congr 1; omega⟩
  · exact ⟨q+d, by rw [he]; congr 1; omega⟩

/-- If the six branch differences and the leading coefficient are units, every
transformed quintic branch difference has valuation zero. -/
theorem ordinary_differences {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (r : Index → S) (c : S) (hc : IsUnit c)
    (separate : ∀ i j : Index, i ≠ j → IsUnit (r i-r j)) (i j : Fin 5) (ij : i ≠ j) :
    addVal S (oddRoot c (r fixedBranch) (r ∘ others) i - oddRoot c (r fixedBranch) (r ∘ others) j)=0 := by
  have hv : ∀ i j : Index, i ≠ j → addVal S (r i-r j)=((if i.1=j.1 then 0 else 0 : ℕ):ℕ∞) := by
    intro k l h
    simp [addVal_eq_zero_iff.mpr (separate _ _ h)]
  simpa using oddRoot_order r c 0 0 (addVal_eq_zero_iff.mpr hc) hv i j ij

/-- Dividing by a square leaves a unit of the integral root ring. -/
theorem square_times_unit {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {x π : S} (hp : Irreducible π) {e : ℕ} (h : addVal S x=((2*e:ℕ):ℕ∞)) :
    ∃ a : Sˣ, x = (π^e)^2*(a:S) := by
  have nx : x ≠ 0 := fun ex => ENat.natCast_ne_top _ (by rw [← h,ex,addVal_zero])
  obtain ⟨m,v,hm⟩ := eq_unit_mul_pow_irreducible nx hp
  have em : m=2*e := ENat.natCast_inj.mp ((addVal_def _ v hp m hm).symm.trans h)
  refine ⟨v,?_⟩
  rw [hm,em,←pow_mul,Nat.mul_comm 2 e,mul_comm]

end
end SixContactFour
#print axioms SixContactFour.oddRoot_order
#print axioms SixContactFour.all_even
#print axioms SixContactFour.ordinary_differences
#print axioms SixContactFour.square_times_unit
