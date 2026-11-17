import Covers
import TripleBudget

/-! Exceptional slopes on the original marked line with all three coefficient sizes summed. -/
namespace ZInQBlueprint.FiveCovers
open Finset Height ZInQBlueprint.SplitRows ZInQBlueprint.OriginalHeightCount Sun28.Ordinary
noncomputable section

theorem bounded_record {x : ℚ} {B K : ℕ} (atx : x∈exceptions B)
    (threshold : Real.log (B:ℝ) ≤ ((K+1:ℕ):ℝ)^24) :
    ∃ s : Record x B K, s.i*s.j*s.k≤K := by
  obtain ⟨box,off,_⟩:=(mem_exceptions x B).mp atx
  obtain ⟨d,u,all,prod⟩:=simultaneous_squareclasses atx threshold
  let k (i : Fin 5) := (d i).natAbs
  have kp (i) : 0<k i := Int.natAbs_pos.mpr (all i).1.ne_zero
  have cap (i) : k i≤K := (single_le_prod (s:=univ) (f:=k) (fun j _=>kp j) (mem_univ i)).trans prod
  have neA : x.num≠0 := off 1
  have neC : x.num-(x.den:ℤ)≠0 := off 2
  have eqn (i) : (oldForm i x.num x.den).natAbs=k i*(u i).natAbs^2 := by
    simpa only [k,Int.natAbs_mul,Int.natAbs_pow] using congrArg Int.natAbs (all i).2.2
  have den : x.den=k 0*(u 0).natAbs^2 := by
    have h := eqn 0
    change (x.den:ℤ).natAbs=_ at h
    simpa only [Int.natAbs_natCast] using h
  obtain ⟨s,e⟩:=record_of_rows (max_le_iff.mp box).1 (max_le_iff.mp box).2 neA neC
    (kp 1) (kp 0) (kp 2) (cap 1) (cap 0) (cap 2) (eqn 1) den (eqn 2)
  change (∏ i,k i)≤K at prod
  rw [Fin.prod_univ_five] at prod
  have t := (Nat.le_mul_of_pos_right (k 0*k 1*k 2) (kp 3)).trans
    ((Nat.le_mul_of_pos_right (k 0*k 1*k 2*k 3) (kp 4)).trans prod)
  exact ⟨s,by rw [e,mul_comm (k 1) (k 0)];exact t⟩

/-- The count for actual failures, with a single product budget for the three squarefree parts. -/
theorem exceptional_count {B K : ℕ} (threshold : Real.log (B:ℝ) ≤ ((K+1:ℕ):ℝ)^24) :
    ((exceptions B).card:ℝ) ≤ 18*((Nat.sqrt (2*B)+1:ℕ):ℝ)*K*(1+Real.log (K:ℝ))^2 :=
  count_with_product _ (fun _ h=>bounded_record h threshold)

end
end ZInQBlueprint.FiveCovers
#print axioms ZInQBlueprint.FiveCovers.bounded_record
#print axioms ZInQBlueprint.FiveCovers.exceptional_count
