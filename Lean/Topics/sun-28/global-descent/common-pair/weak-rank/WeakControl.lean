import WeakRationalClasses
import OddGlobal

namespace Sun28.WeakRank
open Sun28.SelmerRealization Sun28.GlobalSections Sun28.MarkedOdd Sun28.FixedLocalRows
open ZInQ.RouteK ZInQ.RouteK.Selmer
noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The abscissa 20 has squareclass five, and the corresponding point on
E_10 has infinite order. Its ordered covering is already insoluble over Q_5. -/
theorem weak_without_ordered :
    strictPoint 5 10 ∧ (∃ P : RationalPoint 10, ¬IsOfFinAddOrder P) ∧
      ¬Cover ℚ_[5] 10 5 1 ∧ ¬Cover ℚ 10 5 1 := by
  have actual : strictPoint 5 10 := ⟨2,100,by norm_num,by norm_num,by norm_num⟩
  have sf : Squarefree 10 := by
    change Squarefree (2*5:ℕ)
    exact Nat.squarefree_mul_iff.mpr ⟨by decide,(by decide : Nat.Prime 2).squarefree,(by decide : Nat.Prime 5).squarefree⟩
  obtain ⟨P,_,order⟩ := strict_point_rank (b:=5) (k:=2) (l:=10) (by decide) (by decide) rfl sf actual
  have no : ¬Cover ℚ_[5] 10 5 1 := by
    intro H
    have row := (bad_rows (p:=5) (by decide) (by decide) (by decide : 5∣10) sf
      (Int.squarefree_natCast.mpr (by decide : Nat.Prime 5).squarefree) squarefree_one H).1
    norm_num [primeUnit,exponent,←parity_symbol,parity,symbol] at row
  exact ⟨actual,⟨P,order⟩,no,fun h=>no (cover_map h)⟩

end
end Sun28.WeakRank
#print axioms Sun28.WeakRank.weak_without_ordered
