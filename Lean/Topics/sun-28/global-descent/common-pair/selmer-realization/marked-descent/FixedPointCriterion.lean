import GoodMarked
import MarkedSeparation

namespace Sun28.MarkedDescent
open Sun28.SelmerRealization

theorem finite_descent_iff_card :
    FiniteDescent n 526361 1 ↔ (localClasses n).ncard=8 :=
  ⟨And.left,fun size=>⟨size,fixed_membership⟩⟩

theorem prepared_scalar_of_card [AddGroup.FG (RationalPoint n)]
    (size : (localClasses n).ncard=8)
    (point : ∃ P : RationalPoint n, ¬IsOfFinAddOrder P) :
    ∃ e z : ℚ, Sun28.Ordinary.poleBranch 15 Sun28.PointFibres.pole e z :=
  prepared_scalar (finite_descent_iff_card.mpr size) point

end Sun28.MarkedDescent
#print axioms Sun28.MarkedDescent.finite_descent_iff_card
#print axioms Sun28.MarkedDescent.prepared_scalar_of_card
