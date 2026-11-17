import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! Among four sections only the smaller two contact orders can contribute to the loss. -/
namespace ZInQBlueprint.FiveMetric
open Finset

def sectionValue (i : Fin 4) : ℤ := ![0,32,76832,-343] i

private theorem min_dvd {P Q : ℤ} {T : ℕ} (Tnz:T≠0) (div : GCDMonoid.gcd P Q ∣ (T:ℤ))
    (p : ℕ) [Fact p.Prime] (Pnz : P≠0) (Qnz : Q≠0) :
    min (padicValInt p P) (padicValInt p Q) ≤ padicValNat p T := by
  let n:=min (padicValInt p P) (padicValInt p Q)
  have powP : (p:ℤ)^n ∣ P := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa [Int.natAbs_pow] using (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr Pnz)).2
      (min_le_left (padicValInt p P) (padicValInt p Q))
  have powQ : (p:ℤ)^n ∣ Q := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa [Int.natAbs_pow] using (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr Qnz)).2
      (min_le_right (padicValInt p P) (padicValInt p Q))
  have ab: (p:ℤ)^n ∣ (T:ℤ):=(dvd_gcd powP powQ).trans div
  have nat : p^n ∣ T:=by exact_mod_cast ab
  exact (padicValNat_dvd_iff_le Tnz).1 nat

private theorem triple_divisibility {i j k : Fin 4} (ij:i≠j) (ik:i≠k) (jk:j≠k) :
    GCDMonoid.gcd (sectionValue i-sectionValue j) (sectionValue i-sectionValue k) ∣ (823200:ℤ) := by
  revert i j k
  decide

/-- This condition is precisely the ultrametric inequality applied to each pair of section differences. -/
def ContactOrders (p : ℕ) (r : Fin 4→ℤ) : Prop := ∀ i j, i≠j →
    min (r i) (r j) ≤ (padicValInt p (sectionValue i-sectionValue j) : ℤ)

theorem middle_orders {p : ℕ} [Fact p.Prime] {r : Fin 4→ℤ} (h:ContactOrders p r)
    {i j k : Fin 4} (ij:i≠j) (ik:i≠k) (jk:j≠k) :
    min (r i) (min (r j) (r k)) ≤ padicValInt p 823200 := by
  have diff {a b : Fin 4} (ne : a≠b) : sectionValue a-sectionValue b≠0 := by
    revert a b
    decide
  have d:=triple_divisibility ij ik jk
  have val:=min_dvd (p:=p) (Pnz:=diff ij) (Qnz:=diff ik)
    (T:=823200) (by decide) d
  change _ ≤ padicValInt p 823200 at val
  have a:=h i j ij
  have b:=h i k ik
  omega

private theorem smallest_order {p : ℕ} [Fact p.Prime] {r : Fin 4→ℤ} (h:ContactOrders p r) :
    min (min (r 0) (r 1)) (min (r 2) (r 3)) ≤ 0 := by
  have a:=h 0 1 (by decide)
  have b:=h 0 3 (by decide)
  have c:=min_dvd (p:=p) (T:=1) (P:=sectionValue 0-sectionValue 1)
    (Q:=sectionValue 0-sectionValue 3) (by decide) (by decide) (by decide) (by decide)
  have cp : padicValNat p 1 = 0 := by simp [padicValNat]
  change min (padicValInt p (sectionValue 0-sectionValue 1)) (padicValInt p (sectionValue 0-sectionValue 3))≤padicValNat p 1 at c
  rw [cp] at c
  omega

/-- The pole-order loss of (dt)^2 divided by the four branch factors is bounded at every prime. -/
theorem vertical_bound {p : ℕ} [Fact p.Prime] {r : Fin 4→ℤ} (h:ContactOrders p r)
    {v : ℤ} (derivative : ∀ i,r i≤v) :
    -(padicValInt p 823200:ℤ) ≤ 2*v-∑i,r i := by
  have h₀:=middle_orders h (i:=0) (j:=1) (k:=2) (by decide) (by decide) (by decide)
  have h₁:=middle_orders h (i:=0) (j:=1) (k:=3) (by decide) (by decide) (by decide)
  have h₂:=middle_orders h (i:=0) (j:=2) (k:=3) (by decide) (by decide) (by decide)
  have h₃:=middle_orders h (i:=1) (j:=2) (k:=3) (by decide) (by decide) (by decide)
  have small:=smallest_order h
  have d₀:=derivative 0
  have d₁:=derivative 1
  have d₂:=derivative 2
  have d₃:=derivative 3
  rw [Fin.sum_univ_four]
  omega

/-- For an actual rational parameter away from the branch values the required orders occur. -/
theorem rational_contacts {p : ℕ} [Fact p.Prime] (z : ℚ) :
    ContactOrders p (fun i=>padicValRat p (z-sectionValue i)) := by
  intro i j ne
  have distinct : sectionValue i≠sectionValue j := by
    revert i j
    decide
  have eq : (z-(sectionValue j:ℚ))+(-(z-sectionValue i))=(sectionValue i:ℚ)-sectionValue j := by ring
  have nonzero : (sectionValue i:ℚ)-sectionValue j ≠0 := sub_ne_zero.mpr (by exact_mod_cast distinct)
  have u:=padicValRat.min_le_padicValRat_add (p:=p) (eq.trans_ne nonzero)
  rw [eq,padicValRat.neg,min_comm,← Int.cast_sub,padicValRat.of_int] at u
  exact u

/-- Orders of the two sections q and t q. At a pole all four contacts equal v(t). -/
theorem section_pair {p : ℕ} [Fact p.Prime] {r : Fin 4→ℤ} (h:ContactOrders p r) {d t : ℤ}
    (derivative : ∀ i,r i≤d) (chart : 0≤t ∨ ∀ i,r i=t) :
    -(padicValInt p 823200:ℤ) ≤ 2*d-∑i,r i ∧
    -(padicValInt p 823200:ℤ) ≤ t+2*d-∑i,r i := by
  have hol:=vertical_bound h derivative
  refine ⟨hol,?_⟩
  rcases le_or_gt 0 t with pos|neg
  · omega
  · have same:=chart.resolve_left (not_le.mpr neg)
    have order:=derivative 0
    simp only [same,Fin.sum_univ_four] at *
    omega

end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.middle_orders
#print axioms ZInQBlueprint.FiveMetric.vertical_bound
#print axioms ZInQBlueprint.FiveMetric.rational_contacts
#print axioms ZInQBlueprint.FiveMetric.section_pair
