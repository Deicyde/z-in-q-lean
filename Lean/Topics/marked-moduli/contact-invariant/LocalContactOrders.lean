import ContactInvariant
import GlobalTwist

/-! Rational orders with precisely the integer-DVR hypotheses used by the six-root charts. -/
namespace ZInQBlueprint.ContactInvariant
open ResidualFactors IsDiscreteValuationRing
noncomputable section
variable {p : ℕ} [hprime : Fact p.Prime]

/-- The existing normalized DVR valuation on a nonzero integer agrees with its rational order. -/
theorem rational_order_of_addVal {z : ℤ} (k : ℕ)
    (h : addVal ℤ_[p] (z:ℤ_[p])=(k:ℕ∞)) : padicValRat p z=k := by
  have hz : z≠0 := by rintro rfl; simp at h
  have he := GlobalTwist.nat_valuation p z.natAbs (by simpa using hz)
  have eq : addVal ℤ_[p] (z:ℤ_[p])= (z.natAbs.factorization p:ℕ∞) := by
    rcases Int.natAbs_eq z with hpos | hneg
    · have hh : (z:ℤ_[p]) = (z.natAbs:ℤ_[p]) := by
        simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n:ℤ_[p])) hpos
      rw [hh]
      exact he
    · have hh : (z:ℤ_[p]) = -(z.natAbs:ℤ_[p]) := by
        simpa only [Int.cast_neg,Int.cast_natCast] using congrArg (fun n : ℤ => (n:ℤ_[p])) hneg
      rw [hh,AddValuation.map_neg]
      exact he
  have hn := ENat.natCast_inj.mp (eq.symm.trans h)
  rw [padicValRat.of_int,padicValInt,← Nat.factorization_def _ hprime.out,hn]

/-- The positive even-contact and pole branches now use the literal inputs of RationalClusters. -/
theorem cluster_orders (u : ℚ) (hu : u ∉ ZInQ.contactSet) (hp : 5<p) :
    (∀ d : ℕ, 0<d → addVal ℤ_[p] (RationalClusters.F p u)=((2*d:ℕ):ℕ∞) →
      padicValRat p (SixContact.J u)=4*d) ∧
    (∀ g : ℕ, 0<g → addVal ℤ_[p] (RationalClusters.G p u)=(g:ℕ∞) →
      padicValRat p (SixContact.J u)= -6*g) := by
  have hF : ((contactProduct u.num (u.den:ℤ):ℤ):ℤ_[p])=RationalClusters.F p u := by
    simp [RationalClusters.F,contactProduct]
  have hG : ((poleForm u.num (u.den:ℤ):ℤ):ℤ_[p])=RationalClusters.G p u := by
    simp [RationalClusters.G,poleForm]
  obtain ⟨hc,hd⟩ := rational_orders u hu hp
  constructor
  · intro d hpos h
    apply hc d (by exact_mod_cast hpos)
    have hval := rational_order_of_addVal (p:=p) (z:=contactProduct u.num (u.den:ℤ)) (2*d) (hF ▸ h)
    simpa using hval
  · intro g hpos h
    apply hd g (by exact_mod_cast hpos)
    exact rational_order_of_addVal (p:=p) (z:=poleForm u.num (u.den:ℤ)) g (hG ▸ h)
end
end ZInQBlueprint.ContactInvariant
#print axioms ZInQBlueprint.ContactInvariant.rational_order_of_addVal
#print axioms ZInQBlueprint.ContactInvariant.cluster_orders
