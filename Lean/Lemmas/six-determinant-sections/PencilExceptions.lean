import GenusTwoAbelPairs

/-! For a fixed b in genus two, there is at most one q for which b+q
has moving sections. This is the curve calculation in the ruling proof. -/
open AlgebraicCurve
namespace ZInQBlueprint.DeterminantSections
noncomputable section
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
  [Algebra.EssFiniteType K F]

omit [Algebra.EssFiniteType K F] in
private theorem effective_zero {D : Divisor K F} (eff : ∀ p, 0 ≤ D p)
    (deg : Divisor.degree D = 0) : D=0 := by
  classical
  have sum : Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
    conv_lhs => rw [← Finsupp.sum_single D,Finsupp.sum,map_sum]
    exact Finset.sum_congr rfl fun v _ => Divisor.degree_single v (D v)
  rw [sum] at deg
  have nn : ∀ p ∈ D.support, 0 ≤ D p * (p.deg : ℤ) :=
    fun p _ => mul_nonneg (eff p) (Int.natCast_nonneg _)
  have all0 := (Finset.sum_eq_zero_iff_of_nonneg nn).mp deg
  ext p
  by_cases e : D p = 0
  · exact e
  · have h := all0 p (Finsupp.mem_support_iff.mpr e)
    rwa [IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] at h

omit [Algebra.EssFiniteType K F] in
private theorem principal_of_ell {D : Divisor K F} (deg : Divisor.degree D = 0)
    (pos : 0 < ell D) : D ∈ Divisor.principal := by
  have hn : LSpace D ≠ ⊥ := fun e => by
    change 0 < Module.finrank K (LSpace D) at pos
    rw [e,finrank_bot] at pos
    omega
  obtain ⟨f,hf,hnz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let := IsCurveOver.hasPrincipalDivisors (K:=K) (F:=F)
  obtain ⟨A,ha,da⟩ := HasPrincipalDivisors.exists_divisor (K:=K) f hnz
  have ob := (mem_lSpace_iff_ord.mp hf).resolve_left hnz
  have zero : A+D=0 := effective_zero (fun v => by
    rw [Finsupp.add_apply,ha]; have := ob v; omega) (by rw [map_add,da,deg,zero_add])
  rw [show D = -A from eq_neg_of_add_eq_zero_right zero]
  exact neg_mem ⟨f,hnz,ha⟩

/-- The Riemann–Roch relation and canonical degree may be supplied by any
choice of a nonzero differential. No canonical divisor *class* is chosen as input. -/
private theorem at_most_one_special_partner_of_rr (b q r : Place K F) (hg : genusFF K F = 2)
    (Kc : Divisor K F) (deg : Divisor.degree Kc = 2)
    (rr : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D+1-2)
    (hq : 1 < ell (Finsupp.single b 1 + Finsupp.single q 1))
    (hr : 1 < ell (Finsupp.single b 1 + Finsupp.single r 1)) : q = r := by
  let S (p : Place K F) : Divisor K F := Finsupp.single p 1
  have d (p : Place K F) : Divisor.degree (S p) = 1 := by
    rw [show S p = Finsupp.single p 1 by rfl,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed]; norm_num
  have principal (p : Place K F) (hp : 1 < ell (S b + S p)) : Kc - (S b+S p) ∈ Divisor.principal := by
    have star : Divisor.degree (S b + S p) = 2 := by rw [map_add,d,d]; decide
    have h := rr (S b + S p)
    rw [star] at h
    exact principal_of_ell (by rw [map_sub,deg,star,sub_self]) (by omega)
  have P := (Divisor.principal (K:=K) (F:=F)).sub_mem (principal r hr) (principal q hq)
  have eq : (Kc-(S b+S r)) - (Kc-(S b+S q)) = S q-S r := by abel
  rw [eq] at P
  exact eq_of_single_sub_single_principal_of_genus_pos (by omega : 0 < genusFF K F) q r P

theorem at_most_one_special_partner (M : CurveModel K F) (hg : genusFF K F = 2)
    (b q r : Place K F) (hq : 1 < ell (Finsupp.single b 1 + Finsupp.single q 1))
    (hr : 1 < ell (Finsupp.single b 1 + Finsupp.single r 1)) : q = r := by
  obtain ⟨Kc,g,rr⟩ := exists_canonicalDivisor_genus_riemannRoch K F
  have gg := (M.eq_genusFF_of_forall_ell_sub_ell_eq rr).trans hg
  subst g
  obtain ⟨t,ht,hfin,-⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=F)
  have e0 := ell_zero_eq_one_of_constantsAreBase (constantsAreBase_of_isAlgClosed_of_transcendental t ht)
  have r0 := rr 0
  have rc := rr Kc
  rw [sub_zero,map_zero,e0] at r0
  rw [sub_self,e0] at rc
  exact at_most_one_special_partner_of_rr b q r hg Kc (by omega) rr hq hr

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.at_most_one_special_partner
