import SeedLocal
import SeedDirections
import NewTwistPrimes
import TorsionPermutations

namespace Sun28.SeededPartners
open Sun28.SelmerRealization Sun28.PairedClasses Sun28.TwistPrimes
open ZInQ.RouteK
open private avoided_factors from NewTwistPrimes
open private root_at_beta from FamilyLocal

/-- A point on the first covering over Q, in the ordered class (b,1). -/
theorem first_cover {k b q h : ℕ} (bp : 0<b) (qp : 0<q) (high : b<k^2)
    (dec : (k^2-b)*(9*k^2-b)=q*h^2) : Cover ℚ (b*q) b 1 := by
  have dec' := congrArg (fun n:ℕ=>(n:ℚ)) dec
  push_cast [Nat.cast_sub high.le,Nat.cast_sub (by omega : b≤9*k^2)] at dec'
  have kn : (k:ℚ)≠0 := by exact_mod_cast (show k≠0 by rintro rfl;omega)
  have extend := Sun28.LocalOrbit.exchange (K:=ℚ) (l:=b*q) (a:=(q:ℤ)) (c:=(b:ℤ))
    (by push_cast;ring) (by exact_mod_cast qp.ne') (Nat.mul_pos bp qp).ne'
  apply extend
  refine ⟨(3*(k:ℚ)^2-b)/(2*k),((q:ℚ)*h)/(2*k),(3*(k:ℚ)^2+b)/(2*k),1,Or.inr (Or.inr (Or.inr one_ne_zero)),?_,?_⟩
  · push_cast;field_simp [kn];linear_combination dec'
  · push_cast;field_simp [kn];ring

private theorem ternary_seed {k b q h : ℕ} (bm : b%24=17) (high : b<k^2)
    (three : 3∣k) (dec : (k^2-b)*(9*k^2-b)=q*h^2) : q%3=1 := by
  have z := congrArg (fun n:ℕ=>(n:ZMod 3)) dec
  push_cast [Nat.cast_sub high.le,Nat.cast_sub (by omega : b≤9*k^2)] at z
  have zero : (k:ZMod 3)=0 := (ZMod.natCast_eq_zero_iff ..).mpr three
  have bmod : (b:ZMod 3)=2 := (ZMod.natCast_eq_natCast_iff' b 2 3).mpr (by omega)
  rw [zero,bmod] at z
  have table : ∀ a v : ZMod 3, a*v^2=1 → a=1 := by decide
  apply (ZMod.natCast_eq_natCast_iff' q 1 3).mp
  exact table q h (z.symm.trans (by decide))

/-- q can be taken arbitrarily large, with the same prescribed b and d. -/
theorem seeded_pair {b d : ℕ} (ad : AdmissiblePair b d) (B : ℕ) :
    ∃ q : ℕ, B<q ∧ Squarefree (b*q) ∧ (b*q).Coprime (6*d) ∧
       (b*q)%12=11 ∧ ((b*q)*d)%12=11 ∧
       Cover ℚ (b*q) b 1 ∧ ((b:ℤ),1)∈localClasses ((b*q)*d) := by
  obtain ⟨k,p,high,div,bk,dy,large,split,root⟩ := choose_index ad B
  rcases ad with ⟨bp,dp,sb,sd,bd,b6,d6,bm,dm,dat,bat⟩
  have three : 3∣k := (dvd_mul_right _ _).trans div
  have dk : d∣k := (dvd_mul_left _ _).trans div
  have pos := Nat.mul_pos (Nat.sub_pos_of_lt high) (Nat.sub_pos_of_lt (by omega : b<9*k^2))
  obtain ⟨h,_,dec⟩ := sqfNat_mul_sq pos.ne'
  let q := sqfNat ((k^2-b)*(9*k^2-b))
  change (k^2-b)*(9*k^2-b)=q*h^2 at dec
  have sqf : Squarefree q := sqfNat_squarefree _
  have qp : 0<q := Nat.pos_of_ne_zero sqf.ne_zero
  have q4 := dyadic_class (by omega : b%8=1) high dy sqf dec
  have q3 := ternary_seed bm high three dec
  have qc : q.Coprime d := avoided_factors high dk bd dec
  have support (v : ℕ) (pr : v.Prime) (hv : v∣b) : (q:ZMod v)≠0 ∧ IsSquare (q:ZMod v) := by
    let _ : Fact v.Prime := ⟨pr⟩
    have k0 : ¬v∣k := fun D=>pr.not_dvd_one (bk ▸ Nat.dvd_gcd hv D)
    have runit : ¬v∣3 := fun D=>pr.not_dvd_one (b6 ▸ Nat.dvd_gcd hv (D.trans (by decide)))
    have z:=congrArg (fun n:ℕ=>(n:ZMod v)) dec
    push_cast [Nat.cast_sub high.le,Nat.cast_sub (by omega : b≤9*k^2)] at z
    exact root_at_beta ((ZMod.natCast_eq_zero_iff ..).mpr hv) ((ZMod.natCast_eq_zero_iff ..).not.mpr k0)
      (by exact_mod_cast (ZMod.natCast_eq_zero_iff 3 v).not.mpr runit) z
  have bq : b.Coprime q := by
    by_contra bad
    obtain ⟨v,pr,hb,hq⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    exact (support v pr hb).1 ((ZMod.natCast_eq_zero_iff ..).mpr hq)
  have spl (v : ℕ) (pr : v.Prime) (hv : v∣q) : IsSquare (b:ZMod v) := by
    let _ : Fact v.Prime := ⟨pr⟩
    have z:=congrArg (fun n:ℕ=>(n:ZMod v)) dec
    push_cast [Nat.cast_sub high.le,Nat.cast_sub (by omega : b≤9*k^2)] at z
    rw [(ZMod.natCast_eq_zero_iff ..).mpr hv,zero_mul] at z
    rcases mul_eq_zero.mp z with left|right
    · exact ⟨k,by linear_combination -left⟩
    · exact ⟨3*k,by linear_combination -right⟩
  have pdiv := (forced_factor high split root dec).1
  have q6 : q.Coprime 6 := by
    change q.Coprime (2*3)
    apply Nat.Coprime.mul_right
    · exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm
    · exact (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)).symm
  have nmod : (b*q)%12=11 := by rw [Nat.mul_mod,show b%12=5 by omega,show q%12=7 by omega]
  refine ⟨q,large.trans_le (Nat.le_of_dvd qp pdiv),Nat.squarefree_mul_iff.mpr ⟨bq,sb,sqf⟩,
    (b6.mul_right bd).mul_left (q6.mul_right qc),nmod,?_,first_cover bp qp high dec,?_⟩
  · rw [Nat.mul_mod,nmod,show d%12=1 by omega]
  · exact partner_local ⟨bp,dp,sb,sd,bd,b6,d6,bm,dm,dat,bat⟩ bq q3 (fun v pr hv=>(support v pr hv).2) spl

end Sun28.SeededPartners
#print axioms Sun28.SeededPartners.first_cover
#print axioms Sun28.SeededPartners.seeded_pair
