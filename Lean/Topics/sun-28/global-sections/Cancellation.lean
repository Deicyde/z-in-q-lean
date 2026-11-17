import AuxiliaryLocal
import LocalProducts
import NewTwistPrimes

namespace Sun28.GlobalSections
open Sun28.PairedClasses Sun28.PreparedPoles Sun28.TwistExtension Sun28.TwistRank Sun28.TwistPrimes
noncomputable section

theorem local_cancel {p q θ:ℕ} (pp:p.Prime) (odd:p≠2) (unit:¬p∣q*θ)
    (hq:LocalSquareAt p q) (hprod:LocalSquareAt p (q*θ)) : LocalSquareAt p θ := by
  let : Fact p.Prime := ⟨pp⟩
  obtain ⟨u,eu⟩:=LocalQuartics.residue_of_tower hq
  obtain ⟨v,ev⟩:=LocalQuartics.residue_of_tower hprod
  rw [Nat.cast_mul] at ev
  have qn:(q:ZMod p)≠0:=(ZMod.natCast_eq_zero_iff _ _).not.mpr (fun h=>unit (dvd_mul_of_dvd_left h _))
  have tn:(θ:ZMod p)≠0:=(ZMod.natCast_eq_zero_iff _ _).not.mpr (fun h=>unit (dvd_mul_of_dvd_right h _))
  have un:u≠0:=fun h=>qn (by rw [eu,h,zero_mul])
  apply local_square_of_legendre odd ((legendreSym.eq_one_iff' p tn).mpr ?_)
  refine ⟨v/u,?_⟩
  rw [eu] at ev
  field_simp
  linear_combination ev

theorem admissible_quotient {b q θ:ℕ} (a:AdmissiblePair b q)
    (d:AdmissiblePair b (q*θ)) : AdmissiblePair b θ ∧ q.Coprime θ := by
  obtain ⟨bp,qp,bs,qs,bq,b6,q6,bm,qm,_,qAtB⟩:=a
  obtain ⟨_,dt,_,ds,bd,_,d6,_,dm,bAtD,dAtB⟩:=d
  obtain ⟨qt,_,ts⟩:=Nat.squarefree_mul_iff.mp ds
  have pos:0<θ:=Nat.pos_of_ne_zero (fun h=>by simp [h] at dt)
  have bt:=bd.coprime_dvd_right (dvd_mul_left θ q)
  have t6:=d6.coprime_dvd_left (dvd_mul_left θ q)
  refine ⟨⟨bp,pos,bs,ts,bt,b6,t6,bm,?_,?_,?_⟩,qt⟩
  · simpa [Nat.mul_mod,qm] using dm
  · exact fun p pp pt=>bAtD p pp (dvd_mul_of_dvd_right pt _)
  · intro p pp pb
    have nd:¬p∣q*θ:=fun hd=>pp.not_dvd_one (bd ▸ Nat.dvd_gcd pb hd)
    have odd:p≠2:=by rintro rfl;exact Nat.prime_two.not_dvd_one (b6 ▸ Nat.dvd_gcd pb (by decide))
    exact local_cancel pp odd nd (qAtB p pp pb) (dAtB p pp pb)

theorem fixed_quotient {q θ:ℕ} (a:FixedSquares q) (d:FixedSquares (q*θ)) : FixedSquares θ := by
  intro p mem pp odd
  obtain ⟨nd,sd⟩:=d p mem pp odd
  exact ⟨fun z=>nd (dvd_mul_of_dvd_right z _), local_cancel pp odd nd (a p mem pp odd).2 sd⟩

/-- For a squarefree cofactor q whose prime support is required, the old
index construction still gives arbitrarily large factors satisfying all fixed places. -/
theorem fixed_multiple {b q:ℕ} (a:AdmissiblePair b q) (fq:FixedSquares q) (bound:ℕ) :
    ∃ d, bound<d ∧ q∣d ∧ AdmissiblePair b d ∧ FixedSquares d ∧ Family b d := by
  classical
  obtain ⟨bp,qp,bs,qs,bq,b6,q6,bm,_,bAtQ,_⟩:=a
  let Z:=FixedPreparation.primes.filter (fun p=>¬p∣b)
  let D:=∏p∈Z,p
  have zi {p:ℕ} (m:p∈Z) : p.Prime ∧ ¬p∣b := by
    obtain ⟨mem,nd⟩:=Finset.mem_filter.mp m
    exact ⟨(show ∀ p∈FixedPreparation.primes,p.Prime by decide) p mem,nd⟩
  have dp:0<D:=Finset.prod_pos fun p m=>(zi m).1.pos
  have bd:b.Coprime D:=Nat.Coprime.prod_right fun p m=>(zi m).1.coprime_iff_not_dvd.mpr (zi m).2 |>.symm
  have spl {p:ℕ} (mem:p∈q.primeFactors) : SplitRoot b p := by
    obtain ⟨pp,pq,_⟩:=Nat.mem_primeFactors.mp mem
    have nb:¬p∣b:=fun h=>pp.not_dvd_one (bq ▸ Nat.dvd_gcd h pq)
    have n6:¬p∣6:=fun h=>pp.not_dvd_one (q6 ▸ Nat.dvd_gcd pq h)
    obtain ⟨z,hz⟩:=LocalQuartics.residue_of_tower (bAtQ p pp pq)
    let : NeZero p:=⟨pp.ne_zero⟩
    refine ⟨pp,fun h=>(pp.dvd_mul.mp h).elim n6 nb,z.val,?_⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [pow_two] using hz.symm
  have avoid {p:ℕ} (mem:p∈q.primeFactors) : ¬p∣D := by
    obtain ⟨pp,pq,_⟩:=Nat.mem_primeFactors.mp mem
    have cop:p.Coprime D:=Nat.Coprime.prod_right fun t mt=>pp.coprime_iff_not_dvd.mpr (by
      intro pt
      have eq:=((Nat.dvd_prime (zi mt).1).mp pt).resolve_left pp.ne_one
      subst t
      have odd:p≠2:=by rintro rfl;exact Nat.prime_two.not_dvd_one (q6 ▸ Nat.dvd_gcd pq (by decide))
      exact (fq p (Finset.mem_filter.mp mt).1 pp odd).1 pq)
    exact pp.coprime_iff_not_dvd.mp cop
  obtain ⟨p,large,new⟩:=fresh_split bp (max bound D)
  let S:=insert p q.primeFactors
  have ss (t:ℕ) (m:t∈S) : SplitRoot b t := (Finset.mem_insert.mp m).elim (fun e=>e ▸ new) spl
  have aa (t:ℕ) (m:t∈S) : ¬t∣D := (Finset.mem_insert.mp m).elim
    (fun e=>e ▸ Nat.not_dvd_of_pos_of_lt dp ((le_max_right ..).trans_lt large)) avoid
  obtain ⟨k,hk,six,dk,bk,root⟩:=prescribed_index bp dp b6 bd S ss aa
  obtain ⟨d,h,E,ad,_⟩:=family_of_index bp hk bs b6 bk bm six
  have hits {t:ℕ} (m:t∈S):t∣d := (forced_factor hk (ss t m) (root t m) E).1
  have qd:q∣d:=by
    rw [←Nat.prod_primeFactors_of_squarefree qs]
    apply (Nat.prod_primeFactors_dvd_iff ad.2.1.ne').mpr
    exact fun t m=>Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors m,hits (Finset.mem_insert_of_mem m),ad.2.1.ne'⟩
  refine ⟨d,((le_max_left ..).trans_lt large).trans_le (Nat.le_of_dvd ad.2.1 (hits (Finset.mem_insert_self p _))),
    qd,ad,?_,?_⟩
  · intro t mem tp odd
    by_cases tb:t∣b
    · exact ⟨fun td=>tp.not_dvd_one (ad.2.2.2.2.1 ▸ Nat.dvd_gcd tb td),ad.2.2.2.2.2.2.2.2.2.2 t tp tb⟩
    · have inZ:t∈Z:=Finset.mem_filter.mpr ⟨mem,tb⟩
      exact square_at_zero_index tp odd hk tb ((Finset.dvd_prod_of_mem id inZ).trans dk) E
  · have hin : h≠0 := by
      have gt:0<d*h^2:= E ▸ Nat.mul_pos (Nat.sub_pos_of_lt hk) (Nat.sub_pos_of_lt (by omega))
      rintro rfl; simp at gt
    refine ⟨k,h,by exact_mod_cast hin,?_⟩
    have E':=congrArg (fun n:ℕ=>(n:ℚ)) E
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hk.le,Nat.cast_sub (show b≤9*k^2 by omega),Nat.cast_ofNat] using E'

end
end Sun28.GlobalSections
#print axioms Sun28.GlobalSections.local_cancel
#print axioms Sun28.GlobalSections.admissible_quotient
#print axioms Sun28.GlobalSections.fixed_quotient
#print axioms Sun28.GlobalSections.fixed_multiple
