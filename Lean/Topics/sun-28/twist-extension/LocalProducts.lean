import ProductClasses
import UnitLifting
import PrimePatternCRT

namespace Sun28.TwistExtension
open PreparedPoles PairedClasses TwistRank TwistPrimes
noncomputable section

theorem local_mul {p a b : ℕ} (h : LocalSquareAt p a) (k : LocalSquareAt p b) : LocalSquareAt p (a*b) := by
  intro i
  obtain ⟨s,hs⟩:=h i
  obtain ⟨t,ht⟩:=k i
  refine ⟨s*t,?_⟩
  simpa only [mul_pow,Nat.cast_mul] using hs.mul ht

theorem fixed_mul {a b : ℕ} (h : FixedSquares a) (k : FixedSquares b) : FixedSquares (a*b) := by
  intro p m pp odd
  obtain ⟨na,sa⟩:=h p m pp odd
  obtain ⟨nb,sb⟩:=k p m pp odd
  exact ⟨fun d=>(pp.dvd_mul.mp d).elim na nb,local_mul sa sb⟩

theorem admissible_mul {β a b : ℕ} (h : AdmissiblePair β a) (k : AdmissiblePair β b)
    (co : a.Coprime b) : AdmissiblePair β (a*b) := by
  obtain ⟨bp,ap,bs,as,ba,b6,a6,bm,am,bl,al⟩:=h
  obtain ⟨_,cp,_,cs,bc,_,c6,_,cm,cl,dl⟩:=k
  refine ⟨bp,Nat.mul_pos ap cp,bs,(Nat.squarefree_mul co).mpr ⟨as,cs⟩,ba.mul_right bc,b6,
    a6.mul_left c6,bm,by rw [Nat.mul_mod,am,cm],?_,?_⟩
  · intro p pp div
    exact (pp.dvd_mul.mp div).elim (bl p pp) (cl p pp)
  · intro p pp div
    exact local_mul (al p pp div) (dl p pp div)

/-- Unit square information at any odd prime at which the index is zero. -/
theorem square_at_zero_index {β k d h p : ℕ} (pp : p.Prime) (odd : p≠2)
    (hk : β<k^2) (nb : ¬p∣β) (zero : p∣k) (eqn : (k^2-β)*(9*k^2-β)=d*h^2) :
    ¬p∣d ∧ LocalSquareAt p d := by
  let : Fact p.Prime := ⟨pp⟩
  have eq:=congrArg (fun n : ℕ=>(n:ZMod p)) eqn
  have nine : β≤9*k^2:=by omega
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hk.le,Nat.cast_sub nine,Nat.cast_ofNat,
    (ZMod.natCast_eq_zero_iff _ _).mpr zero,zero_pow (by decide : 2≠0),mul_zero,zero_sub,neg_mul_neg] at eq
  have bn : (β:ZMod p)≠0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr nb
  have unit : (d:ZMod p)*h^2≠0:=eq ▸ mul_ne_zero bn bn
  have dn:=left_ne_zero_of_mul unit
  have hn : (h:ZMod p)≠0:=fun z=>right_ne_zero_of_mul unit (by simp [z])
  refine ⟨(ZMod.natCast_eq_zero_iff _ _).not.mp dn,local_square_of_legendre odd ((legendreSym.eq_one_iff' p dn).mpr ?_)⟩
  refine ⟨(β:ZMod p)/h,?_⟩
  field_simp
  linear_combination -eq

/-- An arbitrarily large quartic output satisfying all fixed finite-place tests
and avoiding any specified positive D prime to β. -/
theorem fixed_factor {β D : ℕ} (bp : 0<β) (bs : Squarefree β) (b6 : β.Coprime 6)
    (bm : β%24=17) (dp : 0<D) (co : β.Coprime D) (bound : ℕ) :
    ∃ d : ℕ, bound<d ∧ AdmissiblePair β d ∧ FixedSquares d ∧ Family β d ∧ d.Coprime D := by
  classical
  let S:=FixedPreparation.primes.filter (fun p=>¬p∣β)
  let M:=∏ p∈S,p
  have info {p : ℕ} (m : p∈S) : p.Prime ∧ ¬p∣β := by
    obtain ⟨mem,nd⟩:=Finset.mem_filter.mp m
    exact ⟨(show ∀ p∈FixedPreparation.primes,p.Prime by decide) p mem,nd⟩
  have mp : 0<M:=Finset.prod_pos fun p h=>(info h).1.pos
  have cm : β.Coprime M:=Nat.Coprime.prod_right fun i m=>(info m).1.coprime_iff_not_dvd.mpr (info m).2 |>.symm
  let D':=M*D
  have pos : 0<D':=Nat.mul_pos mp dp
  have cp : β.Coprime D':=cm.mul_right co
  obtain ⟨p,large,spl⟩:=fresh_split bp (max bound D')
  have nd : ¬p∣D':=Nat.not_dvd_of_pos_of_lt pos ((le_max_right ..).trans_lt large)
  obtain ⟨k,hk,six,div,bk,roots⟩:=prescribed_index bp pos b6 cp {p}
    (by simpa using spl) (by simpa using nd)
  obtain ⟨d,h,eq,adm,_⟩:=family_of_index bp hk bs b6 bk bm six
  have hit: p∣d:=(forced_factor hk spl (roots p (Finset.mem_singleton_self _)) eq).1
  have prime₀ (q : ℕ) (qp : q.Prime) (nq : ¬q∣β) (dq : q∣k) : ¬q∣d := by
    by_cases two : q=2
    · subst q
      exact fun z=>Nat.prime_two.not_dvd_one (adm.2.2.2.2.2.2.1 ▸ Nat.dvd_gcd z (by decide : 2∣6))
    · exact (square_at_zero_index qp two hk nq dq eq).1
  refine ⟨d,((le_max_left ..).trans_lt large).trans_le (Nat.le_of_dvd adm.2.1 hit),adm,?_,?_,?_⟩
  · intro q mem qp odd
    by_cases qb : q∣β
    · exact ⟨fun x=>qp.not_dvd_one (adm.2.2.2.2.1 ▸ Nat.dvd_gcd qb x),adm.2.2.2.2.2.2.2.2.2.2 q qp qb⟩
    · have inS : q∈S:=Finset.mem_filter.mpr ⟨mem,qb⟩
      have divM : q∣M:=Finset.dvd_prod_of_mem id inS
      exact square_at_zero_index qp odd hk qb (divM.trans ((dvd_mul_right _ _).trans div)) eq
  · have nine : β≤9*k^2:=by omega
    have hne : h≠0:=by
      intro z
      have z0 : 0<d*h^2 := eq ▸ Nat.mul_pos (Nat.sub_pos_of_lt hk) (Nat.sub_pos_of_lt (by omega))
      simp [z] at z0
    refine ⟨k,h,by exact_mod_cast hne,?_⟩
    have E:=congrArg (fun n : ℕ=>(n:ℚ)) eq
    simpa only [Nat.cast_mul,Nat.cast_sub hk.le,Nat.cast_sub nine,Nat.cast_pow,Nat.cast_ofNat] using E
  · by_contra bad
    obtain ⟨q,qp,qd,qD⟩:=Nat.Prime.not_coprime_iff_dvd.mp bad
    have nq : ¬q∣β := fun z=>qp.not_dvd_one (co ▸ Nat.dvd_gcd z qD)
    exact prime₀ q qp nq (qD.trans ((dvd_mul_left _ _).trans div)) qd

end
end Sun28.TwistExtension
#print axioms Sun28.TwistExtension.local_mul
#print axioms Sun28.TwistExtension.fixed_mul
#print axioms Sun28.TwistExtension.admissible_mul
#print axioms Sun28.TwistExtension.square_at_zero_index
#print axioms Sun28.TwistExtension.fixed_factor
