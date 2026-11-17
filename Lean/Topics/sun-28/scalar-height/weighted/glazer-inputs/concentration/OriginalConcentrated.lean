import OriginalRows

namespace ZInQBlueprint.OriginalConcentrated
open scoped Classical
open Finset Sun28.Ordinary Sun28.FiveMarkTriples Sun28.MinimalConductors Sun28.HeightFibres ZInQ.RouteK
open ZInQBlueprint.OriginalHeightCount
open private kernel_member from SignedSupport
noncomputable section
set_option maxRecDepth 12000

/-- Every outside positive odd contact divides one specified marked form. -/
def Concentrated (x : ℚ) (j : Fin 5) : Prop :=
  ∀ p ∈ oldContactPrimes core x.num x.den, (p:ℤ) ∣ oldForm j x.num x.den

/-- Four individually fixed signed squareclasses, in projective primitive coordinates. -/
def FourClasses (x:ℚ) (j:Fin 5) : Prop :=
  ∀ i ≠ j, ∃ d w:ℤ, d.natAbs ∣ 210 ∧ w≠0 ∧ oldForm i x.num x.den=d*w^2

theorem retained_kernel {x:ℚ} (off:offMarks x) (j : Fin 5) (single:Concentrated x j)
    {i : Fin 5} (diff:i≠j) : (kernel i x.num x.den).natAbs ∣ 210 := by
  have cop : Int.gcd x.num (x.den:ℤ)=1:=by simpa [Int.gcd] using x.reduced.gcd_eq_one
  have sf:Squarefree (kernel i x.num x.den).natAbs:=Int.squarefree_natAbs.mpr (sqfInt_spec (off i)).1
  rw [←Nat.prod_primeFactors_of_squarefree sf,Nat.prod_primeFactors_dvd_iff (by decide : 210≠0)]
  intro p hp
  have pp:=Nat.prime_of_mem_primeFactors hp
  have odd:= (kernel_member (off i) pp).mp hp
  change p∈core
  by_contra notCore
  have pos : 0<padicValInt p (oldForm i x.num x.den) := by obtain ⟨l,el⟩:=odd; omega
  have inp : p∈oldContactPrimes core x.num x.den := mem_oldContactPrimes.mpr ⟨pp,notCore,i,pos,odd⟩
  have di : p∈formPrimes i x.num x.den :=
    Nat.mem_primeFactors.mpr ⟨pp,dvd_of_one_le_padicValNat pos,Int.natAbs_ne_zero.mpr (off i)⟩
  have dj : p∈formPrimes j x.num x.den := Nat.mem_primeFactors.mpr
    ⟨pp,by simpa using Int.natAbs_dvd_natAbs.mpr (single p inp),Int.natAbs_ne_zero.mpr (off j)⟩
  exact diff (unique_mark cop notCore di dj)

theorem four_classes {x:ℚ} (off:offMarks x) (j:Fin 5) (single:Concentrated x j) : FourClasses x j := by
  intro i diff
  obtain ⟨_,w,live,h⟩:=sqfInt_spec (off i)
  exact ⟨kernel i x.num x.den,w,retained_kernel off j single diff,live,h⟩

def keep (j:Fin 5) : Fin 4 → Fin 5 := j.succAbove

def fourProduct (j:Fin 5) (a b:ℤ) : ℤ := ∏ i : Fin 4, oldForm (keep j i) a b

def signedTwist (j:Fin 5) (x:ℚ) := sqfInt (fourProduct j x.num x.den)

/-- The product of the four retained rows has signed squarefree part of absolute value dividing 210. -/
theorem product_twist {x:ℚ} (off:offMarks x) {j:Fin 5} (single:Concentrated x j) :
    (signedTwist j x).natAbs ∣ 210 ∧ ∃ w:ℤ, w≠0 ∧ fourProduct j x.num x.den=signedTwist j x*w^2 := by
  have live (i:Fin 4) : oldForm (keep j i) x.num x.den≠0:=off _
  have pn : fourProduct j x.num x.den ≠0 := Finset.prod_ne_zero_iff.mpr fun i _=>live i
  obtain ⟨sf,w,wn,fac⟩:=sqfInt_spec pn
  refine ⟨?_,w,wn,fac⟩
  let c:Fin 4→ℤ:=fun i=>kernel (keep j i) x.num x.den
  have repr (i:Fin 4) : ∃ v:ℤ,oldForm (keep j i) x.num x.den=c i*v^2 := by
    obtain ⟨_,v,_,eq⟩:=sqfInt_spec (off (keep j i));exact ⟨v,eq⟩
  choose v hv using repr
  have product : fourProduct j x.num x.den=(∏ i,c i)*(∏ i,v i)^2 := by
    simp only [fourProduct,hv,Finset.prod_mul_distrib,Finset.prod_pow]
  have same : IsSquare ((signedTwist j x:ℤ)*(∏ i,c i)) := by
    apply Rat.isSquare_intCast_iff.mp
    push_cast
    have eq : (signedTwist j x:ℚ)*(w:ℚ)^2=((∏ i,c i:ℤ):ℚ)*((∏ i,v i:ℤ):ℚ)^2 := by exact_mod_cast fac.symm.trans product
    have non : (w:ℚ)≠0:=by exact_mod_cast wn
    refine ⟨((∏ i,c i:ℤ):ℚ)*((∏ i,v i:ℤ):ℚ)/w,?_⟩
    field_simp
    push_cast at eq ⊢
    linear_combination (∏ i,(c i:ℚ))*eq
  have dv : (signedTwist j x)∣∏i,c i:=sf.dvd_of_isSquare_mul same
  have small (i:Fin 4) : (c i).natAbs∣210 := retained_kernel off j single (Fin.succAbove_ne j i)
  have natdiv := Int.natAbs_dvd_natAbs.mpr dv
  change Squarefree (signedTwist j x) at sf
  rw [←Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr sf),Nat.prod_primeFactors_dvd_iff (by decide:210≠0)]
  intro p hp
  have pp:=Nat.prime_of_mem_primeFactors hp
  have a:= (Nat.dvd_of_mem_primeFactors hp).trans natdiv
  rw [Fin.prod_univ_four,Int.natAbs_mul,Int.natAbs_mul,Int.natAbs_mul] at a
  rcases pp.dvd_mul.mp a with h|h
  · rcases pp.dvd_mul.mp h with h|h
    · rcases pp.dvd_mul.mp h with h|h
      · exact Nat.mem_primeFactors.mpr ⟨pp,h.trans (small 0),by decide⟩
      · exact Nat.mem_primeFactors.mpr ⟨pp,h.trans (small 1),by decide⟩
    · exact Nat.mem_primeFactors.mpr ⟨pp,h.trans (small 2),by decide⟩
  · exact Nat.mem_primeFactors.mpr ⟨pp,h.trans (small 3),by decide⟩

private theorem order_product {p:ℕ} (prime:p.Prime) (f:Fin 4→ℤ) (live:∀i,f i≠0) (S:Finset (Fin 4)) :
    padicValInt p (∏i∈S,f i)=∑i∈S,padicValInt p (f i) := by
  let : Fact p.Prime := ⟨prime⟩
  induction S using Finset.induction_on with
  | empty => simp [padicValInt]
  | @insert i S new ih =>
    rw [Finset.prod_insert new,Finset.sum_insert new,padicValInt,Int.natAbs_mul,
        padicValNat.mul (Int.natAbs_ne_zero.mpr (live _))
          (Int.natAbs_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun k _=>live k)))]
    exact congrArg (fun v=>padicValInt p (f i)+v) ih

theorem concentrated_iff_twist {x:ℚ} (off:offMarks x) (j:Fin 5) :
    Concentrated x j ↔ (signedTwist j x).natAbs ∣ 210 := by
  refine ⟨fun h=>(product_twist off h).1,?_⟩
  intro small p inp
  obtain ⟨pp,out,i,pos,odd⟩:=mem_oldContactPrimes.mp inp
  have di : p∈formPrimes i x.num x.den := Nat.mem_primeFactors.mpr
    ⟨pp,dvd_of_one_le_padicValNat pos,Int.natAbs_ne_zero.mpr (off i)⟩
  have a : (p:ℤ)∣oldForm i x.num x.den := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors di)
  by_cases h:i=j
  · simpa [h] using a
  obtain ⟨k,hk⟩:=Fin.exists_succAbove_eq h
  have cop : Int.gcd x.num (x.den:ℤ)=1:=by simpa [Int.gcd] using x.reduced.gcd_eq_one
  have absent (l:Fin 4) (lk:l≠k) : padicValInt p (oldForm (keep j l) x.num x.den)=0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro dv
    have dl : p∈formPrimes (keep j l) x.num x.den := Nat.mem_primeFactors.mpr
      ⟨pp,dv,Int.natAbs_ne_zero.mpr (off _)⟩
    have same:=unique_mark cop out dl di
    exact lk (Fin.succAbove_right_injective (same.trans hk.symm))
  have oddP : Odd (padicValInt p (fourProduct j x.num x.den)) := by
    rw [fourProduct,order_product pp _ (fun l=>off (keep j l)),
      Finset.sum_eq_single_of_mem k (Finset.mem_univ _) (fun l _ ne=>absent l ne)]
    simpa only [keep,hk] using odd
  have pn : fourProduct j x.num x.den ≠0 := Finset.prod_ne_zero_iff.mpr (fun l _=>off (keep j l))
  have pd := Nat.dvd_of_mem_primeFactors ((kernel_member pn pp).mpr oddP)
  exact False.elim (out (Nat.mem_primeFactors.mpr ⟨pp,pd.trans small,by decide⟩))

theorem concentrated_iff_four_classes {x:ℚ} (off:offMarks x) (j:Fin 5) :
    Concentrated x j ↔ FourClasses x j := by
  refine ⟨four_classes off j,?_⟩
  intro h p inp
  obtain ⟨pp,out,i,pos,odd⟩:=mem_oldContactPrimes.mp inp
  have di : p∣(oldForm i x.num x.den).natAbs:=dvd_of_one_le_padicValNat pos
  by_cases e:i=j
  · subst i
    exact Int.natAbs_dvd_natAbs.mp (by simpa using di)
  obtain ⟨d,w,small,wn,fac⟩:=h i e
  have dn : d≠0 := by intro z; simp [z] at fac; exact off _ fac
  have idx:= (kernel_member (off i) pp).mpr odd
  have sf:Squarefree (kernel i x.num x.den):=(sqfInt_spec (off i)).1
  obtain ⟨_,u,un,eq⟩:=sqfInt_spec (off i)
  have sq : IsSquare ((kernel i x.num x.den)*d) := by
    apply Rat.isSquare_intCast_iff.mp
    push_cast
    have q : (kernel i x.num x.den:ℚ)*(u:ℚ)^2=(d:ℚ)*(w:ℚ)^2:=by exact_mod_cast eq.symm.trans fac
    refine ⟨(d:ℚ)*w/u,?_⟩
    have hu : (u:ℚ)≠0:=by exact_mod_cast un
    field_simp
    exact q
  have ip:= Int.natAbs_dvd_natAbs.mpr (sf.dvd_of_isSquare_mul sq)
  exact False.elim (out (Nat.mem_primeFactors.mpr ⟨pp,(Nat.dvd_of_mem_primeFactors idx).trans (ip.trans small),by decide⟩))

end
end ZInQBlueprint.OriginalConcentrated
#print axioms ZInQBlueprint.OriginalConcentrated.retained_kernel
#print axioms ZInQBlueprint.OriginalConcentrated.four_classes
#print axioms ZInQBlueprint.OriginalConcentrated.product_twist

#print axioms ZInQBlueprint.OriginalConcentrated.concentrated_iff_twist
#print axioms ZInQBlueprint.OriginalConcentrated.concentrated_iff_four_classes

