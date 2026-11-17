import CertificateHeights
import SignedSupport
import SignedKernel

/-! The scalar locus has a single quadratic field of odd contact. -/
namespace Sun28.WitnessHeight
open Sun28.Ordinary Sun28.ScalarHeight Sun28.MinimalConductors Sun28.FiveMarkUnits
open ZInQ.RouteK Sun28.FiveDescent Height
noncomputable section

/-- The four finite scalar rows; their product has the same square class as
the product of all five primitive integer rows away from 2. -/
def octic (x : ℚ) : ℚ := (2*x^2+3)*(x^2+1)*(x^2-1199)*(64*x^2+439)
def scalarClass (x : ℚ) : ℤ := sqf (octic x)
def scalarPrimes (x : ℚ) : Finset ℕ := (scalarClass x).natAbs.primeFactors \ oldCutoff

theorem scalar_denominator (x : ℚ) :
    (beta x).den*Nat.gcd 2 (x.den^2)=x.den^2 := by
  have mul := Rat.den_mul_den_eq_den_mul_gcd 2 (x^2)
  have cop : Nat.Coprime (x.num.natAbs^2) (x.den^2) := (x.reduced.pow_left 2).pow_right 2
  norm_num [Int.natAbs_mul] at mul
  rw [cop.gcd_mul_right_cancel 2] at mul
  simpa only [beta,Rat.add_ofNat_den] using mul.symm

private theorem denominator_even {p : ℕ} [hp : Fact p.Prime] (away : p∉oldCutoff) (x:ℚ) :
    Even (padicValInt p ((beta x).den:ℤ)) := by
  have large : 76176<p := by
    by_contra! h
    exact away (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp.out⟩)
  let g:=Nat.gcd 2 (x.den^2)
  have ng : g≠0 := (Nat.gcd_pos_of_pos_left _ (by decide : 0<2)).ne'
  have unit : padicValNat p g=0 := padicValNat.eq_zero_of_not_dvd
    (fun h=>by have d:=Nat.le_of_dvd (by decide : 0<2) (h.trans (Nat.gcd_dvd_left 2 (x.den^2)));omega)
  have eq:=congrArg (padicValNat p) (scalar_denominator x)
  rw [padicValNat.mul (beta x).den_nz ng,unit,add_zero,padicValNat.pow x.den 2] at eq
  change Even (padicValNat p (beta x).den)
  exact ⟨padicValNat p x.den,by omega⟩

private def finiteRows : Finset (Fin 5) := Finset.univ.erase 0
private def scalarValue (x:ℚ) : ℤ := ∏ i∈finiteRows,oldForm i (beta x).num (beta x).den

private theorem scalarValue_identity (x:ℚ) :
    (scalarValue x:ℚ)=octic x*(2*(beta x).den^2:ℚ)^2 := by
  let b:=beta x
  have num : (b.num:ℚ)=b*(b.den:ℚ) := (div_eq_iff (by exact_mod_cast b.den_nz)).mp b.num_div_den
  have indices : finiteRows=({1,2,3,4}:Finset (Fin 5)) := by decide
  change ((∏ i∈finiteRows,oldForm i b.num b.den:ℤ):ℚ)=_
  rw [indices]
  norm_num [oldForm,Int.cast_mul,Int.cast_add,Int.cast_sub]
  change (b.num:ℚ)*(((b.num:ℚ)-(b.den:ℚ))*(((b.num:ℚ)-2401*b.den)*(32*b.num+343*b.den)))=_
  rw [num]
  dsimp [b,beta,octic]
  ring

private theorem scalarValue_ne (x:ℚ) : scalarValue x≠0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => beta_off_forms x j

theorem octic_twist (x:ℚ) : Squarefree (scalarClass x) ∧
    ∃ y:ℚ, y≠0 ∧ octic x=(scalarClass x:ℚ)*y^2 := by
  apply sqf_spec
  intro z
  have v:=scalarValue_identity x
  rw [z,zero_mul] at v
  exact scalarValue_ne x (by exact_mod_cast v)

theorem scalar_support_exact (x : ℚ) :
    oldContactPrimes oldCutoff (beta x).num (beta x).den=scalarPrimes x := by
  let b:=beta x
  obtain ⟨sf,y,ny,pt⟩:=octic_twist x
  have nd : (scalarClass x:ℚ)≠0 := by exact_mod_cast sf.ne_zero
  have ndn : (scalarClass x).natAbs≠0 := Int.natAbs_ne_zero.mpr sf.ne_zero
  let y' : ℚ := y*(2*(beta x).den^2)
  have ny' : y'≠0 := mul_ne_zero ny (by positivity)
  have value : (scalarValue x:ℚ)=(scalarClass x:ℚ)*y'^2 := by
    rw [scalarValue_identity,pt]; dsimp [y'];ring
  ext p
  rw [mem_oldContactPrimes]
  simp only [scalarPrimes,Finset.mem_sdiff,Nat.mem_primeFactors]
  constructor
  · rintro ⟨pr,out,i,_,odd⟩
    let _ : Fact p.Prime := ⟨pr⟩
    have nz : i≠0 := by
      rintro rfl
      change Odd (padicValInt p ((beta x).den:ℤ)) at odd
      exact (Nat.not_even_iff_odd.mpr odd) (denominator_even out x)
    have prod := (product_odd_iff pr out (beta_primitive x) (beta_off_forms x) finiteRows).mpr
      ⟨i,Finset.mem_erase.mpr ⟨nz,Finset.mem_univ _⟩,odd⟩
    change Odd (padicValInt p (scalarValue x)) at prod
    have val := congrArg (padicValRat p) value
    rw [padicValRat.of_int,padicValRat.mul nd (pow_ne_zero 2 ny'),padicValRat.pow] at val
    refine ⟨⟨pr,(ZInQBlueprint.OddSupport.squarefree_odd_order (p:=p) sf).mpr ?_,ndn⟩,out⟩
    obtain ⟨k,eq⟩:=prod
    exact ⟨(k:ℤ)-padicValRat p y',by omega⟩
  · rintro ⟨⟨pr,dvd,_⟩,out⟩
    let _ : Fact p.Prime := ⟨pr⟩
    have val := congrArg (padicValRat p) value
    rw [padicValRat.of_int,padicValRat.mul nd (pow_ne_zero 2 ny'),padicValRat.pow] at val
    obtain ⟨k,eq⟩:=(ZInQBlueprint.OddSupport.squarefree_odd_order sf).mp dvd
    have od : Odd (padicValInt p (scalarValue x)) := by
      rw [Nat.odd_iff];omega
    obtain ⟨i,_,oi⟩:=(product_odd_iff pr out (beta_primitive x) (beta_off_forms x) finiteRows).mp od
    exact ⟨pr,out,i,by obtain ⟨k,eq⟩:=oi;omega,oi⟩

/-- The scalar bound is literally the height bound on this degree-eight quadratic twist. -/
theorem scalar_target_iff (x : ℚ) :
    target (beta x).num (beta x).den ↔
      logHeight₁ (beta x)≤glazerConstant24*(primeProduct (scalarPrimes x):ℝ)^24 := by
  simp only [target,scalar_support_exact,primeProduct,Nat.cast_prod,logHeight_reduced_pair]

end
end Sun28.WitnessHeight
#print axioms Sun28.WitnessHeight.scalar_denominator
#print axioms Sun28.WitnessHeight.octic_twist
#print axioms Sun28.WitnessHeight.scalar_support_exact
#print axioms Sun28.WitnessHeight.scalar_target_iff
