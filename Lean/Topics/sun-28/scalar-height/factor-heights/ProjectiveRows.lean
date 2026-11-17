import TripleSieve

namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

/-- Projective normalization divides all three quadratic values by the same unit square.
Each good residue pair has one of its coordinates equal to one. -/
def coordinates (p n:ℕ) [NeZero n] (pn:p∣n):Finset (ZMod n×ZMod n) :=
  ((squares n).image fun t=>(t,1)) ∪
  (((squares n).filter fun t=> ZMod.castHom pn (ZMod p) t=0).image fun t=>(1,t))

/-- A literal small-integer computation of possible kernels in a single cell. -/
def possible (n:ℕ) [NeZero n] (j:Fin 4) (a b:ZMod n) (k:ℤ):Prop :=
  ∃s∈squares n,(k:ZMod n)*s=(alpha j:ZMod n)*a+(gamma j:ZMod n)*b

theorem homogeneous_projective {x:ℚ} (p n:ℕ) [NeZero n] (prime:p.Prime)
    (pow:∃e:ℕ,n=p^e) (pn:p∣n) :
    ∃t∈coordinates p n pn,∀j:Fin 4,possible n j t.1 t.2 (coeff j x) := by
  let _:Fact p.Prime:=⟨prime⟩
  let a:ZMod n:=x.num
  let b:ZMod n:=x.den
  have unit (z:ℤ) (nz:¬(p:ℤ)∣z) : IsUnit (z:ZMod n):=by
    obtain ⟨e,rfl⟩:=pow
    have nd:¬p∣z.natAbs:=by intro w;exact nz (Int.natAbs_dvd_natAbs.mp (by simpa using w))
    have cp:=((prime.coprime_iff_not_dvd.mpr nd).symm.pow_right e)
    have absU: IsUnit (z.natAbs:ZMod (p^e)):=(ZMod.isUnit_iff_coprime ..).mpr cp
    have absZ:IsUnit (((z.natAbs:ℕ):ℤ):ZMod (p^e)):=by simpa only [Int.cast_natCast] using absU
    rw [Int.natCast_natAbs] at absZ
    by_cases h0:0≤z
    · rwa [abs_of_nonneg h0] at absZ
    · rw [abs_of_neg (by omega:z<0),Int.cast_neg] at absZ
      simpa only [neg_neg] using absZ.neg
  have ev (j:Fin 4):∃u:ZMod n,(alpha j:ZMod n)*a^2+(gamma j:ZMod n)*b^2=(coeff j x:ZMod n)*u^2:=by
    obtain ⟨_,u,_,e⟩:=ZInQ.RouteK.sqfInt_spec (row_ne x j)
    refine ⟨u,?_⟩
    change row j x.num x.den=coeff j x*u^2 at e
    simpa [a,b,row] using congrArg (Int.castRingHom (ZMod n)) e
  by_cases bn:p∣x.den
  · have an:¬(p:ℤ)∣x.num:=fun az=>(Nat.not_coprime_of_dvd_of_dvd prime.one_lt
      (by simpa using Int.natAbs_dvd_natAbs.mpr az) bn) x.reduced
    obtain ⟨aa,haa⟩:=unit x.num an
    have hAa:(aa:ZMod n)=a:=haa
    let inv:ZMod n:=↑aa⁻¹
    have invA:a*inv=1:=by dsimp [inv];rw [←hAa];simp
    let z:ZMod n:=b*inv
    have z0:ZMod.castHom pn (ZMod p) (z^2)=0:=by
      have bp:(x.den:ZMod p)=0:=(ZMod.natCast_eq_zero_iff ..).mpr bn
      simp only [z,b,map_pow,map_mul,map_natCast,bp,zero_mul,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
    refine ⟨(1,z^2),Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨z^2,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,z0⟩,rfl⟩),?_⟩
    intro j
    obtain ⟨u,e⟩:=ev j
    refine ⟨(u*inv)^2,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,?_⟩
    change _=(alpha j:ZMod n)*1+(gamma j:ZMod n)*(b*inv)^2
    linear_combination -inv^2*e+(alpha j:ZMod n)*(a*inv+1)*(invA)
  · have ni:¬(p:ℤ)∣(x.den:ℤ):=by exact_mod_cast bn
    obtain ⟨bb,hbb⟩:=unit (x.den:ℤ) ni
    have hBb:(bb:ZMod n)=b:=by simpa [b] using hbb
    let inv:ZMod n:=↑bb⁻¹
    have invB:b*inv=1:=by dsimp [inv];rw [←hBb];simp
    let z:ZMod n:=a*inv
    refine ⟨(z^2,1),Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨z^2,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,rfl⟩),?_⟩
    intro j
    obtain ⟨u,e⟩:=ev j
    refine ⟨(u*inv)^2,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,?_⟩
    change _=(alpha j:ZMod n)*(a*inv)^2+(gamma j:ZMod n)*1
    linear_combination -inv^2*e+(gamma j:ZMod n)*(b*inv+1)*invB

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.homogeneous_projective
