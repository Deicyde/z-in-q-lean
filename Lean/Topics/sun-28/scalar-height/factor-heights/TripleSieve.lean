import ThreeFactors

namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def rowsAt (i:Fin 4):Fin 3→Fin 4 :=
  ![![1,2,3],![0,2,3],![0,1,3],![0,1,2]] i

def allowed (j:Fin 4):Finset ℤ :=
  let ds:Finset ℤ:=(210:ℕ).divisors.image fun n:ℕ=>(n:ℤ)
  if j=2 then ds ∪ ds.image Neg.neg else ds

def triples (i:Fin 4) (x:ℚ):ℤ×ℤ×ℤ :=
  (coeff (rowsAt i 0) x,coeff (rowsAt i 1) x, coeff (rowsAt i 2) x)

private theorem positive (x:ℚ) (j:Fin 4) (ne:j≠2) : 0<value j x := by
  have den:0<(x.den:ℤ)^2:=sq_pos_of_ne_zero (by exact_mod_cast x.den_nz)
  fin_cases j <;> first | contradiction | (norm_num [value,row,alpha,gamma]; nlinarith only [den,sq_nonneg x.num])

theorem permitted {x:ℚ} {i:Fin 4} (h:concentrated x i) (j:Fin 3) :
    coeff (rowsAt i j) x∈allowed (rowsAt i j) := by
  let J:=rowsAt i j
  have ne:(rowsAt i j)≠i:=by fin_cases i <;> fin_cases j <;> decide
  let k:=coeff J x
  have dv:k.natAbs∣210:=concentrated_divisors h ne
  have member : (k.natAbs:ℤ)∈(210:ℕ).divisors.image (fun n:ℕ=>(n:ℤ)) :=
    Finset.mem_image.mpr ⟨_,Nat.mem_divisors.mpr ⟨dv,by decide⟩,rfl⟩
  have sign:J≠2 → 0≤k:=by
    intro ne2
    have pos:=positive x J ne2
    obtain ⟨_,u,un,e⟩:=ZInQ.RouteK.sqfInt_spec (row_ne x J)
    change row J x.num x.den=k*u^2 at e
    exact nonneg_of_mul_nonneg_left (e ▸ pos.le) (sq_pos_of_ne_zero un)
  change k∈allowed J
  unfold allowed
  split_ifs with j2
  · by_cases k0:0≤k
    · exact Finset.mem_union_left _ (by simpa [Int.natAbs_of_nonneg k0] using member)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,member,by simp [abs_of_nonpos (by omega:k≤0)]⟩)
  · simpa [Int.natAbs_of_nonneg (sign j2)] using member

def squares (n:ℕ) [NeZero n]:Finset (ZMod n):=Finset.univ.image fun z:ZMod n=>z^2

def admissible (j:Fin 4) {n:ℕ} [NeZero n] (a b:ZMod n):Finset ℤ :=
  (allowed j).filter fun k=> ((alpha j:ZMod n)*a+(gamma j:ZMod n)*b)
    ∈(squares n).image fun s=>(k:ZMod n)*s

def localTriples (i:Fin 4) (p n:ℕ) [NeZero n] (h:p∣n) : Finset (ℤ×ℤ×ℤ) :=
  let sqs:=squares n
  let primitive:=(sqs ×ˢ sqs).filter fun t=>¬(ZMod.castHom h (ZMod p) t.1=0 ∧ ZMod.castHom h (ZMod p) t.2=0)
  primitive.biUnion fun t=>admissible (rowsAt i 0) t.1 t.2 ×ˢ
    (admissible (rowsAt i 1) t.1 t.2 ×ˢ admissible (rowsAt i 2) t.1 t.2)

theorem in_local {x:ℚ} {i:Fin 4} (h:concentrated x i) (p n:ℕ) [NeZero n]
    (pp:p.Prime) (pn:p∣n) : triples i x∈localTriples i p n pn := by
  let _:Fact p.Prime:=⟨pp⟩
  let A:ZMod n:=(x.num:ZMod n)^2
  let B:ZMod n:=(x.den:ZMod n)^2
  have sq (z:ℤ) : (z:ZMod n)^2∈squares n:=Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩
  have pr:¬(ZMod.castHom pn (ZMod p) A=0 ∧ ZMod.castHom pn (ZMod p) B=0):=by
    rintro ⟨z,w⟩
    change ZMod.castHom pn (ZMod p) ((x.num:ZMod n)^2)=0 at z
    change ZMod.castHom pn (ZMod p) ((x.den:ZMod n)^2)=0 at w
    rw [map_pow,map_intCast] at z
    rw [map_pow,map_natCast] at w
    have pa:=(ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp (sq_eq_zero_iff.mp z)
    have pb:=(ZMod.natCast_eq_zero_iff x.den p).mp (sq_eq_zero_iff.mp w)
    exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt (by simpa using Int.natAbs_dvd_natAbs.mpr pa) pb) x.reduced
  have mem (t:Fin 3):coeff (rowsAt i t) x∈admissible (rowsAt i t) A B:=by
    let j:=rowsAt i t
    obtain ⟨_,u,_,e⟩:=ZInQ.RouteK.sqfInt_spec (row_ne x j)
    have ev:(alpha j:ZMod n)*A+(gamma j:ZMod n)*B=(coeff j x:ZMod n)*(u:ZMod n)^2:=by
      change row j x.num (x.den:ℤ)=coeff j x*u^2 at e
      simpa [A,B,row] using congrArg (Int.castRingHom (ZMod n)) e
    exact Finset.mem_filter.mpr ⟨permitted h t,Finset.mem_image.mpr ⟨_,sq u,ev.symm⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(A,B),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨sq x.num,?_⟩,pr⟩,
    Finset.mem_product.mpr ⟨mem 0,Finset.mem_product.mpr ⟨mem 1,mem 2⟩⟩⟩
  simpa [B] using sq (x.den:ℤ)

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.permitted
#print axioms Sun28.FactorHeights.in_local
