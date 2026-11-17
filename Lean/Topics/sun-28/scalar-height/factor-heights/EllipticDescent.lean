import TripleSieve

namespace Sun28.FactorHeights
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Data (squareclass, quadratic coefficient, complementary divisor) for the two isogeny descents. -/
def descentRows : Fin 6 → ℤ×ℤ×ℤ :=
  ![(2,10,12),(2,-20,2),(2,503,14048),(3,-1006,46875),(5,-1006,28125),(15,-1006,9375)]
def modulus : Fin 6→ℕ := ![32,64,5,64,32,9]
def localPrime : Fin 6→ℕ := ![2,2,5,2,2,3]
instance (j:Fin 6):NeZero (modulus j) := ⟨by fin_cases j <;> decide⟩

def quartic {R:Type*} [CommRing R] (e A c u v:R) : R :=
  e*u^4 + A*u^2*v^2 + c*v^4

private def obstructed (p n:ℕ) [NeZero n] (pn:p∣n) (row:ℤ×ℤ×ℤ) : Prop :=
  ∀u∈squares n, ∀v∈squares n,
    ¬(ZMod.castHom pn (ZMod p) u=0 ∧ ZMod.castHom pn (ZMod p) v=0) →
    (row.1:ZMod n)*u^2+(row.2.1:ZMod n)*u*v+(row.2.2:ZMod n)*v^2∉squares n

private instance (p n:ℕ) [NeZero n] (pn:p∣n) (r:ℤ×ℤ×ℤ) : Decidable (obstructed p n pn r) := by
  unfold obstructed;infer_instance

private theorem prime_dvd (i:Fin 6) : localPrime i∣modulus i:=by fin_cases i <;> decide

private theorem block (i:Fin 6) : obstructed (localPrime i) (modulus i) (prime_dvd i) (descentRows i) := by
  fin_cases i <;> decide

/-- Each listed homogeneous space has an elementary primitive modular obstruction. -/
theorem six_quartic_obstructions (j:Fin 6) {u v z:ℤ} (cop:u.natAbs.Coprime v.natAbs) :
    z^2≠quartic (descentRows j).1 (descentRows j).2.1 (descentRows j).2.2 u v := by
  intro eq
  let p:=localPrime j
  let n:=modulus j
  have pp:p.Prime:=by fin_cases j <;> decide
  let _:Fact p.Prime:=⟨pp⟩
  have mem (a:ℤ):(a:ZMod n)^2∈squares n:=Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have prim:¬(ZMod.castHom (prime_dvd j) (ZMod p) ((u:ZMod n)^2)=0 ∧
      ZMod.castHom (prime_dvd j) (ZMod p) ((v:ZMod n)^2)=0):=by
    rintro ⟨a,b⟩
    rw [map_pow,map_intCast] at a b
    have up:=(ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp (sq_eq_zero_iff.mp a)
    have vp:=(ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp (sq_eq_zero_iff.mp b)
    exact (Nat.not_coprime_of_dvd_of_dvd pp.one_lt (by simpa using Int.natAbs_dvd_natAbs.mpr up)
      (by simpa using Int.natAbs_dvd_natAbs.mpr vp)) cop
  apply block j _ (mem u) _ (mem v) prim
  convert mem z using 1
  have e:((z:ZMod n)^2)=quartic ((descentRows j).1:ZMod n) ((descentRows j).2.1:ZMod n)
    ((descentRows j).2.2:ZMod n) (u:ZMod n) (v:ZMod n):=by
    simpa [quartic] using congrArg (Int.castRingHom (ZMod n)) eq
  rw [e];unfold quartic;ring

private def count (n:ℕ) [NeZero n] (a b:ℤ):ℕ :=
  1+((Finset.univ:Finset (ZMod n×ZMod n)).filter
    fun z=>z.2^2=z.1*(z.1+(a:ZMod n))*(z.1+(b:ZMod n))).card

theorem good_reduction_counts :
    count 7 4 6=4 ∧ count 11 4 6=8 ∧ count 7 64 439=4 ∧ count 11 64 439=12 := by decide

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.six_quartic_obstructions
#print axioms Sun28.FactorHeights.good_reduction_counts
