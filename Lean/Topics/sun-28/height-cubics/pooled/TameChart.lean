import PrimeRoles

namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres ZInQ.RouteK Height Refinement
open private height_div from ContactHeight
noncomputable section

/-- The dyadic and triadic universal bounds and the two minor primes 5 and 7. -/
def exceptional : ℕ := 2^8*3^5*5^2*7^2
def cap (r:ThreeRows) (A B:ℤ) :=
  exceptional*primeProduct (baseSet r.center A B)*(primeProduct (squareSet r.a A B))^2*
    (primeProduct (cubeSet r.b A B))^2

theorem base_prime {i:Fin 5} {A B:ℤ} {p:ℕ} (mem:p∈baseSet i A B) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp mem).1

theorem cap_pos (r:ThreeRows) (A B:ℤ) : 0<cap r A B := by
  unfold cap
  have h (i:Fin 5):0<primeProduct (baseSet i A B) :=
    Nat.pos_of_ne_zero (prime_product_nonzero _ (fun _ m=>base_prime m))
  have c (i:Fin 5):0<primeProduct (cubeSet i A B):=
    Nat.pos_of_ne_zero (prime_product_nonzero _ (fun _ m=>base_prime (Finset.mem_filter.mp m).1))
  have s (i:Fin 5):0<primeProduct (squareSet i A B):=
    Nat.pos_of_ne_zero (prime_product_nonzero _ (fun _ m=>base_prime (Finset.mem_filter.mp m).1))
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (h _)) (pow_pos (s _) _)) (pow_pos (c _) _)

private theorem core_eq : core={2,3,5,7} := by
  have p2 : Nat.Prime 2 := by decide
  have p3 : Nat.Prime 3 := by decide
  have p5 : Nat.Prime 5 := by decide
  have p7 : Nat.Prime 7 := by decide
  rw [core,show (210:ℕ)=2*3*5*7 by decide]
  simp (disch := decide) only [Nat.primeFactors_mul,p2.primeFactors,p3.primeFactors,p5.primeFactors,p7.primeFactors]
  decide

theorem conductor_dvd_cap (r:ThreeRows) {A B u:ℤ} (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0)
    (sq:left r A B=sqfInt (left r A B)*u^2)
    (data:EllipticEstimates (frey (sqfInt (left r A B)) (cubePart (right r A B)) u (cubeRoot (right r A B)))) :
    data.N∣cap r A B := by
  let D:=primeProduct (baseSet r.center A B)
  let G:=primeProduct (squareSet r.a A B)
  let H:=primeProduct (cubeSet r.b A B)
  change data.N∣exceptional*D*G^2*H^2
  have exc:exceptional∣exceptional*D*G^2*H^2:=⟨D*G^2*H^2,by ring⟩
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p k prime h
  apply (pow_dvd_pow p ((prime.pow_dvd_iff_le_factorization data.pos.ne').1 h)).trans
  by_cases p2:p=2
  · subst p;exact (pow_dvd_pow _ data.two).trans ((show 2^8∣exceptional by decide).trans exc)
  by_cases p3:p=3
  · subst p;exact (pow_dvd_pow _ data.three).trans ((show 3^5∣exceptional by decide).trans exc)
  have tame:=data.tame p prime p2 p3
  by_cases small:p∈core
  · have m:p∈({2,3,5,7}:Finset ℕ):=by
      rwa [←core_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton] at m
    rcases m with z|z|z|z
    · exact False.elim (p2 z)
    · exact False.elim (p3 z)
    · subst p;exact (pow_dvd_pow _ tame).trans ((show 5^2∣exceptional by decide).trans exc)
    · subst p;exact (pow_dvd_pow _ tame).trans ((show 7^2∣exceptional by decide).trans exc)
  have tests:=local_roles r cop off sq prime small
  by_cases base:p∈baseSet r.center A B
  · obtain ⟨bad,unit⟩:=tests.2 base
    rw [data.multiplicative p prime bad unit,pow_one]
    have dv:p∣D:=Finset.dvd_prod_of_mem (fun q:ℕ=>q) base
    exact dv.trans ⟨exceptional*G^2*H^2,by ring⟩
  by_cases sqp:p∈squareSet r.a A B
  · have dv:p∣G:=Finset.dvd_prod_of_mem (fun q:ℕ=>q) sqp
    exact (pow_dvd_pow _ tame).trans ((pow_dvd_pow_of_dvd dv 2).trans ⟨exceptional*D*H^2,by ring⟩)
  by_cases cb:p∈cubeSet r.b A B
  · have dv:p∣H:=Finset.dvd_prod_of_mem (fun q:ℕ=>q) cb
    exact (pow_dvd_pow _ tame).trans ((pow_dvd_pow_of_dvd dv 2).trans (dvd_mul_left _ _))
  have good:¬(p:ℤ)∣(frey (sqfInt (left r A B)) (cubePart (right r A B)) u (cubeRoot (right r A B))).Δ:=
    fun bad=>(tests.1 bad).elim sqp (fun h=>h.elim cb base)
  rw [data.good p prime good,pow_zero];exact one_dvd _

theorem height_of_chart (pub:PublishedElliptic) (r:ThreeRows) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) : pairLogHeight A B≤heightBound (cap r A B) := by
  let P:=left r A B
  let Q:=right r A B
  let R:=baseRow r A B
  let d:=sqfInt P
  let e:=cubePart Q
  let v:=cubeRoot Q
  have pn:P≠0:=mul_ne_zero (det_ne r.ib) (off _)
  have qn:Q≠0:=mul_ne_zero (det_ne r.ia.symm) (off _)
  have rn:R≠0:=mul_ne_zero (det_ne r.ab) (off _)
  obtain ⟨ds,u,_,eq⟩:=sqfInt_spec pn
  have pe:P=d*u^2:=eq
  have qe:Q=e*v^3:=factor_cube qn
  have dn:d≠0:=ds.ne_zero
  have en:e≠0:=fun h=>qn (by rw [qe,h,zero_mul])
  have sum:P+Q=R:=minor_identity _ _ _ A B
  have de:(frey d e u v).Δ≠0:=by
    rw [frey_discriminant,←pe,←qe,sum]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero _ dn)) (pow_ne_zero _ en)) rn
  obtain ⟨data⟩:=pub _ de
  have div:=conductor_dvd_cap r cop off pe data
  have larger:=bound_mono data.pos (Nat.le_of_dvd (cap_pos r A B) div)
  apply le_trans _ larger
  have J:=frey_j pe qe sum dn en rn
  have ht:=j_height_conductor data
  have hX:=crossRatio_height r.a r.b r.center r.ab r.ia.symm r.ib.symm cop off
  change pairLogHeight A B≤logHeight₁ ((P:ℚ)/R)+32 at hX
  have rr:(R:ℚ)≠0:=by exact_mod_cast rn
  have X: (P:ℚ)/R=1-jRatio (frey d e u v)/1728:=by
    rw [J];field_simp;exact_mod_cast (show P=R-Q by omega)
  rw [X] at hX
  have dd:=height_div (jRatio (frey d e u v)) 1728
  have con:logHeight₁ (1728:ℚ)≤10:=by
    rw [Rat.logHeight₁_eq_log_max]
    norm_num
    have c:=Real.log_le_log (by norm_num:(0:ℝ)<1728) (show (1728:ℝ)≤2^11 by norm_num)
    rw [Real.log_pow] at c
    have a:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    have b:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<3 / 2)
    have c2:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<(4 / 3))
    have log2:Real.log (2:ℝ)=Real.log (3/2)+Real.log (4/3):=by rw [←Real.log_mul (by norm_num) (by norm_num)];norm_num
    norm_num at c
    linarith only [log2,b,c2,c]
  have add:=logHeight₁_add_le (1:ℚ) (-(jRatio (frey d e u v)/1728))
  have wt:(totalWeight ℚ:ℝ)=1:=by rw [NumberField.totalWeight_eq_finrank];simp
  rw [logHeight₁_one,logHeight₁_neg,wt,one_mul] at add
  rw [sub_eq_add_neg] at hX
  unfold heightBound
  linarith only [hX,dd,add,ht,con,Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)]

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.base_prime
#print axioms Sun28.HeightCubics.Pooled.cap_pos
#print axioms Sun28.HeightCubics.Pooled.conductor_dvd_cap
#print axioms Sun28.HeightCubics.Pooled.height_of_chart
