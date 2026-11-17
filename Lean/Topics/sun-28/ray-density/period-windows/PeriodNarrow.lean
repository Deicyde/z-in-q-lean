import PeriodFrame

namespace Sun28.PeriodWindows
open Sun28.QualitativeRows Sun28.ContactFactors Sun28.ContactSieve Sun28.ScalarPlaces Sun28.TwistRank
open Sun28.FixedPreparation Sun28.RealPoleBounds Sun28.GaussianSelection Sun28.Exceptional
open Sun28.Forward Sun28.FiniteWitness Sun28.ScalarHeight Sun28.Ordinary
open ManuscriptV15.Arithmetic
noncomputable section
open scoped Classical
open private note_ray_norm from RaySelection

/-- A single-set recurrence. The set only tests one rational prime at a time. -/
def Narrow (S : ℕ → Prop) : Prop :=
  ∀ (coeff : Finset ℤ) (Y : ℕ), ∃ u>Y, ∃ m : ℕ, 0 < m ∧ m^4≤u ∧
    ∀ h∈coeff, ∃ p : ℕ, (p:ℤ)=(u:ℤ)+h*(m:ℤ)^2 ∧ S p

/-- The relative-density parameter may depend on the finite guard K. -/
def PositivePrimeDensity (S : ℕ → Prop) : Prop :=
  ∃ δ : ℝ, 0<δ ∧ ∃ N₀ : ℕ, ∀ N≥N₀,
    δ * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N+1)).filter (fun n=>S n)).card:ℝ)

def NarrowTheorem : Prop :=
  ∀ S : ℕ→Prop, (∀ p,S p→p.Prime) → PositivePrimeDensity S → Narrow S

theorem guarded_values {S : ℕ→Prop} (primes : ∀ p,S p→p.Prime) (recurs : Narrow S)
    (A : Fin 3→ℚ) (Y H d : ℕ) (dp : 0<d) :
    ∃ u v : ℕ, ∃ h : PrimeValues A u v, 0<v ∧ d∣v ∧ H*(dilation A*v)^2<u ∧
      ∀ i∈shifts A, Y<h.value i ∧ S (h.value i) := by
  classical
  let coeff:=(shifts A).image fun r=>offset (dilation A) r*(d:ℤ)^2
  let B:=coeff.sup Int.natAbs+H*(dilation A*d)^2+Y+1
  have bp:0<B:=by dsimp [B];omega
  obtain ⟨u,large,m,mp,quartic,seq⟩:=recurs coeff (4*B^2)
  have safe:B*m^2+B<u:=by
    by_cases sm:m^2≤B
    · have z:=Nat.mul_le_mul_left B sm
      nlinarith only [large,z,bp,Nat.le_mul_self B]
    · have zz:B+1 ≤ m^2:=by omega
      have z:=Nat.mul_le_mul_right (m^2) zz
      nlinarith only [quartic,z,large,show 2 ≤ m^2 by omega]
  have vals (i : ↥(shifts A)) : ∃ p:ℕ, Y<p ∧
      (p:ℤ)=(u:ℤ)+offset (dilation A) i.val*((d*m:ℕ):ℤ)^2 ∧ S p := by
    let c:=offset (dilation A) i.val*(d:ℤ)^2
    have mem:c∈coeff:=Finset.mem_image_of_mem _ i.property
    have size:c.natAbs≤B:=(Finset.le_sup (f:=Int.natAbs) mem).trans (by dsimp [B];omega)
    obtain ⟨p,eq,ok⟩:=seq c mem
    have low:-(B:ℤ)≤c:=by omega
    have z : (B:ℤ)*(m:ℤ)^2+B<(u:ℤ):=by exact_mod_cast safe
    have yp:(Y:ℤ)<p:=by
      have yB:Y≤B:=by dsimp [B];omega
      nlinarith only [z,eq,mul_le_mul_of_nonneg_right low (sq_nonneg (m:ℤ)),
        show (Y:ℤ)≤B by exact_mod_cast yB]
    refine ⟨p,by exact_mod_cast yp,?_,ok⟩
    rw [eq];push_cast; dsimp [c];ring
  choose p lower eq mem using vals
  let h : PrimeValues A u (d*m):={
    value:=fun i=>if hi:i∈shifts A then p ⟨i,hi⟩ else 0
    prime:=fun i hi=>by simpa [hi] using primes _ (mem ⟨i,hi⟩)
    equation:=fun i hi=>by simpa [hi] using eq ⟨i,hi⟩ }
  refine ⟨u,d*m,h,Nat.mul_pos dp mp,dvd_mul_right ..,?_,fun i hi=>?_⟩
  · have le:H*(dilation A*d)^2≤B:=by dsimp [B];omega
    nlinarith only [safe,Nat.mul_le_mul_right (m^2) le]
  · simpa [h,hi] using And.intro (lower ⟨i,hi⟩) (mem ⟨i,hi⟩)

theorem frame_of_narrow {X : ℤ} (w : Window X) (L : ℕ)
    (recur : Narrow (cleanPrime (guard (integerRadicand X) L))) : Nonempty (PeriodFrame w L) := by
  classical
  let A:=fixedScale w.n
  let K:=guard (integerRadicand X) L
  let threshold:=slopeThreshold A w.C (1/2)
  obtain ⟨H,hH⟩:=exists_nat_gt threshold
  obtain ⟨Y,hY⟩:=exists_nat_gt (primeSize A 65)
  obtain ⟨u,v,values,vp,div,slopeNat,vals⟩:=guarded_values (fun _ h => h.1) recur A Y H
    (requiredDivisor A) (divisor_positive A)
  have sl : threshold<(slope A u v:ℝ) := by
    apply hH.trans
    have pos:0<(dilation A*v:ℕ):=Nat.mul_pos (dilation_positive A) vp
    have h:(H:ℝ)*((dilation A*v:ℕ):ℝ)^2<u:=by exact_mod_cast slopeNat
    simpa [Sun28.ContactFactors.slope] using (lt_div_iff₀ (sq_pos_of_pos (show (0:ℝ)<(dilation A*v:ℕ) by exact_mod_cast pos))).mpr h
  have alive : ∀ j,A j≠0 := fun j=>(actual_scales_positive w.n (fun i=>(w.roots.odd i).1.ne') j).ne'
  have good i hi := large_prime_exclusions A 65 alive
    (hY.trans (show (Y:ℝ)<(values.value i:ℝ) by exact_mod_cast (vals i hi).1))
  have cert (i : ↥(shifts A)) := (vals i i.property).2.2
  choose π norm r16 r7 clean free using cert
  have rays : RayValues values := by
    intro d hd
    obtain ⟨dy,sv⟩:=note_ray_norm (r16 ⟨d,hd⟩) (r7 ⟨d,hd⟩)
    rw [norm] at dy sv
    exact ⟨by exact_mod_cast (good d hd).1,dy,sv⟩
  have ex : ∀ j,∀ p∈selected values j, ¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0 := by
    intro j p hp
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hp
    have g := (good (-b/A j) (shift_mem A j hb)).2
    exact ⟨g.1,g.2.1,g.2.2 j⟩
  have roots (i : ↥(shifts A)) : ∃ z:ZMod (values.value i), z^2=2 ∧
      ZInQ.pointCount (values.value i) (-(3-z)^2)=adjacentNorm (π i) true ∧
      ZInQ.pointCount (values.value i) (-(3+z)^2)=adjacentNorm (π i) false := by
    let _:=Fact.mk (values.prime _ i.property)
    exact Sun28.CMReduction.exists_oriented_root (norm i) (r16 i) (r7 i)
  choose z sq plus minus using roots
  let o:=periodAt values (fun d hd=>(rays d hd).1) z sq
  have dvd (i : ↥(shifts A)) (s : Bool) : o i s ∣ adjacentNorm (π i) s := by
    have h:=periodAt_dvd values (fun d hd=>(rays d hd).1) z sq i s
    cases s
    · simpa only [curveOrders,Bool.false_eq_true,ite_false,sub_neg_eq_add,minus] using h
    · simpa only [curveOrders,ite_true,plus] using h
  have nf (i : ↥(shifts A)) (s : Bool) : adjacentNorm (π i) s ≠ 0 := by
    intro eq
    have d:=ray_dyadic (r16 i)
    cases s <;> simp_all
  refine ⟨⟨u,v,values,vp,div,sl,rays,ex,z,sq,fun i=>?_,fun i s=>?_,fun q pp odd le i s d=>?_⟩⟩
  · have g : (o i false).gcd (o i true) ∣ (adjacentNorm (π i) false).gcd (adjacentNorm (π i) true) :=
      Nat.dvd_gcd ((Nat.gcd_dvd_left ..).trans (dvd i false)) ((Nat.gcd_dvd_right ..).trans (dvd i true))
    have vv:=ray_dyadic (r16 i)
    have gg:=gcd_four_of_mixed (Nat.pos_of_ne_zero (nf i true)) (Nat.pos_of_ne_zero (nf i false))
      vv.1 vv.2 (clean i)
    rw [Nat.gcd_comm (adjacentNorm (π i) false),gg] at g
    exact g.trans (Nat.dvd_factorial (by decide) (by decide))
  · have h:=(Nat.factorization_le_iff_dvd (periodAt_positive values _ z sq i s).ne' (nf i s)).mpr (dvd i s) 2
    simp only [Nat.factorization_def _ Nat.prime_two] at h
    have d:=ray_dyadic (r16 i)
    cases s
    · exact h.trans d.2.le
    · exact h.trans (d.1.le.trans (by decide))
  · exact free i q pp odd le s (d.trans (dvd i s))

theorem frame_of_density (taoZiegler : NarrowTheorem) {X : ℤ} (w : Window X) (L : ℕ)
    (density : PositivePrimeDensity (cleanPrime (guard (integerRadicand X) L))) :
    Nonempty (PeriodFrame w L) := frame_of_narrow w L (taoZiegler _ (fun _ h=>h.1) density)

end
end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.guarded_values
#print axioms Sun28.PeriodWindows.frame_of_narrow
#print axioms Sun28.PeriodWindows.frame_of_density
