import LocalSupport

set_option maxRecDepth 2500
namespace Sun28.HeightCubics.Refinement
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK Height
open private height_div from ContactHeight
noncomputable section

/-- The conductor, its local conditions and the two Faltings heights of a
rational elliptic curve.  Separate fields record the published statements. -/
structure EllipticEstimates (E:WeierstrassCurve ℤ) where
  N : ℕ
  pos : 0<N
  good : ∀ p:ℕ,p.Prime → ¬(p:ℤ)∣E.Δ → N.factorization p=0
  multiplicative : ∀ p:ℕ,p.Prime → (p:ℤ)∣E.Δ → ¬(p:ℤ)∣E.c₄ → N.factorization p=1
  tame : ∀ p:ℕ,p.Prime → p≠2 → p≠3 → N.factorization p≤2
  two : N.factorization 2≤8
  three : N.factorization 3≤5
  stable : ℝ
  relative : ℝ
  baseChange : stable≤relative
  jHeight : logHeight₁ (jRatio E)≤12*stable+6*Real.log (max 1 stable)+75.84
  faltings : relative≤(1/4)*(N:ℝ)*(Real.log (N:ℝ))^2+9

/-- von Känel, §2.1, §2.2, (3.5) and Proposition 6.1;
the multiplicative criterion is Silverman, AEC VII.5.1. -/
def PublishedElliptic : Prop :=
  ∀ E:WeierstrassCurve ℤ,E.Δ≠0 → Nonempty (EllipticEstimates E)

def conductorCap (r:ThreeRows) (A B:ℤ) : ℕ :=
  62208*heightRadical A B^2*noncubic r.b A B^2*hidden r.center A B

private theorem member_dvd {p:ℕ} {S:Finset ℕ} (hp:p∈S) : p∣primeProduct S :=
  Finset.dvd_prod_of_mem (fun n:ℕ=>n) hp

/-- Each denominator prime outside the measured odd support occurs only once. -/
theorem conductor_dvd (r:ThreeRows) {A B u:ℤ} (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0)
    (sq:left r A B=sqfInt (left r A B)*u^2)
    (data:EllipticEstimates (frey (sqfInt (left r A B)) (cubePart (right r A B)) u (cubeRoot (right r A B)))) :
    data.N∣conductorCap r A B := by
  let T:=heightRadical A B
  let U:=noncubic r.b A B
  let H:=hidden r.center A B
  change data.N∣62208*T^2*U^2*H
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p k prime power
  have ord: k≤data.N.factorization p:=(prime.pow_dvd_iff_le_factorization data.pos.ne').1 power
  have cap: p^k∣p^(data.N.factorization p):=pow_dvd_pow p ord
  apply cap.trans
  by_cases p2:p=2
  · subst p
    exact (pow_dvd_pow 2 data.two).trans ((show 2^8∣62208 by decide).trans ⟨T^2*U^2*H,by ring⟩)
  by_cases p3:p=3
  · subst p
    exact (pow_dvd_pow 3 data.three).trans ((show 3^5∣62208 by decide).trans ⟨T^2*U^2*H,by ring⟩)
  have tame:=data.tame p prime p2 p3
  by_cases seen:p∈support A B
  · have dvd:p∣T:=by change p∣heightRadical A B; rw [←product_support];exact member_dvd seen
    exact (pow_dvd_pow p tame).trans ((pow_dvd_pow_of_dvd dvd 2).trans ⟨62208*U^2*H,by ring⟩)
  have test:=local_tests r cop off sq prime seen
  by_cases c:p∈residualMark A B r.center
  · obtain ⟨bad,unit⟩:=test.2 c
    rw [data.multiplicative p prime bad unit,pow_one]
    exact (member_dvd c).trans (dvd_mul_left H _)
  by_cases b:p∈defective r.b A B
  · have dvd:p∣U:=member_dvd b
    exact (pow_dvd_pow p tame).trans ((pow_dvd_pow_of_dvd dvd 2).trans ⟨62208*T^2*H,by ring⟩)
  have good:¬(p:ℤ)∣(frey (sqfInt (left r A B)) (cubePart (right r A B)) u (cubeRoot (right r A B))).Δ:=
    fun h=>(test.1 h).elim b c
  rw [data.good p prime good,pow_zero]
  exact one_dvd _

theorem j_height_conductor {W:WeierstrassCurve ℤ} (h:EllipticEstimates W) :
    logHeight₁ (jRatio W)≤(9/2)*(h.N:ℝ)*(Real.log (h.N:ℝ))^2+238 := by
  let C:ℝ:=(1/4)*(h.N:ℝ)*(Real.log (h.N:ℝ))^2+9
  have cost:0≤(1/4:ℝ)*(h.N:ℝ)*(Real.log (h.N:ℝ))^2:=by positivity
  have pos:1≤C:=by dsimp [C];linarith
  have upper:=h.baseChange.trans h.faltings
  have cap:max 1 h.stable≤C:=max_le pos upper
  have logs:Real.log (max 1 h.stable)≤C:=
    (Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).trans (by linarith only [cap])
  dsimp only [C] at logs
  linarith only [h.jHeight,upper,logs]

def heightBound (n:ℕ) : ℝ := (9/2)*(n:ℝ)*(Real.log (n:ℝ))^2+281

theorem bound_mono {m n:ℕ} (np : 0 < m) (capNat : m ≤ n) : heightBound m≤heightBound n := by
  have one:1≤(m:ℝ):=Nat.one_le_cast.mpr np
  have mpos:0<(m:ℝ):=by positivity
  have cap:(m:ℝ)≤(n:ℝ):=by exact_mod_cast capNat
  have loss:=mul_le_mul cap (pow_le_pow_left₀ (Real.log_nonneg one) (Real.log_le_log mpos cap) 2)
    (sq_nonneg _) (mpos.le.trans cap)
  unfold heightBound
  linarith only [loss]

theorem marked_height (pub:PublishedElliptic) (r:ThreeRows) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) : pairLogHeight A B≤heightBound (conductorCap r A B) := by
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
  have div:=conductor_dvd r cop off pe data
  have uq:0<noncubic r.b A B:=by
    unfold noncubic
    apply Nat.pos_of_ne_zero
    exact prime_product_nonzero _ (fun p mem=>(Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp (Finset.mem_filter.mp mem).1).1))
  have hr:0<hidden r.center A B:=by
    unfold hidden
    apply Nat.pos_of_ne_zero
    exact prime_product_nonzero _ (fun p mem=>(Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp mem).1))
  have tp:=Nat.mul_pos pos_cutoff (pos_odd A B)
  have positive:0<conductorCap r A B:=by unfold conductorCap;exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos tp _)) (pow_pos uq 2)) hr
  have larger:=bound_mono data.pos (Nat.le_of_dvd positive div)
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
end Sun28.HeightCubics.Refinement
#print axioms Sun28.HeightCubics.Refinement.conductor_dvd
#print axioms Sun28.HeightCubics.Refinement.j_height_conductor
#print axioms Sun28.HeightCubics.Refinement.bound_mono
#print axioms Sun28.HeightCubics.Refinement.marked_height
