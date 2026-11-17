import PellCutoff

/-! One chart at each original contact. The cross multiplication in a chart
replaces four affine slopes by the same three integer square roots. -/
namespace Sun28.HeightFibres
open ZInQ.RouteK Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors Sun28.FiveMarkTriples
noncomputable section
set_option exponentiation.threshold 2000
set_option maxRecDepth 8192

private def leftRow (i : Fin 5) : Fin 5 := ![1,0,0,0,0] i
private def midRow (i : Fin 5) : Fin 5 := ![2,2,1,1,1] i
private def rightRow (i : Fin 5) : Fin 5 := ![3,3,3,2,2] i
private def U (i : Fin 5) := det i (midRow i)
private def V (i : Fin 5) := det i (rightRow i)
private def W (i : Fin 5) := det i (leftRow i)
private def delta₁ (i : Fin 5) := V i*det (leftRow i) (midRow i)
private def delta₂ (i : Fin 5) := U i*det (leftRow i) (rightRow i)
private def mult (i : Fin 5) : Fin 3→ℤ := ![U i*V i,W i*V i,W i*U i]

private theorem catalogue (i : Fin 5) :
    (∀ j,(mult i j)≠0 ∧ (mult i j).natAbs≤2^32) ∧
    delta₁ i≠0 ∧ delta₂ i≠0 ∧ delta₁ i≠delta₂ i ∧
    (delta₁ i).natAbs≤2^32 ∧ (delta₂ i).natAbs≤2^32 := by
  have e : ∀ n : Fin 5,(∀ j,(mult n j)≠0 ∧ (mult n j).natAbs≤2^32) ∧
    delta₁ n≠0 ∧ delta₂ n≠0 ∧ delta₁ n≠delta₂ n ∧
    (delta₁ n).natAbs≤2^32 ∧ (delta₂ n).natAbs≤2^32 := by decide
  exact e i

private theorem equation_rows (i : Fin 5) (A B : ℤ) :
    mult i 0*oldForm (leftRow i) A B-mult i 1*oldForm (midRow i) A B=delta₁ i*oldForm i A B ∧
    mult i 0*oldForm (leftRow i) A B-mult i 2*oldForm (rightRow i) A B=delta₂ i*oldForm i A B := by
  fin_cases i <;> constructor <;> norm_num [mult,U,V,W,delta₁,delta₂,det,coeffA,coeffB,oldForm,leftRow,midRow,rightRow] <;> ring

private theorem linear_log {g z : ℤ} (ng : g≠0) (nz:z≠0)
    (small : g.natAbs≤2^32) : numberLog (g*z)≤numberLog z+32 := by
  have hg : numberLog g≤Real.log (2^32) := Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr ng)
    (by exact_mod_cast small)
  rw [Real.log_pow] at hg
  rw [log_mul_int ng nz]
  norm_num at hg
  linarith only [hg,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]

private theorem sum_log {x y : ℤ} (nx : x≠0) (_ny : y≠0) (nz : x-y≠0) {T : ℝ}
    (hx : numberLog x≤T) (hy : numberLog y≤T) : numberLog (x-y)≤T+1 := by
  let n:=max x.natAbs y.natAbs
  have nn : 0<n := lt_of_lt_of_le (Int.natAbs_pos.mpr nx) (Nat.le_max_left ..)
  have h: (x-y).natAbs ≤ 2*n := by
    have a:=Int.natAbs_add_le x (-y)
    rw [Int.natAbs_neg] at a
    change (x-y).natAbs≤2*max x.natAbs y.natAbs
    rw [sub_eq_add_neg]
    omega
  have hp : (0:ℝ)<(x-y).natAbs := by exact_mod_cast Int.natAbs_pos.mpr nz
  have logb:=Real.log_le_log hp (show ((x-y).natAbs:ℝ)≤2*(n:ℝ) by exact_mod_cast h)
  rw [Real.log_mul (by norm_num) (by exact_mod_cast nn.ne')] at logb
  have l : Real.log (n:ℝ)≤T := by
    rcases le_total x.natAbs y.natAbs with h|h
    · simpa only [numberLog,n,max_eq_right h] using hy
    · simpa only [numberLog,n,max_eq_left h] using hx
  unfold numberLog
  linarith only [logb,l,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]

private theorem denominator_recovery {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5) {X : ℝ}
    (large : numberLog (oldForm (leftRow i) A B)≤X) (small : numberLog (oldForm i A B)≤X) :
    pairLogHeight A B≤X+33 := by
  have a : A≠0:=off 1
  have b : B≠0:=off 0
  rw [pair_as_max a b]
  fin_cases i
  · change numberLog A≤X at large
    change numberLog B≤X at small
    exact max_le (by linarith) (by linarith)
  · change numberLog B≤X at large
    change numberLog A≤X at small
    exact max_le (by linarith) (by linarith)
  · change numberLog B≤X at large
    change numberLog (A-B)≤X at small
    have h:=sum_log (show A-B≠0 from off 2) (neg_ne_zero.mpr b) (show A-B-(-B)≠0 by omega) small
      (by simpa [numberLog] using large : numberLog (-B)≤X)
    rw [show A-B-(-B)=A by ring] at h
    exact max_le (by linarith) (by linarith)
  · change numberLog B≤X at large
    change numberLog (A-2401*B)≤X at small
    have const:=linear_log (by decide : (-2401:ℤ)≠0) b (by decide)
    have h:=sum_log (show A-2401*B≠0 from off 3) (mul_ne_zero (by decide : (-2401:ℤ)≠0) b)
      (show A-2401*B-(-2401*B)≠0 by omega) (small.trans (by linarith : X≤X+32))
      (const.trans (by linarith : numberLog B+32≤X+32))
    rw [show A-2401*B-(-2401*B)=A by ring] at h
    exact max_le (by linarith) (by linarith)
  · change numberLog B≤X at large
    change numberLog (32*A+343*B)≤X at small
    have const:=linear_log (by decide : (343:ℤ)≠0) b (by decide)
    have h:=sum_log (show 32*A+343*B≠0 from off 4) (mul_ne_zero (by decide : (343:ℤ)≠0) b)
      (show 32*A+343*B-343*B≠0 by omega) (small.trans (by linarith : X≤X+32))
      (const.trans (by linarith : numberLog B+32≤X+32))
    rw [show 32*A+343*B-343*B=32*A by ring,log_mul_int (by decide : (32:ℤ)≠0) a] at h
    exact max_le (by linarith only [h,nonneg_numberLog (by decide : (32:ℤ)≠0)]) (by linarith)

/-- All five centered Pell systems. The logarithm of the selected row is the
only size input besides the signed odd radical. -/
theorem every_contact_height (pell : PublishedPell312) (regulator : RegulatorBound)
    (disc : BiquadraticDiscriminants) {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5) :
    let T:ℝ:=heightRadical A B
    pairLogHeight A B≤2^800*T^19+2^500*T^10*(numberLog (oldForm i A B)+32) := by
  let f:=oldForm i A B
  let T:ℝ:=heightRadical A B
  let Z:=numberLog f+32
  let l:=leftRow i
  let m:=midRow i
  let n:=rightRow i
  obtain ⟨_,a,na,ea⟩:=sqfInt_spec (off l)
  obtain ⟨_,b,_,eb⟩:=sqfInt_spec (off m)
  obtain ⟨_,c,_,ec⟩:=sqfInt_spec (off n)
  change oldForm l A B=kernel l A B*a^2 at ea
  change oldForm m A B=kernel m A B*b^2 at eb
  change oldForm n A B=kernel n A B*c^2 at ec
  let G (j : Fin 3) (r : Fin 5):=mult i j*kernel r A B
  obtain ⟨mu,nd,ne,de,bd,be⟩:=catalogue i
  have live (r : Fin 5):kernel r A B≠0:=(sqfInt_spec (off r)).1.ne_zero
  have gn (j r) : G j r≠0:=mul_ne_zero (mu j).1 (live r)
  have scale (j r) : ((G j r).natAbs:ℝ)≤2^32*T := by
    change (((mult i j*kernel r A B).natAbs:ℕ):ℝ)≤_
    rw [Int.natAbs_mul,Nat.cast_mul]
    exact mul_le_mul (by exact_mod_cast (mu j).2) (Nat.cast_le.mpr (kernel_bound off r)) (by positivity) (by positivity)
  have right₁ : numberLog (delta₁ i*f)≤Z := linear_log nd (off i) bd
  have right₂ : numberLog (delta₂ i*f)≤Z := linear_log ne (off i) be
  have fn : f≠0:=off i
  have diff : delta₁ i*f≠delta₂ i*f := fun e=>de (mul_right_cancel₀ fn e)
  have row:=equation_rows i A B
  change mult i 0*oldForm l A B-mult i 1*oldForm m A B=delta₁ i*f ∧
    mult i 0*oldForm l A B-mult i 2*oldForm n A B=delta₂ i*f at row
  rw [ea,eb,ec] at row
  have t:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have tp:0≤T:=by linarith
  have s1:1≤2^32*T:=by linarith
  have z1:1≤Z:=by dsimp [Z];linarith only [nonneg_numberLog fn]
  have est : numberLog a≤2^185*(2^32*T)^19+2^165*(2^32*T)^10*Z := by
    apply pell_integer_height pell regulator disc (a:=a) (b:=b) (c:=c) s1 (le_trans (by norm_num : (0:ℝ)≤1) z1)
      (gn 0 l) (gn 1 m) (gn 2 n) (scale 0 l) (scale 1 m) (scale 2 n)
      (mul_ne_zero nd fn) (mul_ne_zero ne fn) diff right₁ right₂
    · dsimp [G];linear_combination row.1
    · dsimp [G];linear_combination row.2
  have ga : numberLog (oldForm l A B)=numberLog (kernel l A B)+2*numberLog a := by
    rw [ea,pow_two,log_mul_int (live l) (mul_ne_zero na na),log_mul_int na na];ring
  have lg : numberLog (kernel l A B)≤T := (Real.log_le_sub_one_of_pos
    (by exact_mod_cast Int.natAbs_pos.mpr (live l) : 0<((kernel l A B).natAbs:ℝ))).trans
      (by have e:((kernel l A B).natAbs:ℝ)≤T:=Nat.cast_le.mpr (kernel_bound off l);linarith)
  have poly : (2:ℝ)^185*(2^32*T)^19=2^793*T^19 := by rw [mul_pow];ring
  have poly' : (2:ℝ)^165*(2^32*T)^10*Z=2^485*T^10*Z := by rw [mul_pow];ring
  rw [poly,poly'] at est
  let X:ℝ:=(2:ℝ)^798*T^19+2^497*T^10*Z
  have t19:T≤T^19:=by simpa using pow_le_pow_right₀ t (by decide : 1≤19)
  have one:1≤T^19:=one_le_pow₀ t
  have t10:1≤T^10:=one_le_pow₀ t
  have zz:Z≤T^10*Z:=by simpa using mul_le_mul_of_nonneg_right t10 (le_trans (by norm_num) z1)
  have p:0≤T^10*Z:=by linarith
  have h : numberLog (oldForm l A B)≤X := by
    dsimp [X]
    linarith only [ga,lg,est,t19,one,p]
  have j : numberLog f≤X := by
    have zj:numberLog f≤Z:=by dsimp [Z];linarith
    dsimp [X]
    linarith only [zj,zz,one,p]
  have data:=denominator_recovery off i h j
  change pairLogHeight A B≤X+33 at data
  change pairLogHeight A B≤2^800*T^19+2^500*T^10*Z
  dsimp [X] at data
  linarith only [data,one,p]

theorem contact_sector (pell : PublishedPell312) (regulator : RegulatorBound)
    (disc : BiquadraticDiscriminants) {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5)
    (small : numberLog (oldForm i A B)≤(heightRadical A B:ℝ)^14) : target A B := by
  let T:ℝ:=heightRadical A B
  have one : 1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have h:=every_contact_height pell regulator disc off i
  change pairLogHeight A B≤2^800*T^19+2^500*T^10*(numberLog (oldForm i A B)+32) at h
  have lo : T^19≤T^24:=pow_le_pow_right₀ one (by decide)
  have base : 1≤T^14:=one_le_pow₀ one
  change numberLog (oldForm i A B)≤T^14 at small
  have z:numberLog (oldForm i A B)+32≤33*T^14:=by linarith only [small,base]
  have m:=mul_le_mul_of_nonneg_left z (show 0≤(2:ℝ)^500*T^10 by positivity)
  rw [show (2:ℝ)^500*T^10*(33*T^14)=33*2^500*T^24 by ring] at m
  have hcap:pairLogHeight A B≤2^810*T^24:=by
    calc
      _ ≤ _ := h
      _ ≤ 2^800*T^24+33*2^500*T^24 :=
        add_le_add (mul_le_mul_of_nonneg_left lo (by positivity)) m
      _ = ((2:ℝ)^800+33*2^500)*T^24 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (by decide : (2:ℕ)^800+33*2^500≤2^810)) (pow_nonneg (le_trans (by norm_num) one) _)
  have endpt:=hcap.trans (original_margin A B)
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using endpt

def AllFiveLarge : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,(heightRadical A B:ℝ)^14<numberLog (oldForm i A B)) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) → target A B

/-- What survives both the ten old tests and all five new Pell systems. -/
theorem original_iff_all_five_large (units : PublishedCorollary72) (pell : PublishedPell312)
    (regulator : RegulatorBound) (disc : BiquadraticDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ AllFiveLarge := by
  classical
  constructor
  · exact fun full A B cop off _ _=>full A B cop off
  · intro remain
    apply (original_iff_exact_least units).mpr
    intro A B cop off fail
    by_cases test : ∃ i,numberLog (oldForm i A B)≤(heightRadical A B:ℝ)^14
    · obtain ⟨i,hi⟩:=test
      exact contact_sector pell regulator disc off i hi
    · exact remain A B cop off (fun i=>lt_of_not_ge (fun hi=>test ⟨i,hi⟩)) fail

end
end Sun28.HeightFibres
#print axioms Sun28.HeightFibres.every_contact_height
#print axioms Sun28.HeightFibres.contact_sector
#print axioms Sun28.HeightFibres.original_iff_all_five_large
