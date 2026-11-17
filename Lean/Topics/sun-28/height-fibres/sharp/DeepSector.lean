import SharpPell

/-! Only large logarithms at all five marked points can remain after the
simultaneous Pell and minimal-conductor estimates. -/
namespace Sun28.HeightFibres.Sharp
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors ZInQ.RouteK
open private leftRow midRow rightRow mult delta₁ delta₂ catalogue linear_log equation_rows denominator_recovery from FivePencils
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 1500

theorem centered_estimate (pell : PublishedPell312) (regulator : Regulator35)
    (disc : ConductorDiscriminants) {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5) :
    let T:ℝ:=heightRadical A B
    pairLogHeight A B≤2^175*T^2*(ell T)^7+2^165*T*(ell T)^4*(numberLog (oldForm i A B)+32) := by
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
  have z1:1≤Z:=by dsimp [Z];linarith only [nonneg_numberLog fn]
  let S:=support A B
  have pr (p : ℕ) (hp:p∈S):p.Prime:=support_primes hp
  have cap : (primeProduct S:ℝ)=T:=congrArg (fun m:ℕ=>(m:ℝ)) (product_support A B)
  have gs (j:Fin 3) (r:Fin 5) : (G j r).natAbs.primeFactors⊆S:=scaled_support off i j r
  have est : numberLog a≤2^170*T^2*(ell T)^7+2^160*T*(ell T)^4*Z := by
    apply integral_pell pell regulator disc pr (a:=a) (b:=b) (c:=c) t cap
      (le_trans (by norm_num : (0:ℝ)≤1) z1) (gn 0 l) (gn 1 m) (gn 2 n)
      (gs 0 l) (gs 1 m) (gs 2 n) (scale 0 l) (scale 1 m) (scale 2 n)
      (mul_ne_zero nd fn) (mul_ne_zero ne fn) diff right₁ right₂
    · dsimp [G];linear_combination row.1
    · dsimp [G];linear_combination row.2
  have ga : numberLog (oldForm l A B)=numberLog (kernel l A B)+2*numberLog a := by
    rw [ea,pow_two,log_mul_int (live l) (mul_ne_zero na na),log_mul_int na na];ring
  have lg : numberLog (kernel l A B)≤T := (Real.log_le_sub_one_of_pos
    (by exact_mod_cast Int.natAbs_pos.mpr (live l) : 0<((kernel l A B).natAbs:ℝ))).trans
      (by have e:((kernel l A B).natAbs:ℝ)≤T:=Nat.cast_le.mpr (kernel_bound off l);linarith)
  let E:=ell T
  let V:=T^2*E^7
  let W:=T*E^4
  change numberLog a≤2^170*T^2*E^7+2^160*T*E^4*Z at est
  rw [show (2:ℝ)^170*T^2*E^7=2^170*V by dsimp [V];ring,
    show (2:ℝ)^160*T*E^4*Z=2^160*(W*Z) by dsimp [W];ring] at est
  have eo:1≤E:=by dsimp [E,ell];linarith [Real.log_nonneg t]
  have base : T≤V:=by
    calc
      _ ≤ T^2:=by simpa using pow_le_pow_right₀ t (by decide : 1≤2)
      _ ≤ T^2*E^7:=by simpa only [mul_one] using
           mul_le_mul_of_nonneg_left (one_le_pow₀ eo (n:=7)) (sq_nonneg T)
  have v1:1≤V:=t.trans base
  have w1:1≤W:=one_le_mul_of_one_le_of_one_le t (one_le_pow₀ eo)
  have zz:Z≤W*Z:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right w1 (le_trans (by norm_num) z1)
  let X:ℝ:=2^173*V+2^163*(W*Z)
  have lhs:numberLog (oldForm l A B)≤X:=by dsimp [X];linarith only [ga,lg,est,base,v1,zz,z1]
  have rhs:numberLog f≤X:=by
    have nz : numberLog f≤Z:=by dsimp [Z];linarith
    dsimp [X];linarith only [nz,zz,v1,z1]
  have data:=denominator_recovery off i lhs rhs
  change pairLogHeight A B≤X+33 at data
  change pairLogHeight A B≤2^175*T^2*E^7+2^165*T*E^4*Z
  rw [show (2:ℝ)^175*T^2*E^7=2^175*V by dsimp [V];ring,
      show (2:ℝ)^165*T*E^4*Z=2^165*(W*Z) by dsimp [W];ring]
  dsimp [X] at data
  linarith only [data,v1,zz,z1]

/-- The factor 625 allows the simpler pure-power sector without any change
in the published coefficient. -/
def small (T F : ℝ) := (ell T)^4*F≤625*T^23

theorem contact_deep (pell : PublishedPell312) (regulator : Regulator35)
    (disc : ConductorDiscriminants) {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5)
    (test : small (heightRadical A B) (numberLog (oldForm i A B))) : target A B := by
  let T:ℝ:=heightRadical A B
  let E:=ell T
  let F:=numberLog (oldForm i A B)
  have t:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have tp:0≤T:=by linarith
  have eo:1≤E:=by dsimp [E,ell];linarith [Real.log_nonneg t]
  have ep:0≤E:=by linarith
  have eT:E≤T:=by dsimp [E,ell];linarith only [Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) t)]
  have A1 : T^2*E^7≤T^24:=calc
    _ ≤ T^2*T^7:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ep eT _) (sq_nonneg T)
    _ = T^9:=by ring
    _ ≤ _:=pow_le_pow_right₀ t (by decide)
  have A2 : T*E^4≤T^24:=calc
    _ ≤ T*T^4:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ep eT _) tp
    _ = T^5:=by ring
    _ ≤ _:=pow_le_pow_right₀ t (by decide)
  change E^4*F≤625*T^23 at test
  have m:=mul_le_mul_of_nonneg_left test tp
  have pr : T*E^4*F≤625*T^24:=by
    calc
      _ = T*(E^4*F):=by ring
      _ ≤ _:=m
      _ = _:=by ring
  have pp:=pow_nonneg tp 24
  have H:=centered_estimate pell regulator disc off i
  change pairLogHeight A B≤2^175*T^2*E^7+2^165*T*E^4*(F+32) at H
  rw [show (2:ℝ)^175*T^2*E^7=2^175*(T^2*E^7) by ring,
    show (2:ℝ)^165*T*E^4*(F+32)=2^165*(T*E^4*F)+32*2^165*(T*E^4) by ring] at H
  have cap : pairLogHeight A B≤2^175*T^24+657*2^165*T^24 := by linarith only [H,A1,A2,pr]
  have C:(2:ℝ)^175+657*2^165≤2^200:=by norm_num
  have cmp : pairLogHeight A B≤2^810*T^24 := calc
    _ ≤ _ := cap
    _ = ((2:ℝ)^175+657*2^165)*T^24:=by ring
    _ ≤ (2:ℝ)^200*T^24:=mul_le_mul_of_nonneg_right C pp
    _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by decide)) pp
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using cmp.trans (original_margin A B)

theorem power22 (pell : PublishedPell312) (regulator : Regulator35)
    (disc : ConductorDiscriminants) {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5)
    (smallForm : numberLog (oldForm i A B)≤(heightRadical A B:ℝ)^22) : target A B := by
  let T:ℝ:=heightRadical A B
  have one:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  apply contact_deep pell regulator disc off i
  unfold small
  calc
    _ ≤ (625*T)*T^22:=mul_le_mul (ell_four one) smallForm
      (nonneg_numberLog (off i)) (by dsimp [T];positivity)
    _ = _:=by ring

def Deep : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,625*(heightRadical A B:ℝ)^23<(ell (heightRadical A B))^4*numberLog (oldForm i A B)) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) → target A B

theorem original_iff_deep (units : PublishedCorollary72) (pell : PublishedPell312)
    (regulator : Regulator35) (disc : ConductorDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ Deep := by
  classical
  constructor
  · exact fun full A B cop off _ _=>full A B cop off
  · intro survive;apply (original_iff_exact_least units).mpr
    intro A B cop off bad
    by_cases covered:∃ i,small (heightRadical A B) (numberLog (oldForm i A B))
    · obtain ⟨i,test⟩:=covered
      exact contact_deep pell regulator disc off i test
    · exact survive A B cop off (fun i=>lt_of_not_ge (fun test=>covered ⟨i,test⟩)) bad

end
end Sun28.HeightFibres.Sharp
#print axioms Sun28.HeightFibres.Sharp.centered_estimate
#print axioms Sun28.HeightFibres.Sharp.contact_deep
#print axioms Sun28.HeightFibres.Sharp.power22
#print axioms Sun28.HeightFibres.Sharp.original_iff_deep
