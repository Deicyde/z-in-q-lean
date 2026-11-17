import LogBudget
import HeightArithmetic

namespace HeightSpecialization.Analytic
open IndependentIndices Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
variable {K : Type} [Field K] [LE K] [LT K] [LawfulOrderLT K] [IsLinearOrder K] [OrderedRing K]

def radius (sigma ps : List Nat) := product sigma*product ps
def sizeX (sigma ps : List Nat) (t : Nat) := 2^16*fixedPart sigma*(product ps*plusProduct ps)*t

/-- The non-CM geometric and modular inputs preceding (HD3). The bounds on the
isogeny factor use twice the Faltings-height inequality to clear its half. -/
structure ModularFibre (l : LogLaw K) (sigma ps : List Nat) (A : K) where
  t : Nat
  g : Nat
  gf : Nat
  d : Nat
  genusPos : 0<g
  degreePos : 0<d
  characters : CharacterData sigma ps t
  genus : 12*g≤sizeX sigma ps t
  degree : d≤2304*radius sigma ps
  formPos : 0<gf
  cyclotomicDegree : ∀e,t=2^(e+1) → 2^e≤gf
  J : K
  U : K
  belyi : J≤((13000000*g*(sizeX sigma ps t)^5:Nat):K)
  isogeny : (gf:K)*A+2*U≤2*J+2*variation l g d J
  bost : -((3*g:Nat):K)≤2*U

private theorem numerical_size {sigma ps : List Nat} {t : Nat} (tp : 0<t)
    (sp : ∀p∈sigma,0<p) (mp : ∀p∈ps,0<p) :
    65536≤sizeX sigma ps t ∧ radius sigma ps≤sizeX sigma ps t := by
  have fixedPos:=Nat.mul_pos (product_pos _ sp) (plus_pos sigma)
  have variablePos:=Nat.mul_pos (product_pos _ mp) (plus_pos ps)
  have productPos:=Nat.mul_pos (Nat.mul_pos fixedPos variablePos) tp
  have general:=Nat.mul_le_mul_left (2^16) productPos
  rw [Nat.mul_one] at general
  have scale : 1≤2^16*(plusProduct sigma)*(plusProduct ps)*t :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (plus_pos sigma)) (plus_pos ps)) tp
  have bound:=Nat.mul_le_mul_left (radius sigma ps) scale
  rw [Nat.mul_one] at bound
  unfold sizeX fixedPart radius at *
  constructor
  · exact Nat.le_trans general (by apply Nat.le_of_eq;ac_rfl)
  · exact Nat.le_trans bound (by apply Nat.le_of_eq;ac_rfl)

private theorem scale_identity (sigma ps : List Nat) (a t : Nat) :
    t*hd3 a sigma ps t=a*(sizeX sigma ps t)^6 := by
  unfold hd3 sizeX
  simp only [Nat.mul_pow]
  rw [show t^6=t^5*t from Nat.pow_succ t 5]
  ac_rfl

theorem ModularFibre.height_bound {l : LogLaw K} {sigma ps : List Nat} {A : K}
    (f : ModularFibre l sigma ps A) (sp : ∀p∈sigma,0<p) (mp : ∀p∈ps,0<p) :
    A≤((hd3 4333334 sigma ps f.t:Nat):K) := by
  obtain ⟨big,scale⟩:=numerical_size f.characters.orderPos sp mp
  have d:=Nat.le_trans f.degree (Nat.mul_le_mul_left 2304 scale)
  have result:=modular_height l f.g f.d f.gf f.t _ f.genus f.genusPos f.degreePos d big
      (character_multiplicity f.characters f.formPos f.cyclotomicDegree) A f.J f.U f.belyi f.isogeny f.bost
  apply Classical.byContradiction
  intro bad
  have lt : ((hd3 4333334 sigma ps f.t:Nat):K)<A := by grind
  have clash:=OrderedRing.mul_lt_mul_of_pos_left lt (OrderedRing.pos_natCast_of_pos _ f.characters.orderPos)
  rw [←Semiring.natCast_mul,scale_identity] at clash
  grind

/-- CM uses the selected source's stable height bound. The complementary branch
supplies the Jacobian/isogeny estimates and character values of its modular fibre. -/
def FibreInput (l : LogLaw K) (sigma ps : List Nat) (A : K) :=
  A≤((854*radius sigma ps:Nat):K) ∨ Nonempty (ModularFibre l sigma ps A)

private theorem height_cap {h A : K} {N B : Nat} (G : h≤2*bigger 0 A+128)
    (f : A≤(B:K)) (bound : 2*B+128≤N) : h≤(N:K) := by
  have mx:=bigger_le (x:=(0:K)) OrderedRing.natCast_nonneg f
  have n:=OrderedRing.natCast_le_natCast_of_le (R:=K) _ _ bound
  simp only [Semiring.natCast_add,Semiring.natCast_mul] at n
  grind

private theorem support_pos {ps : List Nat} (prime : ∀p∈ps,IsContactPrime p) : ∀p∈support ps,0<p := by
  intro p m
  have h:=(prime p ((mem_support ..).mp m)).1
  omega

/-- Generic exponent-17 estimate with the manuscript's unconditioned character factor. -/
theorem analytic_height17 (l : LogLaw K) (sigma ps : List Nat) (h A : K)
    (sp : ∀p∈sigma,0<p) (prime : ∀p∈ps,IsContactPrime p)
    (G : h≤2*bigger 0 A+128) (input : FibreInput l sigma (support ps) A) :
    h≤(((coefficient 4333334 sigma ((cap sigma)^5)+128)*(radical ps)^17:Nat):K) := by
  rcases input with cm|pack
  · apply height_cap G cm
    rw [←distinct_product ps prime]
    exact cm_majorant _ _ (by decide) (Nat.pow_pos (Nat.pow_pos (by decide))) sp (support_pos prime)
  · let f:=Classical.choice pack
    exact height_cap G (f.height_bound sp (support_pos prime)) (noncm_bound _ _ prime f.characters)

theorem analytic_nonempty (l : LogLaw K) (sigma ps : List Nat) (h A : K) {r u : Nat}
    (sp : ∀p∈sigma,0<p) (prime : ∀p∈ps,IsContactPrime p) (member : ∃p,p∈ps)
    (r2 : 2≤r) (pMin : ∀p∈ps,r≤p) (u2 : 2≤u) (ordinary : (cap sigma)^5*(r+1)^6≤u*r^11)
    (G : h≤2*bigger 0 A+128) (input : FibreInput l sigma (support ps) A) :
    h≤(((coefficient 4333334 sigma u+128)*(radical ps)^17:Nat):K) := by
  rcases input with cm|pack
  · apply height_cap G cm
    rw [←distinct_product ps prime]
    exact cm_majorant _ _ (by decide) (by omega) sp (support_pos prime)
  · let f:=Classical.choice pack
    exact height_cap G (f.height_bound sp (support_pos prime))
       (nonempty_bound _ _ prime member r2 pMin u2 ordinary f.characters)

/-- The bounded finite test is a certificate that all primes below r belong to sigma. -/
def primesBelow (sigma : List Nat) (r : Nat) : Prop := ∀p : Fin r,1<p.val →
    (∀d : Fin r,d.val∣p.val → d.val=1 ∨ d.val=p.val) → p.val∈sigma
instance (sigma : List Nat) (r : Nat) : Decidable (primesBelow sigma r) := by unfold primesBelow;infer_instance

theorem exact_cutoffs : primesBelow scalarSet 11 ∧ primesBelow detectorSet 19 := by decide +kernel

theorem minimal_prime {sigma : List Nat} {r p : Nat} (low : primesBelow sigma r)
    (prime : IsContactPrime p) (away : p∉sigma) : r≤p := by
  apply Classical.byContradiction
  intro bad
  exact away (low ⟨p,by omega⟩ prime.1 (fun d hd=>prime.2 d.val hd))

def branchFactor (ps : List Nat) (nonempty : Nat) := if ps=[] then 16^5 else nonempty

theorem optimal_integer_costs : 10*11^11 < 16^5*12^6 ∧ 257^11 < 256^5*258^6 ∧ 16^5=1048576 := by decide

private theorem selected_bound (l : LogLaw K) (sigma ps : List Nat) (h A : K) {r u : Nat}
    (sp : ∀p∈sigma,0<p) (cap16 : cap sigma=16) (low : primesBelow sigma r) (r2 : 2≤r)
    (u2 : 2≤u) (factor : (cap sigma)^5*(r+1)^6≤u*r^11)
    (prime : ∀p∈ps,IsContactPrime p) (away : ∀p∈ps,p∉sigma)
    (G : h≤2*bigger 0 A+128) (input : FibreInput l sigma (support ps) A) :
    h≤(((coefficient 4333334 sigma (branchFactor ps u)+128)*(radical ps)^17:Nat):K) := by
  by_cases empty : ps=[]
  · rw [branchFactor,if_pos empty,←cap16]
    exact analytic_height17 l sigma ps h A sp prime G input
  · rw [branchFactor,if_neg empty]
    have member : ∃p,p∈ps := by cases ps with | nil => contradiction | cons p ps => exact ⟨p,by simp⟩
    exact analytic_nonempty l sigma ps h A sp prime member r2
        (fun p m=>minimal_prime low (prime p m) (away p m)) u2 factor G input

theorem scalar_height17 (l : LogLaw K) (ps : List Nat) (h A : K)
    (prime : ∀p∈ps,IsContactPrime p) (away : ∀p∈ps,p∉scalarSet)
    (G : h≤2*bigger 0 A+128) (input : FibreInput l scalarSet (support ps) A) :
    h≤(((coefficient 4333334 scalarSet (branchFactor ps 11)+128)*(radical ps)^17:Nat):K) :=
  selected_bound l scalarSet ps h A (by simp [scalarSet]) exact_caps.1 exact_cutoffs.1
    (by decide) (by decide) fixed_costs.2 prime away G input

theorem detector_height17 (l : LogLaw K) (ps : List Nat) (h A : K)
    (prime : ∀p∈ps,IsContactPrime p) (away : ∀p∈ps,p∉detectorSet)
    (G : h≤2*bigger 0 A+128) (input : FibreInput l detectorSet (support ps) A) :
    h≤(((coefficient 4333334 detectorSet (branchFactor ps 2)+128)*(radical ps)^17:Nat):K) :=
  selected_bound l detectorSet ps h A (by simp [detectorSet]) exact_caps.2 exact_cutoffs.2
    (by decide) (by decide) fixed_costs.1 prime away G input

private theorem inherited_constant {sigma ps : List Nat} {h : K} {u : Nat}
    (low : u≤16^5) (c : coefficient (2^23) sigma (16^5)+128=HeightClosure.constant sigma)
    (height : h≤(((coefficient 4333334 sigma (branchFactor ps u)+128)*(radical ps)^17:Nat):K)) :
    h≤((HeightClosure.constant sigma*(radical ps)^17:Nat):K) := by
  have cap : branchFactor ps u≤16^5 := by unfold branchFactor;split <;> omega
  have scale:=Nat.mul_le_mul_right ((2^16*fixedPart sigma)^6) (by decide : 2*4333334≤2*2^23)
  have bound:=Nat.mul_le_mul_right ((radical ps)^17) (Nat.add_le_add_right (Nat.mul_le_mul scale cap) 128)
  change (coefficient 4333334 sigma (branchFactor ps u)+128)*(radical ps)^17≤
    (coefficient (2^23) sigma (16^5)+128)*(radical ps)^17 at bound
  rw [c] at bound
  exact Std.le_trans height (OrderedRing.natCast_le_natCast_of_le _ _ bound)

theorem scalar_manuscript_constant (l : LogLaw K) (ps : List Nat) (h A : K)
    (prime : ∀p∈ps,IsContactPrime p) (away : ∀p∈ps,p∉scalarSet)
    (G : h≤2*bigger 0 A+128) (input : FibreInput l scalarSet (support ps) A) :
    h≤((HeightClosure.constant scalarSet*(radical ps)^17:Nat):K) :=
  inherited_constant (by decide : 11≤16^5) (by simpa only [exact_caps.1] using exact_constants.1)
    (scalar_height17 l ps h A prime away G input)

theorem detector_manuscript_constant (l : LogLaw K) (ps : List Nat) (h A : K)
    (prime : ∀p∈ps,IsContactPrime p) (away : ∀p∈ps,p∉detectorSet)
    (G : h≤2*bigger 0 A+128) (input : FibreInput l detectorSet (support ps) A) :
    h≤((HeightClosure.constant detectorSet*(radical ps)^17:Nat):K) :=
  inherited_constant (by decide : 2≤16^5) (by simpa only [exact_caps.2] using exact_constants.2)
    (detector_height17 l ps h A prime away G input)

end HeightSpecialization.Analytic
