module

public import Std

@[expose] public section

/-! The guarded pole branch and its binary quartic model over the rationals.
The parameters are homogeneous representatives for two points of the projective line.
The nonzero product in the surface equation will force both representatives to be valid. -/
namespace PoleSurface

def den (A u v : Rat) : Rat := v^2 + 3*A*u^2
def num (A u v : Rat) : Rat := v^2 - A*u^2
def quartic (A u v : Rat) : Rat := num A u v * den A u v

def Conic (A c p : Rat) : Prop := p^2 = A*(1-c)*(1+3*c)

def Guarded (A H : Rat) : Prop :=
  ∃ e z r₁ r₂ w : Rat, e*H*z*w = 1 ∧
    r₁^2 = A*(A-e)*(A+3*e) ∧
    r₂^2 = A*(A*z^2-e*H)*(A*z^2+3*(e*H))

def Surface (A H : Rat) : Prop :=
  H ≠ 0 ∧ ∃ u₁ v₁ u₂ v₂ W : Rat, W ≠ 0 ∧
    quartic A u₁ v₁ * quartic A u₂ v₂ = H*W^2

private def Coupled (A H : Rat) : Prop :=
  H ≠ 0 ∧ ∃ c₁ p₁ c₂ p₂ z : Rat, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ z ≠ 0 ∧
    Conic A c₁ p₁ ∧ Conic A c₂ p₂ ∧ H*c₁ = c₂*z^2

private theorem cancelRight {a b s : Rat} (hs : s ≠ 0) (h : a*s = b*s) : a=b := by
  grind

private theorem mulNonzero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 := by
  grind

private theorem sqNonzero {a : Rat} (ha : a ≠ 0) : a^2 ≠ 0 := by grind

/-- Clear the single scale shared by an abscissa and its ordinate. -/
private theorem scaled (A s c p e r : Rat) (hs : s ≠ 0)
    (hc : c*s=e) (hp : p*s=r) :
    Conic A c p ↔ r^2 = A*(s-e)*(s+3*e) := by
  subst e
  subst r
  unfold Conic
  have lhs : (p*s)^2 = p^2*s^2 := by grobner
  have rhs : A*(s-c*s)*(s+3*(c*s)) = (A*(1-c)*(1+3*c))*s^2 := by grobner
  rw [lhs,rhs]
  exact ⟨fun h => congrArg (fun b : Rat => b*s^2) h, cancelRight (sqNonzero hs)⟩

theorem chart_point (A u v : Rat) (hd : den A u v ≠ 0) :
    Conic A (num A u v / den A u v) (4*A*u*v / den A u v) := by
  apply (scaled A (den A u v) _ _ _ _ hd (Rat.div_mul_cancel hd) (Rat.div_mul_cancel hd)).2
  unfold den num
  grobner

/-- When 1+3c=0 the representative is (1,0); otherwise it is (p,A(1+3c)).
The point (c,p)=(1,0) is included in the second chart. -/
theorem chart_covers {A c p : Rat} (hA : A ≠ 0) (h : Conic A c p) :
    ∃ u v : Rat, den A u v ≠ 0 ∧ c * den A u v = num A u v ∧
      p * den A u v = 4*A*u*v := by
  unfold Conic at h
  by_cases he : 1+3*c=0
  · have hp : p=0 := by rw [he] at h; grind
    refine ⟨1, 0, ?_, ?_, ?_⟩ <;> simp only [den, num] <;> grind
  · let v := A*(1+3*c)
    have hd : den A p v = 4*A^2*(1+3*c) := by
      unfold den v
      rw [h]
      grobner
    have hn : num A p v = c*(4*A^2*(1+3*c)) := by
      unfold num v
      rw [h]
      grobner
    refine ⟨p,v,?_,?_,?_⟩
    · rw [hd]
      exact mulNonzero (mulNonzero (by decide) (sqNonzero hA)) he
    · rw [hn,hd]
    · rw [hd]
      unfold v
      grobner

theorem endpoints (A : Rat) (hA : A ≠ 0) :
    den A 0 1 ≠ 0 ∧ num A 0 1 / den A 0 1 = 1 ∧
    den A 1 0 ≠ 0 ∧ num A 1 0 / den A 1 0 = -1/3 := by
  have hd : den A 1 0 ≠ 0 := by unfold den; grind
  have h := Rat.div_mul_cancel (a := num A 1 0) hd
  have h0 : den A 0 1 = 1 := by unfold den; grobner
  have h1 : num A 0 1 = 1 := by unfold num; grobner
  refine ⟨by rw [h0]; decide, ?_, hd, ?_⟩
  · rw [h0,h1]
    simpa only [Rat.mul_one] using (Rat.div_mul_cancel (a := 1) (b := 1) (by decide))
  · apply cancelRight hd
    rw [h]
    unfold num den
    grobner

private theorem guarded_coupled (A H : Rat) (hA : A ≠ 0) :
    Guarded A H ↔ Coupled A H := by
  constructor
  · rintro ⟨e,z,r₁,r₂,w,guard,h₁,h₂⟩
    have he : e ≠ 0 := by intro hz; rw [hz] at guard; grind
    have hH : H ≠ 0 := by intro hz; rw [hz] at guard; grind
    have hz : z ≠ 0 := by intro h; rw [h] at guard; grind
    let s := A*z^2
    have hs : s ≠ 0 := mulNonzero hA (sqNonzero hz)
    let c₁ := e/A
    let c₂ := e*H/s
    have hc₁ : c₁*A=e := Rat.div_mul_cancel hA
    have hc₂ : c₂*s=e*H := Rat.div_mul_cancel hs
    refine ⟨hH,c₁,r₁/A,c₂,r₂/s,z,?_,?_,hz,?_,?_,?_⟩
    · intro h; rw [h, Rat.zero_mul] at hc₁; exact he hc₁.symm
    · intro h; rw [h, Rat.zero_mul] at hc₂; exact mulNonzero he hH hc₂.symm
    · exact (scaled A A _ _ _ _ hA hc₁ (Rat.div_mul_cancel hA)).2 h₁
    · exact (scaled A s _ _ _ _ hs hc₂ (Rat.div_mul_cancel hs)).2 h₂
    · apply cancelRight hA
      calc H*c₁*A = H*(c₁*A) := by grobner
           _ = e*H := by rw [hc₁]; grobner
           _ = c₂*s := hc₂.symm
           _ = c₂*z^2*A := by unfold s; grobner
  · rintro ⟨hH,c₁,p₁,c₂,p₂,z,hc₁,_,hz,h₁,h₂,link⟩
    let e := c₁*A
    let s := A*z^2
    have he : e ≠ 0 := mulNonzero hc₁ hA
    have hs : s ≠ 0 := mulNonzero hA (sqNonzero hz)
    have guard := Rat.mul_inv_cancel (e*H*z) (mulNonzero (mulNonzero he hH) hz)
    have hc₂ : c₂*s = e*H := by unfold e s; grobner
    exact ⟨e,z,p₁*A,p₂*s,(e*H*z)⁻¹,guard,
      (scaled A A _ _ _ _ hA rfl rfl).1 h₁,
      (scaled A s _ _ _ _ hs hc₂ rfl).1 h₂⟩

private theorem nonzeroFactors {a b : Rat} (h : a*b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by grind

private theorem divNonzero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a/b ≠ 0 := by
  intro h
  have eqn := Rat.div_mul_cancel (a := a) hb
  rw [h, Rat.zero_mul] at eqn
  exact ha eqn.symm

private theorem productInChart {A u₁ v₁ u₂ v₂ c₁ c₂ : Rat}
    (h₁ : c₁ * den A u₁ v₁ = num A u₁ v₁)
    (h₂ : c₂ * den A u₂ v₂ = num A u₂ v₂) :
    quartic A u₁ v₁ * quartic A u₂ v₂ =
      c₁*c₂*(den A u₁ v₁ * den A u₂ v₂)^2 := by
  unfold quartic
  rw [← h₁, ← h₂]
  grobner

/-- The equation for the two nonzero square-root witnesses is symmetric
    via z * W = a * k, where k is the product of chart denominators. -/
private theorem switchSquare {a b H k z W : Rat} (hz : z ≠ 0) (hW : W ≠ 0)
    (witness : z*W = a*k) : H*a = b*z^2 ↔ a*b*k^2 = H*W^2 := by
  constructor
  · intro link
    apply cancelRight (sqNonzero hz)
    calc a*b*k^2*z^2 = a*k^2*(b*z^2) := by grobner
         _ = H*(a*k)^2 := by rw [← link]; grobner
         _ = H*W^2*z^2 := by rw [← witness]; grobner
  · intro link
    apply cancelRight (sqNonzero hW)
    calc H*a*W^2 = a*(H*W^2) := by grobner
         _ = b*(a*k)^2 := by rw [← link]; grobner
         _ = b*z^2*W^2 := by rw [← witness]; grobner

private theorem coupled_surface (A H : Rat) (hA : A ≠ 0) :
    Coupled A H ↔ Surface A H := by
  constructor
  · rintro ⟨hH,c₁,p₁,c₂,p₂,z,hc₁,_,hz,h₁,h₂,link⟩
    obtain ⟨u₁,v₁,hd₁,hn₁,_⟩ := chart_covers hA h₁
    obtain ⟨u₂,v₂,hd₂,hn₂,_⟩ := chart_covers hA h₂
    let k := den A u₁ v₁ * den A u₂ v₂
    let W := c₁*k/z
    have hk : k ≠ 0 := mulNonzero hd₁ hd₂
    have hW : W ≠ 0 := divNonzero (mulNonzero hc₁ hk) hz
    have root : z*W = c₁*k := by rw [Rat.mul_comm]; exact Rat.div_mul_cancel hz
    refine ⟨hH,u₁,v₁,u₂,v₂,W,hW,?_⟩
    exact (productInChart hn₁ hn₂).trans ((switchSquare hz hW root).1 link)
  · rintro ⟨hH,u₁,v₁,u₂,v₂,W,hW,eqn⟩
    have nonzero : quartic A u₁ v₁ * quartic A u₂ v₂ ≠ 0 := by
      rw [eqn]; exact mulNonzero hH (sqNonzero hW)
    obtain ⟨hf₁,hf₂⟩ := nonzeroFactors nonzero
    obtain ⟨hn₁,hd₁⟩ := nonzeroFactors hf₁
    obtain ⟨hn₂,hd₂⟩ := nonzeroFactors hf₂
    let c₁ := num A u₁ v₁ / den A u₁ v₁
    let c₂ := num A u₂ v₂ / den A u₂ v₂
    let k := den A u₁ v₁ * den A u₂ v₂
    let z := c₁*k/W
    have hc₁ : c₁ ≠ 0 := divNonzero hn₁ hd₁
    have hc₂ : c₂ ≠ 0 := divNonzero hn₂ hd₂
    have hk : k ≠ 0 := mulNonzero hd₁ hd₂
    have hz : z ≠ 0 := divNonzero (mulNonzero hc₁ hk) hW
    have root : z*W = c₁*k := Rat.div_mul_cancel hW
    have prod := productInChart (Rat.div_mul_cancel (a := num A u₁ v₁) hd₁)
      (Rat.div_mul_cancel (a := num A u₂ v₂) hd₂)
    exact ⟨hH,c₁,_,c₂,_,z,hc₁,hc₂,hz,chart_point A u₁ v₁ hd₁,
      chart_point A u₂ v₂ hd₂,(switchSquare hz hW root).2 (prod.symm.trans eqn)⟩

/-- For every nonzero A and every H, the original five rational witnesses for
    the fixed branch exist exactly when the two binary quartic parameters and
    a nonzero W exist. H=0 is included; both sides are empty there. -/
theorem guarded_iff_surface (A H : Rat) (hA : A ≠ 0) :
    Guarded A H ↔ Surface A H :=
  (guarded_coupled A H hA).trans (coupled_surface A H hA)

/-- Specialization to the two coefficients determined by a fixed Boolean
    branch m and nonzero input B in V8. -/
theorem fixed_branch (m B : Rat) (hm : m ≠ 0) (hB : B ≠ 0) :
    Guarded (m*B) ((m*B)*(m*B-B^2)) ↔ Surface (m*B) ((m*B)*(m*B-B^2)) :=
  guarded_iff_surface _ _ (mulNonzero hm hB)

/-- A nonzero binary quartic value has a nonzero denominator and gives a
    nonzero homogeneous pair. Thus the existential coordinates represent
    projective-line points. -/
theorem valid_pair {A u v : Rat} (h : quartic A u v ≠ 0) :
    den A u v ≠ 0 ∧ (u ≠ 0 ∨ v ≠ 0) := by
  have hd := (nonzeroFactors h).2
  exact ⟨hd, by
    by_cases hu : u=0
    · right; intro hv; rw [hu,hv] at hd; unfold den at hd; grind
    · exact Or.inl hu⟩

/-- Rescaling representatives by t rescales the quartic by the fourth power. -/
theorem quartic_homogeneous (A t u v : Rat) :
    quartic A (t*u) (t*v) = t^4 * quartic A u v := by
  unfold quartic num den
  grobner

/-- Canonical rational projective-line points: (s,1) for a finite slope, or (1,0). -/
inductive ProjectiveLine where
  | finite (s : Rat)
  | infinity

def ProjectiveLine.coords : ProjectiveLine → Rat × Rat
  | .finite s => (s,1)
  | .infinity => (1,0)

def ProjectiveLine.value (t : ProjectiveLine) (A : Rat) : Rat :=
  quartic A t.coords.1 t.coords.2

private theorem normalizeRep {A u v : Rat} (valid : u ≠ 0 ∨ v ≠ 0) :
    ∃ (t : ProjectiveLine) (k : Rat), k ≠ 0 ∧ quartic A u v = k^4 * t.value A := by
  by_cases hv : v = 0
  · have hu : u ≠ 0 := valid.resolve_right (fun h => h hv)
    subst v
    refine ⟨.infinity,u,hu,?_⟩
    simpa only [ProjectiveLine.value, ProjectiveLine.coords, Rat.mul_one, Rat.mul_zero] using (quartic_homogeneous A u 1 0)
  · refine ⟨.finite (u/v),v,hv,?_⟩
    have huv : v*(u/v)=u := by rw [Rat.mul_comm]; exact Rat.div_mul_cancel hv
    simpa only [ProjectiveLine.value, ProjectiveLine.coords, huv, Rat.mul_one] using (quartic_homogeneous A v (u/v) 1)

def ProjectiveSurface (A H : Rat) : Prop :=
  H ≠ 0 ∧ ∃ (t₁ t₂ : ProjectiveLine) (W : Rat),
    W ≠ 0 ∧ t₁.value A * t₂.value A = H*W^2

theorem surface_iff_projective (A H : Rat) : Surface A H ↔ ProjectiveSurface A H := by
  constructor
  · rintro ⟨hH,u₁,v₁,u₂,v₂,W,hW,eqn⟩
    have nonzero : quartic A u₁ v₁ * quartic A u₂ v₂ ≠ 0 := by
      rw [eqn]; exact mulNonzero hH (sqNonzero hW)
    obtain ⟨hf₁,hf₂⟩ := nonzeroFactors nonzero
    obtain ⟨t₁,k₁,hk₁,eq₁⟩ := normalizeRep (A := A) (valid_pair hf₁).2
    obtain ⟨t₂,k₂,hk₂,eq₂⟩ := normalizeRep (A := A) (valid_pair hf₂).2
    let k := k₁^2*k₂^2
    have hk : k ≠ 0 := mulNonzero (sqNonzero hk₁) (sqNonzero hk₂)
    have scaledW : W/k*k=W := Rat.div_mul_cancel hk
    refine ⟨hH,t₁,t₂,W/k,divNonzero hW hk,?_⟩
    apply cancelRight (sqNonzero hk)
    calc t₁.value A*t₂.value A*k^2 =
            (k₁^4*t₁.value A)*(k₂^4*t₂.value A) := by unfold k; grobner
         _ = H*W^2 := by rw [← eq₁,← eq₂]; exact eqn
         _ = H*((W/k)*k)^2 := congrArg (fun x : Rat => H*x^2) scaledW.symm
         _ = H*(W/k)^2*k^2 := by grobner
  · rintro ⟨hH,t₁,t₂,W,hW,eqn⟩
    exact ⟨hH,t₁.coords.1,t₁.coords.2,t₂.coords.1,t₂.coords.2,W,hW,eqn⟩

/-- The exact guarded V8 branch with two parameters in P¹(Q), including infinity. -/
theorem fixed_branch_projective (m B : Rat) (hm : m ≠ 0) (hB : B ≠ 0) :
    Guarded (m*B) ((m*B)*(m*B-B^2)) ↔
      ProjectiveSurface (m*B) ((m*B)*(m*B-B^2)) :=
  (fixed_branch m B hm hB).trans (surface_iff_projective _ _)

end PoleSurface

#print axioms PoleSurface.fixed_branch_projective
