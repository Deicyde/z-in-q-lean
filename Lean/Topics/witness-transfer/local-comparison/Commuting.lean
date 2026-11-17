import FiniteJet

namespace WitnessTransfer.FiniteJet
open Lean.Grind
attribute [local instance] Semiring.natCast

variable {R : Type} [CommRing R]

def coeff : (n : Nat) → J R n → Nat → R
  | 0, _, _ => 0
  | _+1, f, 0 => f.1
  | n+1, f, i+1 => coeff n f.2 i

theorem ext_coeff (n : Nat) {a b : J R n}
    (same : ∀ i, i<n → coeff n a i=coeff n b i) : a=b := by
  induction n with
  | zero => exact @Subsingleton.elim Unit inferInstance a b
  | succ n ih =>
    apply Prod.ext
    · exact same 0 (by omega)
    · exact ih (fun i h => same (i+1) (by omega))

theorem coeff_plus (n) (a b : J R n) (i) :
    coeff n (plus n a b) i=coeff n a i+coeff n b i := by
  induction n generalizing i with
  | zero => simp only [coeff]; grobner
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih ..

theorem coeff_scale (n) (c : R) (a : J R n) (i) :
    coeff n (scale n c a) i=c*coeff n a i := by
  induction n generalizing i with
  | zero => simp only [coeff]; grobner
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih ..

theorem coeff_cut (n) (a : J R (n+1)) (i) (bound : i<n) :
    coeff n (cut n a) i=coeff (n+1) a i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih _ _ (by omega)

theorem times_leading (n) (a b : J R n) (i) (bound : i<n)
    (zero : ∀ j,j<i → coeff n b j=0) :
    coeff n (times n a b) i=coeff n a 0*coeff n b i := by
  induction i generalizing n with
  | zero => cases n with
    | zero => omega
    | succ n => rfl
  | succ i ih =>
    cases n with
    | zero => omega
    | succ n =>
      change coeff n (plus n (scale n a.1 b.2) (times n a.2 (cut n b))) i=_
      rw [coeff_plus,coeff_scale,ih n a.2 (cut n b) (by omega)
          (fun j hj => (coeff_cut n b j (by omega)).trans (zero j (by omega))),
        coeff_cut n b i (by omega),zero i (by omega)]
      change a.1*coeff n b.2 i+coeff n a.2 0*0=a.1*coeff n b.2 i
      grobner

theorem plug_leading (n) (u f : J R n) (i) (bound : i<n)
    (zero : ∀ j,j<i → coeff n f j=0) :
    coeff n (plug n u f) i=(coeff n u 0)^i*coeff n f i := by
  induction i using Nat.strongRecOn generalizing n with
  | ind i ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero => change f.1=u.1^0*f.1; rw [Semiring.pow_zero]; grobner
      | succ i =>
        have inner (a : Nat) (ha : a≤i) :
            coeff n (plug n (cut n u) f.2) a=(coeff n (cut n u) 0)^a*coeff n f.2 a :=
          ih a (by omega) n (cut n u) f.2 (by omega) (fun j hj => zero (j+1) (by omega))
        change coeff n (times n (cut n u) (plug n (cut n u) f.2)) i=_
        rw [times_leading n _ _ i (by omega) (by
          intro a ha
          rw [inner a (by omega), show coeff n f.2 a=0 from zero (a+1) (by omega)]
          grobner),inner i (by omega), coeff_cut n u 0 (by omega),Semiring.pow_succ]
        change u.1*(u.1^i*coeff n f.2 i)=(u.1^i*u.1)*coeff n f.2 i
        grobner

/-- Commutation is an identity on the two multipliers themselves. No condition on
the coefficients of the unknown error is required. -/
def commutes : (n : Nat) → J R n → J R n → Prop
  | 0, _, _ => True
  | n+1, m, d => cut n (times (n+1) d (plug (n+1) d m)) =
      cut n (times (n+1) m (plug (n+1) m d))

private theorem plug_comm (n) (m d f : J R n) (comm : commutes n m d) :
    plug n d (plug n m f)=plug n m (plug n d f) := by
  rw [double_substitution,double_substitution]
  cases n with
  | zero => rfl
  | succ n =>
    change (f.1,times n _ (plug n _ f.2)) = (f.1,times n _ (plug n _ f.2))
    rw [show cut n (times (n+1) d (plug (n+1) d m))=_ from comm]

theorem error_doubles (n) (m d f : J R n) (b : R) (comm : commutes n m d)
    (chart : plug n d f=scale n 2 f) :
    plug n d (plus n (plug n m f) (scale n (-b) f)) =
      scale n 2 (plus n (plug n m f) (scale n (-b) f)) := by
  have swap := plug_comm n m d f comm
  rw [plug_plus,swap,plug_scale,chart,plug_scale,scale_plus,scale_scale,scale_scale,
      CommSemiring.mul_comm (-b) (2:R)]

/-- Every commuting tangent-b multiplier is linear in the chart through degree n−1. -/
theorem linearizes {K : Type} [Field K] [IsCharP K 0]
    (n) (m d f : J K n) (b : K) (hd : coeff n d 0=2) (hb : coeff n m 0=b)
    (hf : coeff n f 0=0) (comm : commutes n m d)
    (chart : plug n d f=scale n 2 f) :
    plug n m f=scale n b f := by
  let e := plus n (plug n m f) (scale n (-b) f)
  have eql : plug n d e=scale n 2 e := error_doubles n m d f b comm chart
  have zero : ∀ i,i<n → coeff n e i=0 := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      intro hi
      by_cases low : i≤1
      · change coeff n (plus n _ _) i=0
        rw [coeff_plus,coeff_scale,plug_leading n m f i hi (by
          intro j h; have : j=0 := by omega
          exact this ▸ hf),hb]
        rcases (show i=0 ∨ i=1 from by omega) with h|h
        · rw [h,hf]; grobner
        · rw [h,Semiring.pow_one]; grobner
      · have h := congrArg (fun a => coeff n a i) eql
        change coeff n (plug n d e) i=coeff n (scale n 2 e) i at h
        rw [coeff_scale,plug_leading n d e i hi (fun j hj => ih j hj (by omega)),hd] at h
        have hn : 2^1 < (2:Nat)^i := Nat.pow_lt_pow_right (by decide) (by omega)
        have ne : (2:K)^i ≠ 2 := by
          intro same
          have eq : (((2:Nat)^i:Nat):K)=((2:Nat):K) := by
            rw [Semiring.natCast_pow,← Semiring.ofNat_eq_natCast (α:=K) 2]; exact same
          have en := (IsCharP.natCast_ext_iff (α:=K) 0).mp eq
          simp only [Nat.mod_zero] at en; omega
        have fac : ((2:K)^i-2)*coeff n e i=0 := by grobner
        exact (Field.of_mul_eq_zero fac).resolve_left (fun x => ne (by grobner))
  apply ext_coeff n
  intro i hi
  have h:=zero i hi
  change coeff n (plus n _ _) i=0 at h
  rw [coeff_plus,coeff_scale] at h
  rw [coeff_scale]
  grobner

#print axioms double_substitution
#print axioms error_doubles
#print axioms linearizes
end WitnessTransfer.FiniteJet
