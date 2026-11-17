import MarkedCovers
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.PadicNumbers
import ZInQKernel.RouteK.Slots.Basic

namespace Sun28.SelmerRealization
open ZInQ.RouteK Sun28.SupportMatrix

noncomputable section

def twistCurve (l : ℕ) : WeierstrassCurve ℚ := ⟨0,2*(l:ℚ),0,-3*(l:ℚ)^2,0⟩
abbrev RationalPoint (l : ℕ) := (twistCurve l).toAffine.Point

/-- Local class in the order (x+3l,x-l). Homogeneous coordinates include
the four classes of the displayed rational two-torsion. -/
def Cover (K : Type*) [Field K] (l : ℕ) (a b : ℤ) : Prop :=
  ∃ X Y Z T : K, (X≠0 ∨ Y≠0 ∨ Z≠0 ∨ T≠0) ∧
    (a:K)*(b:K)*X^2-(b:K)*Y^2=(l:K)*T^2 ∧
    (a:K)*Z^2-(a:K)*(b:K)*X^2=3*(l:K)*T^2

def localClasses (l : ℕ) : Set (ℤ × ℤ) :=
  {ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ Cover ℝ l ab.1 ab.2 ∧
    ∀ (p : ℕ) [Fact p.Prime], Cover ℚ_[p] l ab.1 ab.2}

theorem rational_cover (l : ℕ) (b : ℤ) :
    Cover ℚ l b 1 ↔ MarkedCover (b:ℚ) (l:ℚ) := by
  simp only [Cover,MarkedCover,Int.cast_one,mul_one,one_mul,mul_sub]

/-- The customary exceptional-coordinate rule at the three roots, written
up to rational squares. For b=0 or a=0 a raw coordinate never occurs. -/
def raw (l : ℕ) : RationalPoint l → ℚ × ℚ
  | .zero => (1,1)
  | .some x _ _ => if x=0 then (3*l,-(l:ℚ)) else if x=(l:ℚ) then (l,1)
      else if x= -3*(l:ℚ) then (3,-(l:ℚ)) else (x+3*l,x-l)

def labels (l : ℕ) (P : RationalPoint l) : ℤ × ℤ :=
  (sqf (raw l P).1, sqf (raw l P).2)

private theorem affine_eq {l : ℕ} {x y : ℚ}
    (h : (twistCurve l).toAffine.Nonsingular x y) :
    y^2=x*(x-l)*(x+3*l) := by
  have eq := (WeierstrassCurve.Affine.equation_iff _ _).mp h.1
  simp [twistCurve,WeierstrassCurve.toAffine] at eq
  linear_combination eq

private theorem of_coordinates {l : ℕ} {x y : ℚ} (h : y^2=x*(x-l)*(x+3*l))
    (a b : ℤ) {v w : ℚ} (vn : v≠0) (wn : w≠0)
    (one : x+3*l=a*v^2) (two : x-l=b*w^2) (an : (a:ℚ)≠0) (bn : (b:ℚ)≠0) :
    Cover ℚ l a b := by
  let u := y/((a:ℚ)*b*v*w)
  have xu : x=(a:ℚ)*b*u^2 := by
    dsimp [u]
    field_simp [an,bn,vn,wn]
    rw [two,one] at h
    linear_combination -h
  use u,w,v,1
  exact ⟨Or.inr (Or.inr (Or.inr one_ne_zero)),by rw [←xu,←two];ring,
    by rw [←xu,←one];ring⟩

private theorem equivalent_cover {l : ℕ} {a b c e : ℤ} {r s : ℚ} (rn : r≠0) (sn : s≠0)
    (A : (c:ℚ)=(a:ℚ)*r^2) (B : (e:ℚ)=(b:ℚ)*s^2) (given : Cover ℚ l c e) :
    Cover ℚ l a b := by
  obtain ⟨X,Y,Z,T,h,h1,h2⟩:=given
  refine ⟨r*s*X,s*Y,r*Z,T,?_,?_,?_⟩
  · rcases h with h|h|h|h
    · exact Or.inl (mul_ne_zero (mul_ne_zero rn sn) h)
    · exact Or.inr (Or.inl (mul_ne_zero sn h))
    · exact Or.inr (Or.inr (Or.inl (mul_ne_zero rn h)))
    · exact Or.inr (Or.inr (Or.inr h))
  · rw [A,B] at h1
    linear_combination h1
  · rw [A,B] at h2
    linear_combination h2

private theorem primitive_cover {l : ℕ} (a b : ℤ) (an : (a:ℚ)≠0) (bn : (b:ℚ)≠0)
    (given : Cover ℚ l a b) : Cover ℚ l (sqf a) (sqf b) := by
  obtain ⟨_,r,rn,A⟩ := sqf_spec an
  obtain ⟨_,s,sn,B⟩ := sqf_spec bn
  exact equivalent_cover rn sn A B given

/-- All rational points, including infinity and points of order two, give
rational points on their explicitly normalized covering intersections. -/
theorem labels_cover {l : ℕ} (lp : 0<l) (P : RationalPoint l) :
    Cover ℚ l (labels l P).1 (labels l P).2 := by
  have ln : (l:ℚ)≠0 := by exact_mod_cast lp.ne'
  cases P with
  | zero =>
    change Cover ℚ l (sqf (1:ℚ)) (sqf (1:ℚ))
    apply primitive_cover 1 1 (by norm_num) (by norm_num)
    exact ⟨1,1,1,0,Or.inl one_ne_zero,by norm_num,by norm_num⟩
  | @some x y ns =>
    by_cases x0 : x=0
    · subst x
      simp only [labels,raw,↓reduceIte]
      have id : (3*(l:ℚ))=((3*(l:ℤ):ℤ):ℚ) := by push_cast;rfl
      have id2 : -(l:ℚ)=((-(l:ℤ):ℤ):ℚ) := by push_cast;rfl
      rw [id,id2]
      apply primitive_cover _ _ (by push_cast;exact mul_ne_zero (by norm_num) ln)
        (by push_cast;exact neg_ne_zero.mpr ln)
      exact ⟨0,1,1,1,Or.inr (Or.inl one_ne_zero),by push_cast;ring,by push_cast;ring⟩
    by_cases xl : x=(l:ℚ)
    · subst x
      simp only [labels,raw,x0,↓reduceIte]
      change Cover ℚ l (sqf ((l:ℤ):ℚ)) (sqf ((1:ℤ):ℚ))
      apply primitive_cover _ _ ln (by norm_num)
      exact ⟨1,0,2,1,Or.inl one_ne_zero,by push_cast;ring,by push_cast;ring⟩
    by_cases xm : x= -3*(l:ℚ)
    · subst x
      simp only [labels,raw,x0,xl,↓reduceIte]
      change Cover ℚ l (sqf ((3:ℤ):ℚ)) (sqf ((-(l:ℤ):ℤ):ℚ))
      apply primitive_cover _ _ (by norm_num) (by push_cast;exact neg_ne_zero.mpr ln)
      exact ⟨1,2,0,1,Or.inl one_ne_zero,by push_cast;ring,by push_cast;ring⟩
    simp only [labels,raw,x0,xl,xm,↓reduceIte]
    have un : x+3*(l:ℚ)≠0 := by intro h;apply xm;linarith
    have vn := sub_ne_zero.mpr xl
    obtain ⟨fu,u,hu,eu⟩ := sqf_spec un
    obtain ⟨fv,v,hv,ev⟩ := sqf_spec vn
    exact of_coordinates (affine_eq ns) _ _ hu hv eu ev (by exact_mod_cast fu.ne_zero)
      (by exact_mod_cast fv.ne_zero)

theorem cover_map {K : Type*} [Field K] [CharZero K] {l : ℕ} {a b : ℤ}
    (h : Cover ℚ l a b) : Cover K l a b := by
  obtain ⟨X,Y,Z,T,ok,one,two⟩ := h
  use (algebraMap ℚ K) X,(algebraMap ℚ K) Y,(algebraMap ℚ K) Z,(algebraMap ℚ K) T
  constructor
  · simpa only [ne_eq,map_eq_zero] using ok
  · constructor
    · simpa only [map_sub,map_mul,map_pow,map_natCast,map_intCast,map_ofNat] using
          congrArg (algebraMap ℚ K) one
    · simpa only [map_sub,map_mul,map_pow,map_natCast,map_intCast,map_ofNat] using
          congrArg (algebraMap ℚ K) two

theorem labels_local {l : ℕ} (lp : 0<l) (P : RationalPoint l) :
    labels l P ∈ localClasses l := by
  have nz (K : ℚ) (h : K≠0) := (sqf_spec h).1
  have ln : (l:ℚ)≠0 := by exact_mod_cast lp.ne'
  have raw_nonzero : (raw l P).1≠0 ∧ (raw l P).2≠0 := by
    cases P with
    | zero => exact ⟨one_ne_zero,one_ne_zero⟩
    | @some x y h =>
      simp only [raw]
      split
      · exact ⟨mul_ne_zero (by norm_num) ln,neg_ne_zero.mpr ln⟩
      split
      · exact ⟨ln,one_ne_zero⟩
      split
      · exact ⟨by norm_num,neg_ne_zero.mpr ln⟩
      rename_i h0 hl hm
      exact ⟨by dsimp;intro e;apply hm;linarith,sub_ne_zero.mpr hl⟩
  exact ⟨nz _ raw_nonzero.1,nz _ raw_nonzero.2,cover_map (labels_cover lp P),
    fun p _=>cover_map (labels_cover lp P)⟩

end
end Sun28.SelmerRealization
#print axioms Sun28.SelmerRealization.rational_cover
#print axioms Sun28.SelmerRealization.labels_cover
#print axioms Sun28.SelmerRealization.cover_map
#print axioms Sun28.SelmerRealization.labels_local
