import SpecializedProjection

namespace Sun28.ConeCount
open Finset Sun28.QuadricSieve Sun28.ConeSieve
noncomputable section
open scoped Classical

abbrev Point (R : Type*) := Coordinates R
abbrev Classes := (q : ℕ) → Finset (Point (ZMod q))

def normalized (B : ℕ) (x : Point ℤ) : Point ℝ :=
  ((x.1.1/B,x.1.2/B),(x.2.1.1/B,x.2.1.2/B),x.2.2/B)

def cube (r : ℕ) : Finset (Point ℤ) :=
  let I:=interval r
  ((I ×ˢ I) ×ˢ (I ×ˢ I) ×ˢ I)

def coneBox (κ : ℤ) (R B : ℕ) := (cube (R*B)).filter (onCone κ)

def good (κ : ℤ) (q : ℕ) : Prop := q.Prime ∧ q≠2 ∧ (κ:ZMod q)≠0

def primitive (κ : ℤ) (q : ℕ) [NeZero q] : Finset (Point (ZMod q)) :=
  univ.filter fun x=>onCone (κ:ZMod q) x ∧ x≠0

def accepts (s : Finset ℕ) (V : Classes) (x : Point ℤ) : Prop := ∀ q∈s,reduction q x∈V q

def count (κ : ℤ) (R B : ℕ) (ψ : Point ℝ→ℝ) (s : Finset ℕ) (V : Classes) : ℝ :=
  ∑ x∈(coneBox κ R B).filter (accepts s V), ψ (normalized B x)

def dilate (q : ℕ) (x : Point ℤ) : Point ℤ :=
  ((q*x.1.1,q*x.1.2),(q*x.2.1.1,q*x.2.1.2),q*x.2.2)

theorem mem_cube {r : ℕ} (x : Point ℤ) : x∈cube r ↔
    |x.1.1|≤(r:ℤ) ∧ |x.1.2|≤(r:ℤ) ∧ |x.2.1.1|≤(r:ℤ) ∧ |x.2.1.2|≤(r:ℤ) ∧ |x.2.2|≤(r:ℤ) := by
  simp only [cube,interval,mem_product,mem_Icc,abs_le]
  tauto

private theorem mul_window (q r : ℕ) (pos : 0<q) (a : ℤ) :
    |(q:ℤ)*a|≤((q*r:ℕ):ℤ) ↔ |a|≤r := by
  rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Nat.cast_mul]
  exact mul_le_mul_iff_right₀ (by exact_mod_cast pos)

theorem in_dilated_box {κ : ℤ} {q : ℕ} (pos : 0<q) (R B : ℕ) (x : Point ℤ) :
    dilate q x∈coneBox κ R (q*B) ↔ x∈coneBox κ R B := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩,v⟩
  have qp : (q:ℤ)≠0 := by exact_mod_cast pos.ne'
  have scale (a b c d v : ℤ) :
      (q*a)^2+(q*b)^2-(q*c)^2-(q*d)^2=κ*(q*v)^2 ↔ a^2+b^2-c^2-d^2=κ*v^2 := by
    rw [show (q*a)^2+(q*b)^2-(q*c)^2-(q*d)^2=(q:ℤ)^2*(a^2+b^2-c^2-d^2) by ring,
      show κ*(q*v)^2=(q:ℤ)^2*(κ*v^2) by ring]
    exact mul_right_inj' (pow_ne_zero 2 qp)
  simp only [coneBox,mem_filter,mem_cube,onCone,dilate]
  rw [show R*(q*B)=q*(R*B) by ring]
  simp only [mul_window q _ pos,scale]

theorem scaled_dilate {q : ℕ} (pos : 0<q) (B : ℕ) (x : Point ℤ) :
    normalized (q*B) (dilate q x)=normalized B x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩,v⟩
  have nz : (q:ℝ)≠0 := by exact_mod_cast pos.ne'
  have h (x:ℤ) : (((q:ℤ)*x : ℤ):ℝ)/((q*B:ℕ):ℝ)=(x:ℝ)/B := by
    push_cast
    exact mul_div_mul_left _ _ nz
  simp only [normalized,dilate,h]

theorem reduction_zero {q : ℕ} (x : Point ℤ) : reduction q x=0 ↔ ∃ y : Point ℤ,x=dilate q y := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩,v⟩
  have zero (x : ℤ) : (x:ZMod q)=0 ↔ (q:ℤ)∣x := ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  constructor
  · intro e
    have ea := congrArg (fun t : Point (ZMod q)=>t.1.1) e
    have eb := congrArg (fun t : Point (ZMod q)=>t.1.2) e
    have ec := congrArg (fun t : Point (ZMod q)=>t.2.1.1) e
    have ed := congrArg (fun t : Point (ZMod q)=>t.2.1.2) e
    have ev := congrArg (fun t : Point (ZMod q)=>t.2.2) e
    obtain ⟨aa,ha⟩:=(zero a).mp ea
    obtain ⟨bb,hb⟩:=(zero b).mp eb
    obtain ⟨cc,hc⟩:=(zero c).mp ec
    obtain ⟨dd,hd⟩:=(zero d).mp ed
    obtain ⟨vv,hv⟩:=(zero v).mp ev
    exact ⟨((aa,bb),(cc,dd),vv),by simp [ha,hb,hc,hd,hv,dilate]⟩
  · rintro ⟨⟨⟨u,w⟩,⟨g,h⟩,j⟩,e⟩
    rw [e];simp [reduction,dilate]

end
end Sun28.ConeCount
#print axioms Sun28.ConeCount.mem_cube
#print axioms Sun28.ConeCount.in_dilated_box
#print axioms Sun28.ConeCount.scaled_dilate
#print axioms Sun28.ConeCount.reduction_zero
