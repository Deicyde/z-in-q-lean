import RationalPade
import ChartSupport
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent Triangular Triangular.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

def PPair.support (k : PPair) := [k.xslot,k.xslot+1,k.xslot+2,k.xslot+3]

theorem pair_support_visible (k : PPair) : ∀ i∈k.support, visible i=true := by
  have h : k.support.all visible=true := by cases k <;> decide
  exact List.all_eq_true.mp h

private theorem pair_support (k : PPair) :
    reads (k.support++[k.slot,k.slot+1]).contains k.f=true ∧ reads (k.support++[k.slot,k.slot+1]).contains k.g=true := by cases k <;> decide

theorem blank_agree (k : PPair) {x y : Assignment} (h : ∀ i∈k.support,x i=y i) :
    value (k.blank x) k.f=value (k.blank y) k.f ∧ value (k.blank x) k.g=value (k.blank y) k.g := by
  have agree (i : Nat) (ok : (k.support++[k.slot,k.slot+1]).contains i=true) : k.blank x i=k.blank y i := by
    by_cases a : i=k.slot <;> by_cases b : i=k.slot+1 <;> simp [PPair.blank,put,a,b]
    exact h i (by simpa [a,b] using ok)
  exact ⟨reads_supported (pair_support k).1 _ _ agree,reads_supported (pair_support k).2 _ _ agree⟩

private theorem ab_agree (k : PPair) {x y : Assignment} (h : ∀ i∈k.support,x i=y i) :
    k.A x=k.A y ∧ k.B x=k.B y := by
  have a := h k.xslot (by simp [PPair.support]);have b := h (k.xslot+1) (by simp [PPair.support])
  simp only [PPair.A,PPair.B,PPair.w0,PPair.w1,a,b,and_self]

theorem uv_agree (k : PPair) {x y : Assignment} (h : ∀ i∈k.support,x i=y i) : k.U x=k.U y ∧ k.V x=k.V y := by
  obtain ⟨f,g⟩ := blank_agree k h;obtain ⟨a,b⟩ := ab_agree k h
  simp only [PPair.U,PPair.V,PPair.det,f,g,a,b,and_self]

private theorem cram (k : PPair) (x : Assignment) (u v : Rat) :
    (value (k.blank x) k.f+k.A x*u+2*k.B x*v=0 ∧ value (k.blank x) k.g+k.B x*u+k.A x*v=0) ↔
      k.U x=u ∧ k.V x=v := by
  let a:=k.A x;let b:=k.B x;let f:=value (k.blank x) k.f;let g:=value (k.blank x) k.g
  have nz := pair_det_ne k x
  have cu : k.U x*k.det x=2*b*g-a*f := Rat.div_mul_cancel nz
  have cv : k.V x*k.det x=b*f-a*g := Rat.div_mul_cancel nz
  change (f+a*u+2*b*v=0 ∧ g+b*u+a*v=0) ↔ _
  have diag : k.det x=a*a-(2*b)*b := rfl
  constructor
  · rintro ⟨left,right⟩
    have equalU : k.U x*k.det x=u*k.det x := by rw [cu,diag];grobner
    have equalV : k.V x*k.det x=v*k.det x := by rw [cv,diag];grobner
    exact ⟨by grind,by grind⟩
  · rintro ⟨uEq,vEq⟩
    rw [uEq] at cu;rw [vEq] at cv
    have z₁ : (f+a*u+2*b*v)*k.det x=0 := by rw [diag] at cu cv ⊢;grobner
    have z₂ : (g+b*u+a*v)*k.det x=0 := by rw [diag] at cu cv ⊢;grobner
    exact ⟨(Rat.mul_eq_zero.mp z₁).resolve_right nz,(Rat.mul_eq_zero.mp z₂).resolve_right nz⟩

theorem pade_iff (g : Bool) (k : PPair) (z : Assignment) (hs : pivotOK g z) :
    (value z k.f=0 ∧ value z k.g=0) ↔ k.U z=z k.slot ∧ k.V z=z (k.slot+1) := by
  rw [pade_f g k z hs,pade_g g k z hs]; exact cram ..

theorem fill_U (k : PPair) (z : Assignment) : fillPairs z k.slot=k.U z := by cases k <;> rfl
theorem fill_V (k : PPair) (z : Assignment) : fillPairs z (k.slot+1)=k.V z := by cases k <;> rfl

theorem point_pade (g : Bool) (y : Fin 130→Rat) (k : PPair) :
    value (chartPoint g y) k.f=0 ∧ value (chartPoint g y) k.g=0 := by
  apply (pade_iff g k _ (point_pivots g y)).mpr
  have coords (i : Nat) (hi : i∈k.support) : chartPoint g y i=middle g y i := by
    have v := pair_support_visible k i hi
    exact fillPairs_keep _ (by simp [visible,apart] at v;exact v.2)
  obtain ⟨u,v⟩ := uv_agree k coords
  exact ⟨u.trans (fill_U k _).symm,v.trans (fill_V k _).symm⟩
end PhysicalProjection
