import SieveA
import SieveB
import SieveC
import SieveD
import PrimeRows

namespace Sun28.FactorHeights
noncomputable section

def configurations : Fin 4 → Finset (ℤ×ℤ×ℤ) :=
  ![{(1,1,1)},{(2,1,1),(14,-35,7)},{(2,1,1)},{(2,1,1)}]

theorem five_configurations {x:ℚ} {i:Fin 4} (h:concentrated x i) :
    triples i x ∈ configurations i := by
  fin_cases i
  · exact remainingA h
  · exact remainingB h
  · exact remainingC h
  · exact remainingD h

def affineRow (i:Fin 4) (x:ℚ) : ℚ := (alpha i:ℚ)*x^2+(gamma i:ℚ)

theorem affine_factor (i:Fin 4) (x:ℚ) :
    ∃u:ℚ,u≠0 ∧ affineRow i x=(coeff i x:ℚ)*u^2 := by
  obtain ⟨_,u,un,e⟩:=ZInQ.RouteK.sqfInt_spec (row_ne x i)
  change row i x.num (x.den:ℤ)=coeff i x*u^2 at e
  have bn:(x.den:ℚ)≠0:=by exact_mod_cast x.den_nz
  have eq:(alpha i:ℚ)*(x.num:ℚ)^2+(gamma i:ℚ)*(x.den:ℚ)^2=(coeff i x:ℚ)*(u:ℚ)^2:=by
    exact_mod_cast e
  have id:(x.num:ℚ)=x*x.den:=(div_eq_iff bn).mp x.num_div_den
  rw [id] at eq
  refine ⟨u/x.den,div_ne_zero (by exact_mod_cast un) bn,?_⟩
  unfold affineRow
  field_simp
  linear_combination eq

def elliptic (m n X:ℚ):Prop:=∃Y:ℚ,Y≠0 ∧ Y^2=X*(X+m)*(X+n)

private theorem pairAB {x:ℚ} (nz:x≠0) (ac:coeff 0 x=2) (bc:coeff 1 x=1) :
    elliptic 4 6 (4*x^2) := by
  obtain ⟨u,un,eu⟩:=affine_factor 0 x
  obtain ⟨v,vn,ev⟩:=affine_factor 1 x
  rw [ac] at eu;rw [bc] at ev
  norm_num [affineRow,alpha,gamma] at eu ev
  refine ⟨8*x*u*v,by positivity,?_⟩
  calc
    (8*x*u*v)^2=32*x^2*(2*u^2)*v^2:=by ring
    _= _:=by rw [←eu,←ev];ring

private theorem pairBD {x:ℚ} (nz:x≠0) (bc:coeff 1 x=1) (dc:coeff 3 x=1) :
    elliptic 64 439 (64*x^2) := by
  obtain ⟨u,un,eu⟩:=affine_factor 1 x
  obtain ⟨v,vn,ev⟩:=affine_factor 3 x
  rw [bc] at eu;rw [dc] at ev
  norm_num [affineRow,alpha,gamma] at eu ev
  refine ⟨64*x*u*v,by positivity,?_⟩
  calc
    (64*x*u*v)^2=4096*x^2*u^2*v^2:=by ring
    _= _:=by rw [←eu,←ev];ring

def conics (x:ℚ) (k l m:ℤ):Prop :=
  ∃u v w:ℚ, u≠0 ∧ v≠0 ∧ w≠0 ∧ 2*x^2+3=k*u^2 ∧
    x^2-1199=l*v^2 ∧ 64*x^2+439=m*w^2

private theorem conicsOf {x:ℚ} {k l m:ℤ} (t:triples 1 x=(k,l,m)) : conics x k l m := by
  change (coeff 0 x,coeff 2 x,coeff 3 x)=(k,l,m) at t
  simp only [Prod.mk.injEq] at t
  obtain ⟨u,un,eu⟩:=affine_factor 0 x
  obtain ⟨v,vn,ev⟩:=affine_factor 2 x
  obtain ⟨w,wn,ew⟩:=affine_factor 3 x
  rw [t.1] at eu;rw [t.2.1] at ev;rw [t.2.2] at ew
  exact ⟨u,v,w,un,vn,wn,by simpa [affineRow,alpha,gamma] using eu,
    by simpa [affineRow,alpha,gamma,sub_eq_add_neg] using ev,by simpa [affineRow,alpha,gamma] using ew⟩

/-- The concentrated scalar sector maps either to one of two elliptic curves away
from its rational two-torsion or to one of two fixed three-conic systems. -/
theorem concentrated_alternatives {x:ℚ} (ne:x≠0) (hc:∃i,concentrated x i) :
    elliptic 4 6 (4*x^2) ∨ elliptic 64 439 (64*x^2) ∨ conics x 2 1 1 ∨ conics x 14 (-35) 7 := by
  obtain ⟨i,hi⟩:=hc
  fin_cases i
  · have h:=Finset.mem_singleton.mp (remainingA hi)
    change (coeff 1 x,coeff 2 x,coeff 3 x)=(1,1,1) at h
    simp only [Prod.mk.injEq] at h
    exact Or.inr (Or.inl (pairBD ne h.1 h.2.2))
  · have h:=remainingB hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact Or.inr (Or.inr (h.imp conicsOf conicsOf))
  · have h:=Finset.mem_singleton.mp (remainingC hi)
    change (coeff 0 x,coeff 1 x,coeff 3 x)=(2,1,1) at h
    simp only [Prod.mk.injEq] at h
    exact Or.inl (pairAB ne h.1 h.2.1)
  · have h:=Finset.mem_singleton.mp (remainingD hi)
    change (coeff 0 x,coeff 1 x,coeff 2 x)=(2,1,1) at h
    simp only [Prod.mk.injEq] at h
    exact Or.inl (pairAB ne h.1 h.2.1)

def sextic (x:ℚ):ℚ:=(2*x^2+3)*(x^2-1199)*(64*x^2+439)

theorem two_sextics {x:ℚ} (point:conics x 2 1 1 ∨ conics x 14 (-35) 7) :
    ∃Y:ℚ, Y≠0 ∧ (sextic x=2*Y^2 ∨ sextic x=(-70)*Y^2) := by
  rcases point with ⟨u,v,w,un,vn,wn,eu,ev,ew⟩|⟨u,v,w,un,vn,wn,eu,ev,ew⟩
  · refine ⟨u*v*w,by positivity,Or.inl ?_⟩
    unfold sextic;rw [eu,ev,ew];push_cast;ring
  · refine ⟨7*u*v*w,by positivity,Or.inr ?_⟩
    unfold sextic;rw [eu,ev,ew];push_cast;ring

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.five_configurations
#print axioms Sun28.FactorHeights.affine_factor
#print axioms Sun28.FactorHeights.concentrated_alternatives
#print axioms Sun28.FactorHeights.two_sextics
