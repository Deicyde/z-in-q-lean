import RealizeEight
import PreparedExample
import HeegnerSupport

namespace Sun28.SelmerRealization
open Sun28.PointFibres Sun28.PairedClasses Sun28.PreparedPoles Sun28.PrescribedPoints
  Sun28.TwistExtension Sun28.Ordinary Sun28.SupportMatrix
noncomputable section

def multiplier : ℕ := 25815704738179
def n : ℕ := 13588380161692636619

theorem n_shape : n=526361*multiplier ∧ Squarefree n ∧ n%12=11 ∧ n.Coprime (6*526681) := by
  refine ⟨by decide,?_,by decide,by decide⟩
  rw [show n=11*(109*(439*(283*(1433*(4373*14557))))) by decide]
  simp only [Nat.squarefree_mul_iff]
  exact ⟨by decide,(show Nat.Prime 11 by norm_num).squarefree,by decide,
    (show Nat.Prime 109 by norm_num).squarefree,by decide,(show Nat.Prime 439 by norm_num).squarefree,
    by decide,(show Nat.Prime 283 by norm_num).squarefree,by decide,(show Nat.Prime 1433 by norm_num).squarefree,
    by decide,(show Nat.Prime 4373 by norm_num).squarefree,(show Nat.Prime 14557 by norm_num).squarefree⟩

/-- The point on the second twist, with its square root of x divided by b. -/
theorem explicit_second :
    let t : ℚ := 7666895317 / 2
    let y : ℚ := 91438563476392049667809999316240290757 / 8
    t ≠ 0 ∧ y ≠ 0 ∧ y^2=(526361*t^2)*(526361*t^2-(n:ℚ)*526681)*
      (526361*t^2+3*((n:ℚ)*526681)) := by norm_num [n]

theorem fixed_of_first (pt : MarkedCover (526361:ℚ) n) :
    NonzeroPair (526361:ℚ) 526681 ∧ Realized 526361 526681 := by
  obtain ⟨u,v,w,un,vn,wn,one,two⟩ :=
    cover_affine (b:=526361) (l:=(n:ℚ)) (by norm_num) (by norm_num [n])
      (by norm_num) (by norm_num [n]) pt
  have eq : ((526361:ℚ)*u*v*w)^2=(526361*u^2)*(526361*u^2-n)*(526361*u^2+3*n) := by
    rw [one,two];ring
  obtain ⟨tn,yn,second⟩ := explicit_second
  refine ⟨⟨n,u,7666895317/2,526361*u*v*w,91438563476392049667809999316240290757/8,
    by norm_num [n],un,tn,mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) un) vn) wn,yn,eq,second⟩,
    n,by decide,n_shape.2.1,n_shape.2.2.2,⟨u,526361*u*v*w,un,eq⟩,
    7666895317/2,91438563476392049667809999316240290757/8,tn,?_⟩
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using second

theorem fixed_of_eight (separates : KummerSeparation n) (finite : FiniteDescent n 526361 1)
    (eight : EightPointClasses n) :
    NonzeroPair (526361:ℚ) 526681 ∧ Realized 526361 526681 :=
  fixed_of_first (marked_of_descent (by decide) separates eight finite)

theorem prepared_scalar_of_eight (separates : KummerSeparation n)
    (finite : FiniteDescent n 526361 1) (eight : EightPointClasses n) :
    ∃ e z : ℚ, poleBranch 15 pole e z := by
  have h := prescribed_classes
  obtain ⟨u,un,U⟩ := h.beta_scale
  obtain ⟨v,vn,V⟩ := h.theta_scale
  exact (branch_iff_surface (by exact_mod_cast h.beta_positive) (by exact_mod_cast h.theta_positive.ne') un vn U V).mpr
    ((surface_iff_one_or_nonzero (by exact_mod_cast h.beta_positive) (by exact_mod_cast h.theta_positive.ne')).mpr
      (Or.inr (fixed_of_eight separates finite eight).1))

end
end Sun28.SelmerRealization
#print axioms Sun28.SelmerRealization.n_shape
#print axioms Sun28.SelmerRealization.explicit_second
#print axioms Sun28.SelmerRealization.fixed_of_first
#print axioms Sun28.SelmerRealization.fixed_of_eight
#print axioms Sun28.SelmerRealization.prepared_scalar_of_eight
