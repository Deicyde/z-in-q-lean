import LastWildSlope
import Mathlib.Tactic

namespace ZInQBlueprint.WildLevel
noncomputable section

/-- An entry in the positive part of a finite lower ramification filtration:
the group order and the codimension of the subspace fixed by that group. -/
structure WildEntry where
  order : ℕ
  codim : ℕ
  positive : 0<order
  dimension : codim≤2

def orders (s : List WildEntry) := s.map WildEntry.order
def swanNumerator (s : List WildEntry) := (s.map fun row=>row.order*row.codim).sum

theorem swan_rank_two (s : List WildEntry) : swanNumerator s≤2*herbrandNumerator (orders s) := by
  induction s with
  | nil => simp [swanNumerator,orders,herbrandNumerator]
  | cons r t ih =>
    have h:=Nat.mul_le_mul_left r.order r.dimension
    simp only [swanNumerator,orders,herbrandNumerator,List.map_cons,List.sum_cons,mul_add] at ih ⊢
    omega

/-- Data read from the finite residual extension and the rank-two inertia
action. The tame term is computed on the full representation. Positive
groups in the residual field detect the wild action. The wild constructor
records the different of the two levels of a last-group degree-p tower. -/
inductive LowerInertia (p wildOrder a : ℕ) : Prop
  | tame (unramifiedWild : wildOrder=1) (t : ℕ) (tameDim : t≤2) (artin : a=t)
  | wild (m e₀ d₀ d₁ t : ℕ) (s : List WildEntry) (wildSize : wildOrder=p^m)
      (baseIndex : 0<e₀) (positiveWild : 0<m) (tameDim : t≤2)
      (artin : p*e₀*a=p*e₀*t+swanNumerator s)
      (differentTower : p*e₀-1+((orders s).map (·-1)).sum=d₁+p*d₀)
      (cyclicDifferent : d₁=(s.length+1)*(p-1))
      (baseDifferent : d₀≤e₀-1+e₀*(m-1)) (upperDifferent : d₁≤p-1+p*e₀)

theorem tame_conductor {p a : ℕ} (hp : 2≤p) (data : LowerInertia p 1 a) : a≤2 := by
  cases data with
  | tame _ t dim formula => omega
  | wild m _ _ _ _ _ eqn _ pos _ _ _ _ _ _ =>
    have h : p≤p^m := by simpa using Nat.pow_le_pow_right (by omega : 0<p) (show 1≤m by omega)
    omega

theorem dyadic_conductor {k a : ℕ} (small : k≤16) (data : LowerInertia 2 k a) : a≤12 := by
  cases data with
  | tame _ t dim formula => omega
  | wild m e₀ d₀ d₁ t s size he hm ht artin htower hcyc hbase htop =>
    have mBound : m≤4 := by
      by_contra! h
      have power:=Nat.pow_le_pow_right (by decide : 0<2) (show 5≤m by omega)
      omega
    have pos : ∀ n∈orders s,1≤n := by
      intro n hn
      obtain ⟨r,_,rfl⟩:=List.mem_map.mp hn
      exact r.positive
    have slope:=last_slope (p:=2) (e₀:=e₀) (m:=m) (d₀:=d₀) (d₁:=d₁) (orders s)
      (by decide) he hm pos htower (by simpa [orders] using hcyc) hbase htop
    have wildBound := swan_rank_two s
    have full : 2*e₀*a≤2*(2*e₀+herbrandNumerator (orders s)) := by
      have h := Nat.mul_le_mul_left (2*e₀) ht
      rw [artin]
      omega
    have bound:=conductor_from_last (p:=2) (e₀:=e₀) (m:=m) (a:=a) (orders s)
      (by decide) he slope full
    omega

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.swan_rank_two
#print axioms ZInQBlueprint.WildLevel.tame_conductor
#print axioms ZInQBlueprint.WildLevel.dyadic_conductor
