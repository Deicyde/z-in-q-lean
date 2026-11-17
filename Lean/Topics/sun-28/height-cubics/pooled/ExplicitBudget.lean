import CutoffPool

namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres
noncomputable section

/-- The exact low-prime contribution, the equality O=O15 O3, and a
five-chart average remove the two classifications of odd prime order. -/
theorem chart_of_classes {A B:ℤ} (cop:Int.gcd A B=1)
    (budget:35^5*classProduct oldCutoff .evenNoncube A B^3*classProduct oldCutoff .evenCube A B≤
      6^5*heightRadical A B^110*classProduct oldCutoff .oddCube A B^2) : ChartTest A B := by
  let L:=lowWeight A B
  let O:=classProduct oldCutoff .oddNoncube A B
  let J:=classProduct oldCutoff .oddCube A B
  let H:=classProduct oldCutoff .evenNoncube A B
  let F:=classProduct oldCutoff .evenCube A B
  let T:=heightRadical A B
  let C:=cutoffProduct
  have odd:oddProduct A B=O*J:=odd_classes cop
  have ident:T=C*(O*J):=by change cutoffProduct*oddProduct A B=_;rw [odd]
  have fac:weight A B=L*(O^5*J^3*H^3*F):=split_weight A B
  have lim:210^5*L≤C^5:=low_weight_bound cop
  have h:35^5*(H^3*F)≤6^5*T^110*J^2:=by simpa only [Nat.mul_assoc] using budget
  have s:1225^5*L*(H^3*F)≤C^5*T^110*J^2:=by
    have scaled:=Nat.mul_le_mul_left (35^5*L) h
    have left:1225^5*L*(H^3*F)=(35^5*L)*(35^5*(H^3*F)):=by ring
    have right:(35^5*L)*(6^5*T^110*J^2)=(210^5*L)*(T^110*J^2):=by ring
    rw [←left,right] at scaled
    exact scaled.trans ((Nat.mul_le_mul_right _ lim).trans_eq (by ring))
  apply chart_of_product
  rw [fac]
  calc
    1225^5*(L*(O^5*J^3*H^3*F))=(1225^5*L*(H^3*F))*(O^5*J^3):=by ring
    _ ≤ (C^5*T^110*J^2)*(O^5*J^3):=Nat.mul_le_mul_right _ s
    _ = T^110*(C*(O*J))^5:=by ring
    _ = T^115:=by rw [←ident];ring

theorem failure_classes {A B:ℤ} (cop:Int.gcd A B=1) (fail:¬ChartTest A B) :
    6^5*heightRadical A B^110*classProduct oldCutoff .oddCube A B^2 <
      35^5*classProduct oldCutoff .evenNoncube A B^3*classProduct oldCutoff .evenCube A B :=
  lt_of_not_ge (fun h=>fail (chart_of_classes cop h))

/-- The published-cutoff version in the preceding independent review. -/
theorem review_test {A B:ℤ} (cop:Int.gcd A B=1)
    (budget:classProduct oldCutoff .evenNoncube A B^3*classProduct oldCutoff .evenCube A B≤
      36^5*heightRadical A B^105*oddProduct A B^5*classProduct oldCutoff .oddCube A B^2) :
    ChartTest A B := by
  apply chart_of_classes cop
  let T:=heightRadical A B
  let O:=oddProduct A B
  let J:=classProduct oldCutoff .oddCube A B
  have co:210≤cutoffProduct:=by rw [←core_product];exact support_mono core_subset (fun _ m=>(Finset.mem_filter.mp m).2)
  have a:210*O≤T:=Nat.mul_le_mul_right O co
  have power:(210*O)^5≤T^5:=Nat.pow_le_pow_left a 5
  calc
    _=35^5*(classProduct oldCutoff .evenNoncube A B^3*classProduct oldCutoff .evenCube A B):=by ring
    _ ≤35^5*(36^5*T^105*O^5*J^2):=Nat.mul_le_mul_left _ budget
    _ =6^5*T^105*J^2*(210*O)^5:=by ring
    _ ≤6^5*T^105*J^2*T^5:=Nat.mul_le_mul_left _ power
    _ =6^5*T^110*J^2:=by ring

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.chart_of_classes
#print axioms Sun28.HeightCubics.Pooled.failure_classes
#print axioms Sun28.HeightCubics.Pooled.review_test
