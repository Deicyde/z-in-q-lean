import DoublingTests

namespace ZInQBlueprint.MarkedTorsion

section
variable {R : Type*} [CommRing R]

def dup (a b c:R) (p:R×R) : R×R := (N a b c p.1 p.2, D a b c p.1 p.2)
inductive Test | atStart | atDouble | atFour | threeAfterDouble
  deriving DecidableEq
def test (a b c : R) (i:Test) (u v:R) : R :=
  let p := dup a b c (u,v)
  let q := dup a b c p
  match i with
  | .atStart => F a b c u v
  | .atDouble => F a b c p.1 p.2
  | .atFour => F a b c q.1 q.2
  | .threeAfterDouble => Psi a b c p.1 p.2

end

theorem exponent_test {a b c d u v:ℚ} (dn:d≠0) (vn:v≠0)
    (P:(twist a b c d).toAffine.Point) (h:Represents P u v)
    (ord:(4:ℕ) • P=0 ∨ (6:ℕ) • P=0 ∨ (8:ℕ) • P=0) :
    ∃ j, test a b c j u v=0 := by
  let p:=dup a b c (u,v)
  let q:=dup a b c p
  have p1 : Represents (P+P) p.1 p.2 := represents_double dn P h
  have p2 : Represents ((P+P)+(P+P)) q.1 q.2 := represents_double dn _ p1
  have p3 := represents_double dn _ p2
  have step1 (z:p.2=0) : test a b c .atStart u v=0 := by
    change 4*v*F a b c u v=0 at z
    exact (mul_eq_zero.mp z).resolve_left (mul_ne_zero (by norm_num) vn)
  have step2 (z:q.2=0) : ∃ j,test a b c j u v=0 := by
    change 4*p.2*F a b c p.1 p.2=0 at z
    by_cases v0:p.2=0
    · exact ⟨.atStart,step1 v0⟩
    · exact ⟨.atDouble,(mul_eq_zero.mp z).resolve_left (mul_ne_zero (by norm_num) v0)⟩
  rcases ord with four|six|eight
  · have t : (P+P)+(P+P)=0 := by convert four using 1;abel
    rw [t] at p2;exact step2 p2
  · have t : (P+P)+(P+P)= -(P+P) := by apply eq_neg_of_add_eq_zero_left;convert six using 1;abel
    rw [t] at p2
    have same := cross dn _ ((represents_neg _).mp p2) p1
    change N a b c p.1 p.2 * p.2 = D a b c p.1 p.2 * p.1 at same
    have id:=three_identity a b c p.1 p.2
    rw [same,sub_self] at id
    by_cases v0:p.2=0
    · exact ⟨.atStart,step1 v0⟩
    · exact ⟨.threeAfterDouble,(mul_eq_zero.mp id.symm).resolve_left (neg_ne_zero.mpr v0)⟩
  · have t : ((P+P)+(P+P))+((P+P)+(P+P))=0 := by convert eight using 1;abel
    rw [t] at p3
    change 4*q.2*F a b c q.1 q.2=0 at p3
    by_cases v0:q.2=0
    · exact step2 v0
    · exact ⟨.atFour,(mul_eq_zero.mp p3).resolve_left (mul_ne_zero (by norm_num) v0)⟩

end ZInQBlueprint.MarkedTorsion
#print axioms ZInQBlueprint.MarkedTorsion.exponent_test
