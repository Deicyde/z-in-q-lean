import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Projective configurations modulo 17. A projectivity is determined by
the images of three points. Only the 120 ordered triples of distinct
points of the six-set are needed in each test. -/
namespace ZInQBlueprint.OddBranchPullback.ModSeventeen

abbrev F := ZMod 17
abbrev Point := F × F

def infinity : Point := (1,0)
def affine (x : F) : Point := (x,1)
def six : List Point := [infinity, affine (-3), affine (-1), affine 0, affine 1, affine 3]
def five : List Point := [infinity, affine 0, affine 1, affine 4, affine 10]
def line : List Point := infinity :: (List.finRange 17).map (fun x => affine (x.val : F))

structure Matrix2 where
  a : F
  b : F
  c : F
  d : F

def act (M : Matrix2) (x : Point) : Point := (M.a*x.1+M.b*x.2,M.c*x.1+M.d*x.2)
def cross (x y : Point) : F := x.1*y.2-x.2*y.1
def adj (M : Matrix2) : Matrix2 := ⟨M.d,-M.b,-M.c,M.a⟩
def multiply (M N : Matrix2) : Matrix2 :=
  ⟨M.a*N.a+M.b*N.c,M.a*N.b+M.b*N.d,M.c*N.a+M.d*N.c,M.c*N.b+M.d*N.d⟩

/-- Matrix sending an ordered triple to 0, 1, ∞. It is invertible when
the three points are distinct. Its adjugate is its projective inverse. -/
def frame (z o p : Point) : Matrix2 :=
  ⟨z.2*cross o p,-z.1*cross o p,p.2*cross o z,-p.1*cross o z⟩

def frames : List Matrix2 := do
  let z ← six
  let o ← six
  let p ← six
  guard (cross z o != 0 && cross o p != 0 && cross p z != 0)
  return adj (frame z o p)

def imageIn (M : Matrix2) (S : List Point) (x : Point) : Bool :=
  S.any (fun y => cross (act M x) y == 0)

def fixes (M : Matrix2) (x : Point) : Bool := cross (act M x) x == 0

def embeddings : List Matrix2 :=
  (frames.map (fun M => multiply M (frame infinity (affine 0) (affine 1)))).filter
    (fun M => five.all (imageIn M six))

def involutions : List Matrix2 :=
  (frames.map (fun M => multiply M (frame infinity (affine (-3)) (affine (-1))))).filter
    (fun M => M.a+M.d == 0 && six.all (imageIn M six) && !(six.any (fixes M)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
/-- The trace-zero test picks nontrivial projective involutions in odd
characteristic. Every listed frame is invertible. -/
theorem contact_map_counts : frames.length = 120 ∧ embeddings.length = 0 ∧
    involutions.length = 4 ∧ (involutions.filter (fun M => line.any (fixes M))).length = 0 := by
  decide

end ZInQBlueprint.OddBranchPullback.ModSeventeen
#print axioms ZInQBlueprint.OddBranchPullback.ModSeventeen.contact_map_counts
