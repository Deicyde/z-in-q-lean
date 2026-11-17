import TriChain8
open ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 1300000
def boundAt (i : Nat) := inside i=true → i∉([120,121,189,175,188,190,197,198,186,187,199,142,191,180,181,192,78,79,193,182,183,194,88,89,195,196,184,185,201,200,202,130,131,132,145,146,209,210,211,154,203,204,205,206,207,208,213,212,214,133,134,157,158,221,222,223,166,215,216,217,218,219,220,225,224,226,169,178,179,94,95,100,101]:List Nat) → 1≤code i ∧ code i≤153 ∧ back (code i)=i
theorem range0 : ∀ j : Fin 8, boundAt (j.val+0) := by unfold boundAt; decide
theorem range8 : ∀ j : Fin 8, boundAt (j.val+8) := by unfold boundAt; decide
theorem range16 : ∀ j : Fin 8, boundAt (j.val+16) := by unfold boundAt; decide
theorem range24 : ∀ j : Fin 8, boundAt (j.val+24) := by unfold boundAt; decide
theorem range32 : ∀ j : Fin 8, boundAt (j.val+32) := by unfold boundAt; decide
theorem range40 : ∀ j : Fin 8, boundAt (j.val+40) := by unfold boundAt; decide
theorem range48 : ∀ j : Fin 8, boundAt (j.val+48) := by unfold boundAt; decide
theorem range56 : ∀ j : Fin 8, boundAt (j.val+56) := by unfold boundAt; decide
theorem range64 : ∀ j : Fin 8, boundAt (j.val+64) := by unfold boundAt; decide
theorem range72 : ∀ j : Fin 8, boundAt (j.val+72) := by unfold boundAt; decide
end Triangular.Data
