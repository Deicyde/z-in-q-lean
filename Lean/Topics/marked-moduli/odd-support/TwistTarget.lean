import PublicTwistHeight
import ZInQKernel.MainGreenTao

/-! The fixed-curve height hypothesis occupies precisely the six-contact slot
of the frozen public theorem. -/
namespace ZInQBlueprint.OddSupport

theorem frozenTarget_of_twistBound
    (estimate : TwistBound publicTwistConstant) (rank : ZInQ.CertifiedRank) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank
    (sixContactMin_of_twistBound estimate) rank

#print axioms frozenTarget_of_twistBound
end ZInQBlueprint.OddSupport
