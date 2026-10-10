module
public import FourPapersCommon.PartialDerivativeCommutation

@[expose] public section

/-! Genuine mixed first and third derivatives in two real parameters. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_real_parameters_commute (U : ℝ×ℝ→F) (a b : ℝ)
    (hU : ContDiffAt ℝ ∞ U (a,b)) :
    deriv (fun r=>deriv (fun θ=>U (r,θ)) b) a=
      deriv (fun θ=>deriv (fun r=>U (r,θ)) a) b :=
  partialParamSpatialDerivative_commute 1 1 U (a,b) hU

theorem deriv_real_parameters_commute_third (U : ℝ×ℝ→F) (a b : ℝ)
    (hU : ContDiffAt ℝ ∞ U (a,b)) :
    deriv (fun r=>deriv (deriv (fun θ=>U (r,θ))) b) a=
      deriv (deriv (fun θ=>deriv (fun r=>U (r,θ)) a)) b :=
  partialParamSpatialDerivative_commute_third 1 1 1 U (a,b) hU

end FourPapersCommon
