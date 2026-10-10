module
public import QuantitativeFollowup.FollowupCavityDecouplingCoordinates

@[expose] public section

/-! Actual old-disorder/old-field coordinate projection of cavity parameters. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def cavityRestParameterProjection (n : ℕ) :
    AnisotropicParameter (n+1)→L[ℝ]AnisotropicParameter n :=
  LinearMap.toContinuousLinearMap
    { toFun:=fun P=>WithLp.toLp 2 (Sum.elim
        (fun e=>P (Sum.inl (cavityRestCouplingEmbedding n e)))
        (fun i=>P (Sum.inr i.castSucc)))
      map_add':=by intro P Q;ext i;cases i <;> simp
      map_smul':=by intro c P;ext i;cases i <;> simp }

@[simp] theorem cavityRestParameterProjection_point (n : ℕ)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    cavityRestParameterProjection n (anisotropicParameterPoint g x)=
      anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x) := by
  ext i
  cases i <;> rfl

end QuantitativeFollowup
