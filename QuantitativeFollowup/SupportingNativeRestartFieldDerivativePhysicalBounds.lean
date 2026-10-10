module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativePhysical
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeAffine

@[expose] public section

/-! Common field moduli for the actual finite continuation-square functions.
They depend on the model and feature, and not on profile depth or nodes. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

def anisotropicRestartFieldEnergyMap (D : AnisotropicSpinModel n) :
    Field n→L[ℝ]FiniteStateField (Configuration n) :=
  (anisotropicEnergyMap D).comp (anisotropicFieldInjection n)

theorem anisotropicFiniteRestartPosteriorSquare_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (v : ℕ) (i : Fin n) :
    LipschitzWith (4*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊)
      (anisotropicFiniteRestartPosteriorSquare D s g q v i) := by
  let cs:=vectorClampedScheme s q q.property
  let L:=fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l)
  let G:=fun H=>∫z,cascadePosteriorRetainedSquare (fun _ : Configuration n=>0)
    (anisotropicSchemeMass cs) L (k+2) v (cavityCoordinateFeature i) H z
    ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass cs) L (k+2) H
  let c:=anisotropicEnergyMap D (anisotropicDisorderInjection n g)
  let A:=anisotropicRestartFieldEnergyMap D
  have he : anisotropicFiniteRestartPosteriorSquare D s g q v i=(fun x=>G (c+A x)) := by
    funext x
    simp only [anisotropicFiniteRestartPosteriorSquare,G,c,A,anisotropicRestartFieldEnergyMap,map_add,
      ContinuousLinearMap.comp_apply,cs,L]
  rw [he]
  have hA : LipschitzWith ‖A‖₊ (fun x=>c+A x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm,add_sub_add_left_eq_sub,←map_sub,coe_nnnorm] using A.le_opNorm (x-y)
  exact (cascadePosterior_retained_square_lipschitz (fun _ : Configuration n=>0)
    (anisotropicSchemeMass cs) (anisotropicSchemeMass_nonneg cs) (anisotropicSchemeMass_le_one cs 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step cs)) L (k+2) v (cavityCoordinateFeature i)).comp
      hA

theorem anisotropicFiniteRestartPosteriorSquare_differential_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (v : ℕ) (i : Fin n) :
    LipschitzWith (31*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊^2)
      (fderiv ℝ (anisotropicFiniteRestartPosteriorSquare D s g q v i)) := by
  let cs:=vectorClampedScheme s q q.property
  let L:=fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l)
  let G:=fun H=>∫z,cascadePosteriorRetainedSquare (fun _ : Configuration n=>0)
    (anisotropicSchemeMass cs) L (k+2) v (cavityCoordinateFeature i) H z
    ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass cs) L (k+2) H
  let c:=anisotropicEnergyMap D (anisotropicDisorderInjection n g)
  let A:=anisotropicRestartFieldEnergyMap D
  have hG : Differentiable ℝ G := fun H=>(hasFDerivAt_cascadePosterior_retained_square
    (fun _ : Configuration n=>0) (anisotropicSchemeMass cs) (anisotropicSchemeMass_nonneg cs)
    (anisotropicSchemeMass_le_one cs 0) (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step cs))
    L (k+2) v (cavityCoordinateFeature i) H).differentiableAt
  have he : anisotropicFiniteRestartPosteriorSquare D s g q v i=(fun x=>G (c+A x)) := by
    funext x
    simp only [anisotropicFiniteRestartPosteriorSquare,G,c,A,anisotropicRestartFieldEnergyMap,map_add,
      ContinuousLinearMap.comp_apply,cs,L]
  rw [he]
  exact fderiv_affine_pullback_lipschitz G hG _
    (cascadePosterior_retained_square_differential_lipschitz (fun _ : Configuration n=>0)
      (anisotropicSchemeMass cs) (anisotropicSchemeMass_nonneg cs) (anisotropicSchemeMass_le_one cs 0)
      (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step cs)) L (k+2) v (cavityCoordinateFeature i)) A c

end QuantitativeFollowup
