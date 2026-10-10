module
public import QuantitativeFollowup.AnisotropicMeasureDerivative
public import FourPapersCommon.FiniteStateCascadeAllJets
public import FourPapersCommon.SmoothUniformLimit

@[expose] public section

/-! The actual arbitrary-profile anisotropic root potential is spatially
smooth, with genuine positive jets bounded independently of profile depth.
Every jet is identified from the checked dyadic uniform approximation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k:ℕ}

def anisotropicSpatialJetBound (D:AnisotropicSpinModel n)(r:ℕ):ℝ:=
  finiteStateSpatialJetBound (Configuration n) n r*‖anisotropicEnergyMap D‖^r

theorem anisotropicSpatialJetBound_nonneg (D:AnisotropicSpinModel n)(r:ℕ):
    0≤anisotropicSpatialJetBound D r:=by
  exact mul_nonneg (finiteStateSpatialJetBound_nonneg _ _ _) (by positivity)

theorem norm_anisotropicFinitePotential_jet_le_uniform (D:AnisotropicSpinModel n)
    (s:RSBScheme k)(j r:ℕ)(hr:1≤r)(P:AnisotropicParameter n):
    ‖iteratedFDeriv ℝ r (anisotropicFinitePotential D s j) P‖≤anisotropicSpatialJetBound D r:=by
  let L:=fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)
  let F:=finiteStateGaussianTerminalCascade (fun _:Configuration n=>0) (anisotropicSchemeMass s) L j
  have hdec:Antitone (anisotropicSchemeMass s):=
    antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s)
  change ‖iteratedFDeriv ℝ r (F ∘ anisotropicEnergyMap D) P‖≤_
  rw [(anisotropicEnergyMap D).iteratedFDeriv_comp_right
    (contDiff_finiteStateGaussianTerminalCascade _ _ (anisotropicSchemeMass_nonneg s) L j) P (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right
    (norm_finiteStateCascade_jet_le_uniform _ _ (anisotropicSchemeMass_nonneg s)
      (anisotropicSchemeMass_le_one s 0) hdec L j r hr _) (by positivity)

theorem anisotropicMeasurePotential_spatialSmooth_and_jets (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure):
    ContDiff ℝ ∞ (anisotropicMeasurePotential D μ) ∧
    ∀r,TendstoUniformly (fun j=>iteratedFDeriv ℝ r (anisotropicDyadicPotential D μ j))
      (iteratedFDeriv ℝ r (anisotropicMeasurePotential D μ)) atTop:=by
  exact contDiff_uniformLimit_of_uniform_jet_bounds (anisotropicDyadicPotential D μ)
    (anisotropicMeasurePotential D μ)
    (fun j=>contDiff_anisotropicFinitePotential D _ _) (anisotropicSpatialJetBound D)
    (anisotropicSpatialJetBound_nonneg D)
    (fun r hr j P=>norm_anisotropicFinitePotential_jet_le_uniform D _ _ r (by omega) P)
    (tendstoUniformly_anisotropicDyadicPotential D μ)

theorem contDiff_anisotropicMeasurePotential (D:AnisotropicSpinModel n)(μ:Paper.ParisiMeasure):
    ContDiff ℝ ∞ (anisotropicMeasurePotential D μ):=
  (anisotropicMeasurePotential_spatialSmooth_and_jets D μ).1

theorem norm_anisotropicMeasurePotential_jet_le_uniform (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure)(r:ℕ)(hr:1≤r)(P:AnisotropicParameter n):
    ‖iteratedFDeriv ℝ r (anisotropicMeasurePotential D μ) P‖≤anisotropicSpatialJetBound D r:=by
  apply le_of_tendsto (((anisotropicMeasurePotential_spatialSmooth_and_jets D μ).2 r).tendsto_at P).norm
  exact Eventually.of_forall fun j=>norm_anisotropicFinitePotential_jet_le_uniform D _ _ r hr P

end QuantitativeFollowup
