module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVariance

@[expose] public section

/-! Actual normalized transition product for the fixed rest system with
arbitrary positive last variance. Normalization is derived by Gaussian
product integration, retaining zero-mass and zero-length cells. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityLastVariance_depthKernel_product (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (b : ℝ) (hb : 0 < b) (j : ℕ)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    (anisotropicDepthKernel (cavityLastVarianceModel n β ρ hβ hρ b hb) s j
      (anisotropicParameterPoint g x)).map (cavityIndependentParameterSplit n) =
    (anisotropicDepthKernel (followupCavityRestSpinModel n β ρ hβ hρ) s j
      (anisotropicParameterPoint (cavityRestDisorderProjection n g)
        (cavityRestFieldProjection n x))).prod
      (cavityScalarDepthKernel s (Real.sqrt b) j (x (Fin.last n))) := by
  let D := cavityLastVarianceModel n β ρ hβ hρ b hb
  let R := followupCavityRestSpinModel n β ρ hβ hρ
  let β0 := Real.sqrt b
  let δ := s.q (k+2-j)-s.q (k+1-j)
  let m := anisotropicSchemeMass s j
  let P := anisotropicParameterPoint g x
  let Pr := anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)
  let Lr := anisotropicSchemeInput R s j
  let Fr := fun z : QuantitativePaper.Field n => anisotropicFinitePotential R s j (Pr+Lr z)
  let Fs := fun z : ℝ => cavityScalarFinite s β0 j (x (Fin.last n)+Real.sqrt (β0^2*δ)*z)
  let F := fun z : QuantitativePaper.Field n×ℝ => m*Fr z.1+m*Fs z.2
  have hmFr : Measurable Fr :=
    (contDiff_anisotropicFinitePotential R s j).continuous.measurable.comp
      (measurable_const.add Lr.measurable)
  have hmFs : Measurable Fs := (measurable_cavityScalarFinite s β0 j).comp (by fun_prop)
  have hmF : Measurable F :=
    ((hmFr.const_mul m).comp measurable_fst).add ((hmFs.const_mul m).comp measurable_snd)
  have hδ : 0≤δ := sub_nonneg.mpr (s.q_mono' _ (Nat.sub_le _ _) _ (by omega))
  have hc : Real.sqrt (β0^2*δ)=Real.sqrt δ*Real.sqrt (b) := by
    dsimp only [β0]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (b))]
    exact mul_comm _ _
  have hid : (fun z : QuantitativePaper.Field (n+1) => m*anisotropicFinitePotential D s j
      (P+anisotropicSchemeInput D s j z)) = F ∘ cavityFieldSplit n := by
    funext z
    dsimp only [Function.comp_def, F, Fr, Fs, P]
    rw [anisotropicSchemeInput_apply, cavityAnisotropicPoint_add_field, cavityLastVariance_finitePotential_product]
    rw [map_add, map_smul, cavityLastVariance_rest_noise]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, D, cavityLastVariance_last_noise]
    rw [hc, mul_add]
    congr 1
    · rw [anisotropicSchemeInput_apply, cavityAnisotropicPoint_add_field]
      rfl
    · congr 2
      dsimp only [cavityFieldSplit, δ]
      ring
  have ht : ((stdGaussian (QuantitativePaper.Field (n+1))).tilted
      (fun z => m*anisotropicFinitePotential D s j (P+anisotropicSchemeInput D s j z))).map
        (cavityFieldSplit n) =
      ((stdGaussian (QuantitativePaper.Field n)).tilted (fun z => m*Fr z)).prod
        ((gaussianReal 0 1).tilted (fun z => m*Fs z)) := by
    rw [hid, map_tilted_pullback _ _ (measurable_cavityFieldSplit n) F hmF,
      stdGaussian_map_cavityFieldSplit]
    change (((stdGaussian (QuantitativePaper.Field n)).prod (gaussianReal 0 1)).tilted
      (fun z => m*Fr z.1+m*Fs z.2)) = _
    exact tilted_prod_add (stdGaussian (QuantitativePaper.Field n)) (gaussianReal 0 1)
      (fun z : QuantitativePaper.Field n => m*Fr z) (fun z : ℝ => m*Fs z)
      (hmFr.const_mul m) (hmFs.const_mul m)
      (integrable_exp_finiteStateGaussian_lipschitz (anisotropicFinitePotential R s j)
        (anisotropicFinitePotential_lipschitz R s j) Lr Pr m)
      (integrable_exp_cavityScalarFinite_shift s β0 j _ (β0^2*δ) m)
  have hj : cavityIndependentParameterSplit n ∘
      (fun z : QuantitativePaper.Field (n+1) => P+anisotropicSchemeInput D s j z) =
      Prod.map (fun z : QuantitativePaper.Field n => Pr+Lr z)
        (fun z : ℝ => x (Fin.last n)+Real.sqrt (β0^2*δ)*z) ∘ cavityFieldSplit n := by
    funext z
    dsimp only [Function.comp_def, cavityIndependentParameterSplit, P, Prod.map]
    rw [anisotropicSchemeInput_apply, cavityAnisotropicPoint_add_field,
      cavityRestParameterProjection_point, map_add, map_smul, cavityLastVariance_rest_noise]
    apply Prod.ext
    · rw [anisotropicSchemeInput_apply, cavityAnisotropicPoint_add_field]
      rfl
    · change x (Fin.last n) + Real.sqrt δ * (anisotropicNoiseMap D z) (Fin.last n) =
        x (Fin.last n) + Real.sqrt (β0^2*δ) * z (Fin.last n)
      rw [show (anisotropicNoiseMap D z) (Fin.last n) =
        Real.sqrt (b) * z (Fin.last n) from
          cavityLastVariance_last_noise n β ρ hβ hρ b hb z, hc]
      ring
  change (finiteStateGaussianStepKernel m (anisotropicSchemeInput D s j)
    (anisotropicFinitePotential D s j) P).map (cavityIndependentParameterSplit n) = _
  rw [finiteStateGaussianStepKernel_apply _ _ _ (contDiff_anisotropicFinitePotential D s j).continuous.measurable,
    finiteStateGaussianStepLaw_eq_map_tilted _ _ _ (contDiff_anisotropicFinitePotential D s j).continuous.measurable,
    Measure.map_map (measurable_cavityIndependentParameterSplit n) (by fun_prop), hj,
    ←Measure.map_map (by fun_prop) (measurable_cavityFieldSplit n), ht,
    ←Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    cavityScalarDepthKernel_apply]
  change _ = (finiteStateGaussianStepKernel m Lr (anisotropicFinitePotential R s j) Pr).prod _
  rw [finiteStateGaussianStepKernel_apply _ _ _ (contDiff_anisotropicFinitePotential R s j).continuous.measurable,
    finiteStateGaussianStepLaw_eq_map_tilted _ _ _ (contDiff_anisotropicFinitePotential R s j).continuous.measurable]


end QuantitativeFollowup
