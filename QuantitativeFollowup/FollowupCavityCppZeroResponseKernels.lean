module
public import QuantitativeFollowup.FollowupCavityDecouplingStepKernel

@[expose] public section

/-! The whole normalized cavity transition splits into an independent rest
transition and scalar transition at zero incident coupling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityScalarRawDepthKernel (s : RSBScheme k) (β : ℝ) (j : ℕ) : Kernel ℝ ℝ :=
  ((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ (gaussianReal 0 1)).map
    (fun p => p.1 + Real.sqrt (β^2 * (s.q (k+2-j)-s.q (k+1-j))) * p.2)

instance cavityScalarRawDepthKernel_markov (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    IsMarkovKernel (cavityScalarRawDepthKernel s β j) := by
  unfold cavityScalarRawDepthKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem cavityScalarRawDepthKernel_apply (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    cavityScalarRawDepthKernel s β j x = (gaussianReal 0 1).map
      (fun z => x + Real.sqrt (β^2 * (s.q (k+2-j)-s.q (k+1-j))) * z) := by
  rw [cavityScalarRawDepthKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left]
  rfl

def cavityScalarDepthNormalizer (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ∫ y, Real.exp (anisotropicSchemeMass s j * cavityScalarFinite s β j y)
    ∂cavityScalarRawDepthKernel s β j x

def cavityScalarDepthKernel (s : RSBScheme k) (β : ℝ) (j : ℕ) : Kernel ℝ ℝ :=
  (cavityScalarRawDepthKernel s β j).withDensity (fun x y => ENNReal.ofReal
    (Real.exp (anisotropicSchemeMass s j * cavityScalarFinite s β j y) /
      cavityScalarDepthNormalizer s β j x))

theorem cavityScalarDepthKernel_apply (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    cavityScalarDepthKernel s β j x =
      ((gaussianReal 0 1).tilted (fun z => anisotropicSchemeMass s j *
        cavityScalarFinite s β j (x + Real.sqrt (β^2*(s.q (k+2-j)-s.q (k+1-j)))*z))).map
        (fun z => x + Real.sqrt (β^2*(s.q (k+2-j)-s.q (k+1-j)))*z) := by
  have hF := (measurable_cavityScalarFinite s β j).const_mul (anisotropicSchemeMass s j)
  have hm : Measurable (cavityScalarDepthNormalizer s β j) :=
    hF.exp.stronglyMeasurable.integral_kernel.measurable
  rw [cavityScalarDepthKernel, Kernel.withDensity_apply _
    ((hF.comp measurable_snd).exp.div (hm.comp measurable_fst)).ennreal_ofReal]
  change (cavityScalarRawDepthKernel s β j x).tilted
    (fun y => anisotropicSchemeMass s j*cavityScalarFinite s β j y) = _
  rw [cavityScalarRawDepthKernel_apply]
  exact (map_tilted_pullback (gaussianReal 0 1) _ (by fun_prop) _ hF).symm

instance cavityScalarDepthKernel_markov (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    IsMarkovKernel (cavityScalarDepthKernel s β j) := by
  constructor
  intro x
  rw [cavityScalarDepthKernel_apply]
  haveI := isProbabilityMeasure_tilted
    (integrable_exp_cavityScalarFinite_shift s β j x
      (β^2*(s.q (k+2-j)-s.q (k+1-j))) (anisotropicSchemeMass s j))
  exact (Measure.isProbabilityMeasure_map_iff
    (show Measurable (fun z : ℝ => x + Real.sqrt (β^2*(s.q (k+2-j)-s.q (k+1-j)))*z)
      from by fun_prop).aemeasurable).mpr inferInstance

def cavityIndependentParameterSplit (n : ℕ) (P : AnisotropicParameter (n+1)) :
    AnisotropicParameter n × ℝ := (cavityRestParameterProjection n P, P (Sum.inr (Fin.last n)))

theorem measurable_cavityIndependentParameterSplit (n : ℕ) :
    Measurable (cavityIndependentParameterSplit n) :=
  (cavityRestParameterProjection n).measurable.prodMk (by fun_prop)

@[simp] theorem cavityIndependentParameterSplit_point (n : ℕ)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    cavityIndependentParameterSplit n (anisotropicParameterPoint g x) =
      (anisotropicParameterPoint (cavityRestDisorderProjection n g)
        (cavityRestFieldProjection n x), x (Fin.last n)) := by
  exact Prod.ext (cavityRestParameterProjection_point n g x) rfl

theorem cavityDepthKernel_zero_product (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (j : ℕ)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    (anisotropicDepthKernel (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩) s j
      (anisotropicParameterPoint g x)).map (cavityIndependentParameterSplit n) =
    (anisotropicDepthKernel (followupCavityRestSpinModel n β ρ hβ hρ) s j
      (anisotropicParameterPoint (cavityRestDisorderProjection n g)
        (cavityRestFieldProjection n x))).prod
      (cavityScalarDepthKernel s (followupCavityScalarBeta n β ρ) j (x (Fin.last n))) := by
  let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩
  let R := followupCavityRestSpinModel n β ρ hβ hρ
  let β0 := followupCavityScalarBeta n β ρ
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
  have hc : Real.sqrt (β0^2*δ)=Real.sqrt δ*Real.sqrt (followupCavityD n β ρ) := by
    dsimp only [β0, followupCavityScalarBeta]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (followupCavityD n β ρ))]
    exact mul_comm _ _
  have hid : (fun z : QuantitativePaper.Field (n+1) => m*anisotropicFinitePotential D s j
      (P+anisotropicSchemeInput D s j z)) = F ∘ cavityFieldSplit n := by
    funext z
    dsimp only [Function.comp_def, F, Fr, Fs, P]
    rw [anisotropicSchemeInput_apply, cavityAnisotropicPoint_add_field, followupCavityFinitePotential_zero]
    rw [map_add, map_smul, cavityRestFieldProjection_noise_zero]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, D, cavityLastNoise_zero]
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
      cavityRestParameterProjection_point, map_add, map_smul, cavityRestFieldProjection_noise_zero]
    apply Prod.ext
    · rw [anisotropicSchemeInput_apply, cavityAnisotropicPoint_add_field]
      rfl
    · change x (Fin.last n) + Real.sqrt δ * (anisotropicNoiseMap D z) (Fin.last n) =
        x (Fin.last n) + Real.sqrt (β0^2*δ) * z (Fin.last n)
      rw [show (anisotropicNoiseMap D z) (Fin.last n) =
        Real.sqrt (followupCavityD n β ρ) * z (Fin.last n) from
          cavityLastNoise_zero n β ρ hβ hρ z, hc]
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
