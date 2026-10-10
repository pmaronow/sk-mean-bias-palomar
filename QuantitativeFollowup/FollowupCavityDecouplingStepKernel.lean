module
public import QuantitativeFollowup.FollowupCavityDecouplingFinite
public import QuantitativeFollowup.FollowupCavityDecouplingParameter
public import FourPapersCommon.IndependentProductTilt
public import FourPapersCommon.TiltedPushforward

@[expose] public section

/-! The actual normalized Gaussian transition, projected to the old fields,
is exactly the rest transition. All masses and zero increments are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 150000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

 theorem cavityDepthKernel_rest_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) :
    (anisotropicDepthKernel (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) s j
      (anisotropicParameterPoint g x)).map (cavityRestParameterProjection n)=
      anisotropicDepthKernel (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)) := by
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩
  let R:=followupCavityRestSpinModel n β ρ hβ hρ
  let β0:=followupCavityScalarBeta n β ρ
  let δ:=s.q (k+2-j)-s.q (k+1-j)
  let m:=anisotropicSchemeMass s j
  let P:=anisotropicParameterPoint g x
  let Pr:=anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)
  let Lr:=anisotropicSchemeInput R s j
  let Fr:=fun z : QuantitativePaper.Field n=>anisotropicFinitePotential R s j (Pr+Lr z)
  let Fs:=fun z : ℝ=>cavityScalarFinite s β0 j (x (Fin.last n)+Real.sqrt (β0^2*δ)*z)
  let F:=fun z : QuantitativePaper.Field n×ℝ=>m*Fr z.1+m*Fs z.2
  have hmFr : Measurable Fr :=
    (contDiff_anisotropicFinitePotential R s j).continuous.measurable.comp
      (measurable_const.add Lr.measurable)
  have hmFs : Measurable Fs := (measurable_cavityScalarFinite s β0 j).comp
    (show Measurable (fun z : ℝ=>x (Fin.last n)+Real.sqrt (β0^2*δ)*z) from by fun_prop)
  have hmF : Measurable F :=
    ((hmFr.const_mul m).comp measurable_fst).add ((hmFs.const_mul m).comp measurable_snd)
  have hδ : 0≤δ:=sub_nonneg.mpr (s.q_mono' _ (Nat.sub_le _ _) _ (by omega))
  have hc : Real.sqrt (β0^2*δ)=Real.sqrt δ*Real.sqrt (followupCavityD n β ρ) := by
    dsimp only [β0,followupCavityScalarBeta]
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (followupCavityD n β ρ))]
    exact mul_comm _ _
  have hid : (fun z : QuantitativePaper.Field (n+1)=>m*anisotropicFinitePotential D s j
      (P+anisotropicSchemeInput D s j z))=F ∘ cavityFieldSplit n := by
    funext z
    dsimp only [Function.comp_def,F,Fr,Fs,P]
    rw [anisotropicSchemeInput_apply,cavityAnisotropicPoint_add_field,
      followupCavityFinitePotential_zero]
    rw [map_add,map_smul,cavityRestFieldProjection_noise_zero]
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,D,cavityLastNoise_zero]
    rw [hc,mul_add]
    congr 1
    · rw [anisotropicSchemeInput_apply,cavityAnisotropicPoint_add_field]
      rfl
    · congr 2
      dsimp only [cavityFieldSplit,δ]
      ring
  have heFr:=integrable_exp_finiteStateGaussian_lipschitz (anisotropicFinitePotential R s j)
    (anisotropicFinitePotential_lipschitz R s j) Lr Pr m
  have heFs:=integrable_exp_cavityScalarFinite_shift s β0 j (x (Fin.last n)) (β0^2*δ) m
  have hmr : Measurable (fun z : QuantitativePaper.Field n=>m*Fr z) :=hmFr.const_mul m
  have hms : Measurable (fun z : ℝ=>m*Fs z) :=hmFs.const_mul m
  have ht : ((stdGaussian (QuantitativePaper.Field (n+1))).tilted
      (fun z=>m*anisotropicFinitePotential D s j (P+anisotropicSchemeInput D s j z))).map
        (cavityRestFieldProjection n)=
      (stdGaussian (QuantitativePaper.Field n)).tilted (fun z=>m*Fr z) := by
    rw [hid]
    have hproj : cavityRestFieldProjection n=Prod.fst ∘ cavityFieldSplit n:=rfl
    rw [hproj,←Measure.map_map measurable_fst (measurable_cavityFieldSplit n),
      map_tilted_pullback _ _ (measurable_cavityFieldSplit n) F hmF,
      stdGaussian_map_cavityFieldSplit]
    change (((stdGaussian (QuantitativePaper.Field n)).prod (gaussianReal 0 1)).tilted
      (fun z=>m*Fr z.1+m*Fs z.2)).map Prod.fst=_
    exact tilted_prod_add_map_fst (stdGaussian (QuantitativePaper.Field n)) (gaussianReal 0 1)
      (fun z : QuantitativePaper.Field n=>m*Fr z) (fun z : ℝ=>m*Fs z) hmr hms heFr heFs
  have hj : (cavityRestParameterProjection n) ∘
      (fun z : QuantitativePaper.Field (n+1)=>P+anisotropicSchemeInput D s j z)=
      (fun z : QuantitativePaper.Field n=>Pr+Lr z) ∘ cavityRestFieldProjection n := by
    funext z
    dsimp only [Function.comp_def,P,Pr,Lr]
    rw [anisotropicSchemeInput_apply,cavityAnisotropicPoint_add_field,
      cavityRestParameterProjection_point,map_add,map_smul,cavityRestFieldProjection_noise_zero,
      anisotropicSchemeInput_apply,cavityAnisotropicPoint_add_field]
  change (finiteStateGaussianStepKernel m (anisotropicSchemeInput D s j)
      (anisotropicFinitePotential D s j) P).map (cavityRestParameterProjection n)=
      finiteStateGaussianStepKernel m Lr (anisotropicFinitePotential R s j) Pr
  rw [finiteStateGaussianStepKernel_apply _ _ _ (contDiff_anisotropicFinitePotential D s j).continuous.measurable,
    finiteStateGaussianStepKernel_apply _ _ _ (contDiff_anisotropicFinitePotential R s j).continuous.measurable,
    finiteStateGaussianStepLaw_eq_map_tilted _ _ _ (contDiff_anisotropicFinitePotential D s j).continuous.measurable,
    finiteStateGaussianStepLaw_eq_map_tilted _ _ _ (contDiff_anisotropicFinitePotential R s j).continuous.measurable,
    Measure.map_map (cavityRestParameterProjection n).measurable (by fun_prop),hj,
    ←Measure.map_map (by fun_prop) (cavityRestFieldProjection n).measurable,ht]

end QuantitativeFollowup
