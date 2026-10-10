module
public import HexagonPaper.EdgeLikelihoodFinitePath
public import QuantitativeFollowup.AnisotropicNoiseProfileStability

@[expose] public section

/-! Uniform common-noise convergence of the actual restarted continuous
edge path under weak convergence of arbitrary deterministic profiles. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem edgeDiffusionPath_profile_norm_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) :
    ‖edgeDiffusionPath D μ g q x sample-edgeDiffusionPath D ν g q x sample‖≤
      ‖anisotropicUnitInput D‖*anisotropicNoiseProfileError D μ ν*
        Real.exp (anisotropicWhitenedDriftLip D) := by
  have hc : 0≤‖anisotropicUnitInput D‖*anisotropicNoiseProfileError D μ ν*
      Real.exp (anisotropicWhitenedDriftLip D) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (anisotropicNoiseProfileError_nonneg D μ ν))
      (Real.exp_pos _).le
  apply (ContinuousMap.norm_le _ hc).mpr
  intro r
  let t:=((r:ℝ)-(q:ℝ)).toNNReal
  have ht : t≤vectorRestartHorizon q :=
    Real.toNNReal_le_toNNReal (sub_le_sub_right r.property.2 _)
  have htr : (t:ℝ)∈Icc (0:ℝ) (1-(q:ℝ)) :=
    ⟨t.coe_nonneg,by
      have hh : (t:ℝ)≤(vectorRestartHorizon q:ℝ):=by exact_mod_cast ht
      simpa only [vectorRestartHorizon,Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)] using hh⟩
  have hb:=norm_anisotropicRestartNoiseStatePath_profile_sub_le D μ ν g q x x
    (vectorCanonicalBrownianPath sample.2) (t:ℝ) htr
  rw [anisotropicRestartNoiseStatePath_canonical D μ g q x t ht sample,
    anisotropicRestartNoiseStatePath_canonical D ν g q x t ht sample,
    sub_self,norm_zero,zero_add] at hb
  change ‖(anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartState D μ g q x t sample))-
    (anisotropicDisorderInjection n g+anisotropicUnitInput D
      (anisotropicRestartState D ν g q x t sample))‖≤_
  rw [add_sub_add_left_eq_sub,←map_sub]
  exact ((anisotropicUnitInput D).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring))

theorem tendsto_edgeDiffusionPath_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>edgeDiffusionPath D (μ j) g q x sample) l
      (𝓝 (edgeDiffusionPath D ν g q x sample)) := by
  have he : Tendsto (fun j=>‖anisotropicUnitInput D‖*anisotropicNoiseProfileError D (μ j) ν*
      Real.exp (anisotropicWhitenedDriftLip D)) l (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using
      ((tendsto_anisotropicNoiseProfileError D μ ν
        (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ)).const_mul
          ‖anisotropicUnitInput D‖).mul_const (Real.exp (anisotropicWhitenedDriftLip D))
  have hh:=squeeze_zero (fun j=>norm_nonneg _)
    (fun j=>edgeDiffusionPath_profile_norm_sub_le D (μ j) ν g q x sample) he
  exact tendsto_of_tendsto_of_dist tendsto_const_nhds (by
    simpa only [dist_eq_norm,norm_sub_rev,Function.comp_def] using hh)

end HexagonPaper
